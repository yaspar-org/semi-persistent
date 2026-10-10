// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E-graph export: write the whole graph as JSON for an external extractor.
//!
//! Extraction inside Semper minimizes an additive per-node cost ([`crate::extract`]).
//! A cost that is not additive — one that depends on a node's siblings, or on which
//! subterms the result shares — cannot be expressed that way, so the consumer of this
//! format is an extractor that runs outside the engine and reads the saturated graph.
//!
//! The shape is the one `egglog --to-json` produces, with one addition: an AC node
//! writes each child once and its multiplicity in `"mults"`, parallel to `"children"`.
//! A child is never listed once per occurrence. A tool written against the egglog format
//! reads every other node without changes; for an AC node it reads a missing `"mults"`
//! entry as a count of one, which is the egglog reading of a child listed once.
//!
//! ```json
//! {
//!   "nodes": { "<node id>": { "op": "...", "children": ["<node id>", ...],
//!                             "mults": [1, ...],
//!                             "eclass": "<class id>", "cost": 1.0,
//!                             "subsumed": false } },
//!   "class_data": { "<class id>": { "type": "<sort name>" } },
//!   "op_kinds": { "<op name>": "plain" | "comm" | "a" | "ac" | "aci" | "lit" },
//!   "root_eclasses": ["<class id>"]
//! }
//! ```
//!
//! Names and orders come from the content colouring (`crate::canon_colour`): a class
//! is `{sort}-{colour}`, a node `n{colour}-{sort}`, nodes and classes are written in
//! name order, and an AC, ACI, or commutative node's children in name order. Two runs
//! that build the same e-graph therefore write the same bytes
//! (`doc/goal-stable-extraction.md`, step 2). `class_data` carries each class's
//! `colour`.
//!
//! An e-node stores child *classes*, not child nodes, so each entry in `children`
//! names one member of the child class: the member whose name sorts first. A consumer
//! that needs the child's class reads that member's `eclass`. A consumer that needs a *value* stored under the child,
//! such as the bounds of an interval, is reading a literal-carrying node, and
//! `duplicate_literal_classes` reports whether any class held two distinct such
//! nodes — the one case where naming a single member would lose information.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use crate::registry::OpKind;
use std::collections::BTreeMap;
use std::fmt::Write;

/// What [`EGraph::to_egraph_json`] wrote, for a caller that wants to report on it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DumpStats {
    pub nodes: usize,
    pub classes: usize,
    /// Classes holding more than one literal-carrying node. Zero in the expected
    /// case; a nonzero count means a consumer reading a value through a child
    /// reference could read a different member than the one the parent was built
    /// with.
    pub duplicate_literal_classes: usize,
    /// Refinement rounds the content colouring ran (`crate::canon_colour`).
    pub colour_rounds: usize,
    /// Groups of more than one class sharing a content colour (structurally symmetric
    /// classes, `doc/goal-stable-extraction.md` decision 4). Zero on the corpus.
    pub symmetric_groups: usize,
}

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    /// Serialize the graph, marking `root`'s class as the root e-class.
    ///
    /// Every name and every order in the output comes from the content colouring
    /// (`crate::canon_colour`, `doc/goal-stable-extraction.md` decision 2), so two runs
    /// that build the same e-graph write the same bytes, whatever ids they allocated.
    pub fn to_egraph_json(&self, root: Cfg::G) -> (String, DumpStats) {
        // A congruent duplicate is omitted, not emitted with a flag: children are named
        // by class here, so its entry would be identical to its twin's and would only
        // inflate a consumer's node count and per-class choice set. The `FLAG_CONGRUENT_DUP` invariant keeps every class non-empty.
        // The colouring's members are exactly the nodes written.
        let colouring = self.canon_colours();
        let members = &colouring.members;
        let mut stats = DumpStats {
            // The nodes written: the colouring's members, which omit congruent duplicates.
            // `self.len()` counted those too (bug #9: 4 where the dump wrote 3).
            nodes: members.iter().map(Vec::len).sum(),
            classes: members.len(),
            duplicate_literal_classes: 0,
            colour_rounds: colouring.rounds,
            symmetric_groups: colouring.symmetric_groups(),
        };
        for v in members {
            if v.iter().filter(|&&id| self.node_lit(id).is_some()).count() > 1 {
                stats.duplicate_literal_classes += 1;
            }
        }

        // Ids carry their sort name so a consumer can tell an MLTL node from an
        // interval or a literal by inspecting the id alone, which is what the
        // egglog format's consumers do: `{sort}-{colour}` for a class,
        // `n{colour}-{sort}` for a node.
        let sort_of = |id: Cfg::G| -> &str {
            self.sorts()
                .name(self.ops().info(self.node_op(id)).return_sort)
        };
        // Classes that share a colour are structurally symmetric (decision 4). They are
        // told apart by their rank in smallest-member-id order: ids are not content, but
        // the extracted term cannot depend on the rank, since every choice an extractor
        // makes is a function of colours and the two classes' coloured structures are
        // equal. A rebuilt graph has no such classes (every class holds a finite term,
        // and two classes with a common finite term are one class), so the suffix is
        // written only for a graph dumped before its rebuild, or on a hash collision.
        let mut groups: BTreeMap<crate::canon_colour::Colour, Vec<usize>> = BTreeMap::new();
        for (ci, &c) in colouring.class_colour.iter().enumerate() {
            groups.entry(c).or_default().push(ci);
        }
        let mut suffix: Vec<String> = vec![String::new(); members.len()];
        for g in groups.values_mut() {
            if g.len() < 2 {
                continue;
            }
            g.sort_by_key(|&ci| members[ci].first().map(|id| id.to_usize()));
            for (k, &ci) in g.iter().enumerate() {
                suffix[ci] = format!("x{k}");
            }
        }
        let class_names: Vec<String> = (0..members.len())
            .map(|ci| {
                let sort = members[ci].first().map(|&id| sort_of(id)).unwrap_or("");
                format!("{sort}-{}{}", colouring.class_colour[ci].hex(), suffix[ci])
            })
            .collect();
        // Within a class, members have distinct colours unless their children are
        // symmetric classes; such a repeat is told apart by its rank in id order.
        let node_names: Vec<Vec<String>> = (0..members.len())
            .map(|ci| {
                let mut seen: BTreeMap<crate::canon_colour::Colour, usize> = BTreeMap::new();
                members[ci]
                    .iter()
                    .zip(&colouring.node_colour[ci])
                    .map(|(&id, &c)| {
                        let k = seen.entry(c).or_insert(0);
                        let repeat = if *k == 0 {
                            String::new()
                        } else {
                            format!("y{k}")
                        };
                        *k += 1;
                        format!("n{}{}{repeat}-{}", c.hex(), suffix[ci], sort_of(id))
                    })
                    .collect()
            })
            .collect();
        // A child reference names one member of the child class: the one whose name
        // sorts first, a choice made by content.
        let reference: Vec<&str> = node_names
            .iter()
            .map(|ns| ns.iter().min().map(String::as_str).unwrap_or(""))
            .collect();

        let meta = self.ops().meta_table();
        // Nodes in name order.
        let mut order: Vec<(&str, usize, usize)> = Vec::new();
        for (ci, ns) in node_names.iter().enumerate() {
            for (j, n) in ns.iter().enumerate() {
                order.push((n.as_str(), ci, j));
            }
        }
        order.sort_unstable();
        let mut out = String::from("{\n \"nodes\": {\n");
        let mut first = true;
        for &(name, ci, j) in &order {
            let id = members[ci][j];
            if !first {
                out.push_str(",\n");
            }
            first = false;
            let op = match self.get_lit_val(id) {
                // A literal node's `op` is its value, the way egglog writes a
                // primitive: a consumer parses the bound of an interval out of it.
                Some(v) => escape(&v.to_string()),
                None => escape(self.node_op_name(id)),
            };
            // Each stored child once, with its multiplicity: an AC child of count k is one
            // entry, and the count is written in `"mults"`, parallel to `"children"`.
            let mut children: Vec<(&str, Cfg::M)> = Vec::new();
            self.for_each_child(id, |child, mult| {
                let Some(k) = colouring.class_of(self.class_repr(child)) else {
                    return;
                };
                children.push((reference[k], mult));
            });
            let info = self.ops().info(self.node_op(id));
            // An AC, ACI, or commutative node's children are stored in class-id order;
            // they are written in name order, so the order is content too.
            if matches!(
                info.kind,
                OpKind::MSet { .. } | OpKind::Set { .. } | OpKind::Commutative { .. }
            ) {
                children.sort_unstable();
            }
            let mults = if matches!(info.kind, OpKind::MSet { .. }) {
                format!(
                    ", \"mults\": [{}]",
                    children
                        .iter()
                        .map(|(_, m)| m.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            } else {
                String::new()
            };
            let subsumed = self.node_flags(id) & crate::node_types::FLAG_SUBSUMED != 0;
            let _ = write!(
                out,
                "  \"{name}\": {{\"op\": \"{op}\", \"children\": [{}]{mults}, \
                 \"eclass\": \"{}\", \"cost\": {}, \"subsumed\": {subsumed}}}",
                children
                    .iter()
                    .map(|(c, _)| format!("\"{c}\""))
                    .collect::<Vec<_>>()
                    .join(", "),
                class_names[ci],
                meta[self.node_op(id).to_usize()].cost,
            );
        }
        out.push_str("\n },\n \"class_data\": {\n");
        let mut by_name: Vec<usize> = (0..members.len()).collect();
        by_name.sort_unstable_by(|&x, &y| class_names[x].cmp(&class_names[y]));
        let mut first = true;
        for &ci in &by_name {
            if !first {
                out.push_str(",\n");
            }
            first = false;
            let sort = members[ci].first().map(|&id| sort_of(id)).unwrap_or("");
            // `colour`: the class's content colour, additive to egglog's format.
            let _ = write!(
                out,
                "  \"{}\": {{\"type\": \"{}\", \"colour\": \"{}\"}}",
                class_names[ci],
                escape(sort),
                colouring.class_colour[ci].hex()
            );
        }
        // `op_kinds`: whether each operator's child order carries meaning. An AC, ACI, or
        // commutative node's children are stored in canonical order, which is *class-id*
        // order, so two runs that build the same graph with different ids emit them in
        // different order. A consumer comparing two dumps for content equality has to know
        // which of those orders to ignore, and the node entries alone do not say. Additive,
        // so a reader written against egglog's format still works.
        out.push_str("\n },\n \"op_kinds\": {\n");
        let mut kinds: BTreeMap<&str, &str> = BTreeMap::new();
        for ids in members {
            for &id in ids {
                let info = self.ops().info(self.node_op(id));
                kinds.insert(
                    info.name.as_str(),
                    match &info.kind {
                        OpKind::Normal { .. } => "plain",
                        OpKind::Commutative { .. } => "comm",
                        OpKind::A { .. } => "a",
                        OpKind::MSet { .. } => "ac",
                        OpKind::Set { .. } => "aci",
                        OpKind::Lit => "lit",
                    },
                );
            }
        }
        let mut first = true;
        for (name, kind) in &kinds {
            if !first {
                out.push_str(",\n");
            }
            first = false;
            let _ = write!(out, "  \"{}\": \"{kind}\"", escape(name));
        }
        let root_name = colouring
            .class_of(self.class_repr(root))
            .and_then(|ci| class_names.get(ci))
            .map(String::as_str)
            .unwrap_or_default();
        let _ = write!(out, "\n }},\n \"root_eclasses\": [\"{root_name}\"]\n}}\n");
        (out, stats)
    }
}
