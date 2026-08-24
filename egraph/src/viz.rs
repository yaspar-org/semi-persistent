// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E-graph visualization: export to GraphViz DOT.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use std::fmt::Write;

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Emit GraphViz DOT representation.
    pub fn to_dot(&self) -> String {
        let mut out = String::from("digraph egraph {\n  compound=true\n  clusterrank=local\n\n");

        // Typed ids on both sides of the grouping. Holding raw `usize` copies here meant
        // re-minting each member twice below — once per pass — to recover an id the scan
        // had already produced.
        let mut classes: std::collections::BTreeMap<Cfg::G, Vec<Cfg::G>> =
            std::collections::BTreeMap::new();
        for gid in self.node_ids() {
            classes.entry(self.class_repr(gid)).or_default().push(gid);
        }

        for (repr, members) in &classes {
            let repr = repr.to_usize();
            let _ = write!(out, "  subgraph cluster_{repr} {{\n    style=dotted\n");
            for (idx, &gid) in members.iter().enumerate() {
                let op = self.node_op_name(gid);
                let label = match self.node_lit(gid) {
                    Some(lit) => format!("{op}({v})", v = self.lits().get(lit)),
                    None => op.to_string(),
                };
                let _ = writeln!(out, "    {repr}.{idx}[label = \"{label}\"]");
            }
            let _ = writeln!(out, "  }}");
        }

        for (&class_id, members) in &classes {
            let class_repr = class_id.to_usize();
            for (idx, &gid) in members.iter().enumerate() {
                let mut arg_i = 0usize;
                let arity = self.node_arity(gid);
                self.for_each_child(gid, |child, mult| {
                    let anchor = Self::anchor(arg_i, arity);
                    let child_id = self.class_repr(child);
                    let child_repr = child_id.to_usize();
                    let ml = if mult > Cfg::M::ONE { format!(", label=\"×{mult}\"") } else { String::new() };
                    if child_id == class_id {
                        // self-edge: point to self with lhead
                        let _ = writeln!(out, "  {class_repr}.{idx}{anchor} -> {class_repr}.{idx}:n [lhead=cluster_{class_repr}{ml}]");
                    } else {
                        let _ = writeln!(out, "  {class_repr}.{idx}{anchor} -> {child_repr}.0 [lhead=cluster_{child_repr}{ml}]");
                    }
                    arg_i += 1;
                });
            }
        }

        out.push_str("}\n");
        out
    }

    fn node_arity(&self, id: Cfg::G) -> usize {
        let mut count = 0;
        self.for_each_child(id, |_, _| count += 1);
        count
    }

    fn anchor(i: usize, len: usize) -> &'static str {
        match (len, i) {
            (1, 0) => "",
            (2, 0) => ":sw",
            (2, 1) => ":se",
            (3, 0) => ":sw",
            (3, 1) => ":s",
            (3, 2) => ":se",
            _ => "",
        }
    }

    /// Write DOT to a file, render with `dot`, and open the result.
    pub fn show(&self, label: &str) {
        let dot = self.to_dot();
        let safe = label.replace(|c: char| !c.is_alphanumeric() && c != '_' && c != '-', "_");
        let dot_path = std::env::temp_dir().join(format!("sp_{safe}.dot"));
        let svg_path = std::env::temp_dir().join(format!("sp_{safe}.svg"));
        std::fs::write(&dot_path, &dot).expect("failed to write dot");

        let status = std::process::Command::new("dot")
            .args(["-Tsvg", "-o"])
            .arg(&svg_path)
            .arg(&dot_path)
            .status();

        match status {
            Ok(s) if s.success() => {
                eprintln!("Wrote {}", svg_path.display());
                #[cfg(target_os = "macos")]
                {
                    let _ = std::process::Command::new("open")
                        .arg("-a")
                        .arg("Safari")
                        .arg(&svg_path)
                        .spawn();
                }
                #[cfg(target_os = "linux")]
                {
                    let _ = std::process::Command::new("xdg-open")
                        .arg(&svg_path)
                        .spawn();
                }
            }
            _ => {
                eprintln!("dot not found or failed; wrote {}", dot_path.display());
            }
        }
    }
}
