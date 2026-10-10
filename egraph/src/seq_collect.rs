// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The assembly of a sequence pattern's matches at one node (Semper design chapter
//! 23, "Execution"): from each child's rows for each item, the assignments of the
//! node's children to the items that `doc/sequence-patterns.md` defines.
//!
//! Under A, the parses of the items over the child sequence, maximal at gaps; under
//! AC and ACI, the simple items' injective assignment, then per remaining child the
//! (filter, row) choices with `:except` applied, the rest to the bare sequence or no
//! match. A node's matches are a set of binding environments (Edge cases 2), and a
//! node over `MAX_MATCHES` is reported as `OVER_BOUND`.
//!
//! The per-child rows come from a [`Source`]: route 1 matches the live e-graph
//! (`collection.rs`), the relational engine probes the filter sub-queries on the
//! round's snapshot (`crate::seq_query`). Both run this code, so both enumerate the
//! matches in one order. `X` is the literal representation of the source: the
//! model's values for route 1, interned ids for the relational engine.

use std::collections::BTreeMap;

/// A value in a match environment. `Hash` is structural, as [`value_eq`] is, so equal
/// values hash equally.
#[derive(Clone, Debug, Hash)]
pub enum Value<G, X> {
    Class(G),
    Lit(X),
    /// A multiplicity, native: the hidden column `{sequence}:mult` of an AC sequence,
    /// read by splices, and a multiplicity a rule names (`:k`), read as an `i64`
    /// literal where an expression uses it.
    Count(u64),
    Seq(Vec<Value<G, X>>),
    Tuples(Vec<Vec<Value<G, X>>>),
}

/// Structural equality of two values (classes compared as the representatives the
/// source gave, which is what every stored class is).
pub fn value_eq<G: PartialEq, X: PartialEq>(a: &Value<G, X>, b: &Value<G, X>) -> bool {
    match (a, b) {
        (Value::Class(x), Value::Class(y)) => x == y,
        (Value::Lit(x), Value::Lit(y)) => x == y,
        (Value::Count(x), Value::Count(y)) => x == y,
        (Value::Seq(x), Value::Seq(y)) => {
            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| value_eq(p, q))
        }
        (Value::Tuples(x), Value::Tuples(y)) => {
            x.len() == y.len()
                && x.iter().zip(y).all(|(p, q)| {
                    p.len() == q.len() && p.iter().zip(q).all(|(a, b)| value_eq(a, b))
                })
        }
        _ => false,
    }
}

/// Variable slots of a pattern, bound or not.
pub type Slots<G, X> = Vec<Option<Value<G, X>>>;

/// A match's bindings by name.
pub type Env<G, X> = BTreeMap<String, Value<G, X>>;

pub fn slots_eq<G: PartialEq, X: PartialEq>(a: &Slots<G, X>, b: &Slots<G, X>) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(x, y)| match (x, y) {
            (None, None) => true,
            (Some(x), Some(y)) => value_eq(x, y),
            _ => false,
        })
}

pub fn env_eq<G: PartialEq, X: PartialEq>(a: &Env<G, X>, b: &Env<G, X>) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|((ka, va), (kb, vb))| ka == kb && value_eq(va, vb))
}

/// "§Edge cases 2: Filter rows are deduplicated by their bindings, not by member".
pub fn dedup_slots<G: PartialEq, X: PartialEq>(rows: Vec<Slots<G, X>>) -> Vec<Slots<G, X>> {
    let mut out: Vec<Slots<G, X>> = Vec::with_capacity(rows.len());
    for r in rows {
        if !out.iter().any(|o| slots_eq(o, &r)) {
            out.push(r);
        }
    }
    out
}

/// The name of an AC sequence's multiplicity column. `:` cannot occur in a program
/// variable, so the column cannot collide with a name a rule binds.
pub fn mult_column(name: &str) -> String {
    format!("{name}:mult")
}

/// The most matches one node may produce; a node beyond it is skipped with a warning
/// and counted ("§Edge cases 2"), and the run continues.
pub const MAX_MATCHES: usize = 1 << 20;

/// A node's match count exceeded `MAX_MATCHES`.
pub const OVER_BOUND: &str = "more than 2^20 matches at one node";

/// A multiplicity annotation as an interval, Semper design §7.5's table: `:k`
/// any (bound to `k`), `:k>=2`, `:k<5`, `:3`; `!=` an excluded value. `slot` is the
/// variable's slot when the annotation names one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MultCheck {
    pub lo: u64,
    pub hi: u64,
    pub ne: Option<u64>,
    pub slot: Option<usize>,
}

impl MultCheck {
    pub fn accepts(&self, m: u64) -> bool {
        self.lo <= m && m <= self.hi && self.ne != Some(m)
    }
}

/// A sequence rule's left-hand side as the assembly reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spec {
    /// The root is associative (`:assoc` or a fold): items are matched in order.
    pub assoc: bool,
    /// The root is AC with multiplicities: sequences carry multiplicity columns.
    pub ac: bool,
    pub items: Vec<SItem>,
    pub filters: Vec<SFilter>,
    /// Scalar variable names by slot (the simple items' variables).
    pub scalars: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SItem {
    /// A simple item: the `usize`-th simple item of the rule, for its source.
    One(usize, Option<MultCheck>),
    Bare(String),
    Filter(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SFilter {
    pub name: String,
    /// The pattern's variables, then the annotation's multiplicity variable if any.
    pub vars: Vec<String>,
    pub except: Option<usize>,
    pub mult: Option<MultCheck>,
}

/// Where the per-child rows come from.
pub trait Source<G, X> {
    /// The matches of simple item `item` at class `class` extending `scalars`.
    fn one(
        &mut self,
        item: usize,
        class: G,
        scalars: &Slots<G, X>,
    ) -> Result<Vec<Slots<G, X>>, String>;
    /// The rows of filter `fi` at `class`, extending `init` (the filter's slots, with
    /// its multiplicity variable already bound when it has one).
    fn filter(
        &mut self,
        fi: usize,
        class: G,
        init: &Slots<G, X>,
    ) -> Result<Vec<Slots<G, X>>, String>;
}

/// The matches at a node whose children, as classes with multiplicities, are `kids`:
/// under A the parses of the items over the child sequence; under AC and ACI the
/// simple items' assignments, then the filters' (with `:except`), the rest to the
/// bare sequence or no match; the matches a set of binding environments.
pub fn assemble<
    G: Copy + PartialEq + std::hash::Hash,
    X: Clone + PartialEq + std::hash::Hash,
    Src: Source<G, X> + ?Sized,
>(
    spec: &Spec,
    src: &mut Src,
    kids: &[(G, u64)],
) -> Result<Vec<Env<G, X>>, String> {
    let mut out = if spec.assoc {
        match_assoc(spec, src, kids)?
    } else {
        let ones: Vec<(usize, &Option<MultCheck>)> = spec
            .items
            .iter()
            .filter_map(|i| {
                if let SItem::One(j, m) = i {
                    Some((*j, m))
                } else {
                    None
                }
            })
            .collect();
        let mut out = Vec::new();
        let mut used = vec![false; kids.len()];
        assign_ones(
            spec,
            src,
            &ones,
            0,
            kids,
            &mut used,
            &vec![None; spec.scalars.len()],
            &mut out,
        )?;
        out
    };
    // "§Edge cases 2: A node's matches are therefore a set of binding environments".
    let mut set = EnvSet::default();
    for m in out.drain(..) {
        set.insert(m);
    }
    Ok(set.unique)
}

/// A node's matches as a set, in first-seen order: hashed, and compared with
/// [`env_eq`] only within a hash bucket. A pairwise scan was quadratic in the matches,
/// which `:flatten` multiplies by the views (task 4 of
/// `doc/goal-flatten-and-engine-completion.md`).
struct EnvSet<G, X> {
    unique: Vec<Env<G, X>>,
    buckets: std::collections::HashMap<u64, Vec<usize>>,
}

impl<G, X> Default for EnvSet<G, X> {
    fn default() -> Self {
        Self {
            unique: Vec::new(),
            buckets: std::collections::HashMap::new(),
        }
    }
}

impl<G: std::hash::Hash + PartialEq, X: std::hash::Hash + PartialEq> EnvSet<G, X> {
    /// Add `m` unless an equal match is present; whether it was added.
    fn insert(&mut self, m: Env<G, X>) -> bool {
        use std::hash::{Hash, Hasher};
        let mut h = std::hash::DefaultHasher::new();
        m.hash(&mut h);
        let bucket = self.buckets.entry(h.finish()).or_default();
        if bucket.iter().any(|&i| env_eq(&self.unique[i], &m)) {
            return false;
        }
        bucket.push(self.unique.len());
        self.unique.push(m);
        true
    }
}

/// The matches at a node under `:flatten`: the union, as a set, of every view's
/// matches (`crate::flatten`), each kept by its view's demand
/// (`doc/goal-canonical-flatten-views.md`, decision 2): the items, simple and filters,
/// take every element the bare sequences do not. The node's bound applies to the
/// matches assembled over all its views, before the union removes duplicates, so it
/// bounds the work and not only the result: a class that refers to itself several
/// times has many views with largely the same matches.
pub fn assemble_views<
    G: Copy + PartialEq + std::hash::Hash,
    X: Clone + PartialEq + std::hash::Hash,
    Src: Source<G, X> + ?Sized,
>(
    spec: &Spec,
    src: &mut Src,
    views: &[(Vec<(G, u64)>, crate::flatten::Demand<G>)],
) -> Result<Vec<Env<G, X>>, String> {
    let bare: Vec<&String> = spec
        .items
        .iter()
        .filter_map(|i| {
            if let SItem::Bare(n) = i {
                Some(n)
            } else {
                None
            }
        })
        .collect();
    let mut set = EnvSet::default();
    let mut assembled = 0usize;
    let mut left: Vec<G> = Vec::new();
    let mut taken: Vec<G> = Vec::new();
    for (v, demand) in views {
        let ms = assemble(spec, src, v)?;
        assembled = assembled.checked_add(ms.len()).ok_or(OVER_BOUND)?;
        if assembled > MAX_MATCHES {
            return Err(OVER_BOUND.into());
        }
        for m in ms {
            if !demand.unconditional {
                // The view's elements, less one per element a bare sequence holds.
                left.clear();
                left.extend(v.iter().map(|e| e.0));
                for n in &bare {
                    if let Some(Value::Seq(xs)) = m.get(*n) {
                        for x in xs {
                            if let Value::Class(c) = x
                                && let Some(i) = left.iter().position(|l| l == c)
                            {
                                left.swap_remove(i);
                            }
                        }
                    }
                }
                taken.clear();
                taken.extend_from_slice(&left);
                if !demand.accepts(&taken) {
                    continue;
                }
            }
            set.insert(m);
        }
    }
    Ok(set.unique)
}

/// Whether a node's failure is one of the bounds that skip the node and count it
/// (this module's match bound, `crate::flatten`'s view bounds) rather than a fault.
pub fn is_over_bound(e: &str) -> bool {
    e == OVER_BOUND
        || e == crate::flatten::OVER_BOUND
        || e == crate::flatten::MULT_OVERFLOW
        || e == crate::flatten::BEYOND_U64
}

/// The matches under A (`doc/sequence-patterns.md`): the items, concatenated in
/// written order, cover all the children; a simple item is the next child, a run
/// `(..g base)` zero or more consecutive children matching `base`, a gap `..g` zero
/// or more; every parse and every member choice is a match; a run next to a gap is
/// maximal toward it, an empty run included.
fn match_assoc<G: Copy + PartialEq, X: Clone + PartialEq, Src: Source<G, X> + ?Sized>(
    spec: &Spec,
    src: &mut Src,
    kids: &[(G, u64)],
) -> Result<Vec<Env<G, X>>, String> {
    let classes: Vec<G> = kids.iter().map(|k| k.0).collect();
    // Phase 1: each filter's matches on each child, deduplicated by bindings.
    let mut matched: Vec<Vec<Vec<Slots<G, X>>>> = Vec::with_capacity(spec.filters.len());
    for (fi, f) in spec.filters.iter().enumerate() {
        let mut per = Vec::with_capacity(classes.len());
        for &k in &classes {
            per.push(dedup_slots(src.filter(fi, k, &vec![None; f.vars.len()])?));
        }
        matched.push(per);
    }
    let mut st = AssocState {
        env: BTreeMap::new(),
        spans: Vec::new(),
        out: Vec::new(),
    };
    assoc_go(
        spec,
        src,
        &classes,
        &matched,
        0,
        0,
        &vec![None; spec.scalars.len()],
        &mut st,
    )?;
    Ok(st.out)
}

struct AssocState<G, X> {
    env: Env<G, X>,
    spans: Vec<(usize, usize)>,
    out: Vec<Env<G, X>>,
}

#[allow(clippy::too_many_arguments)]
fn assoc_go<G: Copy + PartialEq, X: Clone + PartialEq, Src: Source<G, X> + ?Sized>(
    spec: &Spec,
    src: &mut Src,
    kids: &[G],
    matched: &[Vec<Vec<Slots<G, X>>>],
    it: usize,
    pos: usize,
    scalars: &Slots<G, X>,
    st: &mut AssocState<G, X>,
) -> Result<(), String> {
    let n = kids.len();
    if it == spec.items.len() {
        if pos == n && assoc_maximal(spec, matched, &st.spans) {
            if st.out.len() >= MAX_MATCHES {
                return Err(OVER_BOUND.into());
            }
            let mut env = st.env.clone();
            for (v, x) in spec.scalars.iter().zip(scalars) {
                env.insert(
                    v.clone(),
                    x.clone()
                        .ok_or_else(|| format!("'{v}' unbound after a match"))?,
                );
            }
            st.out.push(env);
        }
        return Ok(());
    }
    let seq =
        |a: usize, b: usize| Value::Seq(kids[a..b].iter().map(|&k| Value::Class(k)).collect());
    match &spec.items[it] {
        SItem::One(j, _) => {
            if pos < n {
                for b in src.one(*j, kids[pos], scalars)? {
                    st.spans.push((pos, pos + 1));
                    assoc_go(spec, src, kids, matched, it + 1, pos + 1, &b, st)?;
                    st.spans.pop();
                }
            }
        }
        SItem::Bare(name) => {
            for end in pos..=n {
                st.env.insert(name.clone(), seq(pos, end));
                st.spans.push((pos, end));
                assoc_go(spec, src, kids, matched, it + 1, end, scalars, st)?;
                st.spans.pop();
            }
            st.env.remove(name);
        }
        SItem::Filter(fi) => {
            let f = &spec.filters[*fi];
            // "a run: zero or more consecutive children matching `base`".
            for end in pos..=n {
                if end > pos && matched[*fi][end - 1].is_empty() {
                    break; // a longer run contains this child too
                }
                // Every member choice over the run's children (an odometer); the empty
                // run has exactly one.
                let mut pick = vec![0usize; end - pos];
                loop {
                    let mut cols: Vec<Vec<Value<G, X>>> = vec![Vec::new(); f.vars.len()];
                    for (j, k) in (pos..end).enumerate() {
                        for (slot, v) in matched[*fi][k][pick[j]].iter().enumerate() {
                            cols[slot].push(v.clone().ok_or_else(|| {
                                format!("'{}' unbound after a match", f.vars[slot])
                            })?);
                        }
                    }
                    st.env.insert(f.name.clone(), seq(pos, end));
                    for (v, col) in f.vars.iter().zip(cols) {
                        st.env.insert(v.clone(), Value::Seq(col));
                    }
                    st.spans.push((pos, end));
                    assoc_go(spec, src, kids, matched, it + 1, end, scalars, st)?;
                    st.spans.pop();
                    let mut d = 0;
                    loop {
                        if d == pick.len() {
                            break;
                        }
                        pick[d] += 1;
                        if pick[d] < matched[*fi][pos + d].len() {
                            break;
                        }
                        pick[d] = 0;
                        d += 1;
                    }
                    if d == pick.len() {
                        break;
                    }
                }
            }
            st.env.remove(&f.name);
            for v in &f.vars {
                st.env.remove(v);
            }
        }
    }
    Ok(())
}

/// "A run next to a gap is maximal toward it: the gap's adjacent child does not match
/// the run's pattern. This holds for an empty run too".
fn assoc_maximal<G, X>(
    spec: &Spec,
    matched: &[Vec<Vec<Slots<G, X>>>],
    spans: &[(usize, usize)],
) -> bool {
    for w in 0..spec.items.len().saturating_sub(1) {
        match (&spec.items[w], &spec.items[w + 1]) {
            (SItem::Filter(fi), SItem::Bare(_)) => {
                let (s, e) = spans[w + 1];
                if s < e && !matched[*fi][s].is_empty() {
                    return false;
                }
            }
            (SItem::Bare(_), SItem::Filter(fi)) => {
                let (s, e) = spans[w];
                if s < e && !matched[*fi][e - 1].is_empty() {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

/// "Simple items take distinct children first, every assignment enumerated". Under
/// AC an unannotated item takes a child of multiplicity exactly 1 and an annotated
/// one a child its annotation accepts, binding the multiplicity (maximum partition,
/// Semper design §7.5).
#[allow(clippy::too_many_arguments)]
fn assign_ones<G: Copy + PartialEq, X: Clone + PartialEq, Src: Source<G, X> + ?Sized>(
    spec: &Spec,
    src: &mut Src,
    ones: &[(usize, &Option<MultCheck>)],
    i: usize,
    kids: &[(G, u64)],
    used: &mut Vec<bool>,
    scalars: &Slots<G, X>,
    out: &mut Vec<Env<G, X>>,
) -> Result<(), String> {
    if i == ones.len() {
        let rest: Vec<(G, u64)> = kids
            .iter()
            .zip(used.iter())
            .filter(|(_, u)| !**u)
            .map(|(k, _)| *k)
            .collect();
        return assign_filters(spec, src, &rest, scalars, out);
    }
    let (item, mult) = ones[i];
    for j in 0..kids.len() {
        if used[j] {
            continue;
        }
        let (k, m) = kids[j];
        let mut base = scalars.clone();
        match mult {
            None if spec.ac && m != 1 => continue,
            None => {}
            Some(mc) => {
                if !mc.accepts(m) {
                    continue;
                }
                if let Some(slot) = mc.slot {
                    let v = Value::Count(m);
                    match &base[slot] {
                        Some(old) if !value_eq(old, &v) => continue,
                        Some(_) => {}
                        None => base[slot] = Some(v),
                    }
                }
            }
        }
        for b in src.one(item, k, &base)? {
            used[j] = true;
            let res = assign_ones(spec, src, ones, i + 1, kids, used, &b, out);
            used[j] = false;
            res?;
        }
    }
    Ok(())
}

/// "Filters then take every remaining child matching their pattern ... a child
/// matching several is assigned to each in turn, every assignment a match.
/// `:except other` removes the children `other`'s pattern matches ... The bare
/// sequence takes the rest". Under AC a filter's annotation restricts the children
/// it takes, an unannotated filter takes only multiplicity 1, and each sequence carries
/// its multiplicity column.
fn assign_filters<G: Copy + PartialEq, X: Clone + PartialEq, Src: Source<G, X> + ?Sized>(
    spec: &Spec,
    src: &mut Src,
    rest: &[(G, u64)],
    scalars: &Slots<G, X>,
    out: &mut Vec<Env<G, X>>,
) -> Result<(), String> {
    // Phase 1: each filter's matches on each remaining child, independently,
    // deduplicated by bindings; the multiplicity annotation checked and its variable
    // bound before the pattern is matched.
    let mut matched: Vec<Vec<Vec<Slots<G, X>>>> = Vec::with_capacity(spec.filters.len());
    for (fi, f) in spec.filters.iter().enumerate() {
        let mut per = Vec::with_capacity(rest.len());
        for &(k, m) in rest {
            let mut init: Slots<G, X> = vec![None; f.vars.len()];
            let rows = match &f.mult {
                Some(mc) if !mc.accepts(m) => vec![],
                Some(mc) => {
                    if let Some(slot) = mc.slot {
                        init[slot] = Some(Value::Count(m));
                    }
                    src.filter(fi, k, &init)?
                }
                // Absent multiplicity means 1 in every rule (decided 2026-09-30): an
                // unannotated filter takes only a child of multiplicity exactly 1, as an
                // unannotated ordinary AC element does. Under ACI and A every multiplicity
                // is 1, so this restricts AC only.
                None if m != 1 => vec![],
                None => src.filter(fi, k, &init)?,
            };
            per.push(dedup_slots(rows));
        }
        matched.push(per);
    }
    // Phase 2: per child, the (filter, bindings) it may take.
    let mut choices: Vec<Vec<(usize, &Slots<G, X>)>> = Vec::with_capacity(rest.len());
    for ci in 0..rest.len() {
        let mut cs = Vec::new();
        for (fi, f) in spec.filters.iter().enumerate() {
            if f.except.is_some_and(|o| !matched[o][ci].is_empty()) {
                continue;
            }
            for b in &matched[fi][ci] {
                cs.push((fi, b));
            }
        }
        choices.push(cs);
    }
    let bare = spec.items.iter().find_map(|i| {
        if let SItem::Bare(n) = i {
            Some(n)
        } else {
            None
        }
    });
    let to_bare: Vec<(G, u64)> = rest
        .iter()
        .zip(&choices)
        .filter(|(_, c)| c.is_empty())
        .map(|(k, _)| *k)
        .collect();
    if bare.is_none() && !to_bare.is_empty() {
        return Ok(());
    }
    let branching: Vec<usize> = (0..rest.len())
        .filter(|&ci| !choices[ci].is_empty())
        .collect();
    let count = branching.iter().try_fold(1usize, |acc, &ci| {
        acc.checked_mul(choices[ci].len())
            .filter(|&n| n <= MAX_MATCHES)
    });
    match count.and_then(|c| c.checked_add(out.len())) {
        Some(total) if total <= MAX_MATCHES => {}
        _ => return Err(OVER_BOUND.into()),
    }
    let mut pick = vec![0usize; branching.len()];
    loop {
        let mut env = BTreeMap::new();
        for (fi, f) in spec.filters.iter().enumerate() {
            let mut elems = Vec::new();
            let mut mults = Vec::new();
            let mut cols: Vec<Vec<Value<G, X>>> = vec![Vec::new(); f.vars.len()];
            for (bi, &ci) in branching.iter().enumerate() {
                let (cf, b) = choices[ci][pick[bi]];
                if cf != fi {
                    continue;
                }
                elems.push(Value::Class(rest[ci].0));
                mults.push(Value::Count(rest[ci].1));
                for (slot, v) in b.iter().enumerate() {
                    cols[slot].push(
                        v.clone()
                            .ok_or_else(|| format!("'{}' unbound after a match", f.vars[slot]))?,
                    );
                }
            }
            env.insert(f.name.clone(), Value::Seq(elems));
            if spec.ac {
                env.insert(mult_column(&f.name), Value::Seq(mults));
            }
            for (v, col) in f.vars.iter().zip(cols) {
                env.insert(v.clone(), Value::Seq(col));
            }
        }
        if let Some(n) = bare {
            env.insert(
                n.clone(),
                Value::Seq(to_bare.iter().map(|&(k, _)| Value::Class(k)).collect()),
            );
            if spec.ac {
                env.insert(
                    mult_column(n),
                    Value::Seq(to_bare.iter().map(|&(_, m)| Value::Count(m)).collect()),
                );
            }
        }
        for (v, x) in spec.scalars.iter().zip(scalars) {
            env.insert(
                v.clone(),
                x.clone()
                    .ok_or_else(|| format!("'{v}' unbound after a match"))?,
            );
        }
        out.push(env);
        // Next assignment (an odometer over the branching children's choices).
        let mut d = 0;
        loop {
            if d == pick.len() {
                return Ok(());
            }
            pick[d] += 1;
            if pick[d] < choices[branching[d]].len() {
                break;
            }
            pick[d] = 0;
            d += 1;
        }
    }
}
