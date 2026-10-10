// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The reference matcher for sequence patterns: every match of a pattern, enumerated
//! by brute force from `doc/sequence-patterns.md` and from nothing else.
//!
//! It is the definition the engine is tested against, so it is written to be read
//! against the design document: each rule cites the clause it implements, quoted in
//! the form "§Section: clause". It is slow on purpose (it enumerates every split and
//! every assignment and filters afterwards) and knows nothing of Semper's engine: an
//! e-graph here is a list of classes, each a list of members.
//!
//! A node's matches are a set of binding environments: "§Edge cases 2: A node's
//! matches are therefore a set of binding environments, not a multiset".
#![allow(dead_code)]

use std::collections::BTreeMap;

pub type ClassId = usize;

/// How an operator's children are read. Folds (`:assoc-left`, `:assoc-right`) are
/// `Assoc`: "§Semantics: A (`:assoc`, folds)".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Positional arguments.
    Plain,
    /// `:assoc` and folds: an ordered child sequence.
    Assoc,
    /// `:assoc-comm-idem`: a set of children.
    Aci,
    /// `:assoc-comm`: distinct children, each with a multiplicity.
    Ac,
}

/// A member of a class: an operator over child classes, or a literal. Under AC,
/// `mults[i]` is the multiplicity of `kids[i]` and the kids are distinct; elsewhere
/// `mults` is empty.
#[derive(Clone, Debug)]
pub struct Member {
    pub op: String,
    pub kids: Vec<ClassId>,
    pub mults: Vec<u64>,
    pub lit: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Graph {
    pub classes: Vec<Vec<Member>>,
    pub kinds: BTreeMap<String, Kind>,
    /// Global `let` names and the class each is bound to.
    pub globals: BTreeMap<String, ClassId>,
    /// Each n-ary operator's laws (unit as a class, inverse by name), the input of the
    /// one normalization the reference calls for `:flatten` views
    /// (`semi_persistent_egraph::nary_canon::normalize`). An operator without an entry
    /// has its kind's laws and no unit or inverse.
    pub laws: BTreeMap<String, semi_persistent_egraph::nary_canon::NaryLaws<ClassId, String>>,
}

impl Graph {
    pub fn class(&mut self, members: Vec<Member>) -> ClassId {
        self.classes.push(members);
        self.classes.len() - 1
    }
    pub fn node(op: &str, kids: &[ClassId]) -> Member {
        Member {
            op: op.into(),
            kids: kids.to_vec(),
            mults: vec![],
            lit: None,
        }
    }
    /// An AC node over distinct children with multiplicities.
    pub fn node_ac(op: &str, kids: &[(ClassId, u64)]) -> Member {
        Member {
            op: op.into(),
            kids: kids.iter().map(|k| k.0).collect(),
            mults: kids.iter().map(|k| k.1).collect(),
            lit: None,
        }
    }
    pub fn lit(v: &str) -> Member {
        Member {
            op: String::new(),
            kids: vec![],
            mults: vec![],
            lit: Some(v.into()),
        }
    }
    fn kind(&self, op: &str) -> Kind {
        self.kinds.get(op).copied().unwrap_or(Kind::Plain)
    }
}

/// A multiplicity annotation, "§Multiplicities and `zip`: The forms and their
/// intervals are those of ordinary AC elements": `:k` (any, bound to `k`), `:k>=2`,
/// `:k<5`, `:3`. An interval `[lo, hi]`, an optional excluded value (`:k!=2`), and
/// the variable it binds, if any.
#[derive(Clone, Debug)]
pub struct Mult {
    pub var: Option<String>,
    pub lo: u64,
    pub hi: u64,
    pub ne: Option<u64>,
}

impl Mult {
    pub fn var(v: &str) -> Mult {
        Mult {
            var: Some(v.into()),
            lo: 1,
            hi: u64::MAX,
            ne: None,
        }
    }
    pub fn exact(n: u64) -> Mult {
        Mult {
            var: None,
            lo: n,
            hi: n,
            ne: None,
        }
    }
    pub fn at_least(v: &str, n: u64) -> Mult {
        Mult {
            var: Some(v.into()),
            lo: n,
            hi: u64::MAX,
            ne: None,
        }
    }
    pub fn accepts(&self, m: u64) -> bool {
        self.lo <= m && m <= self.hi && self.ne != Some(m)
    }
}

/// "§Grammar: pattern ::= var | literal | (Op child*)".
#[derive(Clone, Debug)]
pub enum Pat {
    Var(String),
    Lit(String),
    App(String, Vec<Item>),
}

/// "§Grammar: child ::= pattern | ..name | (..name base)", with `:except name` and a
/// multiplicity annotation on a filter.
#[derive(Clone, Debug)]
pub enum Item {
    /// "one child", with an optional multiplicity annotation (AC).
    One(Pat, Option<Mult>),
    /// "`..name` is one construct with an optional filter: bare, it constrains nothing".
    Bare(String),
    /// "with `base`, every child it takes matches `base`".
    Filter {
        name: String,
        base: Pat,
        except: Option<String>,
        mult: Option<Mult>,
    },
}

impl Item {
    pub fn one(p: Pat) -> Item {
        Item::One(p, None)
    }
    pub fn filter(name: &str, base: Pat) -> Item {
        Item::Filter {
            name: name.into(),
            base,
            except: None,
            mult: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Val {
    Class(ClassId),
    /// A multiplicity.
    Int(u64),
    Seq(Vec<Val>),
}

pub type Env = BTreeMap<String, Val>;

/// The name of an AC sequence's multiplicity column: "§Semantics, Under AC and ACI:
/// Under AC a filter's children carry their multiplicities"; the bare sequence's
/// likewise. Named `{sequence}:mult`, a name no program variable can have.
pub fn mult_column(name: &str) -> String {
    format!("{name}:mult")
}

/// "§Grammar: `base` is the ordinary pattern language ... filters do not nest". True
/// when `p` contains no filter.
pub fn is_base(p: &Pat) -> bool {
    match p {
        Pat::Var(_) | Pat::Lit(_) => true,
        Pat::App(_, items) => items.iter().all(|i| match i {
            Item::One(p, _) => is_base(p),
            Item::Bare(_) => true,
            Item::Filter { .. } => false,
        }),
    }
}

/// The names a base pattern binds, in order of first appearance; globals excluded
/// ("§Grammar: A name bound by a global `let` is the global").
fn base_vars(g: &Graph, p: &Pat, out: &mut Vec<String>) {
    let push = |n: &String, out: &mut Vec<String>| {
        if !out.contains(n) {
            out.push(n.clone())
        }
    };
    match p {
        Pat::Var(x) => {
            if !g.globals.contains_key(x) {
                push(x, out);
            }
        }
        Pat::Lit(_) => {}
        Pat::App(_, items) => {
            for i in items {
                match i {
                    Item::One(p, m) => {
                        base_vars(g, p, out);
                        if let Some(Mult { var: Some(v), .. }) = m {
                            push(v, out);
                        }
                    }
                    Item::Bare(n) => push(n, out),
                    Item::Filter { .. } => unreachable!("a filter inside a filter"),
                }
            }
        }
    }
}

fn set(mut v: Vec<Env>) -> Vec<Env> {
    v.sort();
    v.dedup();
    v
}

/// Every match of `p` against class `c`, extending `env`.
pub fn match_class(g: &Graph, p: &Pat, c: ClassId, env: &Env) -> Vec<Env> {
    match p {
        Pat::Var(x) => {
            // "§Grammar: A name bound by a global `let` is the global, resolved through
            // `GlobalCtx` as in ordinary patterns, inside a filter as elsewhere."
            if let Some(&gc) = g.globals.get(x) {
                return if gc == c { vec![env.clone()] } else { vec![] };
            }
            match env.get(x) {
                Some(Val::Class(b)) => {
                    if *b == c {
                        vec![env.clone()]
                    } else {
                        vec![]
                    }
                }
                Some(other) => panic!("'{x}' is {other:?}, not a class"),
                None => {
                    let mut e = env.clone();
                    e.insert(x.clone(), Val::Class(c));
                    vec![e]
                }
            }
        }
        Pat::Lit(v) => {
            if g.classes[c].iter().any(|m| m.lit.as_deref() == Some(v)) {
                vec![env.clone()]
            } else {
                vec![]
            }
        }
        Pat::App(op, items) => {
            // "§Semantics, Member choice: Where a class has several members matching a
            // pattern, each is a separate match, as for simple patterns."
            let mut out = Vec::new();
            for m in &g.classes[c] {
                if m.lit.is_none() && &m.op == op {
                    out.extend(match_member(g, op, items, m, env));
                }
            }
            set(out)
        }
    }
}

fn match_member(g: &Graph, op: &str, items: &[Item], m: &Member, env: &Env) -> Vec<Env> {
    let kids: Vec<(ClassId, u64)> = if g.kind(op) == Kind::Ac {
        m.kids
            .iter()
            .copied()
            .zip(m.mults.iter().copied())
            .collect()
    } else {
        m.kids.iter().map(|&k| (k, 1)).collect()
    };
    match_children(g, op, items, &kids, env)
}

/// Every match of the items against one node's children, given as `(class,
/// multiplicity)` (multiplicity 1 except under AC).
pub fn match_children(
    g: &Graph,
    op: &str,
    items: &[Item],
    kids: &[(ClassId, u64)],
    env: &Env,
) -> Vec<Env> {
    set(match g.kind(op) {
        Kind::Plain => {
            if items.len() != kids.len() || !items.iter().all(|i| matches!(i, Item::One(_, None))) {
                return vec![];
            }
            let mut envs = vec![env.clone()];
            for (i, &(k, _)) in items.iter().zip(kids) {
                let Item::One(p, _) = i else { unreachable!() };
                envs = envs.iter().flat_map(|e| match_class(g, p, k, e)).collect();
            }
            envs
        }
        Kind::Assoc => {
            let ks: Vec<ClassId> = kids.iter().map(|k| k.0).collect();
            match_assoc(g, items, &ks, env)
        }
        Kind::Aci | Kind::Ac => match_unordered(g, g.kind(op) == Kind::Ac, items, kids, env),
    })
}

/// The leaf groups of an opening tree: for each opened instance with no opening below
/// it, the classes directly under it. Empty for the stored children.
pub type Leaves = Vec<Vec<ClassId>>;

/// A canonical view, and the leaf groups of every opening tree giving it.
pub type FlatView = (Vec<(ClassId, u64)>, Vec<Leaves>);

/// The flattened views of an `op` node whose children are `kids` (`:flatten`,
/// `doc/goal-flatten-and-engine-completion.md`, decision 2, as narrowed by
/// `doc/goal-canonical-flatten-views.md`, decision 2): each child class `X` is kept
/// whole, or replaced by the view of one of its `op` members, recursively, unless `X`
/// is already open on the path. The root's class is not on the path. Multiplicities
/// multiply through each opened member. Each view is canonized by the one
/// normalization (`nary_canon::normalize`), and a view whose canonical form is not a
/// node is dropped. Distinct canonical views, in sorted order, each with the leaf
/// groups of every opening tree that gives it.
pub fn views(g: &Graph, op: &str, kids: &[(ClassId, u64)]) -> Vec<FlatView> {
    #[allow(clippy::type_complexity)]
    fn raw(
        g: &Graph,
        op: &str,
        kids: &[(ClassId, u64)],
        mult: u64,
        path: &[ClassId],
    ) -> Vec<(Vec<(ClassId, u64)>, Leaves)> {
        let mut acc: Vec<(Vec<(ClassId, u64)>, Leaves)> = vec![(vec![], vec![])];
        for &(x, j) in kids {
            let k = mult * j;
            let mut opts: Vec<(Vec<(ClassId, u64)>, Leaves)> = vec![(vec![(x, k)], vec![])];
            if !path.contains(&x) {
                let mut p = path.to_vec();
                p.push(x);
                for m in g.classes[x]
                    .iter()
                    .filter(|m| m.lit.is_none() && m.op == op)
                {
                    let mk: Vec<(ClassId, u64)> = if g.kind(op) == Kind::Ac {
                        m.kids
                            .iter()
                            .copied()
                            .zip(m.mults.iter().copied())
                            .collect()
                    } else {
                        m.kids.iter().map(|&c| (c, 1)).collect()
                    };
                    for (v, leaves) in raw(g, op, &mk, k, &p) {
                        let leaves = if leaves.is_empty() {
                            vec![v.iter().map(|e| e.0).collect()]
                        } else {
                            leaves
                        };
                        opts.push((v, leaves));
                    }
                }
            }
            let mut next = Vec::new();
            for (av, al) in &acc {
                for (ov, ol) in &opts {
                    let mut v = av.clone();
                    v.extend_from_slice(ov);
                    let mut l = al.clone();
                    l.extend(ol.iter().cloned());
                    next.push((v, l));
                }
            }
            acc = next;
        }
        acc
    }
    use semi_persistent_egraph::multiplicity::{Multiplicity, MultiplicityLike};
    use semi_persistent_egraph::nary_canon::{NaryKind, NaryLaws, Normal, normalize};
    let laws = g.laws.get(op).cloned().unwrap_or(NaryLaws {
        kind: match g.kind(op) {
            Kind::Ac => NaryKind::Ac { nilpotent: None },
            Kind::Aci => NaryKind::Aci,
            Kind::Assoc | Kind::Plain => NaryKind::Assoc,
        },
        unit: None,
        inverse: None,
    });
    // The class of `inv(x)`: a member of operator `inv` over the single child `x`.
    let inverse_class = |inv: String, x: ClassId| {
        g.classes.iter().position(|ms| {
            ms.iter()
                .any(|m| m.lit.is_none() && m.op == inv && m.kids == [x])
        })
    };
    let mut by_view: BTreeMap<Vec<(ClassId, u64)>, Vec<Leaves>> = BTreeMap::new();
    for (v, leaves) in raw(g, op, kids, 1, &[]) {
        let mut kids: Vec<(ClassId, Multiplicity)> = v
            .into_iter()
            .map(|(c, k)| {
                (
                    c,
                    Multiplicity::try_from_u64(k).expect("a multiplicity in range"),
                )
            })
            .collect();
        if normalize(&laws, &mut kids, inverse_class) == Normal::Node {
            let c: Vec<(ClassId, u64)> = kids
                .into_iter()
                .map(|(c, k)| (c, k.to_u64().expect("a test count fits u64")))
                .collect();
            by_view.entry(c).or_default().push(leaves);
        }
    }
    by_view.into_iter().collect()
}

/// Every match at an `op` node under `:flatten`: the union, as a set, of its views'
/// matches ("§Edge cases 2: A node's matches are therefore a set of binding
/// environments"), each kept by the demand rule (`doc/goal-canonical-flatten-views.md`,
/// decision 2): for some opening tree giving the view, every leaf directly holds a class
/// an item takes. The items take every element the bare sequences do not.
pub fn match_flattened(
    g: &Graph,
    op: &str,
    items: &[Item],
    kids: &[(ClassId, u64)],
    env: &Env,
) -> Vec<Env> {
    let bare: Vec<&String> = items
        .iter()
        .filter_map(|i| if let Item::Bare(n) = i { Some(n) } else { None })
        .collect();
    let mut out = Vec::new();
    for (v, alts) in views(g, op, kids) {
        for m in match_children(g, op, items, &v, env) {
            // Count each class's elements, then remove those the bare sequences hold.
            let mut left: BTreeMap<ClassId, i64> = BTreeMap::new();
            for &(c, _) in &v {
                *left.entry(c).or_default() += 1;
            }
            for n in &bare {
                if let Some(Val::Seq(xs)) = m.get(*n) {
                    for x in xs {
                        if let Val::Class(c) = x {
                            *left.entry(*c).or_default() -= 1;
                        }
                    }
                }
            }
            let taken: std::collections::BTreeSet<ClassId> = left
                .into_iter()
                .filter(|&(_, k)| k > 0)
                .map(|(c, _)| c)
                .collect();
            if alts.iter().any(|leaves| {
                leaves
                    .iter()
                    .all(|grp| grp.iter().any(|c| taken.contains(c)))
            }) {
                out.push(m);
            }
        }
    }
    set(out)
}

/// The old entry point: an A or ACI node's children as classes.
pub fn match_node(g: &Graph, op: &str, items: &[Item], kids: &[ClassId], env: &Env) -> Vec<Env> {
    let kids: Vec<(ClassId, u64)> = kids.iter().map(|&k| (k, 1)).collect();
    match_children(g, op, items, &kids, env)
}

/// The matches of a filter's base against one child: each is the child's local
/// bindings, from a fresh environment ("§Grammar: Variables under a filter are
/// sequence variables, one entry per matched child"). Deduplicated:
/// "§Edge cases 2: Filter rows are deduplicated by their bindings, not by member".
fn element_matches(g: &Graph, base: &Pat, c: ClassId) -> Vec<Env> {
    assert!(is_base(base), "§Grammar: filters do not nest");
    set(match_class(g, base, c, &Env::new()))
}

fn matches_base(g: &Graph, base: &Pat, c: ClassId) -> bool {
    !element_matches(g, base, c).is_empty()
}

fn insert_new(e: &mut Env, k: String, v: Val) {
    if e.insert(k.clone(), v).is_some() {
        panic!("'{k}' is bound twice");
    }
}

/// Binds a filter's name and its variables as sequences, one entry per child, in
/// the children's order; under AC also the multiplicity column and the filter's
/// multiplicity variable.
#[allow(clippy::too_many_arguments)]
fn bind_filter(
    g: &Graph,
    env: &Env,
    name: &str,
    base: &Pat,
    mult: &Option<Mult>,
    ac: bool,
    kids: &[(ClassId, u64)],
    locals: &[&Env],
) -> Env {
    let mut e = env.clone();
    insert_new(
        &mut e,
        name.to_string(),
        Val::Seq(kids.iter().map(|&(k, _)| Val::Class(k)).collect()),
    );
    let mut vars = Vec::new();
    base_vars(g, base, &mut vars);
    for v in vars {
        let col: Vec<Val> = locals.iter().map(|l| l[&v].clone()).collect();
        insert_new(&mut e, v.clone(), Val::Seq(col));
    }
    if ac {
        let col = Val::Seq(kids.iter().map(|&(_, m)| Val::Int(m)).collect());
        insert_new(&mut e, mult_column(name), col.clone());
        // "§Multiplicities and `zip`: outside, `k : Seq(mult)`, parallel to `xs`".
        if let Some(Mult { var: Some(k), .. }) = mult {
            insert_new(&mut e, k.clone(), col);
        }
    }
    e
}

/// The cartesian product of per-child choices.
fn product<T: Clone>(choices: &[Vec<T>]) -> Vec<Vec<T>> {
    let mut out = vec![vec![]];
    for cs in choices {
        out = out
            .iter()
            .flat_map(|p| {
                cs.iter().map(move |c| {
                    let mut q = p.clone();
                    q.push(c.clone());
                    q
                })
            })
            .collect();
    }
    out
}

// ── A ──────────────────────────────────────────────────────────────────────────

/// "§Semantics, Under A: the items, concatenated in written order, cover all the
/// children ... Every parse is a match."
fn match_assoc(g: &Graph, items: &[Item], kids: &[ClassId], env: &Env) -> Vec<Env> {
    let mut out = Vec::new();
    let mut spans = Vec::new();
    assoc_go(g, items, kids, 0, 0, env, &mut spans, &mut out);
    out
}

#[allow(clippy::too_many_arguments)]
fn assoc_go(
    g: &Graph,
    items: &[Item],
    kids: &[ClassId],
    it: usize,
    pos: usize,
    env: &Env,
    spans: &mut Vec<(usize, usize)>,
    out: &mut Vec<Env>,
) {
    let n = kids.len();
    if it == items.len() {
        // "cover all the children".
        if pos == n && maximal_assoc(g, items, kids, spans) {
            out.push(env.clone());
        }
        return;
    }
    match &items[it] {
        // "§Semantics table, A: `pattern`: the next child".
        Item::One(p, _) => {
            if pos < n {
                for e in match_class(g, p, kids[pos], env) {
                    spans.push((pos, pos + 1));
                    assoc_go(g, items, kids, it + 1, pos + 1, &e, spans, out);
                    spans.pop();
                }
            }
        }
        // "`..name`: a gap: zero or more consecutive children".
        Item::Bare(name) => {
            for end in pos..=n {
                let mut e = env.clone();
                insert_new(
                    &mut e,
                    name.clone(),
                    Val::Seq(kids[pos..end].iter().map(|&k| Val::Class(k)).collect()),
                );
                spans.push((pos, end));
                assoc_go(g, items, kids, it + 1, end, &e, spans, out);
                spans.pop();
            }
        }
        // "`(..name base)`: a run: zero or more consecutive children matching `base`".
        Item::Filter {
            name,
            base,
            except,
            mult,
        } => {
            assert!(except.is_none(), "`:except` is an AC and ACI construct");
            for end in pos..=n {
                let per_child: Vec<Vec<Env>> = kids[pos..end]
                    .iter()
                    .map(|&k| element_matches(g, base, k))
                    .collect();
                if per_child.iter().any(|c| c.is_empty()) {
                    break; // a longer run contains this non-matching child too
                }
                let taken: Vec<(ClassId, u64)> = kids[pos..end].iter().map(|&k| (k, 1)).collect();
                for combo in product(&per_child) {
                    let locals: Vec<&Env> = combo.iter().collect();
                    let e = bind_filter(g, env, name, base, mult, false, &taken, &locals);
                    spans.push((pos, end));
                    assoc_go(g, items, kids, it + 1, end, &e, spans, out);
                    spans.pop();
                }
            }
        }
    }
}

/// "§Semantics, Under A: A run next to a gap is maximal toward it: the gap's adjacent
/// child does not match the run's pattern. This holds for an empty run too".
fn maximal_assoc(g: &Graph, items: &[Item], kids: &[ClassId], spans: &[(usize, usize)]) -> bool {
    for w in 0..items.len().saturating_sub(1) {
        match (&items[w], &items[w + 1]) {
            // A run followed by a gap: the gap's first child must not match the run.
            (Item::Filter { base, .. }, Item::Bare(_)) => {
                let (s, e) = spans[w + 1];
                if s < e && matches_base(g, base, kids[s]) {
                    return false;
                }
            }
            // A gap followed by a run: the gap's last child must not match the run.
            (Item::Bare(_), Item::Filter { base, .. }) => {
                let (s, e) = spans[w];
                if s < e && matches_base(g, base, kids[e - 1]) {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

// ── AC and ACI ─────────────────────────────────────────────────────────────────

/// "§Semantics, Under AC and ACI: Simple items take distinct children first, every
/// assignment enumerated ... Filters then take every remaining child matching their
/// pattern ... a child matching several is assigned to each in turn ... The bare
/// sequence takes the rest".
fn match_unordered(
    g: &Graph,
    ac: bool,
    items: &[Item],
    kids: &[(ClassId, u64)],
    env: &Env,
) -> Vec<Env> {
    let ones: Vec<(&Pat, &Option<Mult>)> = items
        .iter()
        .filter_map(|i| {
            if let Item::One(p, m) = i {
                Some((p, m))
            } else {
                None
            }
        })
        .collect();
    let filters: Vec<&Item> = items
        .iter()
        .filter(|i| matches!(i, Item::Filter { .. }))
        .collect();
    let bares: Vec<&String> = items
        .iter()
        .filter_map(|i| if let Item::Bare(n) = i { Some(n) } else { None })
        .collect();
    // "§Semantics table, AC and ACI: `..name` ... at most one per node".
    assert!(bares.len() <= 1, "two bare sequences under AC or ACI");
    let mut out = Vec::new();
    let mut used = vec![false; kids.len()];
    ones_go(
        g,
        ac,
        &ones,
        0,
        &filters,
        bares.first().copied(),
        kids,
        &mut used,
        env,
        &mut out,
    );
    out
}

/// "Simple items take distinct children first". Under AC an unannotated element
/// takes only a child of multiplicity exactly 1, and an annotated one a child whose
/// multiplicity the annotation accepts, binding its variable (Semper design chapter
/// 9, maximum partition).
#[allow(clippy::too_many_arguments)]
fn ones_go(
    g: &Graph,
    ac: bool,
    ones: &[(&Pat, &Option<Mult>)],
    i: usize,
    filters: &[&Item],
    bare: Option<&String>,
    kids: &[(ClassId, u64)],
    used: &mut Vec<bool>,
    env: &Env,
    out: &mut Vec<Env>,
) {
    if i == ones.len() {
        let rest: Vec<(ClassId, u64)> = kids
            .iter()
            .zip(used.iter())
            .filter(|(_, u)| !**u)
            .map(|(k, _)| *k)
            .collect();
        filters_go(g, ac, filters, bare, &rest, env, out);
        return;
    }
    let (p, mult) = ones[i];
    for j in 0..kids.len() {
        if used[j] {
            continue;
        }
        let (k, m) = kids[j];
        let mut base = env.clone();
        match mult {
            None if m != 1 => continue,
            None => {}
            Some(ms) => {
                if !ms.accepts(m) {
                    continue;
                }
                if let Some(v) = &ms.var {
                    match base.get(v) {
                        Some(Val::Int(b)) if *b != m => continue,
                        Some(Val::Int(_)) => {}
                        Some(other) => panic!("'{v}' is {other:?}, not a multiplicity"),
                        None => {
                            base.insert(v.clone(), Val::Int(m));
                        }
                    }
                }
            }
        }
        for e in match_class(g, p, k, &base) {
            used[j] = true;
            ones_go(g, ac, ones, i + 1, filters, bare, kids, used, &e, out);
            used[j] = false;
        }
    }
}

/// "Filters then take every remaining child matching their pattern; ... a child
/// matching several is assigned to each in turn, every assignment a match. `:except
/// other` removes the children `other`'s pattern matches ... The bare sequence takes
/// the rest". Under AC a filter's multiplicity annotation restricts which children
/// it takes; an unannotated filter takes any multiplicity (decision of 2026-09-29).
fn filters_go(
    g: &Graph,
    ac: bool,
    filters: &[&Item],
    bare: Option<&String>,
    rest: &[(ClassId, u64)],
    env: &Env,
    out: &mut Vec<Env>,
) {
    let parts: Vec<(&String, &Pat, &Option<String>, &Option<Mult>)> = filters
        .iter()
        .map(|f| match f {
            Item::Filter {
                name,
                base,
                except,
                mult,
            } => (name, base, except, mult),
            _ => unreachable!(),
        })
        .collect();
    // Phase 1: each filter's matches on each remaining child, the multiplicity
    // annotation included.
    let matched: Vec<Vec<Vec<Env>>> = parts
        .iter()
        .map(|(_, base, _, mult)| {
            rest.iter()
                .map(|&(k, m)| {
                    // An unannotated filter takes a child of multiplicity exactly 1, as
                    // an unannotated ordinary AC element does: absent multiplicity means 1
                    // in every rule (decided 2026-09-30). Under ACI and A every
                    // multiplicity is 1, so this is a restriction under AC only.
                    let ok = match mult.as_ref() {
                        Some(ms) => ms.accepts(m),
                        None => m == 1,
                    };
                    if ok {
                        element_matches(g, base, k)
                    } else {
                        vec![]
                    }
                })
                .collect()
        })
        .collect();
    let index = |name: &str| {
        parts
            .iter()
            .position(|p| p.0.as_str() == name)
            .unwrap_or_else(|| panic!("`:except {name}` names no sibling filter"))
    };
    // Per child: the (filter, local match) choices; empty means the bare sequence.
    let mut choices: Vec<Vec<(usize, Env)>> = Vec::new();
    // `ci` indexes every filter's row of `matched`, not one sequence.
    #[allow(clippy::needless_range_loop)]
    for ci in 0..rest.len() {
        let mut cs = Vec::new();
        for (fi, (_, _, except, _)) in parts.iter().enumerate() {
            if let Some(other) = except
                && !matched[index(other)][ci].is_empty()
            {
                continue;
            }
            for m in &matched[fi][ci] {
                cs.push((fi, m.clone()));
            }
        }
        choices.push(cs);
    }
    let to_bare: Vec<(ClassId, u64)> = rest
        .iter()
        .zip(&choices)
        .filter(|(_, c)| c.is_empty())
        .map(|(k, _)| *k)
        .collect();
    if bare.is_none() && !to_bare.is_empty() {
        return;
    }
    let branching: Vec<usize> = (0..rest.len())
        .filter(|&ci| !choices[ci].is_empty())
        .collect();
    let per: Vec<Vec<(usize, Env)>> = branching.iter().map(|&ci| choices[ci].clone()).collect();
    for combo in product(&per) {
        let mut e = env.clone();
        for (fi, (name, base, _, mult)) in parts.iter().enumerate() {
            let taken: Vec<((ClassId, u64), &Env)> = branching
                .iter()
                .zip(combo.iter())
                .filter(|(_, (f, _))| *f == fi)
                .map(|(&ci, (_, l))| (rest[ci], l))
                .collect();
            let ks: Vec<(ClassId, u64)> = taken.iter().map(|(k, _)| *k).collect();
            let ls: Vec<&Env> = taken.iter().map(|(_, l)| *l).collect();
            e = bind_filter(g, &e, name, base, mult, ac, &ks, &ls);
        }
        if let Some(b) = bare {
            insert_new(
                &mut e,
                b.clone(),
                Val::Seq(to_bare.iter().map(|&(k, _)| Val::Class(k)).collect()),
            );
            if ac {
                insert_new(
                    &mut e,
                    mult_column(b),
                    Val::Seq(to_bare.iter().map(|&(_, m)| Val::Int(m)).collect()),
                );
            }
        }
        out.push(e);
    }
}
