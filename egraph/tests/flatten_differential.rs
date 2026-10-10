// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `:flatten` for ordinary rules (`Step::Flatten`) against a brute-force reference.
//!
//! The reference computes every flattened view of a node by recursion over a model of
//! the e-graph read back through its public accessors, independently of the engine's
//! enumerator, and matches each pattern against those views. The engine's matches,
//! projected onto the pattern's own variables and the root node, must equal the
//! reference's as multisets: a missing match, an extra one, and a duplicated one are
//! all differences. Without the tag the reference reads the stored children only, so
//! the same comparison also pins that an untagged rule matches as before.
//!
//! **Views** (`doc/goal-flatten-and-engine-completion.md`, decision 2 and task 3). For a
//! node `n` of an n-ary operator `f`, each child class `X` contributes one of:
//! - `X` itself, kept whole, unless every member of `X` is an `f` node (a class with no
//!   member visible to the matcher is kept, so that a shielded or fully subsumed child
//!   behaves as it does without the tag);
//! - for each `f` member `m` of `X`, the view of `m`'s children, recursively, unless `X`
//!   is already open on the path from `n`. The root's own class is not on the path.
//!
//! A view is normalized by kind: a sequence in order for `:assoc`, a multiset with
//! multiplied and summed multiplicities for AC, a set for ACI. Distinct views are
//! matched once each. "Member" means a node the matcher's index holds: not subsumed,
//! in a matchable class.

use std::collections::{BTreeMap, BTreeSet};

use semi_persistent_egraph::config::EGraphConfig;
use semi_persistent_egraph::ematch::run_query;
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::index::{IndexStore, VariantIndex};
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::multiplicity::MultiplicityLike;
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::registry::OpKind;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::schedule::{IndexStats, schedule_with_stats};

type EG = semi_persistent_egraph::EGraph<DefaultConfig, MachineLit, true, false>;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

// ── The model ────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Plain,
    Assoc,
    Ac,
    Aci,
}

/// A class id of the round's snapshot, as a plain number.
type Class = u64;

#[derive(Clone, Debug)]
struct Node {
    id: u64,
    op: OpId,
    /// The children, canonical, in stored order; the multiplicity is 1 except under AC.
    kids: Vec<(Class, u64)>,
}

/// The e-graph as the matcher sees it after a rebuild: each class's members.
struct Model {
    members: BTreeMap<Class, Vec<Node>>,
    kinds: BTreeMap<OpId, Kind>,
    names: BTreeMap<String, OpId>,
    /// Each operator's laws, its unit resolved to a model class: the input of the one
    /// normalization (`nary_canon::normalize`), which the reference calls.
    laws: BTreeMap<OpId, semi_persistent_egraph::nary_canon::NaryLaws<Class, OpId>>,
}

impl Model {
    fn read(eg: &EG, index: &IndexStore<DefaultConfig>) -> Model {
        let canon = |g: ENodeId| -> Class {
            index
                .round_repr(g)
                .unwrap_or_else(|| eg.find_const(g))
                .to_usize() as Class
        };
        let mut kinds = BTreeMap::new();
        let mut laws = BTreeMap::new();
        let mut names = BTreeMap::new();
        let mut members: BTreeMap<Class, Vec<Node>> = BTreeMap::new();
        for id in eg.node_ids() {
            if eg.node_flags(id) & semi_persistent_egraph::node_types::FLAG_SUBSUMED != 0
                || eg.is_class_matchable(id) == Some(false)
            {
                continue;
            }
            let op = eg.node_op(id);
            let kind = match &eg.ops().info(op).kind {
                OpKind::A { .. } => Kind::Assoc,
                OpKind::MSet { .. } => Kind::Ac,
                OpKind::Set { .. } => Kind::Aci,
                _ => Kind::Plain,
            };
            kinds.insert(op, kind);
            names.insert(eg.node_op_name(id).to_string(), op);
            let l = eg.nary_laws(op);
            laws.insert(
                op,
                semi_persistent_egraph::nary_canon::NaryLaws {
                    kind: l.kind,
                    unit: eg.unit_node(op).map(canon),
                    inverse: l.inverse,
                },
            );
            let kids: Vec<(Class, u64)> = match kind {
                Kind::Plain => {
                    let mut b = Vec::new();
                    eg.for_each_child(id, |c, _| b.push((canon(c), 1)));
                    b
                }
                Kind::Assoc => {
                    let mut b = Vec::new();
                    eg.seq_children(id, &mut b);
                    b.into_iter().map(|c| (canon(c), 1)).collect()
                }
                Kind::Ac => {
                    let mut b = Vec::new();
                    eg.mset_children(id, &mut b);
                    b.into_iter()
                        .map(|(c, m)| (canon(c), m.to_u64().expect("a test count fits u64")))
                        .collect()
                }
                Kind::Aci => {
                    let mut b = Vec::new();
                    eg.set_children(id, &mut b);
                    b.into_iter().map(|c| (canon(c), 1)).collect()
                }
            };
            members.entry(canon(id)).or_default().push(Node {
                id: id.to_usize() as u64,
                op,
                kids,
            });
        }
        Model {
            members,
            kinds,
            names,
            laws,
        }
    }

    fn members(&self, c: Class) -> &[Node] {
        self.members.get(&c).map_or(&[], |v| v.as_slice())
    }

    fn op(&self, name: &str) -> Option<OpId> {
        self.names.get(name).copied()
    }
}

// ── Reference views ──────────────────────────────────────────────────────────

type View = Vec<(Class, u64)>;

/// Every raw view of `n`'s children under operator `f`, before normalization: the
/// product, over the children, of each child's options.
/// The leaf groups of an opening tree: for each opened instance with no opening below
/// it, the classes directly under it. An empty list is the stored children, opened
/// nowhere.
type Leaves = Vec<Vec<Class>>;

/// Every raw view of `n`'s children under operator `f`, before normalization, with the
/// leaf groups of its opening tree: the product, over the children, of each child's
/// options. A child class is always kept whole as one option; an `f` member of it is
/// opened as another, unless the class is already open on the path
/// (`doc/goal-canonical-flatten-views.md`, decision 2: only a needed opening makes a
/// match, so keeping is never excluded).
fn raw_views(
    model: &Model,
    n: &Node,
    f: OpId,
    mult: u64,
    path: &BTreeSet<Class>,
) -> Vec<(View, Leaves)> {
    let mut acc: Vec<(View, Leaves)> = vec![(Vec::new(), Vec::new())];
    for &(x, j) in &n.kids {
        let k = mult * j;
        let mut opts: Vec<(View, Leaves)> = vec![(vec![(x, k)], Vec::new())];
        if !path.contains(&x) {
            let mut p = path.clone();
            p.insert(x);
            for m in model.members(x).iter().filter(|m| m.op == f) {
                for (v, leaves) in raw_views(model, m, f, k, &p) {
                    // Nothing opened below: this instance is a leaf, its group the
                    // classes directly under it.
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

/// The opening trees that give one canonical view, each as its leaf groups.
type Alts = Vec<Leaves>;

/// The demand rule (decision 2): a match is kept when, for some opening tree giving its
/// view, every leaf directly holds a class the items take. Interior openings are then
/// needed through the leaves below them. The stored view has no leaves.
fn demanded(alts: &Alts, taken: &BTreeSet<Class>) -> bool {
    alts.iter()
        .any(|leaves| leaves.iter().all(|g| g.iter().any(|c| taken.contains(c))))
}

/// A raw view canonized by the one normalization (`nary_canon::normalize`), with the
/// operator's laws and the model's inverse lookup; `None` when its canonical form is not
/// a node, which is then not matched.
fn canonical(model: &Model, op: OpId, v: View) -> Option<View> {
    use semi_persistent_egraph::multiplicity::Multiplicity;
    use semi_persistent_egraph::nary_canon::{Normal, normalize};
    let laws = model.laws[&op];
    let mut kids: Vec<(Class, Multiplicity)> = v
        .iter()
        .map(|&(c, k)| {
            (
                c,
                Multiplicity::try_from_u64(k).expect("a multiplicity in range"),
            )
        })
        .collect();
    let inverse_class = |inv: OpId, x: Class| {
        model
            .members
            .iter()
            .find(|(_, ms)| {
                ms.iter()
                    .any(|m| m.op == inv && m.kids.first().map(|k| k.0) == Some(x))
            })
            .map(|(c, _)| *c)
    };
    match normalize(&laws, &mut kids, inverse_class) {
        Normal::Node => Some(
            kids.into_iter()
                .map(|(c, k)| (c, k.to_u64().expect("a test count fits u64")))
                .collect(),
        ),
        _ => None,
    }
}

/// The views `n` is matched against: the stored children without the tag, every
/// distinct normalized view with it.
fn views(model: &Model, n: &Node, flatten: bool) -> Vec<(View, Alts)> {
    if !flatten {
        return vec![(n.kids.clone(), vec![Vec::new()])];
    }
    let mut by_view: BTreeMap<View, Alts> = BTreeMap::new();
    for (v, leaves) in raw_views(model, n, n.op, 1, &BTreeSet::new()) {
        if let Some(c) = canonical(model, n.op, v) {
            by_view.entry(c).or_default().push(leaves);
        }
    }
    by_view.into_iter().collect()
}

// ── Patterns ─────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
enum Rest {
    None,
    /// Leading (`:assoc` only) or, for every kind, trailing.
    Pre(String),
    Suf(String),
}

#[derive(Clone, Debug)]
enum P {
    Var(String),
    /// A plain operator over its children, positionally.
    App(String, Vec<P>),
    NAry(String, Vec<P>, Rest),
}

fn v(s: &str) -> P {
    P::Var(s.into())
}
fn app(op: &str, ps: Vec<P>) -> P {
    P::App(op.into(), ps)
}
fn nary(op: &str, ps: Vec<P>) -> P {
    P::NAry(op.into(), ps, Rest::None)
}
fn nary_suf(op: &str, ps: Vec<P>, r: &str) -> P {
    P::NAry(op.into(), ps, Rest::Suf(r.into()))
}
fn nary_pre(op: &str, ps: Vec<P>, r: &str) -> P {
    P::NAry(op.into(), ps, Rest::Pre(r.into()))
}

fn surface(p: &P) -> String {
    match p {
        P::Var(x) => x.clone(),
        P::App(op, ps) => {
            let kids: Vec<String> = ps.iter().map(surface).collect();
            format!("({op} {})", kids.join(" "))
        }
        P::NAry(op, ps, rest) => {
            let kids: Vec<String> = ps.iter().map(surface).collect();
            match rest {
                Rest::None => format!("({op} {})", kids.join(" ")),
                Rest::Pre(r) => format!("({op} ..{r} {})", kids.join(" ")),
                Rest::Suf(r) => format!("({op} {} ..{r})", kids.join(" ")),
            }
        }
    }
}

/// The variables a match is projected onto: every pattern variable and rest.
fn vars(p: &P, out: &mut BTreeSet<String>) {
    match p {
        P::Var(x) => {
            out.insert(x.clone());
        }
        P::App(_, ps) => ps.iter().for_each(|q| vars(q, out)),
        P::NAry(_, ps, rest) => {
            ps.iter().for_each(|q| vars(q, out));
            if let Rest::Pre(r) | Rest::Suf(r) = rest {
                out.insert(r.clone());
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Val {
    Class(Class),
    /// A rest: a sequence in order, or a set or multiset sorted by class.
    Rest(Vec<(Class, u64)>),
}

type Env = BTreeMap<String, Val>;

// ── The reference matcher ────────────────────────────────────────────────────

fn bind(env: &Env, x: &str, val: Val) -> Option<Env> {
    match env.get(x) {
        Some(prev) if *prev != val => None,
        Some(_) => Some(env.clone()),
        None => {
            let mut e = env.clone();
            e.insert(x.to_string(), val);
            Some(e)
        }
    }
}

/// Every way `p` matches class `c` extending `env`, once per member and view, as the
/// engine enumerates them.
fn match_class(model: &Model, p: &P, c: Class, env: &Env, flatten: bool) -> Vec<Env> {
    match p {
        P::Var(x) => bind(env, x, Val::Class(c)).into_iter().collect(),
        P::App(op, ps) => {
            let Some(o) = model.op(op) else { return vec![] };
            let mut out = Vec::new();
            for m in model.members(c).iter().filter(|m| m.op == o) {
                if m.kids.len() != ps.len() {
                    continue;
                }
                let mut envs = vec![env.clone()];
                for (q, &(k, _)) in ps.iter().zip(&m.kids) {
                    envs = envs
                        .iter()
                        .flat_map(|e| match_class(model, q, k, e, flatten))
                        .collect();
                }
                out.extend(envs);
            }
            out
        }
        P::NAry(op, ps, rest) => {
            let Some(o) = model.op(op) else { return vec![] };
            let mut out = Vec::new();
            for m in model.members(c).iter().filter(|m| m.op == o) {
                out.extend(match_node(model, m, ps, rest, env, flatten));
            }
            out
        }
    }
}

fn match_node(
    model: &Model,
    n: &Node,
    ps: &[P],
    rest: &Rest,
    env: &Env,
    flatten: bool,
) -> Vec<Env> {
    let kind = model.kinds[&n.op];
    let mut out = Vec::new();
    for (view, alts) in views(model, n, flatten) {
        let d = Demand {
            alts: &alts,
            flatten,
        };
        match kind {
            Kind::Assoc | Kind::Plain => match_seq(model, ps, rest, &view, env, &d, &mut out),
            Kind::Aci => {
                let mut used = vec![false; view.len()];
                match_aci(model, ps, 0, rest, &view, &mut used, env, &d, &mut out)
            }
            Kind::Ac => {
                let mut res: Vec<(Class, u64)> = view.clone();
                match_ac(model, ps, 0, rest, &mut res, env, &d, &mut out)
            }
        }
    }
    out
}

/// A view's opening trees, and whether item patterns match flattened.
struct Demand<'a> {
    alts: &'a Alts,
    flatten: bool,
}

fn match_seq(
    model: &Model,
    ps: &[P],
    rest: &Rest,
    view: &[(Class, u64)],
    env: &Env,
    d: &Demand<'_>,
    out: &mut Vec<Env>,
) {
    let flatten = d.flatten;
    // The fixed items' slice of the view, and the rest's name and slice.
    type Split<'a> = (&'a [(Class, u64)], Option<(&'a String, &'a [(Class, u64)])>);
    let (fixed, r): Split<'_> = match rest {
        Rest::None if view.len() == ps.len() => (view, None),
        Rest::Suf(name) if view.len() >= ps.len() => {
            (&view[..ps.len()], Some((name, &view[ps.len()..])))
        }
        Rest::Pre(name) if view.len() >= ps.len() => {
            let split = view.len() - ps.len();
            (&view[split..], Some((name, &view[..split])))
        }
        _ => return,
    };
    let taken: BTreeSet<Class> = fixed.iter().map(|e| e.0).collect();
    if !demanded(d.alts, &taken) {
        return;
    }
    let mut envs = vec![env.clone()];
    for (q, &(k, _)) in ps.iter().zip(fixed) {
        envs = envs
            .iter()
            .flat_map(|e| match_class(model, q, k, e, flatten))
            .collect();
    }
    for e in envs {
        match r {
            None => out.push(e),
            Some((name, s)) => {
                let val = Val::Rest(s.iter().map(|&(c, _)| (c, 1)).collect());
                out.extend(bind(&e, name, val));
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn match_aci(
    model: &Model,
    ps: &[P],
    i: usize,
    rest: &Rest,
    view: &[(Class, u64)],
    used: &mut Vec<bool>,
    env: &Env,
    d: &Demand<'_>,
    out: &mut Vec<Env>,
) {
    let flatten = d.flatten;
    if i == ps.len() {
        let taken: BTreeSet<Class> = (0..view.len())
            .filter(|&j| used[j])
            .map(|j| view[j].0)
            .collect();
        if !demanded(d.alts, &taken) {
            return;
        }
        match rest {
            Rest::None => {
                if used.iter().all(|&u| u) {
                    out.push(env.clone());
                }
            }
            Rest::Pre(name) | Rest::Suf(name) => {
                let mut s: Vec<(Class, u64)> = (0..view.len())
                    .filter(|&j| !used[j])
                    .map(|j| (view[j].0, 1))
                    .collect();
                s.sort();
                out.extend(bind(env, name, Val::Rest(s)));
            }
        }
        return;
    }
    // A bound variable takes the first unused position of its class, as the engine's
    // decomposition does; on a normalized set there is at most one.
    if let P::Var(x) = &ps[i]
        && let Some(Val::Class(c)) = env.get(x)
    {
        if let Some(j) = (0..view.len()).find(|&j| !used[j] && view[j].0 == *c) {
            used[j] = true;
            match_aci(model, ps, i + 1, rest, view, used, env, d, out);
            used[j] = false;
        }
        return;
    }
    for j in 0..view.len() {
        if used[j] {
            continue;
        }
        used[j] = true;
        for e in match_class(model, &ps[i], view[j].0, env, flatten) {
            match_aci(model, ps, i + 1, rest, view, used, &e, d, out);
        }
        used[j] = false;
    }
}

/// AC: an unannotated item takes an entry of multiplicity exactly 1 (§7.5).
#[allow(clippy::too_many_arguments)]
fn match_ac(
    model: &Model,
    ps: &[P],
    i: usize,
    rest: &Rest,
    res: &mut Vec<(Class, u64)>,
    env: &Env,
    d: &Demand<'_>,
    out: &mut Vec<Env>,
) {
    let flatten = d.flatten;
    if i == ps.len() {
        // An item takes a whole entry, so the entries it took are the zeroed ones.
        let taken: BTreeSet<Class> = res.iter().filter(|e| e.1 == 0).map(|e| e.0).collect();
        if !demanded(d.alts, &taken) {
            return;
        }
        match rest {
            Rest::None => {
                if res.iter().all(|&(_, m)| m == 0) {
                    out.push(env.clone());
                }
            }
            Rest::Pre(name) | Rest::Suf(name) => {
                let mut s: Vec<(Class, u64)> =
                    res.iter().copied().filter(|&(_, m)| m > 0).collect();
                s.sort();
                out.extend(bind(env, name, Val::Rest(s)));
            }
        }
        return;
    }
    if let P::Var(x) = &ps[i]
        && let Some(Val::Class(c)) = env.get(x)
    {
        if let Some(j) = (0..res.len()).find(|&j| res[j].0 == *c && res[j].1 == 1) {
            res[j].1 = 0;
            match_ac(model, ps, i + 1, rest, res, env, d, out);
            res[j].1 = 1;
        }
        return;
    }
    for j in 0..res.len() {
        if res[j].1 != 1 {
            continue;
        }
        res[j].1 = 0;
        for e in match_class(model, &ps[i], res[j].0, env, flatten) {
            match_ac(model, ps, i + 1, rest, res, &e, d, out);
        }
        res[j].1 = 1;
    }
}

/// The reference's matches of a root pattern: one per root node, view, and way.
fn reference(model: &Model, p: &P, flatten: bool) -> BTreeMap<(u64, Env), usize> {
    let mut out = BTreeMap::new();
    let (op, ps, rest) = match p {
        P::NAry(op, ps, rest) => (op, ps.clone(), rest.clone()),
        P::App(op, ps) => (op, ps.clone(), Rest::None),
        P::Var(_) => unreachable!("a root pattern has an operator"),
    };
    let Some(o) = model.op(op) else { return out };
    for ms in model.members.values() {
        for n in ms.iter().filter(|m| m.op == o) {
            let envs = match p {
                P::NAry(..) => match_node(model, n, &ps, &rest, &Env::new(), flatten),
                _ => {
                    if n.kids.len() != ps.len() {
                        continue;
                    }
                    let mut envs = vec![Env::new()];
                    for (q, &(k, _)) in ps.iter().zip(&n.kids) {
                        envs = envs
                            .iter()
                            .flat_map(|e| match_class(model, q, k, e, flatten))
                            .collect();
                    }
                    envs
                }
            };
            for e in envs {
                *out.entry((n.id, e)).or_default() += 1;
            }
        }
    }
    out
}

// ── The engine ───────────────────────────────────────────────────────────────

fn engine(
    eg: &EG,
    index: &IndexStore<DefaultConfig>,
    p: &P,
    flatten: bool,
) -> BTreeMap<(u64, Env), usize> {
    let pats = semi_persistent_egraph::parser::parse_patterns(&surface(p)).expect("parse");
    let fq = semi_persistent_egraph::sortcheck::flatten_surface(&pats, eg.ops()).expect("flatten");
    let mut rq = semi_persistent_egraph::resolve::resolve(
        &fq,
        eg.ops(),
        eg.sorts(),
        &MachineModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .expect("resolve");
    rq.flatten = flatten;
    let root = rq.shape.find_var(&fq.root_vars[0]).expect("root");
    let plan = schedule_with_stats(&rq, &IndexStats::from_index(index));
    let globals = GlobalCtx::<SortId, ENodeId>::new();
    let ms = run_query(&plan, eg, &VariantIndex::naive(index), &globals);
    let canon = |g: ENodeId| -> Class {
        index
            .round_repr(g)
            .unwrap_or_else(|| eg.find_const(g))
            .to_usize() as Class
    };
    let mut names = BTreeSet::new();
    vars(p, &mut names);
    let shape = &rq.shape;
    let mut out = BTreeMap::new();
    for m in &ms {
        let mut env = Env::new();
        for x in &names {
            if let Some(vid) = shape.find_var(x) {
                env.insert(x.clone(), Val::Class(canon(m.get(vid))));
            } else if let Some(i) = shape.seqs.iter().position(|s| s == x) {
                let s = m.seq_slice(semi_persistent_egraph::ast::SeqVarId::new(
                    u16::try_from(i).expect("rest index"),
                ));
                env.insert(
                    x.clone(),
                    Val::Rest(s.iter().map(|&c| (canon(c), 1)).collect()),
                );
            } else if let Some(i) = shape.sets.iter().position(|s| s == x) {
                let s = m.set_slice(semi_persistent_egraph::ast::SetVarId::new(
                    u16::try_from(i).expect("rest index"),
                ));
                let mut r: Vec<(Class, u64)> = s.iter().map(|&c| (canon(c), 1)).collect();
                r.sort();
                env.insert(x.clone(), Val::Rest(r));
            } else if let Some(i) = shape.msets.iter().position(|s| s == x) {
                let s = m.mset_slice(semi_persistent_egraph::ast::MsetVarId::new(
                    u16::try_from(i).expect("rest index"),
                ));
                let mut r: Vec<(Class, u64)> = s
                    .iter()
                    .map(|c| {
                        (
                            canon(DefaultConfig::mset_child_id(c)),
                            DefaultConfig::mset_child_mult(c)
                                .to_u64()
                                .expect("a test count fits u64"),
                        )
                    })
                    .collect();
                r.sort();
                env.insert(x.clone(), Val::Rest(r));
            } else {
                panic!("variable {x} not in the query's shape");
            }
        }
        *out.entry((m.get(root).to_usize() as u64, env)).or_default() += 1;
    }
    out
}

// ── Graphs ───────────────────────────────────────────────────────────────────

const DECLS: &str = "\
(sort E)
(function l0 () E) (function l1 () E) (function l2 () E) (function l3 () E)
(function G (E) E)
(function H (E E) E)
(function And (E) E :assoc-comm-idem)
(function Or (E) E :assoc-comm-idem)
(function Plus (E) E :assoc-comm)
(function Seq (E) E :assoc)
(function S0 () E) (function S1 () E) (function S2 () E) (function S3 () E)
";

/// A random term over the declared operators. N-ary terms nest on purpose: under the
/// surface builder a nested same-operator child is flattened, under a rewrite's
/// right-hand side it is stored nested.
fn term(rng: &mut Rng, names: &[String], depth: u32) -> String {
    let leaf = |rng: &mut Rng| {
        if !names.is_empty() && rng.below(3) == 0 {
            names[rng.below(names.len() as u64) as usize].clone()
        } else {
            format!("(l{})", rng.below(4))
        }
    };
    if depth == 0 {
        return leaf(rng);
    }
    match rng.below(8) {
        0 => leaf(rng),
        1 => format!("(G {})", term(rng, names, depth - 1)),
        2..=5 => {
            let op = ["And", "Or", "Plus", "Seq"][rng.below(4) as usize];
            let k = 2 + rng.below(2);
            let mut kids: Vec<String> = Vec::new();
            for _ in 0..k {
                // A repeated child gives an AC multiplicity above 1.
                if !kids.is_empty() && op == "Plus" && rng.below(3) == 0 {
                    let again = kids[0].clone();
                    kids.push(again);
                } else {
                    kids.push(term(rng, names, depth - 1));
                }
            }
            format!("({op} {})", kids.join(" "))
        }
        _ => format!("(And {} {})", leaf(rng), term(rng, names, depth - 1)),
    }
}

/// A program that builds nesting by every route the goal names: right-hand sides
/// (`add` does not flatten), merges after construction, and cycles.
fn program(rng: &mut Rng) -> String {
    let mut p = String::from(DECLS);
    let mut names: Vec<String> = Vec::new();
    for i in 0..5 {
        let t = term(rng, &names, 2);
        p.push_str(&format!("(let v{i} {t})\n"));
        names.push(format!("v{i}"));
    }
    for k in 0..4 {
        let t = term(rng, &names, 3);
        p.push_str(&format!("(let s{k} (S{k}))\n(rewrite (S{k}) {t})\n"));
    }
    p.push_str("(run 1)\n");
    for k in 0..4 {
        names.push(format!("s{k}"));
    }
    for _ in 0..3 {
        let a = &names[rng.below(names.len() as u64) as usize];
        let b = &names[rng.below(names.len() as u64) as usize];
        p.push_str(&format!("(union {a} {b})\n"));
    }
    if rng.below(2) == 0 {
        // A cycle: the class gains a conjunction over itself.
        let a = &names[rng.below(names.len() as u64) as usize];
        p.push_str(&format!("(union {a} (And (l{}) {a}))\n", rng.below(4)));
    }
    if rng.below(2) == 0 {
        // A class with two conjunction members.
        let a = &names[rng.below(names.len() as u64) as usize];
        p.push_str(&format!(
            "(union {a} (And (l{}) (l{})))\n",
            rng.below(4),
            rng.below(4)
        ));
    }
    p
}

fn build(src: &str) -> EG {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src).expect("parse");
    let mut it =
        Interpreter::<DefaultConfig, MachineLit, MachineModel, true, false>::new(MachineModel);
    let mut globals = GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut it.eg,
        &it.model,
        &mut globals,
    )
    .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    let mut eg = it.eg;
    eg.rebuild();
    eg
}

fn patterns() -> Vec<P> {
    vec![
        nary("And", vec![v("x0"), v("x1")]),
        nary("And", vec![v("x0"), v("x1"), v("x2")]),
        nary_suf("And", vec![v("x0")], "r"),
        nary_suf("And", vec![app("G", vec![v("x0")])], "r"),
        nary_suf(
            "And",
            vec![app("G", vec![v("x0")]), app("G", vec![v("x1")])],
            "r",
        ),
        nary_suf("And", vec![v("x0"), app("G", vec![v("x0")])], "r"),
        nary_suf("And", vec![nary_suf("Or", vec![v("x0")], "q")], "r"),
        nary_suf("And", vec![nary("And", vec![v("x0"), v("x1")])], "r"),
        nary("Plus", vec![v("x0"), v("x1")]),
        nary_suf("Plus", vec![v("x0")], "r"),
        nary_suf("Plus", vec![app("G", vec![v("x0")])], "r"),
        nary("Seq", vec![v("x0"), v("x1")]),
        nary_suf("Seq", vec![v("x0")], "r"),
        nary_pre("Seq", vec![v("x0")], "r"),
        nary_suf("Seq", vec![app("G", vec![v("x0")])], "r"),
        app("G", vec![nary_suf("And", vec![v("x0")], "r")]),
        app("H", vec![v("x0"), nary_suf("Plus", vec![v("x1")], "r")]),
    ]
}

/// Compare engine and reference on `seeds` random programs, for every pattern.
/// Returns the matches compared, and how many (graph, pattern) pairs had a flattened
/// match set different from the untagged one, so the caller can require that the
/// comparison was not vacuous and that nesting was exercised.
fn differential(seeds: std::ops::Range<u64>, flatten: bool) -> (usize, usize) {
    let (mut compared, mut exercised) = (0, 0);
    for seed in seeds {
        let mut rng = Rng(seed.wrapping_mul(0x5851F42D4C957F2D) ^ 0xF1A7);
        let src = program(&mut rng);
        let eg = build(&src);
        let index = IndexStore::build(&eg);
        let model = Model::read(&eg, &index);
        for p in patterns() {
            let want = reference(&model, &p, flatten);
            compared += want.values().sum::<usize>();
            for runtime in [false, true] {
                semi_persistent_egraph::ematch::set_runtime_scheduling(runtime);
                let got = engine(&eg, &index, &p, flatten);
                assert_eq!(
                    got,
                    want,
                    "seed {seed}, pattern {}, flatten {flatten}, runtime scheduling {runtime}\n{src}",
                    surface(&p)
                );
            }
            semi_persistent_egraph::ematch::set_runtime_scheduling(false);
            if flatten && want != reference(&model, &p, false) {
                exercised += 1;
            }
        }
    }
    (compared, exercised)
}

/// Without the tag, the engine's matches are today's: the reference over stored
/// children. This also checks the reference's decomposition against the engine.
#[test]
fn untagged_matches_stored_children() {
    let (compared, _) = differential(0..60, false);
    assert!(compared > 1000, "too few matches compared: {compared}");
}

/// With the tag, the engine's matches are the reference's over every flattened view.
#[test]
fn flattened_matches_reference() {
    let (compared, exercised) = differential(0..60, true);
    eprintln!(
        "flatten differential: {compared} matches compared, {exercised} (graph, pattern) pairs changed by flattening"
    );
    assert!(compared > 1000, "too few matches compared: {compared}");
    assert!(
        exercised > 30,
        "too few (graph, pattern) pairs where flattening changed the matches: {exercised}"
    );
}

// ── Depth and bounds ─────────────────────────────────────────────────────────

/// An e-graph with `E`, a leaf `l0`, a successor `s` for distinct leaves, and an ACI `And`.
fn chain_graph() -> (EG, OpId, OpId, OpId) {
    let mut eg = EG::from_model(&MachineModel);
    let e = eg.intern_sort("E");
    let l0 = eg.register_op0("l0", e);
    let s = eg.register_op1("s", e, e);
    let and = eg.register_kind(
        "And",
        e,
        OpKind::Set {
            arg_sort: e,
            clamp: semi_persistent_egraph::registry::Clamp::Idempotent,
            identity: None,
            cancellative: false,
        },
    );
    (eg, l0, s, and)
}

/// Run `pattern` flattened, with its root bound to `root`: the matches, and the nodes
/// the `Flatten` step skipped.
fn seeded(
    eg: &EG,
    pattern: &str,
    root: ENodeId,
    more: &[(&str, ENodeId)],
) -> (
    Vec<semi_persistent_egraph::ematch::Match<DefaultConfig>>,
    usize,
    semi_persistent_egraph::resolve::MatchShape,
) {
    let index = IndexStore::build(eg);
    let pats = semi_persistent_egraph::parser::parse_patterns(pattern).expect("parse");
    let fq = semi_persistent_egraph::sortcheck::flatten_surface(&pats, eg.ops()).expect("flatten");
    let mut rq = semi_persistent_egraph::resolve::resolve(
        &fq,
        eg.ops(),
        eg.sorts(),
        &MachineModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .expect("resolve");
    rq.flatten = true;
    let rv = rq.shape.find_var(&fq.root_vars[0]).expect("root");
    let mut seeds = vec![(rv, root)];
    for (name, g) in more {
        seeds.push((rq.shape.find_var(name).expect("seeded variable"), *g));
    }
    let pre: Vec<_> = seeds.iter().map(|s| s.0).collect();
    let plan = semi_persistent_egraph::schedule::schedule_with_bound(
        &rq,
        &IndexStats::from_index(&index),
        &pre,
    );
    let mut pool = semi_persistent_egraph::ematch::MatchPool::new();
    semi_persistent_egraph::ematch::run_query_seeded_into(
        &plan,
        eg,
        &VariantIndex::naive(&index),
        &GlobalCtx::<SortId, ENodeId>::new(),
        &mut pool,
        &seeds,
    );
    let ms = (0..pool.len()).map(|j| pool.clone_match(j)).collect();
    (ms, pool.flatten_skipped(), rq.shape)
}

/// A chain of 100,000 nested conjunctions, `And{x_1, C_2}` with `C_i ≡ And{x_i, C_{i+1}}`,
/// each inner class holding no other matchable member, has one view of 100,001 elements.
/// The walk is an explicit stack, so a debug build matches it without exhausting the
/// stack.
///
/// The nesting is built by merges after construction. `EGraph::add` flattens a child
/// class that already holds a conjunction, so building the chain bottom-up would store
/// it flat (and quadratically: each node would absorb every leaf below it). Each
/// conjunction is therefore built over a placeholder `t(x_i)` first; the placeholder is
/// then merged with the next conjunction and subsumed, which leaves the conjunction as
/// its class's only member the index holds.
#[test]
fn deep_chain_flattens_without_recursion() {
    const N: usize = 100_000;
    let (mut eg, l0, s, and) = chain_graph();
    let e = eg.sorts().id_by_name("E").expect("sort");
    let t = eg.register_op1("t", e, e);
    let bottom = eg.add(l0, &[]);
    let mut xs = Vec::with_capacity(N + 1);
    xs.push(eg.add(s, &[bottom]));
    for i in 1..=N {
        let next = eg.add(s, &[xs[i - 1]]);
        xs.push(next);
    }
    // ys[i] stands for C_{i+1}; the last one is the bottom leaf.
    let mut ys: Vec<ENodeId> = (0..N - 1).map(|i| eg.add(t, &[xs[i]])).collect();
    ys.push(bottom);
    let ands: Vec<ENodeId> = (0..N).map(|i| eg.add(and, &[xs[i], ys[i]])).collect();
    for i in 0..N - 1 {
        eg.merge(ys[i], ands[i + 1]);
        eg.subsume(ys[i]);
    }
    eg.rebuild();
    // `z` is seeded to the bottom leaf's class, so the decomposition finds its position
    // directly. With a fresh item it would try every position and copy the rest at
    // each, which is quadratic in the view's length with or without the tag.
    let (ms, skipped, shape) = seeded(&eg, "(And z ..r)", ands[0], &[("z", bottom)]);
    assert_eq!(skipped, 0);
    assert_eq!(
        ms.len(),
        1,
        "one view, and the bottom leaf sits at one position of it"
    );
    let r = shape.sets.iter().position(|n| n == "r").expect("rest");
    let rest = ms[0].set_slice(semi_persistent_egraph::ast::SetVarId::new(
        u16::try_from(r).expect("rest"),
    ));
    assert_eq!(rest.len(), N, "every level's leaf is in the view");
}

/// A node over `MAX_VIEWS` combinations is skipped and counted, and the query goes on
/// to match the other nodes. Two children, each a class with 1,025 conjunction members
/// besides a leaf, give 1,026^2 > 2^20 combinations.
#[test]
fn a_node_over_the_view_bound_is_skipped_and_counted() {
    let (mut eg, l0, s, and) = chain_graph();
    let base = eg.add(l0, &[]);
    let mut leaves = vec![eg.add(s, &[base])];
    for _ in 0..2 * 1025 + 4 {
        let next = eg.add(s, &[*leaves.last().expect("nonempty")]);
        leaves.push(next);
    }
    let (ka, kb) = (leaves[0], leaves[1]);
    for j in 0..1025 {
        let m = eg.add(and, &[leaves[2 + j], base]);
        eg.merge(ka, m);
        let m = eg.add(and, &[leaves[2 + 1025 + j], base]);
        eg.merge(kb, m);
    }
    let over = eg.add(and, &[ka, kb]);
    let fine = eg.add(and, &[leaves[2 * 1025 + 2], leaves[2 * 1025 + 3]]);
    eg.rebuild();
    let (ms, skipped, _) = seeded(&eg, "(And x y ..r)", over, &[]);
    assert_eq!(skipped, 1, "the node over the bound is counted");
    assert!(ms.is_empty(), "and contributes no match");
    let (ms, skipped, _) = seeded(&eg, "(And x y ..r)", fine, &[]);
    assert_eq!(skipped, 0);
    assert_eq!(
        ms.len(),
        2,
        "another node still matches (two orders of its two children)"
    );
}

/// Proofs mode: a union found through a flattened view is justified by the rule, as
/// any rewrite's is, so `explain` of the equality cites it. The rule's left-hand side
/// instance, `And{Not p, Not q, r}`, is not a node: it equals the root `And{Not p, K}`
/// only modulo associativity. Semper's proofs are explanation steps and replay no
/// instance, so nothing in them needs that step; a consumer that replays one would.
#[test]
fn a_flattened_union_cites_the_rule() {
    let program = "\
(sort E)
(function p () E) (function q () E) (function r () E) (function Kc () E)
(function Not (E) E)
(function Or (E) E :assoc-comm-idem)
(function And (E) E :assoc-comm-idem)
(let k (Kc))
(let e (And (Not (p)) k))
(union k (And (Not (q)) (r)))
(rewrite (And (Not a0) (Not a1) ..rest) (And (Not (Or a0 a1)) ..rest) :flatten)
(run 1)
(let want (And (Not (Or (p) (q))) (r)))
(check (= e want))
";
    let cmds = semi_persistent_egraph::parser::parse_program_v2(program).expect("parse");
    let mut it: Interpreter<DefaultConfig, MachineLit, MachineModel, false, true> =
        Interpreter::new(MachineModel);
    let mut sg = GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    let (_, _, e) = it.globals().get("e").expect("e");
    let (_, _, want) = it.globals().get("want").expect("want");
    let mut buf = semi_persistent_egraph::union_find::ProofBuf::new();
    assert!(it.eg.explain(e, want, &mut buf), "no explanation");
    let cited: Vec<&str> = buf
        .steps
        .iter()
        .filter_map(|(_, _, j)| match j {
            semi_persistent_egraph::union_find::Justification::Rewrite { rule_id } => {
                Some(it.eg.rules().name(*rule_id))
            }
            _ => None,
        })
        .collect();
    assert!(
        cited.iter().any(|n| n.starts_with("rewrite_")),
        "the explanation cites no rewrite: {:?}",
        buf.steps
    );
}

// ── Refolding ────────────────────────────────────────────────────────────────

/// A raw view element with the opening instances it lies under, outermost first.
#[derive(Clone, Debug)]
struct Elem {
    class: Class,
    mult: u64,
    path: Vec<usize>,
}

/// A raw view's elements, and its opening instances as (opened class, multiplicity).
type Tree = (Vec<Elem>, Vec<(Class, u64)>);

/// Every raw view of `n` as elements with their instance paths, and the instances, each
/// as (opened class, its multiplicity in the parent).
fn raw_trees(model: &Model, n: &Node, f: OpId) -> Vec<Tree> {
    fn go(
        model: &Model,
        n: &Node,
        f: OpId,
        mult: u64,
        path: &[usize],
        on_path: &BTreeSet<Class>,
        insts: &[(Class, u64)],
    ) -> Vec<Tree> {
        let mut acc: Vec<Tree> = vec![(Vec::new(), insts.to_vec())];
        for &(x, j) in &n.kids {
            let k = mult * j;
            let mut next = Vec::new();
            for (es, is) in &acc {
                let mut kept = es.clone();
                kept.push(Elem {
                    class: x,
                    mult: k,
                    path: path.to_vec(),
                });
                next.push((kept, is.clone()));
                if !on_path.contains(&x) {
                    let mut op = on_path.clone();
                    op.insert(x);
                    for m in model.members(x).iter().filter(|m| m.op == f) {
                        let mut is2 = is.clone();
                        let id = is2.len();
                        is2.push((x, k));
                        let mut p2 = path.to_vec();
                        p2.push(id);
                        for (sub, is3) in go(model, m, f, k, &p2, &op, &is2) {
                            let mut e = es.clone();
                            e.extend(sub);
                            next.push((e, is3));
                        }
                    }
                }
            }
            acc = next;
        }
        acc
    }
    go(model, n, f, 1, &[], &BTreeSet::new(), &[])
}

/// For every match a raw view gives whose own opening tree fails the demand rule, the
/// refolded match is kept: the same item bindings, and the rest of the view in which
/// every maximal unneeded opening is kept whole. That rest equals the dropped one modulo
/// AC and the class equalities, since an opened class equals its member's children
/// (`doc/goal-canonical-flatten-views.md`, step 3, refolding property).
#[test]
fn every_dropped_match_has_its_refolded_match() {
    let (mut dropped, mut checked) = (0usize, 0usize);
    for seed in 0..60u64 {
        let mut rng = Rng(seed.wrapping_mul(0x5851F42D4C957F2D) ^ 0xF1A7);
        let src = program(&mut rng);
        let eg = build(&src);
        let index = IndexStore::build(&eg);
        let model = Model::read(&eg, &index);
        for p in patterns() {
            let P::NAry(op, ps, rest @ (Rest::Suf(_) | Rest::Pre(_))) = &p else {
                continue;
            };
            let (Rest::Suf(rname) | Rest::Pre(rname)) = rest else {
                unreachable!()
            };
            let Some(o) = model.op(op) else { continue };
            let kind = model.kinds[&o];
            for n in model.members.values().flatten().filter(|m| m.op == o) {
                // The kept matches, by the reference proper.
                let kept: BTreeSet<Env> = match_node(&model, n, ps, rest, &Env::new(), true)
                    .into_iter()
                    .collect();
                for (elems, insts) in raw_trees(&model, n, o) {
                    let raw: View = elems.iter().map(|e| (e.class, e.mult)).collect();
                    let Some(view) = canonical(&model, o, raw) else {
                        continue;
                    };
                    let all = vec![Vec::new()];
                    let d = Demand {
                        alts: &all,
                        flatten: true,
                    };
                    let mut ms = Vec::new();
                    match kind {
                        Kind::Assoc | Kind::Plain => {
                            match_seq(&model, ps, rest, &view, &Env::new(), &d, &mut ms)
                        }
                        Kind::Aci => {
                            let mut used = vec![false; view.len()];
                            match_aci(
                                &model,
                                ps,
                                0,
                                rest,
                                &view,
                                &mut used,
                                &Env::new(),
                                &d,
                                &mut ms,
                            )
                        }
                        Kind::Ac => {
                            let mut res = view.clone();
                            match_ac(&model, ps, 0, rest, &mut res, &Env::new(), &d, &mut ms)
                        }
                    }
                    for m in ms {
                        // Taken: the view's classes the rest does not hold.
                        let Some(Val::Rest(r)) = m.get(rname) else {
                            continue;
                        };
                        // Under `:assoc` the items take positions (the first k for a
                        // trailing rest, the last k for a leading one), and a view's
                        // elements are its raw elements in order.
                        let k = ps.len();
                        let seq = matches!(kind, Kind::Assoc | Kind::Plain);
                        let taken_pos: Vec<usize> = match rest {
                            Rest::Suf(_) => (0..k).collect(),
                            _ => (view.len() - k..view.len()).collect(),
                        };
                        let in_rest: BTreeSet<Class> = r.iter().map(|e| e.0).collect();
                        let taken: BTreeSet<Class> = if seq {
                            taken_pos.iter().map(|&i| view[i].0).collect()
                        } else {
                            view.iter()
                                .map(|e| e.0)
                                .filter(|c| !in_rest.contains(c))
                                .collect()
                        };
                        // Needed instances: those a taken element lies under.
                        let mut needed = vec![false; insts.len()];
                        for (pos, e) in elems.iter().enumerate() {
                            let is_taken = if seq {
                                taken_pos.contains(&pos)
                            } else {
                                taken.contains(&e.class)
                            };
                            if is_taken {
                                for &i in &e.path {
                                    needed[i] = true;
                                }
                            }
                        }
                        if needed.iter().all(|&x| x) {
                            continue;
                        }
                        dropped += 1;
                        // Refold: an element under an unneeded instance is replaced by the
                        // outermost unneeded instance on its path, once.
                        let mut refolded: View = Vec::new();
                        let mut seen: BTreeSet<usize> = BTreeSet::new();
                        for e in &elems {
                            match e.path.iter().find(|&&i| !needed[i]) {
                                None => refolded.push((e.class, e.mult)),
                                Some(&i) => {
                                    if seen.insert(i) {
                                        refolded.push(insts[i]);
                                    }
                                }
                            }
                        }
                        let Some(rv) = canonical(&model, o, refolded) else {
                            continue;
                        };
                        // The refolded rest: the refolded view less what the items took.
                        // Unneeded openings lie wholly in the rest, so under `:assoc` the
                        // taken positions are still the first or last k.
                        let mut left: Vec<(Class, u64)> = rv.clone();
                        if seq {
                            left = match rest {
                                Rest::Suf(_) => left[k..].to_vec(),
                                _ => left[..left.len() - k].to_vec(),
                            };
                        } else {
                            left.retain(|e| !taken.contains(&e.0));
                        }
                        let mut rest_val: Vec<(Class, u64)> = match kind {
                            Kind::Ac => left,
                            _ => left.into_iter().map(|(c, _)| (c, 1)).collect(),
                        };
                        if kind != Kind::Assoc && kind != Kind::Plain {
                            rest_val.sort();
                        }
                        let mut want = m.clone();
                        want.insert(rname.clone(), Val::Rest(rest_val));
                        assert!(
                            kept.contains(&want),
                            "seed {seed}, pattern {}, node {}: the dropped match {m:?} has no \
                             refolded match {want:?}",
                            surface(&p),
                            n.id
                        );
                        checked += 1;
                    }
                }
            }
        }
    }
    eprintln!("refolding: {dropped} dropped matches, {checked} refolded matches found");
    assert!(
        checked > 100,
        "too few dropped matches to test refolding: {checked}"
    );
}

/// The four-class chain of `flatten_rest_only.egg`: `_1 ∋ Add{A, _2}`,
/// `_2 ∋ Add{_3, _4, Y}`, `_3 ∋ Add{X, _4}`, `_4 ∋ Add{Y, Z}`, each class also holding a
/// placeholder so that the surface builder does not splice it. `(Add x ..rest)` at
/// `_1` under `:flatten`: the engine equals the reference, and each match opens only
/// the classes on the path to `x`.
#[test]
fn rest_only_chain_matches() {
    let src = "\
(sort E)
(function A () E) (function X () E) (function Y () E) (function Z () E)
(function C1 () E) (function C2 () E) (function C3 () E) (function C4 () E)
(function Add (E) E :assoc-comm)
(let c4 (C4))
(let c3 (C3))
(let c2 (C2))
(union c4 (Add (Y) (Z)))
(union c3 (Add (X) c4))
(union c2 (Add c3 c4 (Y)))
(let c1 (Add (A) c2))
";
    let eg = build(src);
    let index = IndexStore::build(&eg);
    let model = Model::read(&eg, &index);
    let p = nary_suf("Add", vec![v("x")], "rest");
    let want = reference(&model, &p, true);
    let got = engine(&eg, &index, &p, true);
    assert_eq!(got, want);
    let class = |name: &str| {
        let op = model.op(name).expect("op");
        *model
            .members
            .iter()
            .find(|(_, ms)| ms.iter().any(|m| m.op == op))
            .expect("class")
            .0
    };
    let names: BTreeMap<Class, &str> = [
        ("A", class("A")),
        ("X", class("X")),
        ("Y", class("Y")),
        ("Z", class("Z")),
        ("_2", class("C2")),
        ("_3", class("C3")),
        ("_4", class("C4")),
    ]
    .into_iter()
    .map(|(n, c)| (c, n))
    .collect();
    // `_1` is the class of the `Add` node over `A`.
    let add = model.op("Add").expect("Add");
    let root = *model
        .members
        .iter()
        .find(|(_, ms)| {
            ms.iter()
                .any(|m| m.op == add && m.kids.iter().any(|k| k.0 == class("A")))
        })
        .expect("_1")
        .0;
    let show = |c: &Class| names.get(c).copied().unwrap_or("?");
    let mut at_root = 0;
    for ((node, env), k) in &want {
        let n = model.members[&root].iter().any(|m| m.id == *node);
        if !n {
            continue;
        }
        at_root += k;
        let Some(Val::Class(x)) = env.get("x") else {
            continue;
        };
        let Some(Val::Rest(r)) = env.get("rest") else {
            continue;
        };
        let rest: Vec<String> = r.iter().map(|(c, m)| format!("{}:{m}", show(c))).collect();
        eprintln!("x = {}, rest = [{}]", show(x), rest.join(", "));
    }
    eprintln!("{at_root} matches at _1");
    // x = A or _2 opening nothing; _3, _4, or Y opening _2; X opening _2 and _3; Z
    // through each of the two instances of _4. Y inside _4 has multiplicity 2 in that
    // view, which an unannotated item does not take.
    assert_eq!(
        at_root, 8,
        "one match per choice of x and of the classes it opens"
    );
}
