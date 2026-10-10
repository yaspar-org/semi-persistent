// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Stress test for counted children: `(Add a:3 b)` is the AC node `{a:3, b:1}`, built
//! through `add_mset` as one entry per class, never expanded into copies.
//!
//! Every property runs at both multiplicity widths, through the library with the two
//! presets (`DefaultConfig`, 32-bit counts, and `Config64`, 64-bit counts), and catches a
//! panic as a failure rather than letting it end the test binary. The random properties
//! use proptest with a fixed seed and a fixed number of cases, so a run is reproducible and
//! a failure shrinks to a small program.
//!
//! What is covered, by section:
//! 1. an AC count is one stored entry, at every width up to the maximum, in constant time;
//! 2. the counted, expanded, split, nested and normal-form spellings of random terms are
//!    one class, and a spelling with another count is not;
//! 3. the same in a top-level insertion, `let`, `check`, `union`, and a rule right-hand
//!    side, including a multiplicity expression;
//! 4. a count past the width is a reported `multiplicity overflow`, never a wrap or a panic;
//! 5. the boundaries 0, 1, the width's maximum, and one past it;
//! 6. ACI: `x:k` is the class once, for any `k`;
//! 7. A: `x:k` is `k` positions up to `seq_rhs::MAX_WIDTH`, and refused past it at once;
//! 8. matching with multiplicity annotations, naive and semi-naive, and `:flatten` views;
//! 9. extraction prints the counted form, and the printed text reads back as the class.
//!
//! The tests at the end marked `#[ignore]` are defects this file found; each states what it
//! expects and what happens instead.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::panic::AssertUnwindSafe;
use std::time::{Duration, Instant};

use proptest::prelude::*;
use proptest::test_runner::{Config as PtConfig, RngAlgorithm, TestCaseError, TestRng, TestRunner};

use semi_persistent_egraph::canon::{MSetCanon, VarCanon};
use semi_persistent_egraph::config::{EGraphConfig, StorePolicy};
use semi_persistent_egraph::extract::extract_best;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::multiplicity::{MultiplicityLike, OVERFLOW, overflow_message};
use semi_persistent_egraph::nodes::{Config64, DefaultConfig};
use semi_persistent_egraph::registry::OpKind;
use semi_persistent_egraph::saturate::SaturationStrategy;

// ───────────────────────────── harness ─────────────────────────────

/// What a program ended in.
#[derive(Debug)]
enum Outcome {
    Ok(Done),
    Parse(String),
    Sort(String),
    Error(String),
    /// The panic's message: read only through `Debug`, in a failing assertion.
    #[allow(dead_code)]
    Panic(String),
}

/// A finished run: the graph's size and what the named globals' classes hold.
#[derive(Debug)]
struct Done {
    nodes: usize,
    elapsed: Duration,
    globals: BTreeMap<String, ClassInfo>,
    /// Every node whose operator name starts with `H`, printed with its children; a child
    /// in a named global's class prints as `$name`, any other as its extracted term.
    hits: BTreeSet<String>,
}

/// The variadic nodes of one class, and its extracted term.
#[derive(Debug, Default)]
struct ClassInfo {
    /// Each AC node's children, as (extracted child, count), sorted.
    ac: Vec<Vec<(String, u64)>>,
    /// Each ACI node's children, extracted, sorted.
    aci: Vec<Vec<String>>,
    /// Each A node's number of positions.
    seq: Vec<usize>,
    extract: String,
}

impl Outcome {
    fn ok(self, at: &str) -> Done {
        match self {
            Outcome::Ok(d) => d,
            other => panic!("{at}: expected ok, got {other:?}"),
        }
    }
    fn error(self, at: &str) -> String {
        match self {
            Outcome::Error(e) => e,
            other => panic!("{at}: expected a reported error, got {other:?}"),
        }
    }
    fn sort_error(self, at: &str) -> String {
        match self {
            Outcome::Sort(e) => e,
            other => panic!("{at}: expected a sort error, got {other:?}"),
        }
    }
    /// The outcome's text for a property: `Ok(())` when the program ran.
    fn prop_ok(&self) -> Result<(), String> {
        match self {
            Outcome::Ok(_) => Ok(()),
            other => Err(format!("{other:?}")),
        }
    }
}

type Interp<Cfg> = Interpreter<Cfg, MachineLit, MachineModel, true, false>;

fn run_cfg<Cfg>(src: &str, strategy: SaturationStrategy, names: &[&str]) -> Outcome
where
    Cfg: EGraphConfig,
    Cfg::O: std::hash::Hash,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: StorePolicy<Cfg, true>,
{
    let cmds = match semi_persistent_egraph::parser::parse_program_v2(src) {
        Ok(c) => c,
        Err(e) => return Outcome::Parse(e.to_string()),
    };
    let mut interp = Interp::<Cfg>::new(MachineModel);
    interp.set_strategy(strategy);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = match semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    ) {
        Ok(c) => c,
        Err(e) => return Outcome::Sort(e.to_string()),
    };
    let start = Instant::now();
    if let Err(e) = interp.run_checked(&checked) {
        return Outcome::Error(e.to_string());
    }
    let elapsed = start.elapsed();

    let mut named: Vec<(String, Cfg::G)> = Vec::new();
    for &n in names {
        let (id, _) = interp.global(n).unwrap_or_else(|| panic!("no global {n}"));
        named.push((n.to_string(), id));
    }
    let eg = &interp.eg;
    let mut extracted: HashMap<Cfg::G, String> = HashMap::new();
    let mut show = |c: Cfg::G| -> String {
        let r = eg.class_repr(c);
        extracted
            .entry(r)
            .or_insert_with(|| match extract_best(eg, r) {
                Ok(t) => t.to_string(),
                Err(e) => format!("<extract failed: {e}>"),
            })
            .clone()
    };
    let mut infos = BTreeMap::new();
    for (name, id) in &named {
        let repr = eg.class_repr(*id);
        let mut info = ClassInfo::default();
        for n in eg.node_ids() {
            if eg.class_repr(n) != repr {
                continue;
            }
            match eg.ops().info(eg.node_op(n)).kind {
                OpKind::MSet { .. } => {
                    let mut kids = Vec::new();
                    eg.for_each_child(n, |c, m| {
                        kids.push((c, m.to_u64().expect("count fits u64")))
                    });
                    let mut kids: Vec<(String, u64)> =
                        kids.into_iter().map(|(c, m)| (show(c), m)).collect();
                    kids.sort();
                    info.ac.push(kids);
                }
                OpKind::Set { .. } => {
                    let mut kids = Vec::new();
                    eg.for_each_child(n, |c, _| kids.push(c));
                    let mut kids: Vec<String> = kids.into_iter().map(&mut show).collect();
                    kids.sort();
                    info.aci.push(kids);
                }
                OpKind::A { .. } => {
                    let mut positions = 0usize;
                    eg.for_each_child(n, |_, _| positions += 1);
                    info.seq.push(positions);
                }
                _ => {}
            }
        }
        info.ac.sort();
        // A sequence of 2^20 positions extracts as a 2^20-child term: not worth printing.
        info.extract = if info.seq.iter().any(|&p| p > 4096) {
            String::new()
        } else {
            show(*id)
        };
        infos.insert(name.clone(), info);
    }
    let mut hits = BTreeSet::new();
    for n in eg.node_ids() {
        let name = eg.node_op_name(n).to_string();
        if !name.starts_with('H') {
            continue;
        }
        let mut kids = Vec::new();
        eg.for_each_child(n, |c, _| kids.push(c));
        let mut s = format!("({name}");
        for c in kids {
            let r = eg.class_repr(c);
            match named.iter().find(|(_, id)| eg.class_repr(*id) == r) {
                Some((g, _)) => s.push_str(&format!(" ${g}")),
                None => s.push_str(&format!(" {}", show(c))),
            }
        }
        s.push(')');
        hits.insert(s);
    }
    Outcome::Ok(Done {
        nodes: eg.len(),
        elapsed,
        globals: infos,
        hits,
    })
}

/// A multiplicity width, as a configuration preset.
trait Preset {
    const NAME: &'static str;
    /// The width's largest count.
    fn max() -> u64;
    /// The tail every width-carrying overflow message ends in.
    fn width_tail() -> String;
    fn run(src: &str, strategy: SaturationStrategy, names: &[&str]) -> Outcome;
}

macro_rules! preset {
    ($name:ident, $cfg:ty, $label:expr) => {
        struct $name;
        impl Preset for $name {
            const NAME: &'static str = $label;
            fn max() -> u64 {
                <<$cfg as EGraphConfig>::M as MultiplicityLike>::MAX
                    .and_then(|m| m.to_u64())
                    .expect("a bounded width")
            }
            fn width_tail() -> String {
                let m = overflow_message::<<$cfg as EGraphConfig>::M>("X");
                m[m.find("X").unwrap() + 1..].trim().to_string()
            }
            fn run(src: &str, strategy: SaturationStrategy, names: &[&str]) -> Outcome {
                let full = format!("{DECLS}\n{src}");
                match std::panic::catch_unwind(AssertUnwindSafe(|| {
                    run_cfg::<$cfg>(&full, strategy, names)
                })) {
                    Ok(o) => o,
                    Err(p) => Outcome::Panic(
                        p.downcast_ref::<String>()
                            .cloned()
                            .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                            .unwrap_or_else(|| "<non-string panic>".to_string()),
                    ),
                }
            }
        }
    };
}
preset!(W32, DefaultConfig, "32-bit");
preset!(W64, Config64, "64-bit");

const NAIVE: SaturationStrategy = SaturationStrategy::Naive;
const SEMI: SaturationStrategy = SaturationStrategy::SemiNaive;

/// Every program starts with these declarations.
const DECLS: &str = "\
(sort E)
(function L0 () E) (function L1 () E) (function L2 () E) (function L3 () E) (function L4 () E)
(function F (E) E) (function G (E) E) (function W () E) (function Z () E) (function Kc () E)
(function Add (E) E :assoc-comm)
(function Mul (E) E :assoc-comm)
(function And (E) E :assoc-comm-idem)
(function Cat (E) E :assoc)
(function H1 (E E) E) (function H2 (E E) E) (function H3 (E E) E) (function H6 (E E) E)
(function H4 (E E E) E) (function H5 (E E E) E)
";

/// A fixed-seed proptest runner; failures are not persisted to a file.
fn runner(cases: u32) -> TestRunner {
    let config = PtConfig {
        cases,
        failure_persistence: None,
        max_global_rejects: 100_000,
        ..PtConfig::default()
    };
    TestRunner::new_with_rng(
        config,
        TestRng::from_seed(RngAlgorithm::ChaCha, &[0x5e; 32]),
    )
}

fn proptest_run<S: Strategy>(
    cases: u32,
    strategy: S,
    test: impl Fn(S::Value) -> Result<(), TestCaseError>,
) {
    if let Err(e) = runner(cases).run(&strategy, test) {
        panic!("{e}");
    }
}

/// An overflow reported in the shared words, with the width when the report carries one.
fn assert_overflow<P: Preset>(msg: &str, at: &str, starts: bool) {
    if starts {
        assert!(
            msg.starts_with(OVERFLOW),
            "{at} [{}]: the message should start with `{OVERFLOW}`: {msg}",
            P::NAME
        );
        assert!(
            msg.ends_with(&P::width_tail()),
            "{at} [{}]: the message should name the width ({}): {msg}",
            P::NAME,
            P::width_tail()
        );
    } else {
        assert!(
            msg.contains(OVERFLOW),
            "{at} [{}]: the message should contain `{OVERFLOW}`: {msg}",
            P::NAME
        );
    }
}

/// A program runner at one width: the program, the strategy, and extra declarations.
type Runner<'a> = &'a dyn Fn(&str, SaturationStrategy, &[&str]) -> Outcome;

fn both_widths(f: fn(Runner<'_>, u64, &str, &str)) {
    f(&W32::run, W32::max(), W32::NAME, &W32::width_tail());
    f(&W64::run, W64::max(), W64::NAME, &W64::width_tail());
}

// ───────────────────────────── random terms ─────────────────────────────

/// A term over the five leaves, the unary `F`, and the AC operators `Add` and `Mul`, whose
/// children carry counts. Nesting an AC operator in itself is allowed: the count of the
/// inner application multiplies through.
#[derive(Clone, Debug)]
enum T {
    Leaf(u8),
    Wrap(Box<T>),
    Ac(u8, Vec<(T, u64)>),
}

/// The canonical form the engine is expected to store: nested same-operator children
/// spliced with their counts multiplied, equal children coalesced, and a one-child,
/// count-one application replaced by its child.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum N {
    Leaf(u8),
    Wrap(Box<N>),
    Ac(u8, Vec<(N, u64)>),
}

const AC_OPS: [&str; 2] = ["Add", "Mul"];

fn norm(t: &T) -> N {
    match t {
        T::Leaf(i) => N::Leaf(*i),
        T::Wrap(c) => N::Wrap(Box::new(norm(c))),
        T::Ac(op, kids) => {
            let mut m: BTreeMap<N, u64> = BTreeMap::new();
            for (c, k) in kids {
                match norm(c) {
                    N::Ac(o, es) if o == *op => {
                        for (e, j) in es {
                            *m.entry(e).or_default() += k * j;
                        }
                    }
                    n => *m.entry(n).or_default() += k,
                }
            }
            if m.len() == 1 && *m.values().next().unwrap() == 1 {
                return m.into_keys().next().unwrap();
            }
            N::Ac(*op, m.into_iter().collect())
        }
    }
}

fn counted(r: &str, k: u64) -> String {
    if k == 1 {
        r.to_string()
    } else {
        format!("{r}:{k}")
    }
}

#[derive(Clone, Copy, Debug)]
enum Style {
    /// `c:k`.
    Counted,
    /// `c` written `k` times.
    Expanded,
    /// `c:a c:b` with `a + b = k`, children in reverse order.
    Split,
}

fn render(t: &T, s: Style) -> String {
    match t {
        T::Leaf(i) => format!("(L{i})"),
        T::Wrap(c) => format!("(F {})", render(c, s)),
        T::Ac(op, kids) => {
            let mut parts = Vec::new();
            for (c, k) in kids {
                let r = render(c, s);
                match s {
                    Style::Counted => parts.push(counted(&r, *k)),
                    Style::Expanded => parts.extend(std::iter::repeat_n(r, *k as usize)),
                    Style::Split if *k >= 2 => {
                        let a = *k / 2;
                        parts.push(counted(&r, a));
                        parts.push(counted(&r, *k - a));
                    }
                    Style::Split => parts.push(r),
                }
            }
            if matches!(s, Style::Split) {
                parts.reverse();
            }
            format!("({} {})", AC_OPS[*op as usize], parts.join(" "))
        }
    }
}

/// The normal form, flat, children sorted by their printed text as the extractor prints
/// them; `expanded` writes each child `k` times instead of `c:k`.
fn render_n(n: &N, expanded: bool) -> String {
    match n {
        N::Leaf(i) => format!("(L{i})"),
        N::Wrap(c) => format!("(F {})", render_n(c, expanded)),
        N::Ac(op, es) => {
            let mut parts: Vec<String> = Vec::new();
            for (e, k) in es {
                let r = render_n(e, expanded);
                if expanded {
                    parts.extend(std::iter::repeat_n(r, *k as usize));
                } else {
                    parts.push(counted(&r, *k));
                }
            }
            parts.sort();
            format!("({} {})", AC_OPS[*op as usize], parts.join(" "))
        }
    }
}

/// Inner AC applications by position: spliced into a same-operator parent (`flat`), or
/// kept as a child of something else (`atomic`). A class that is both is a known gap, not
/// a counting question: the engine flattens a same-operator child only while its class is
/// referenced nowhere else (`flatten_mset_children`, design §5b), so such a term is not
/// generated here.
fn positions(t: &T, parent: Option<u8>, flat: &mut BTreeSet<N>, atomic: &mut BTreeSet<N>) {
    match t {
        T::Leaf(_) => {}
        T::Wrap(c) => {
            if let T::Ac(..) = **c {
                atomic.insert(norm(c));
            }
            positions(c, None, flat, atomic);
        }
        T::Ac(op, kids) => {
            for (c, _) in kids {
                if let T::Ac(cop, _) = c {
                    if *cop == *op {
                        flat.insert(norm(c));
                    } else {
                        atomic.insert(norm(c));
                    }
                }
                positions(c, Some(*op), flat, atomic);
            }
            let _ = parent;
        }
    }
}

fn no_atomic_conflict(t: &T) -> bool {
    let (mut flat, mut atomic) = (BTreeSet::new(), BTreeSet::new());
    positions(t, None, &mut flat, &mut atomic);
    flat.intersection(&atomic).all(|n| !matches!(n, N::Ac(..)))
}

fn tree() -> impl Strategy<Value = T> {
    let leaf = (0u8..5).prop_map(T::Leaf);
    leaf.prop_recursive(3, 20, 3, |inner| {
        prop_oneof![
            1 => inner.clone().prop_map(|t| T::Wrap(Box::new(t))),
            3 => (0u8..2, prop::collection::vec((inner, 1u64..=4), 1..=3))
                .prop_map(|(o, k)| T::Ac(o, k)),
        ]
    })
}

/// A random AC application at the root, whose normal form is still an AC node, and whose
/// nesting avoids the atomic-class gap.
fn root() -> impl Strategy<Value = T> {
    (0u8..2, prop::collection::vec((tree(), 1u64..=4), 1..=3))
        .prop_map(|(o, k)| T::Ac(o, k))
        .prop_filter("normal form is an AC node", |t| {
            matches!(norm(t), N::Ac(..))
        })
        .prop_filter("no class both spliced and kept", no_atomic_conflict)
}

/// The normal form with its first entry's count raised by one: a different AC node.
fn mutant(n: &N) -> N {
    match n {
        N::Ac(op, es) => {
            let mut es = es.clone();
            es[0].1 += 1;
            N::Ac(*op, es)
        }
        _ => unreachable!("root() keeps AC normal forms"),
    }
}

fn nf_children(n: &N) -> Vec<(String, u64)> {
    let N::Ac(_, es) = n else { unreachable!() };
    let mut v: Vec<(String, u64)> = es.iter().map(|(e, k)| (render_n(e, false), *k)).collect();
    v.sort();
    v
}

// ───────────────────── 1. an AC count is one stored entry ─────────────────────

fn one_entry(
    run: &dyn Fn(&str, SaturationStrategy, &[&str]) -> Outcome,
    max: u64,
    w: &str,
    _: &str,
) {
    let mut ks = vec![2, 3, 1000, 1 << 31, max - 1, max];
    if max == u64::MAX {
        ks.push(1_000_000_000_000_000_000);
    }
    for k in ks {
        let at = format!("[{w}] (Add (L0):{k} (L1))");
        let d = run(&format!("(let t (Add (L0):{k} (L1)))"), NAIVE, &["t"]).ok(&at);
        assert_eq!(d.nodes, 3, "{at}: three nodes, the count is not copies");
        assert!(
            d.elapsed < Duration::from_secs(2),
            "{at}: took {:?}",
            d.elapsed
        );
        let t = &d.globals["t"];
        assert_eq!(
            t.ac,
            vec![vec![("(L0)".to_string(), k), ("(L1)".to_string(), 1)]],
            "{at}"
        );
        assert_eq!(t.extract, format!("(Add (L0):{k} (L1))"), "{at}");

        // The user's spelling: bare global names, `a:k b`.
        let at = format!("[{w}] (Add a:{k} b)");
        let d = run(
            &format!("(let a (L0)) (let b (L1)) (let t (Add a:{k} b))"),
            NAIVE,
            &["t"],
        )
        .ok(&at);
        assert_eq!(d.nodes, 3, "{at}");
        assert_eq!(
            d.globals["t"].ac,
            vec![vec![("(L0)".to_string(), k), ("(L1)".to_string(), 1)]],
            "{at}"
        );

        // A single counted child is still an AC node: `{L0:k}`, not `L0`.
        let at = format!("[{w}] (Add (L0):{k})");
        let d = run(&format!("(let t (Add (L0):{k}))"), NAIVE, &["t"]).ok(&at);
        assert_eq!(d.nodes, 2, "{at}");
        assert_eq!(
            d.globals["t"].ac,
            vec![vec![("(L0)".to_string(), k)]],
            "{at}"
        );

        // A rule right-hand side stores the same single entry.
        let at = format!("[{w}] rhs (Add (L0):{k} (L1))");
        let d = run(
            &format!("(let w (W)) (rewrite (W) (Add (L0):{k} (L1))) (run 1)"),
            SEMI,
            &["w"],
        )
        .ok(&at);
        assert_eq!(d.nodes, 4, "{at}: W, L0, L1, and one Add node");
        assert_eq!(
            d.globals["w"].ac,
            vec![vec![("(L0)".to_string(), k), ("(L1)".to_string(), 1)]],
            "{at}"
        );
    }
}

#[test]
fn ac_count_is_one_entry_up_to_the_width() {
    both_widths(one_entry);
}

/// 10^18 at 32 bits is refused when the term is built, before anything is allocated for
/// it; at 64 bits it is one entry (above).
#[test]
fn ten_to_the_eighteen_at_32_bits_is_refused_at_once() {
    let start = Instant::now();
    let e = W32::run("(let t (Add (L0):1000000000000000000 (L1)))", NAIVE, &[]).error("10^18");
    assert!(start.elapsed() < Duration::from_secs(2));
    assert_overflow::<W32>(&e, "10^18", true);
    assert!(
        e.contains("does not fit the configured multiplicity width"),
        "{e}"
    );
}

// ─────────────── 2 and 9. random spellings are one class; extraction ───────────────

fn spellings_agree<P: Preset>(t: &T) -> Result<(), TestCaseError> {
    let n = norm(t);
    let c = render(t, Style::Counted);
    let prog = format!(
        "(let t0 {c})\n(check (= t0 {}))\n(check (= t0 {}))\n(check (= t0 {}))\n(check (= t0 {}))\n(check (!= t0 {}))",
        render(t, Style::Expanded),
        render(t, Style::Split),
        render_n(&n, false),
        render_n(&n, true),
        render_n(&mutant(&n), false),
    );
    let out = P::run(&prog, NAIVE, &["t0"]);
    let d = match out {
        Outcome::Ok(d) => d,
        other => {
            return Err(TestCaseError::fail(format!(
                "[{}] program\n{prog}\nended in {other:?}",
                P::NAME
            )));
        }
    };
    let info = &d.globals["t0"];
    // The class holds the one normal-form node, whose children carry the counts.
    prop_assert_eq!(&info.ac, &vec![nf_children(&n)], "[{}] {}", P::NAME, prog);
    // 9: the extractor prints the counted normal form...
    prop_assert_eq!(
        &info.extract,
        &render_n(&n, false),
        "[{}] {}",
        P::NAME,
        prog
    );
    // ...and that text reads back as the same class, adding no node.
    let back = format!("(let t0 {c})\n(check (= t0 {}))", info.extract);
    let once = P::run(&format!("(let t0 {c})"), NAIVE, &[]);
    let twice = P::run(&back, NAIVE, &[]);
    match (once, twice) {
        (Outcome::Ok(a), Outcome::Ok(b)) => prop_assert_eq!(a.nodes, b.nodes, "{}", back),
        (a, b) => return Err(TestCaseError::fail(format!("{back}: {a:?} / {b:?}"))),
    }
    Ok(())
}

#[test]
fn random_spellings_are_one_class() {
    proptest_run(1000, root(), |t| {
        spellings_agree::<W32>(&t)?;
        spellings_agree::<W64>(&t)
    });
}

// ─────────────── 3. the same in every place a term is written ───────────────

fn contexts_agree<P: Preset>(t: &T, strategy: SaturationStrategy) -> Result<(), TestCaseError> {
    let n = norm(t);
    let c = render(t, Style::Counted);
    // Top level, union, bare check, and a rule right-hand side, all counted; each is held
    // against the expanded normal form.
    let prog = format!(
        "(let w (W))\n{c}\n(union (Z) {})\n(check (= (Z) {}))\n(check {})\n(rewrite (W) {c})\n(run 1)\n(check (= w {}))\n(check (= w (Z)))",
        render(t, Style::Split),
        render_n(&n, true),
        render(t, Style::Expanded),
        render_n(&n, false),
    );
    P::run(&prog, strategy, &[])
        .prop_ok()
        .map_err(|e| TestCaseError::fail(format!("[{} {strategy:?}]\n{prog}\n{e}", P::NAME)))?;
    // A top-level insertion of the counted spelling adds every node the normal form needs:
    // writing the normal form, counted or expanded, afterwards adds none.
    let alone = P::run(&c, NAIVE, &[]);
    let with_nf = P::run(
        &format!("{c}\n{}\n{}", render_n(&n, false), render_n(&n, true)),
        NAIVE,
        &[],
    );
    match (alone, with_nf) {
        (Outcome::Ok(a), Outcome::Ok(b)) => prop_assert_eq!(a.nodes, b.nodes, "{}", c),
        (a, b) => return Err(TestCaseError::fail(format!("{c}: {a:?} / {b:?}"))),
    }
    Ok(())
}

#[test]
fn every_context_reads_a_count_the_same_way() {
    proptest_run(500, (root(), any::<bool>()), |(t, semi)| {
        let s = if semi { SEMI } else { NAIVE };
        contexts_agree::<W32>(&t, s)?;
        contexts_agree::<W64>(&t, s)
    });
}

/// A multiplicity expression on a right-hand side: `x:(u64::op k d)` over the matched
/// count, with 0 omitting the child.
fn mult_expr<P: Preset>(
    j: u64,
    d: u64,
    mul: bool,
    s: SaturationStrategy,
) -> Result<(), TestCaseError> {
    let (op, r) = if mul {
        ("u64::*", j * d)
    } else {
        ("u64::+", j + d)
    };
    let want = if r == 0 {
        "(G (L1))".to_string()
    } else {
        format!("(G (Add {} (L1)))", counted("(L0)", r))
    };
    let prog = format!(
        "(let w (W))\n(rewrite (W) (Add (L0):{j} (L1)))\n(rewrite (Add x:k (L1)) (G (Add x:({op} k {d}) (L1))))\n(run 2)\n(check (= w {want}))"
    );
    P::run(&prog, s, &[])
        .prop_ok()
        .map_err(|e| TestCaseError::fail(format!("[{} {s:?}]\n{prog}\n{e}", P::NAME)))
}

#[test]
fn rhs_multiplicity_expressions_compute_the_count() {
    proptest_run(
        200,
        (1u64..=6, 0u64..=4, any::<bool>(), any::<bool>()),
        |(j, d, mul, semi)| {
            let s = if semi { SEMI } else { NAIVE };
            mult_expr::<W32>(j, d, mul, s)?;
            mult_expr::<W64>(j, d, mul, s)
        },
    );
}

// ─────────────── 4. overflow is a reported error ───────────────

#[derive(Debug)]
enum Want {
    /// Runs; the global `t` (or `w`) holds an AC node with these children.
    Ok,
    /// `multiplicity overflow: … (the N-bit width …)`.
    Overflow,
    /// A rule's report: contains `multiplicity overflow`.
    RuleOverflow,
}

fn overflow_cases(max: u64) -> Vec<(&'static str, String, Want)> {
    let bits = 64 - max.leading_zeros(); // 32 or 64
    let half = 1u64 << (bits - 1); // 2 * half = max + 1
    let root_lo = (1u64 << (bits / 2)) - 1; // root_lo * root_hi = max
    let root_hi = (1u64 << (bits / 2)) + 1;
    let root = 1u64 << (bits / 2); // root * root = max + 1
    let cube = 1u64 << (bits / 3 + 1); // cube^3 > max
    vec![
        (
            "sum of two entries",
            format!("(let t (Add (L0):{max} (L0)))"),
            Want::Overflow,
        ),
        (
            "split sum",
            format!("(let t (Add (L0):{half} (L0):{half}))"),
            Want::Overflow,
        ),
        (
            "split sum at the max",
            format!(
                "(let t (Add (L0):{} (L0):{half}))\n(check (= t (Add (L0):{max})))",
                half - 1
            ),
            Want::Ok,
        ),
        (
            "nested product at the max",
            format!(
                "(let t (Add (Add (L0):{root_lo} (L1)):{root_hi} (L2)))\n(check (= t (Add (L0):{max} (L1):{root_hi} (L2))))"
            ),
            Want::Ok,
        ),
        (
            "nested product",
            format!("(let t (Add (Add (L0):{root} (L1)):{root} (L2)))"),
            Want::Overflow,
        ),
        (
            "three-level product",
            format!("(let t (Add (Add (Add (L0):{cube} (L1)):{cube} (L2)):{cube} (L3)))"),
            Want::Overflow,
        ),
        (
            "union coalesces",
            format!("(let t (Add (L0):{max} (L1)))\n(union (L0) (L1))\n(run 1)"),
            Want::Overflow,
        ),
        (
            "union coalesces to the max",
            format!(
                "(let t (Add (L0):{} (L1)))\n(union (L0) (L1))\n(run 1)\n(check (= t (Add (L0):{max})))",
                max - 1
            ),
            Want::Ok,
        ),
        (
            "merge reads a coalesced monomial",
            format!(
                "(let t (Add (L0):{max} (L1)))\n(let u (Add (L2) (L0)))\n(rule ((Z)) ((union (L0) (L1)) (union t u)))\n(let z (Z))\n(run 1)"
            ),
            Want::Overflow,
        ),
        (
            "rhs sum",
            format!("(let w (W))\n(rewrite (W) (Add (L0):{max} (L0)))\n(run 1)"),
            Want::RuleOverflow,
        ),
        (
            "rhs x:k x:k",
            format!(
                "(let t (Add (L0):{half} (L1)))\n(rewrite (Add x:k (L1)) (G (Add x:k x:k (L1))))\n(run 1)"
            ),
            Want::RuleOverflow,
        ),
        (
            "rhs x:k x:k at the max",
            format!(
                "(let t (Add (L0):{} (L1)))\n(rewrite (Add x:k (L1)) (G (Add x:k x:k (L1))))\n(run 1)\n(check (= t (G (Add (L0):{} (L1)))))",
                half - 1,
                max - 1
            ),
            Want::Ok,
        ),
        (
            "rhs u64::+ past the width",
            format!(
                "(let t (Add (L0):{half} (L1)))\n(rewrite (Add x:k (L1)) (G (Add x:(u64::+ k k) (L1))))\n(run 1)"
            ),
            Want::RuleOverflow,
        ),
        (
            "rhs u64::* past the width",
            format!(
                "(let t (Add (L0):{root} (L1)))\n(rewrite (Add x:k (L1)) (G (Add x:(u64::* k k) (L1))))\n(run 1)"
            ),
            Want::RuleOverflow,
        ),
        (
            "rhs nested product",
            format!("(let w (W))\n(rewrite (W) (Add (Add (L0):{root} (L1)):{root} (L2)))\n(run 1)"),
            Want::RuleOverflow,
        ),
        (
            "rhs splices a counted rest",
            format!(
                "(let t (Add (L0):{max} (L1)))\n(rewrite (Add (L1) ..r) (G (Add (L0) ..r)))\n(run 1)"
            ),
            Want::RuleOverflow,
        ),
        (
            "ground count of 2^64",
            "(let t (Add (L0):18446744073709551616))".to_string(),
            Want::Overflow,
        ),
        (
            "ground count of 10^30",
            "(let t (Add (L0):1000000000000000000000000000000 (L1)))".to_string(),
            Want::Overflow,
        ),
        (
            "ground count of 2^64 in check",
            "(let t (Add (L0) (L1)))\n(check (!= t (Add (L0):18446744073709551616)))".to_string(),
            Want::Overflow,
        ),
        (
            "ground count of 2^64 in union",
            "(union (Z) (Add (L0):18446744073709551616))".to_string(),
            Want::Overflow,
        ),
        (
            "ground count of 2^64 at top level",
            "(Add (L0):18446744073709551616)".to_string(),
            Want::Overflow,
        ),
    ]
}

fn overflows<P: Preset>() {
    let max = P::max();
    for (name, prog, want) in overflow_cases(max) {
        for s in [NAIVE, SEMI] {
            let at = format!("{name} [{s:?}]\n{prog}\n");
            let out = P::run(&prog, s, &[]);
            match want {
                Want::Ok => {
                    out.ok(&at);
                }
                Want::Overflow => assert_overflow::<P>(&out.error(&at), &at, true),
                Want::RuleOverflow => assert_overflow::<P>(&out.error(&at), &at, false),
            }
        }
    }
}

#[test]
fn overflow_is_reported_at_32_bits() {
    overflows::<W32>();
}

#[test]
fn overflow_is_reported_at_64_bits() {
    overflows::<W64>();
}

/// A count past 2^64 written in a rule is refused before the rule runs. It is not reported
/// in the `multiplicity overflow` words, though: the rule language reads a count as a
/// `u64`, so the parser stops at it (`parser::number`). See the ignored
/// `rule_count_past_u64_is_reported_as_an_overflow` for the wording.
#[test]
fn rule_count_past_u64_is_refused() {
    for (name, prog) in [
        (
            "rhs",
            "(let w (W))\n(rewrite (W) (Add (L0):18446744073709551616 (L1)))\n(run 1)",
        ),
        (
            "pattern",
            "(let t (Add (L0) (L1)))\n(rule ((= e (Add x:18446744073709551616 ..r))) ((H1 e x)))\n(run 1)",
        ),
        (
            "interval",
            "(let t (Add (L0) (L1)))\n(rule ((= e (Add x:k<=18446744073709551616 ..r))) ((H1 e x)))\n(run 1)",
        ),
    ] {
        for out in [W32::run(prog, NAIVE, &[]), W64::run(prog, NAIVE, &[])] {
            assert!(matches!(out, Outcome::Parse(_)), "{name}: {out:?}");
        }
    }
}

fn flatten_view_past_width_prog<P: Preset>() -> String {
    let bits = 64 - P::max().leading_zeros();
    let root = 1u64 << (bits / 2);
    format!(
        "(let t (Add (Kc):{root} (L0)))\n(let k (Kc))\n(union k (Add (L1):{root} (L2)))\n(rule ((= e (Add x:m ..r))) ((H1 e x)) :flatten)\n(run 1)"
    )
}

/// A `:flatten` view whose product is past the width is skipped: the opened view of the
/// outer node, `L1:2^width`, is never matched, the inner node is, and the run goes on.
fn flatten_view_past_width<P: Preset>() {
    let prog = flatten_view_past_width_prog::<P>();
    for s in [NAIVE, SEMI] {
        let d = P::run(&prog, s, &["t", "k"]).ok(&prog);
        assert!(
            d.hits.contains("(H1 $k (L1))") && d.hits.contains("(H1 $k (L2))"),
            "[{} {s:?}] {:?}",
            P::NAME,
            d.hits
        );
        for h in ["(H1 $t (L1))", "(H1 $t (L2))"] {
            assert!(
                !d.hits.contains(h),
                "[{} {s:?}] the overflowing view matched: {:?}",
                P::NAME,
                d.hits
            );
        }
    }
}

#[test]
fn flatten_view_past_the_width_is_skipped() {
    flatten_view_past_width::<W32>();
    flatten_view_past_width::<W64>();
}

/// When one `:flatten` view of a node overflows, the node's other views are skipped too:
/// the stored view `{Kc:2^(w/2), L0}` is representable, and with small counts the same
/// rule matches it (`flatten_views_multiply_counts`), but here it is not matched.
#[test]
fn flatten_overflow_keeps_the_stored_view() {
    for (prog, d) in [
        (
            flatten_view_past_width_prog::<W32>(),
            W32::run(&flatten_view_past_width_prog::<W32>(), NAIVE, &["t", "k"]),
        ),
        (
            flatten_view_past_width_prog::<W64>(),
            W64::run(&flatten_view_past_width_prog::<W64>(), NAIVE, &["t", "k"]),
        ),
    ] {
        let d = d.ok(&prog);
        for h in ["(H1 $t $k)", "(H1 $t (L0))"] {
            assert!(d.hits.contains(h), "{prog}\nmissing {h}: {:?}", d.hits);
        }
    }
}

// ─────────────── 5. boundaries ───────────────

fn boundaries<P: Preset>() {
    let max = P::max();
    let w = P::NAME;
    let over = (max as u128 + 1).to_string();

    // max: accepted, stored as max.
    let d = P::run(&format!("(let t (Add (L0):{max}))"), NAIVE, &["t"]).ok(w);
    assert_eq!(d.globals["t"].ac, vec![vec![("(L0)".to_string(), max)]]);

    // max + 1: refused, everywhere a ground term is written.
    for prog in [
        format!("(let t (Add (L0):{over}))"),
        format!("(Add (L0):{over} (L1))"),
        format!("(check (= (L0) (Add (L0):{over})))"),
        format!("(union (Z) (Add (L1) (L0):{over}))"),
    ] {
        let e = P::run(&prog, NAIVE, &[]).error(&prog);
        assert_overflow::<P>(&e, &prog, true);
        assert!(
            e.contains(&format!("the ground count {over} does not fit")),
            "{prog}: {e}"
        );
    }

    // 0: rejected by the sort checker, in every context.
    for prog in [
        "(let t (Add (L0):0 (L1)))",
        "(Add (L0):0 (L1))",
        "(check (= (L1) (Add (L0):0 (L1))))",
        "(union (Z) (Add (L0):0 (L1)))",
        "(let t (Cat (L0):0 (L1)))",
        "(let t (Add (L0):000 (L1)))",
    ] {
        let e = P::run(prog, NAIVE, &[]).sort_error(prog);
        assert!(
            e.contains("a ground multiplicity is at least 1"),
            "{prog}: {e}"
        );
    }

    // 1: the same node as no annotation, and `(Add c:1)` is `c`.
    let d = P::run(
        "(let t (Add (L0):1 (L1)))\n(let u (Add (L0) (L1)))\n(check (= t u))\n(check (= (Add (L0):1) (L0)))",
        NAIVE,
        &["t"],
    )
    .ok("k = 1");
    assert_eq!(d.nodes, 3, "k = 1 adds no node");
    assert_eq!(
        d.globals["t"].ac,
        vec![vec![("(L0)".to_string(), 1), ("(L1)".to_string(), 1)]]
    );

    // A pattern's exact count at the maximum matches, and one below does not.
    for s in [NAIVE, SEMI] {
        let prog = format!(
            "(let t (Add (L0):{max} (L1)))\n(rule ((= e (Add x:{max} ..r))) ((H1 e x)))\n(rule ((= e (Add x:{} ..r))) ((H2 e x)))\n(rule ((= e (Add x:k>={max} ..r))) ((H3 e x)))\n(run 1)",
            max - 1
        );
        let d = P::run(&prog, s, &["t"]).ok(&prog);
        let want: BTreeSet<String> = ["(H1 $t (L0))", "(H3 $t (L0))"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        assert_eq!(d.hits, want, "[{w} {s:?}]");
    }

    // A right-hand side literal: max fits, max + 1 is refused when the rule is installed
    // (at 64 bits max + 1 is 2^64, which the rule parser refuses: see above), 1 is the plain
    // child and 0 omits it.
    let d = P::run(
        &format!("(let w (W))\n(rewrite (W) (Add (L0):{max} (L1)))\n(run 1)"),
        NAIVE,
        &["w"],
    )
    .ok("rhs max");
    assert_eq!(
        d.globals["w"].ac,
        vec![vec![("(L0)".to_string(), max), ("(L1)".to_string(), 1)]]
    );
    if max < u64::MAX {
        let prog = format!("(let w (W))\n(rewrite (W) (Add (L0):{over} (L1)))\n(run 1)");
        let e = P::run(&prog, NAIVE, &[]).error(&prog);
        assert_overflow::<P>(&e, &prog, false);
    }
    // A written 0 means the element does not occur: refused, as in a ground term. A
    // computed 0 drops the child (`rhs_count_zero_that_empties_an_application_builds_nothing`).
    match P::run(
        "(let w (W))\n(rewrite (W) (G (Add (L0):1 (L1):0 (L2))))\n(run 1)",
        NAIVE,
        &[],
    ) {
        Outcome::Sort(e) => assert!(e.contains("a written multiplicity is at least 1"), "{e}"),
        other => panic!("rhs 1 and 0: expected a sort error, got {other:?}"),
    }
}

#[test]
fn count_boundaries_at_32_bits() {
    boundaries::<W32>();
}

#[test]
fn count_boundaries_at_64_bits() {
    boundaries::<W64>();
}

// ─────────────── 6. ACI ───────────────

/// An ACI operator stores a set, which holds each element once, so a count there has no
/// meaning: it is refused in a ground term, in a pattern, and on a right-hand side, for
/// any count, 1 and counts past every width included. Nothing is built.
fn aci<P: Preset>() {
    let max = P::max();
    for k in [
        "1".to_string(),
        "5".to_string(),
        max.to_string(),
        (max as u128 + 1).to_string(),
        "1000000000000000000000000000000".to_string(),
    ] {
        let ground = format!("(let t (And (L0):{k} (L1)))");
        match P::run(&ground, NAIVE, &[]) {
            Outcome::Sort(e) => assert!(
                e.contains("is ACI (set); multiplicities not allowed"),
                "{e}"
            ),
            other => panic!("{ground}: expected a sort error, got {other:?}"),
        }
    }
    for prog in [
        format!(
            "(let t (Add (L0):{max} (L1)))\n(rewrite (Add x:k (L1)) (G (And x:k (L1))))\n(run 1)"
        ),
        format!("(let w (W))\n(rewrite (W) (And (L0):{max} (L1)))\n(run 1)"),
        "(let t (And (L0) (L1)))\n(rewrite (And x:2 ..r) (W))\n(run 1)".to_string(),
    ] {
        for s in [NAIVE, SEMI] {
            match P::run(&prog, s, &[]) {
                Outcome::Sort(e) | Outcome::Error(e) => {
                    assert!(e.contains("multiplicities not allowed"), "{prog}: {e}")
                }
                other => panic!("{prog}: expected a refusal, got {other:?}"),
            }
        }
    }
}

#[test]
fn aci_counts_are_refused() {
    aci::<W32>();
    aci::<W64>();
}

// ─────────────── 7. A: positions, bounded ───────────────

const MAX_WIDTH: u64 = 1 << 20;
const TOO_WIDE: &str = "an application of more than 2^20 children";

fn seq<P: Preset>() {
    let max = P::max();
    // Exactly MAX_WIDTH positions: accepted, stored as positions.
    let prog = format!("(let t (Cat (L0):{MAX_WIDTH}))");
    let d = P::run(&prog, NAIVE, &["t"]).ok(&prog);
    assert_eq!(d.globals["t"].seq, vec![MAX_WIDTH as usize]);
    let prog = format!(
        "(let t (Cat (L0):{} (L1):{}))",
        MAX_WIDTH / 2,
        MAX_WIDTH / 2
    );
    let d = P::run(&prog, NAIVE, &["t"]).ok(&prog);
    assert_eq!(d.globals["t"].seq, vec![MAX_WIDTH as usize]);

    // One past, as one count or as a sum, and far past: refused, at once.
    for prog in [
        format!("(let t (Cat (L0):{}))", MAX_WIDTH + 1),
        format!(
            "(let t (Cat (L0):{} (L1):{}))",
            MAX_WIDTH / 2,
            MAX_WIDTH / 2 + 1
        ),
        format!("(let t (Cat (L0):{max}))"),
        "(let t (Cat (L0):1000000000000000000000000000000 (L1)))".to_string(),
        format!("(Cat (L1) (L0):{max})"),
    ] {
        let start = Instant::now();
        let e = P::run(&prog, NAIVE, &[]).error(&prog);
        assert!(
            start.elapsed() < Duration::from_secs(2),
            "{prog}: {:?}",
            start.elapsed()
        );
        assert!(e.contains(TOO_WIDE), "{prog}: {e}");
    }

    // A counted nested sequence splices as its positions.
    P::run(
        "(check (= (Cat (Cat (L0) (L1)):3 (L2)) (Cat (L0) (L1) (L0) (L1) (L0) (L1) (L2))))\n(check (= (Cat (L0):3 (L1)) (Cat (L0) (L0):2 (L1))))",
        NAIVE,
        &[],
    )
    .ok("nested seq");

    // A right-hand side: a literal at the bound, one past it, and a matched count far past
    // it, which must be refused before any position is written.
    let prog = format!("(let w (W))\n(rewrite (W) (Cat (L0):{MAX_WIDTH}))\n(run 1)");
    let d = P::run(&prog, NAIVE, &["w"]).ok(&prog);
    assert_eq!(d.globals["w"].seq, vec![MAX_WIDTH as usize]);
    let big = if max == u64::MAX { 1u64 << 63 } else { max };
    for prog in [
        format!(
            "(let w (W))\n(rewrite (W) (Cat (L0):{}))\n(run 1)",
            MAX_WIDTH + 1
        ),
        "(let t (Add (L0):5000000 (L1)))\n(rewrite (Add x:k (L1)) (G (Cat x:k)))\n(run 1)"
            .to_string(),
        format!(
            "(let t (Add (L0):{big} (L1)))\n(rewrite (Add x:k (L1)) (G (Cat x:k (L1))))\n(run 1)"
        ),
    ] {
        for s in [NAIVE, SEMI] {
            let start = Instant::now();
            let e = P::run(&prog, s, &[]).error(&prog);
            assert!(
                start.elapsed() < Duration::from_secs(2),
                "{prog}: {:?}",
                start.elapsed()
            );
            // The rule path reports the positions it could not write; it does not use the
            // ground path's TOO_WIDE text.
            assert!(
                e.contains("positions in the right-hand side is undefined"),
                "{prog}: {e}"
            );
        }
    }
}

#[test]
fn sequence_count_is_positions_up_to_the_bound() {
    seq::<W32>();
    seq::<W64>();
}

// ─────────────── 8. matching on counted nodes ───────────────

/// The rules every matching case installs, with `K` the exact count under test.
fn match_rules(k: u64, flatten: bool) -> String {
    let f = if flatten { " :flatten" } else { "" };
    format!(
        "(rule ((= e (Add x:{k} ..r))) ((H1 e x)){f})
(rule ((= e (Add x:k>=2 ..r))) ((H2 e x)){f})
(rule ((= e (Add x:k<=2 ..r))) ((H3 e x)){f})
(rule ((= e (Add x:{k} y))) ((H4 e x y)){f})
(rule ((= e (Add x:k y:j))) ((H5 e x y)){f})
(rule ((= e (Add x:k!=1 ..r))) ((H6 e x)){f})"
    )
}

/// What `match_rules` should produce on one AC node with these children, the node's class
/// printed as `e`.
fn match_oracle(m: &BTreeMap<String, u64>, k: u64, e: &str, out: &mut BTreeSet<String>) {
    for (x, &c) in m {
        if c == k {
            out.insert(format!("(H1 {e} {x})"));
        }
        if c >= 2 {
            out.insert(format!("(H2 {e} {x})"));
        }
        if c <= 2 {
            out.insert(format!("(H3 {e} {x})"));
        }
        if c != 1 {
            out.insert(format!("(H6 {e} {x})"));
        }
    }
    if m.len() == 2 {
        let v: Vec<(&String, &u64)> = m.iter().collect();
        for (a, b) in [(0, 1), (1, 0)] {
            let ((x, &cx), (y, &cy)) = (v[a], v[b]);
            if cx == k && cy == 1 {
                out.insert(format!("(H4 {e} {x} {y})"));
            }
            out.insert(format!("(H5 {e} {x} {y})"));
        }
    }
}

fn leaf_map() -> impl Strategy<Value = BTreeMap<u8, u64>> {
    prop::collection::btree_map(0u8..5, 1u64..=5, 1..=4)
        .prop_filter("an AC node", |m| m.len() > 1 || m.values().any(|&c| c > 1))
}

fn spell_flat(m: &BTreeMap<u8, u64>, style: Style) -> String {
    let t = T::Ac(0, m.iter().map(|(&i, &k)| (T::Leaf(i), k)).collect());
    render(&t, style)
}

fn named(m: &BTreeMap<u8, u64>) -> BTreeMap<String, u64> {
    m.iter().map(|(i, k)| (format!("(L{i})"), *k)).collect()
}

fn matching<P: Preset>(m: &BTreeMap<u8, u64>, k: u64, style: Style) -> Result<(), TestCaseError> {
    // Built by a rule, so semi-naive sees the node in a later round's delta.
    let prog = format!(
        "(let w (W))\n(rewrite (W) {})\n{}\n(run 3)",
        spell_flat(m, style),
        match_rules(k, false)
    );
    let mut want = BTreeSet::new();
    match_oracle(&named(m), k, "$w", &mut want);
    for s in [NAIVE, SEMI] {
        match P::run(&prog, s, &["w"]) {
            Outcome::Ok(d) => prop_assert_eq!(&d.hits, &want, "[{} {:?}]\n{}", P::NAME, s, prog),
            other => {
                return Err(TestCaseError::fail(format!(
                    "[{} {s:?}]\n{prog}\n{other:?}",
                    P::NAME
                )));
            }
        }
    }
    Ok(())
}

fn style() -> impl Strategy<Value = Style> {
    prop_oneof![
        Just(Style::Counted),
        Just(Style::Expanded),
        Just(Style::Split)
    ]
}

#[test]
fn rules_match_a_counted_node_as_its_expansion() {
    proptest_run(400, (leaf_map(), 1u64..=4, style()), |(m, k, st)| {
        matching::<W32>(&m, k, st)?;
        matching::<W64>(&m, k, st)
    });
}

/// `:flatten`: `t = Add{Kc:j, outer…}` with `Kc ≡ Add{inner…}` is read as
/// `outer + j·inner`, and also as stored, with `Kc` an ordinary child; without `:flatten`
/// only as stored. The inner node is matched as itself either way.
fn flatten_matching<P: Preset>(
    outer: &BTreeMap<u8, u64>,
    inner: &BTreeMap<u8, u64>,
    j: u64,
    k: u64,
) -> Result<(), TestCaseError> {
    let mut outer_parts: Vec<String> = outer
        .iter()
        .map(|(i, c)| counted(&format!("(L{i})"), *c))
        .collect();
    outer_parts.push(counted("(Kc)", j));
    let prog_base = format!(
        "(let k (Kc))\n(let t (Add {}))\n(union k {})\n",
        outer_parts.join(" "),
        spell_flat(inner, Style::Counted)
    );
    let mut view = named(outer);
    for (x, c) in named(inner) {
        *view.entry(x).or_default() += j * c;
    }
    let mut stored = named(outer);
    stored.insert("$k".to_string(), j);
    for flatten in [true, false] {
        let prog = format!("{prog_base}{}\n(run 1)", match_rules(k, flatten));
        let mut want = BTreeSet::new();
        // `Kc`'s class has two members, the leaf and the inner sum, and a `:flatten` rule
        // matches the outer node once per choice: as stored (the leaf) and opened.
        match_oracle(&stored, k, "$t", &mut want);
        if flatten {
            match_oracle(&view, k, "$t", &mut want);
        }
        match_oracle(&named(inner), k, "$k", &mut want);
        for s in [NAIVE, SEMI] {
            match P::run(&prog, s, &["t", "k"]) {
                Outcome::Ok(d) => {
                    prop_assert_eq!(&d.hits, &want, "[{} {:?}]\n{}", P::NAME, s, prog)
                }
                other => {
                    return Err(TestCaseError::fail(format!(
                        "[{} {s:?}]\n{prog}\n{other:?}",
                        P::NAME
                    )));
                }
            }
        }
    }
    Ok(())
}

#[test]
fn flatten_views_multiply_counts() {
    proptest_run(
        300,
        (
            prop::collection::btree_map(0u8..5, 1u64..=3, 1..=2),
            leaf_map(),
            1u64..=3,
            1u64..=6,
        ),
        |(outer, inner, j, k)| {
            flatten_matching::<W32>(&outer, &inner, j, k)?;
            flatten_matching::<W64>(&outer, &inner, j, k)
        },
    );
}

// ─────────────── 9. extraction at the width's maximum ───────────────

fn extract_roundtrip<P: Preset>() {
    let max = P::max();
    let prog = format!("(let t (Add (Add (L0):{max} (L1)):1 (F (Add (L2):{max})):{max}))");
    let d = P::run(&prog, NAIVE, &["t"]).ok(&prog);
    let text = d.globals["t"].extract.clone();
    assert_eq!(
        text,
        format!("(Add (F (Add (L2):{max})):{max} (L0):{max} (L1))")
    );
    let back = format!("{prog}\n(check (= t {text}))");
    let again = P::run(&back, NAIVE, &[]).ok(&back);
    assert_eq!(
        again.nodes, d.nodes,
        "the printed text names nodes that exist"
    );
    // A prints what it stores: the positions. (ACI takes no count: `aci_counts_are_refused`.)
    let d = P::run("(let s (Cat (L0):3 (L1)))", NAIVE, &["s"]).ok("a");
    assert_eq!(d.globals["s"].extract, "(Cat (L0) (L0) (L0) (L1))");
}

#[test]
fn extraction_prints_counts_that_read_back() {
    extract_roundtrip::<W32>();
    extract_roundtrip::<W64>();
}

// ─────────────── defects found ───────────────

/// A right-hand side whose counts leave an AC, ACI or A application with no child, on an
/// operator with no identity, would be a meaningless term. A written count of 0 is refused
/// when the program is checked, as it is in a ground term. A count computed to 0, or an
/// empty rest, drops the child at run time; the action is then skipped
/// (`apply::NO_VALUE`) and the run warns, so the term is never built and nothing panics.
/// Reproducer of the former panic: `tests/egg/mult_rhs_zero_empty.egg`.
#[test]
fn rhs_count_zero_that_empties_an_application_builds_nothing() {
    for prog in [
        "(let w (W))\n(rewrite (W) (G (Add (L0):0)))\n(run 1)",
        "(let w (W))\n(rewrite (W) (G (Cat (L0):0)))\n(run 1)",
    ] {
        for out in [W32::run(prog, NAIVE, &[]), W64::run(prog, SEMI, &[])] {
            match out {
                Outcome::Sort(e) => {
                    assert!(e.contains("a written multiplicity is at least 1"), "{e}")
                }
                other => panic!("{prog}\nexpected a sort error, got {other:?}"),
            }
        }
    }
    for (prog, base) in [
        (
            "(let t (Add (L0):2))\n(rewrite (Add x:k>=2 ..r) (G (Add x:(u64::- k 2) ..r)))\n(run 1)",
            "(let t (Add (L0):2))\n(run 1)",
        ),
        (
            "(let t (Add (L0):3))\n(rewrite (Add x:3 ..r) (G (Add ..r)))\n(run 1)",
            "(let t (Add (L0):3))\n(run 1)",
        ),
    ] {
        for (out, base) in [
            (W32::run(prog, NAIVE, &[]), W32::run(base, NAIVE, &[])),
            (W64::run(prog, SEMI, &[]), W64::run(base, SEMI, &[])),
        ] {
            match (out, base) {
                (Outcome::Ok(d), Outcome::Ok(b)) => {
                    assert_eq!(d.nodes, b.nodes, "{prog}: a node was built")
                }
                (other, _) => panic!("{prog}\nexpected a run that builds nothing, got {other:?}"),
            }
        }
    }
}

/// A count past 2^64 in a rule is a parse error ("Expected number"), while the same count
/// in a ground term is reported as a `multiplicity overflow`. The rule language reads a
/// count with `parser::number` (u64); the ground term reads a `BigUint`.
#[test]
fn rule_count_past_u64_is_reported_as_an_overflow() {
    let prog = "(let w (W))\n(rewrite (W) (Add (L0):18446744073709551616 (L1)))\n(run 1)";
    for out in [W32::run(prog, NAIVE, &[]), W64::run(prog, NAIVE, &[])] {
        match out {
            Outcome::Error(e) | Outcome::Sort(e) | Outcome::Parse(e) => {
                assert!(e.contains(OVERFLOW), "{e}")
            }
            other => panic!("{other:?}"),
        }
    }
}
