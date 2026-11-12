// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Debug mirror of the completion merges (debug builds only).
//!
//! Every merge the AC completion code makes (`cc_round`, `inverse_cancel_repair`,
//! `inverse_law_repair`, `lattice_round`) carries a [`MergeWhy`] tag naming the Lean
//! theorem that justifies it and the data that theorem's preconditions mention
//! (`proofs/lean/SemperProofs/CC/EngineSteps.lean`, `Laws/InvRules.lean`,
//! `Lattice.lean`). `merge_in_classes` hands each merge made inside the completion code
//! to [`EGraph::cc_mirror_on_merge`], which checks the preconditions and panics when one
//! fails or when the merge has no tag.
//!
//! The checker shares no reduction code with the engine: it has its own monomial
//! arithmetic (`m_*`), its own count clamp, rule application, inverse-pair removal,
//! critical pair, degree-lex comparison and integer lattice basis. It reads the state
//! only: stored children, node flags, the union-find, the per-class right-hand-side
//! slots (unit, `atomic`, `min_monomial`), the order keys and the inverse nodes.
//!
//! # Which state the preconditions are read in
//!
//! The Lean state keeps a node's monomial as written when a merge changes `find`
//! (`State.merge` changes `find` only), and the engine's round does the same: `cc_round`
//! reads its rules once, after `rebuild_congruence`, and no node is recanonized before
//! the round ends. The mirror therefore spells monomials as the round started:
//!
//! * the rule table ([`RoundTable`]) is the checker's own scan at the start of the
//!   round: every active node `(M, c)` with `M ≫ rhs(c)`, `rhs` read from the class
//!   slot. This is `State.rules` of the round-start state;
//! * the pair `(P₁, P₂)` and the `Normalize` steps are computed over that table, in
//!   the round-start spelling;
//! * class membership (`inv x = some y`, "the classes merged are the classes of the
//!   materialized nodes") is read through the union-find as it stands at the merge.
//!
//! Two differences from the literal hypotheses of the theorems follow, and the mirror
//! counts each instead of hiding it ([`Note`]):
//!
//! * [`Note::StaleRule`]: the theorems take `r ∈ st.rules` and `Normalize L inv st`
//!   for the state `st` the merge is applied to. Earlier merges of the same round can
//!   retire a rule's node (the (A′) pass sets `FLAG_AC_COLLAPSED`) or move its class's
//!   right-hand side, so a round-start rule need not be a rule of `st`. It is still an
//!   equation of `st` (`State.eqs` only grows under `merge`), which is all the proofs
//!   use (`rules_eqs`). The note is counted when a tagged rule is no rule of `st`, or
//!   when no `Normalize` derivation over the rules of `st` alone is found.
//! * [`Note::Respelled`]: `materialize` canonizes the reduct through the current
//!   union-find and the operator's laws (`add_monomial`), so the node it returns holds
//!   the reduct up to classes merged earlier in the round and law instances, not the
//!   monomial as spelled. The mirror checks that the node's stored monomial is reached
//!   from the reduct, read through the union-find, by law instances (unit drop, count
//!   clamp, inverse-pair removal).
//!
//! # How `Normalize` is checked
//!
//! By search, not by replaying the engine: a depth-first search from `P` over single
//! rewrite steps `M → clamp((M − A) + B)` for the rules `A → B` of the table with
//! `A ≤ M` (and the same rule applied as often as `M` holds `A`, which is that many
//! single steps) and removals of one pair `{x, inv x}`, until it reaches the reduct the
//! engine materialized. The search is bounded by [`SEARCH_CAP`] distinct monomials; a
//! search that exhausts the bound fails the check.

use super::EGraph;
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};
use crate::registry::{Clamp, OpKind};
use crate::typed_routing::NodeRef;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

/// A monomial of the checker: `(class, count)` sorted by class, counts positive.
pub(super) type Mono<G> = Vec<(G, u128)>;

/// Distinct monomials one reachability search may visit.
const SEARCH_CAP: usize = 20_000;

/// The justification kinds, one per Lean precondition shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `superpose_infer`.
    Superpose,
    /// `axiomPair_infer`, `AxiomPair.idem`.
    AxiomIdem,
    /// `axiomPair_infer`, `AxiomPair.nil`.
    AxiomNil,
    /// `axiomPair_infer`, `AxiomPair.invLeft` (R3, `InvInfer.r3_left`).
    AxiomInvLeft,
    /// `axiomPair_infer`, `AxiomPair.invRight` (R3, `InvInfer.r3_right`).
    AxiomInvRight,
    /// `cancelClose_infer`, `CancelPair.c1`.
    CancelC1,
    /// `cancelClose_infer`, `CancelPair.c2`.
    CancelC2,
    /// `cancelClose_infer`, `CancelPair.constant` over a `c1` pair.
    CancelC1Constant,
    /// `cancelClose_infer`, `CancelPair.constant` over a `c2` pair.
    CancelC2Constant,
    /// The (A′) pass: a node and a `Normalize` reduct of it (`pair_infer` with both
    /// sides the node's monomial).
    NormalForm,
    /// `inverseRepair_infer`.
    InverseRepair,
    /// `InvInfer.r1_inj`.
    InvR1Inj,
    /// `InvInfer.r1_inv`.
    InvR1Inv,
    /// `InvInferUK.r2_inv_unit`.
    InvR2InvUnit,
    /// `InvInferUK.r2_unit_inv`.
    InvR2UnitInv,
    /// `InvInferUK.r4`.
    InvR4,
    /// `InvInferUK.r5`.
    InvR5,
    /// `lattice_merge_sound`.
    Lattice,
}

impl Kind {
    pub const ALL: [Kind; 18] = [
        Kind::Superpose,
        Kind::AxiomIdem,
        Kind::AxiomNil,
        Kind::AxiomInvLeft,
        Kind::AxiomInvRight,
        Kind::CancelC1,
        Kind::CancelC2,
        Kind::CancelC1Constant,
        Kind::CancelC2Constant,
        Kind::NormalForm,
        Kind::InverseRepair,
        Kind::InvR1Inj,
        Kind::InvR1Inv,
        Kind::InvR2InvUnit,
        Kind::InvR2UnitInv,
        Kind::InvR4,
        Kind::InvR5,
        Kind::Lattice,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Kind::Superpose => "superpose",
            Kind::AxiomIdem => "axiom_idem",
            Kind::AxiomNil => "axiom_nil",
            Kind::AxiomInvLeft => "axiom_inv_left",
            Kind::AxiomInvRight => "axiom_inv_right",
            Kind::CancelC1 => "cancel_c1",
            Kind::CancelC2 => "cancel_c2",
            Kind::CancelC1Constant => "cancel_c1_constant",
            Kind::CancelC2Constant => "cancel_c2_constant",
            Kind::NormalForm => "normal_form",
            Kind::InverseRepair => "inverse_repair",
            Kind::InvR1Inj => "inv_r1_inj",
            Kind::InvR1Inv => "inv_r1_inv",
            Kind::InvR2InvUnit => "inv_r2_inv_unit",
            Kind::InvR2UnitInv => "inv_r2_unit_inv",
            Kind::InvR4 => "inv_r4",
            Kind::InvR5 => "inv_r5",
            Kind::Lattice => "lattice",
        }
    }
}

/// Where a checked merge differs from the literal hypotheses of its theorem (module
/// docs). Counted per merge, never a failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Note {
    /// The merge is justified by a round-start rule that is no rule of the state the
    /// merge is applied to.
    StaleRule,
    /// A materialized node holds its reduct up to the union-find and law instances.
    Respelled,
    /// The engine builds a side of the pair with the count clamp only, and the Lean
    /// definition applies the full `Laws.clamp` (unit drop, count clamp, inverse walk):
    /// the two differ, and the engine's normalization removes the difference. The
    /// `Normalize` search starts from the Lean side.
    PairClamped,
    /// A materialized monomial is a `Normalize` reduct of the side as the engine built
    /// it and of no side the Lean definition gives: the engine's side keeps a unit class
    /// or an inverse pair that `Laws.clamp` removes, and `Normalize` has no step that
    /// adds one back. The two sides are equal by law instances, so `pair_infer` applies
    /// to the engine's side; the theorem as stated does not.
    FromUnclampedPair,
    /// A materialized monomial is reached from its side by the engine's rewrite steps
    /// (count clamp, inverse pairs removed at the end) and by no sequence of `Rw` steps,
    /// which apply the full `Laws.clamp` after each rewrite: an inverse pair or a unit
    /// the clamp removes early can disable a rule the engine applies later. Each step is
    /// an equation of the state or a law instance, so the reduct is `=_E` to its side;
    /// `Normalize` as stated does not reach it.
    EngineSteps,
    /// A materialized monomial is a `Normalize` reduct of the clamp of a side that the
    /// Lean definition leaves unclamped (the second side of an `AxiomPair`, both sides of
    /// a `CancelPair`) and of no side the definition gives: the engine's normalization
    /// clamps its input before the first rewrite, and `Normalize` has a clamp only inside
    /// a rewrite step. `tests/egg/cc_mirror_cancel_clamp.egg` (`:nilpotent 3`): the C2
    /// pair `({c, d³}, {e})` normalizes to `{c}`, which no `Rw` or `InvCancel` step from
    /// `{c, d³}` reaches. The clamp is a law instance, so `pair_infer` applies.
    ClampedSide,
}

impl Note {
    pub const ALL: [Note; 6] = [
        Note::StaleRule,
        Note::Respelled,
        Note::PairClamped,
        Note::FromUnclampedPair,
        Note::EngineSteps,
        Note::ClampedSide,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Note::StaleRule => "stale_rule",
            Note::Respelled => "respelled",
            Note::PairClamped => "pair_clamped",
            Note::FromUnclampedPair => "from_unclamped_pair",
            Note::EngineSteps => "engine_steps",
            Note::ClampedSide => "clamped_side",
        }
    }
}

static CHECKED: [AtomicU64; Kind::ALL.len()] = [const { AtomicU64::new(0) }; Kind::ALL.len()];
static NOTED: [AtomicU64; Note::ALL.len()] = [const { AtomicU64::new(0) }; Note::ALL.len()];

/// Merges checked so far in this process, per kind.
pub fn counts() -> Vec<(&'static str, u64)> {
    Kind::ALL
        .iter()
        .map(|&k| (k.name(), CHECKED[k as usize].load(Ordering::Relaxed)))
        .collect()
}

/// Checked merges carrying each [`Note`], in this process.
pub fn notes() -> Vec<(&'static str, u64)> {
    Note::ALL
        .iter()
        .map(|&k| (k.name(), NOTED[k as usize].load(Ordering::Relaxed)))
        .collect()
}

/// With `CC_MIRROR_LOG=<file>` every checked merge appends one line (its kind, then its
/// notes) to the file, so counts can be summed over the processes of a test run.
fn log_line(kind: Kind, notes: &[Note]) {
    use std::io::Write;
    static LOG: std::sync::OnceLock<Option<std::sync::Mutex<std::fs::File>>> =
        std::sync::OnceLock::new();
    let log = LOG.get_or_init(|| {
        let path = std::env::var_os("CC_MIRROR_LOG")?;
        let file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .ok()?;
        Some(std::sync::Mutex::new(file))
    });
    if let Some(file) = log {
        let mut line = String::from(kind.name());
        for n in notes {
            line.push(' ');
            line.push_str(n.name());
        }
        line.push('\n');
        if let Ok(mut f) = file.lock() {
            let _ = f.write_all(line.as_bytes());
        }
    }
}

/// Which pair of the round a critical pair is, with the data its Lean definition takes.
/// Rules are named by their node.
#[derive(Clone, Copy, Debug)]
pub(super) enum PairWhy<G> {
    /// `criticalPair L r₁ r₂`.
    Superpose { r1: G, r2: G },
    /// `AxiomPair.idem`: rule and `a ∈ A`.
    Idem { rule: G, a: G },
    /// `AxiomPair.nil`: rule and `a ∈ A`.
    Nil { rule: G, a: G },
    /// `AxiomPair.invLeft`: rule, `a ∈ A`, `inv a = some y`.
    InvLeft { rule: G, a: G, y: G },
    /// `AxiomPair.invRight`: rule, `y ∈ A`, `inv x = some y`.
    InvRight { rule: G, x: G, y: G },
    /// `CancelPair.c1`, or `CancelPair.constant` over it.
    C1 { rule: G },
    /// `CancelPair.c2`, or `CancelPair.constant` over it.
    C2 { r1: G, r2: G },
}

/// Which inference of `inverse_law_repair` a merge is.
#[derive(Clone, Copy, Debug)]
pub(super) enum InvRule<G> {
    /// Two inverse nodes in one class: their children are merged.
    R1Inj,
    /// `node = inv(x)` and `x` holds some `inv(z)`: `node` and `z` are merged.
    R1Inv { node: G },
    /// `node = inv(x)` in the unit class: `x` joins the unit.
    R2InvUnit { node: G },
    /// `node = inv(x)` with `x` in the unit class: `node` joins the unit.
    R2UnitInv { node: G },
    /// `node = inv(x)`: `x^(k−1)` is built and merged with `node`.
    R4 { node: G },
    /// `node = inv(x)` of class `y`: `y^(k−1)` is built and merged with `x`.
    R5 { node: G },
}

/// The justification of one merge of the completion code. The two merged ids are the
/// arguments of the merge, in order.
#[derive(Clone, Debug)]
pub(super) enum MergeWhy<G, O> {
    /// (B) close: `pair` is the pair before normalization, `reducts` the two monomials
    /// materialized; the merge joins the two materialized nodes.
    Pair {
        op: O,
        origin: PairWhy<G>,
        pair: (Mono<G>, Mono<G>),
        reducts: (Mono<G>, Mono<G>),
    },
    /// (A′): `reduct` is the normal form of `node`'s monomial; the merge joins the
    /// materialized node and the class of `node`.
    NormalForm { op: O, node: G, reduct: Mono<G> },
    /// `inverse_cancel_repair`: `reduct` is `node`'s monomial without its inverse pairs;
    /// the merge joins the materialized node and `node`.
    InverseRepair { op: O, node: G, reduct: Mono<G> },
    /// `inverse_law_repair`.
    InverseLaw { op: O, rule: InvRule<G> },
    /// `lattice_round`: the two classes differ by a member of the lattice of `op`'s rows.
    Lattice { op: O },
}

/// One rule of the round-start state.
#[derive(Debug)]
struct RuleRow<G, O> {
    op: O,
    node: G,
    lhs: Mono<G>,
    rhs: Mono<G>,
}

/// The checker's reading of the round-start state: its rules, the monomial of every
/// active node, and the classes that occur as a child.
pub(super) struct RoundTable<G, O> {
    /// Sorted by node.
    rules: Vec<RuleRow<G, O>>,
    /// `(node, op, monomial)` of every active node, sorted by node.
    active: Vec<(G, O, Mono<G>)>,
    /// `(op, class)` for every class a node of `op` lists as a child.
    children: HashSet<(O, G)>,
}

/// An echelon basis of an integer lattice, one row per leading column.
struct Basis<G> {
    cols: HashMap<G, usize>,
    pivots: Vec<Option<Vec<BigInt>>>,
}

/// The mirror's state on the e-graph.
pub(super) struct Mirror<G, O> {
    /// Inside the completion code: every merge must carry a tag.
    in_scope: bool,
    pending: Option<MergeWhy<G, O>>,
    table: Option<RoundTable<G, O>>,
}

impl<G, O> Default for Mirror<G, O> {
    fn default() -> Self {
        Self {
            in_scope: false,
            pending: None,
            table: None,
        }
    }
}

/// An engine monomial in the checker's representation.
pub(super) fn mono<G: Copy + Ord, M: MultiplicityLike>(ms: &[(G, M)]) -> Mono<G> {
    let mut out: Mono<G> = ms.iter().map(|&(g, m)| (g, wide(m))).collect();
    out.sort_unstable_by_key(|p| p.0);
    out
}

fn wide<M: MultiplicityLike>(m: M) -> u128 {
    match m.to_u64() {
        Some(k) => u128::from(k),
        None => u128::try_from(m.to_biguint()).expect("a multiplicity fits 128 bits"),
    }
}

// ── Monomial arithmetic of the checker ──

/// Combine two monomials count by count; `None` when `f` overflows.
fn m_zip<G: Copy + Ord>(
    a: &[(G, u128)],
    b: &[(G, u128)],
    f: impl Fn(u128, u128) -> Option<u128>,
) -> Option<Mono<G>> {
    let mut counts: BTreeMap<G, (u128, u128)> = BTreeMap::new();
    for &(g, k) in a {
        counts.entry(g).or_default().0 = k;
    }
    for &(g, k) in b {
        counts.entry(g).or_default().1 = k;
    }
    let mut out = Vec::with_capacity(counts.len());
    for (g, (x, y)) in counts {
        let k = f(x, y)?;
        if k != 0 {
            out.push((g, k));
        }
    }
    Some(out)
}

/// `a + b`.
fn m_add<G: Copy + Ord>(a: &[(G, u128)], b: &[(G, u128)]) -> Option<Mono<G>> {
    m_zip(a, b, u128::checked_add)
}

/// `a − b`, truncated.
fn m_sub<G: Copy + Ord>(a: &[(G, u128)], b: &[(G, u128)]) -> Mono<G> {
    m_zip(a, b, |x, y| Some(x.saturating_sub(y))).expect("subtraction does not overflow")
}

/// `a ∪ b`, by maximum.
fn m_max<G: Copy + Ord>(a: &[(G, u128)], b: &[(G, u128)]) -> Mono<G> {
    m_zip(a, b, |x, y| Some(x.max(y))).expect("maximum does not overflow")
}

/// `a ∩ b`, by minimum.
fn m_min<G: Copy + Ord>(a: &[(G, u128)], b: &[(G, u128)]) -> Mono<G> {
    m_zip(a, b, |x, y| Some(x.min(y))).expect("minimum does not overflow")
}

fn m_count<G: Copy + Ord>(m: &[(G, u128)], g: G) -> u128 {
    m.iter().find(|p| p.0 == g).map_or(0, |p| p.1)
}

/// `a ≤ b`.
fn m_le<G: Copy + Ord>(a: &[(G, u128)], b: &[(G, u128)]) -> bool {
    a.iter().all(|&(g, k)| k <= m_count(b, g))
}

/// `k` copies of `g`.
fn m_rep<G: Copy + Ord>(g: G, k: u128) -> Mono<G> {
    if k == 0 { Vec::new() } else { vec![(g, k)] }
}

fn m_scale<G: Copy + Ord>(a: &[(G, u128)], q: u128) -> Option<Mono<G>> {
    a.iter()
        .map(|&(g, k)| k.checked_mul(q).map(|k| (g, k)))
        .collect()
}

/// The count clamp of an operator (`Laws.clamp` without the unit drop and the inverse
/// walk, which the stored monomials and the `Normalize` steps carry).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CountClamp {
    None,
    Idempotent,
    Nilpotent(u128),
}

impl CountClamp {
    fn apply<G: Copy + Ord>(self, m: &mut Mono<G>) {
        match self {
            CountClamp::None => {}
            CountClamp::Idempotent => m.iter_mut().for_each(|p| p.1 = 1),
            CountClamp::Nilpotent(k) => {
                m.iter_mut().for_each(|p| p.1 %= k);
                m.retain(|p| p.1 != 0);
            }
        }
    }
}

fn add_note(notes: &mut Vec<Note>, n: Note, on: bool) {
    if on && !notes.contains(&n) {
        notes.push(n);
    }
}

/// The outcome of a reachability search: the labels along a path, or why none was found.
enum Reach {
    Found(Vec<usize>),
    NotFound,
    Budget,
}

/// Depth-first search from `start` to a monomial satisfying `goal`. `succ` lists the
/// one-step successors of a monomial, each with an optional label (a rule index).
fn m_reach<G: Copy + Ord + std::hash::Hash>(
    start: &Mono<G>,
    goal: impl Fn(&Mono<G>) -> bool,
    succ: impl Fn(&Mono<G>, &mut Vec<(Mono<G>, Option<usize>)>),
) -> Reach {
    let mut arena: Vec<(Mono<G>, usize, Option<usize>)> = vec![(start.clone(), usize::MAX, None)];
    let mut seen: HashSet<Mono<G>> = HashSet::new();
    seen.insert(start.clone());
    let mut stack = vec![0usize];
    let mut next: Vec<(Mono<G>, Option<usize>)> = Vec::new();
    while let Some(i) = stack.pop() {
        if goal(&arena[i].0) {
            let mut labels = Vec::new();
            let mut at = i;
            while at != usize::MAX {
                labels.extend(arena[at].2);
                at = arena[at].1;
            }
            return Reach::Found(labels);
        }
        next.clear();
        succ(&arena[i].0, &mut next);
        // Reverse, so the first successor listed is the first explored.
        for (m, label) in next.drain(..).rev() {
            if seen.insert(m.clone()) {
                if arena.len() >= SEARCH_CAP {
                    return Reach::Budget;
                }
                arena.push((m, i, label));
                stack.push(arena.len() - 1);
            }
        }
    }
    Reach::NotFound
}

/// Insert `row` into an echelon basis, keeping one row per leading column.
fn basis_insert(pivots: &mut [Option<Vec<BigInt>>], mut row: Vec<BigInt>) {
    loop {
        let Some(j) = row.iter().position(|v| !v.is_zero()) else {
            return;
        };
        match pivots[j].take() {
            None => {
                if row[j].is_negative() {
                    row.iter_mut().for_each(|v| *v = -&*v);
                }
                pivots[j] = Some(row);
                return;
            }
            Some(mut p) => {
                // Euclid on the leading entries: the row with the smaller leading entry
                // stays as the pivot, the other loses a multiple of it and is inserted.
                if row[j].abs() > p[j].abs() {
                    std::mem::swap(&mut row, &mut p);
                }
                let q = &p[j] / &row[j];
                for k in j..p.len() {
                    let t = &q * &row[k];
                    p[k] -= t;
                }
                if row[j].is_negative() {
                    row.iter_mut().for_each(|v| *v = -&*v);
                }
                pivots[j] = Some(row);
                row = p;
            }
        }
    }
}

/// Whether `v` is an integer combination of the basis rows.
fn basis_member(pivots: &[Option<Vec<BigInt>>], mut v: Vec<BigInt>) -> bool {
    loop {
        let Some(j) = v.iter().position(|x| !x.is_zero()) else {
            return true;
        };
        let Some(p) = &pivots[j] else {
            return false;
        };
        if !(&v[j] % &p[j]).is_zero() {
            return false;
        }
        let q = &v[j] / &p[j];
        for k in j..v.len() {
            let t = &q * &p[k];
            v[k] -= t;
        }
    }
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    /// Enter `cc_round`: read the round-start rules.
    pub(super) fn cc_mirror_enter_round(&mut self) {
        self.cc_mirror.table = Some(self.mirror_round_table());
        self.cc_mirror_enter();
    }

    /// Enter a completion pass that reads no rule table (the repairs, `lattice_round`).
    pub(super) fn cc_mirror_enter(&mut self) {
        debug_assert!(!self.cc_mirror.in_scope, "completion mirror: nested scope");
        self.cc_mirror.in_scope = true;
        self.cc_mirror.pending = None;
    }

    pub(super) fn cc_mirror_exit(&mut self) {
        debug_assert!(
            self.cc_mirror.pending.is_none(),
            "completion mirror: a tag was left pending"
        );
        self.cc_mirror.in_scope = false;
        self.cc_mirror.table = None;
    }

    /// Tag the next merge.
    pub(super) fn cc_mirror_tag(&mut self, why: MergeWhy<Cfg::G, Cfg::O>) {
        debug_assert!(
            self.cc_mirror.pending.is_none(),
            "completion mirror: a tag was left pending"
        );
        self.cc_mirror.pending = Some(why);
    }

    /// Drop the tag of a merge that did not happen (its classes were already one).
    pub(super) fn cc_mirror_untag(&mut self) {
        self.cc_mirror.pending = None;
    }

    /// Called by `merge_in_classes` for every merge of two distinct classes.
    pub(super) fn cc_mirror_on_merge(&mut self, a: Cfg::G, b: Cfg::G) {
        if !self.cc_mirror.in_scope {
            return;
        }
        let Some(why) = self.cc_mirror.pending.take() else {
            panic!("completion mirror: untagged merge of {a:?} and {b:?} in the completion code");
        };
        let table = self.cc_mirror.table.take();
        let verdict = match &why {
            MergeWhy::Lattice { op } => self.mirror_check_lattice(*op, a, b),
            _ => self.mirror_check(&why, a, b, table.as_ref()),
        };
        match verdict {
            Ok((kind, notes)) => {
                CHECKED[kind as usize].fetch_add(1, Ordering::Relaxed);
                for n in &notes {
                    NOTED[*n as usize].fetch_add(1, Ordering::Relaxed);
                }
                log_line(kind, &notes);
            }
            Err(msg) => {
                let rules = table
                    .as_ref()
                    .map(|t| self.mirror_show_rules(t, &why))
                    .unwrap_or_default();
                panic!(
                    "completion mirror: the merge of {a:?} and {b:?} fails its check: {msg}\n\
                     tag: {why:?}\nrules of the operator at the start of the round:\n{rules}"
                );
            }
        }
        self.cc_mirror.table = table;
    }

    fn mirror_show_rules(
        &self,
        table: &RoundTable<Cfg::G, Cfg::O>,
        why: &MergeWhy<Cfg::G, Cfg::O>,
    ) -> String {
        let op = match why {
            MergeWhy::Pair { op, .. }
            | MergeWhy::NormalForm { op, .. }
            | MergeWhy::InverseRepair { op, .. }
            | MergeWhy::InverseLaw { op, .. }
            | MergeWhy::Lattice { op } => *op,
        };
        let mut out = String::new();
        for r in table.rules.iter().filter(|r| r.op == op) {
            out.push_str(&format!(
                "  node {:?}: {:?} -> {:?}{}\n",
                r.node,
                r.lhs,
                r.rhs,
                if self.mirror_rule_current(r) {
                    ""
                } else {
                    "  (no rule of the current state)"
                }
            ));
        }
        out
    }

    // ── Reading the state ──

    fn mirror_is_set(&self, op: Cfg::O) -> bool {
        matches!(self.ops.info(op).kind, OpKind::Set { .. })
    }

    fn mirror_clamp(&self, op: Cfg::O) -> CountClamp {
        match self.ops.info(op).kind {
            OpKind::Set { .. } => CountClamp::Idempotent,
            OpKind::MSet {
                clamp: Clamp::Nilpotent { order },
                ..
            } => CountClamp::Nilpotent(u128::from(order)),
            _ => CountClamp::None,
        }
    }

    fn mirror_cancellative(&self, op: Cfg::O) -> bool {
        matches!(
            self.ops.info(op).kind,
            OpKind::MSet {
                cancellative: true,
                ..
            } | OpKind::Set {
                cancellative: true,
                ..
            }
        )
    }

    /// Whether `id` is a stored monomial node of `op`.
    fn mirror_is_node_of(&self, id: Cfg::G, op: Cfg::O) -> bool {
        matches!(self.node_ref(id), NodeRef::MSet(_) | NodeRef::Set(_)) && self.node_op(id) == op
    }

    /// `m` read through the union-find as it stands, counts of one class added (kept at
    /// one under a set operator).
    fn mirror_through_find(&self, op: Cfg::O, m: &[(Cfg::G, u128)]) -> Mono<Cfg::G> {
        let set = self.mirror_is_set(op);
        let mut counts: BTreeMap<Cfg::G, u128> = BTreeMap::new();
        for &(g, k) in m {
            let e = counts.entry(self.classes.find_const(g)).or_insert(0);
            *e = if set {
                1
            } else {
                e.checked_add(k).expect("a count fits 128 bits")
            };
        }
        counts.into_iter().filter(|p| p.1 != 0).collect()
    }

    /// The stored children of a monomial node, read through the union-find.
    fn mirror_node_monomial(&self, node: Cfg::G) -> Mono<Cfg::G> {
        let mut raw: Mono<Cfg::G> = Vec::new();
        self.for_each_child(node, |g, m| raw.push((g, wide(m))));
        // Two entries of one class are added by `mirror_through_find`; entries of one
        // stored id are added here.
        let mut by_id: BTreeMap<Cfg::G, u128> = BTreeMap::new();
        for (g, k) in raw {
            *by_id.entry(g).or_insert(0) += k;
        }
        let stored: Mono<Cfg::G> = by_id.into_iter().collect();
        self.mirror_through_find(self.node_op(node), &stored)
    }

    /// `rhs(find c)` for the class of `node` under `op`: empty for the unit class, the
    /// class itself when it is atomic, else the monomial of the stored minimal node.
    fn mirror_class_rhs(&self, node: Cfg::G, op: Cfg::O) -> Option<Mono<Cfg::G>> {
        let cls = self.classes.find_const(node);
        if self
            .unit_node(op)
            .is_some_and(|u| self.classes.find_const(u) == cls)
        {
            return Some(Vec::new());
        }
        let repr = self.classes.repr_id(cls)?;
        if self.classes.atomic(repr) {
            return Some(vec![(cls, 1)]);
        }
        let col = self.ops.completion_column(op)?;
        let min = self.classes.min_monomial(repr, col)?;
        Some(self.mirror_node_monomial(min))
    }

    /// `a ≫ b` in degree-lex over the classes' order keys (`degLex`): more children, or
    /// as many and the larger count at the largest key where the counts differ.
    fn mirror_deglex_gt(&self, a: &[(Cfg::G, u128)], b: &[(Cfg::G, u128)]) -> bool {
        let size = |m: &[(Cfg::G, u128)]| m.iter().fold(0u128, |s, p| s.saturating_add(p.1));
        let (sa, sb) = (size(a), size(b));
        if sa != sb {
            return sa > sb;
        }
        let mut by_key: BTreeMap<Cfg::G, (u128, u128)> = BTreeMap::new();
        for &(g, k) in a {
            by_key.entry(self.order_key(g)).or_default().0 += k;
        }
        for &(g, k) in b {
            by_key.entry(self.order_key(g)).or_default().1 += k;
        }
        for (_, (x, y)) in by_key.into_iter().rev() {
            if x != y {
                return x > y;
            }
        }
        false
    }

    /// The inverse relation of `op` under the union-find as it stands: `(x, y)` for every
    /// stored node `inv(x')` with `find x' = x` in class `y`. Sorted.
    fn mirror_inverse(&self, op: Cfg::O) -> Vec<(Cfg::G, Cfg::G)> {
        let Some(inv) = self.inverse_op(op) else {
            return Vec::new();
        };
        let mut rel: Vec<(Cfg::G, Cfg::G)> = self
            .inverse_nodes(inv)
            .into_iter()
            .map(|(node, x)| (self.classes.find_const(x), self.classes.find_const(node)))
            .collect();
        rel.sort_unstable();
        rel.dedup();
        rel
    }

    /// `inv x = some y` or `inv y = some x`, on the classes of `x` and `y`.
    fn mirror_inverse_pair(&self, rel: &[(Cfg::G, Cfg::G)], x: Cfg::G, y: Cfg::G) -> bool {
        let (x, y) = (self.classes.find_const(x), self.classes.find_const(y));
        rel.binary_search(&(x, y)).is_ok() || rel.binary_search(&(y, x)).is_ok()
    }

    /// `Laws.clamp` of the operator (`combinedClamp`, `identityInverseClamp` and the
    /// single-law clamps): drop the unit class, clamp the counts, then the inverse walk
    /// `invWalk`, which visits the classes in ascending order and at `x` with
    /// `inv x = some y` removes `min(#x, #y)` copies of each (pairs of `x` when `y = x`).
    fn mirror_lean_clamp(&self, op: Cfg::O, m: &[(Cfg::G, u128)]) -> Mono<Cfg::G> {
        let unit = self.unit_node(op).map(|u| self.classes.find_const(u));
        let mut out: Mono<Cfg::G> = m.iter().copied().filter(|p| Some(p.0) != unit).collect();
        self.mirror_clamp(op).apply(&mut out);
        let rel = self.mirror_inverse(op);
        if rel.is_empty() {
            return out;
        }
        let classes: Vec<Cfg::G> = out.iter().map(|p| p.0).collect();
        for x in classes {
            let Some(&(_, y)) = rel.iter().find(|p| p.0 == x) else {
                continue;
            };
            let cx = m_count(&out, x);
            let take = if y == x {
                m_rep(x, 2 * (cx / 2))
            } else {
                let k = cx.min(m_count(&out, y));
                m_add(&m_rep(x, k), &m_rep(y, k)).expect("counts of a monomial")
            };
            out = m_sub(&out, &take);
        }
        out
    }

    /// The monomials one `InvCancel` step away from `m`.
    fn mirror_inverse_steps(
        &self,
        rel: &[(Cfg::G, Cfg::G)],
        m: &Mono<Cfg::G>,
        out: &mut Vec<(Mono<Cfg::G>, Option<usize>)>,
    ) {
        if rel.is_empty() {
            return;
        }
        for i in 0..m.len() {
            for j in i..m.len() {
                if i == j && m[i].1 < 2 {
                    continue;
                }
                if self.mirror_inverse_pair(rel, m[i].0, m[j].0) {
                    let pair = if i == j {
                        vec![(m[i].0, 2)]
                    } else {
                        vec![(m[i].0, 1), (m[j].0, 1)]
                    };
                    out.push((m_sub(m, &pair), None));
                }
            }
        }
    }

    /// The checker's scan of the round-start state.
    fn mirror_round_table(&self) -> RoundTable<Cfg::G, Cfg::O> {
        let mut rules = Vec::new();
        let mut active = Vec::new();
        let mut children = HashSet::new();
        let ids: Vec<Cfg::G> = self.completion_node_ids().collect();
        for node in ids {
            let op = self.node_op(node);
            let lhs = self.mirror_node_monomial(node);
            for &(g, _) in &lhs {
                children.insert((op, g));
            }
            if self.node_flags(node) & (FLAG_SUBSUMED | FLAG_AC_COLLAPSED) != 0 {
                continue;
            }
            if let Some(rhs) = self.mirror_class_rhs(node, op)
                && self.mirror_deglex_gt(&lhs, &rhs)
            {
                rules.push(RuleRow {
                    op,
                    node,
                    lhs: lhs.clone(),
                    rhs,
                });
            }
            active.push((node, op, lhs));
        }
        rules.sort_unstable_by_key(|r| r.node);
        active.sort_unstable_by_key(|r| r.0);
        RoundTable {
            rules,
            active,
            children,
        }
    }

    /// Whether a round-start rule is a rule of the state as it stands: its node active,
    /// its right-hand side the class's, and oriented.
    fn mirror_rule_current(&self, r: &RuleRow<Cfg::G, Cfg::O>) -> bool {
        if self.node_flags(r.node) & (FLAG_SUBSUMED | FLAG_AC_COLLAPSED) != 0 {
            return false;
        }
        let Some(rhs) = self.mirror_class_rhs(r.node, r.op) else {
            return false;
        };
        rhs == self.mirror_through_find(r.op, &r.rhs)
            && self.mirror_deglex_gt(&self.mirror_through_find(r.op, &r.lhs), &rhs)
    }

    // ── The checks ──

    /// `goal` is a `Normalize` reduct of `start` under the round-start rules of `op`.
    /// `Ok(true)` when no derivation over the rules of the current state was found.
    ///
    /// With `lean_steps` a rewrite step is `Rw`: `clamp((M − A) + B)` with the full
    /// `Laws.clamp`. Without, it is the engine's step: the count clamp only, the unit
    /// drop and the inverse walk left to the `InvCancel` steps and to `materialize`.
    fn mirror_normalize(
        &self,
        table: &RoundTable<Cfg::G, Cfg::O>,
        op: Cfg::O,
        start: &Mono<Cfg::G>,
        goal: &Mono<Cfg::G>,
        lean_steps: bool,
    ) -> Result<bool, String> {
        let count_clamp = self.mirror_clamp(op);
        let rel = self.mirror_inverse(op);
        // `Laws.clamp` is the identity: a rule may be applied `q` times in one step.
        let identity_clamp = self.mirror_clamp(op) == CountClamp::None
            && self.unit_node(op).is_none()
            && rel.is_empty();
        let rows: Vec<usize> = (0..table.rules.len())
            .filter(|&i| table.rules[i].op == op)
            .collect();
        let search = |allowed: &[usize]| {
            m_reach(
                start,
                |m| m == goal,
                |m, out| {
                    for &i in allowed {
                        let r = &table.rules[i];
                        if !m_le(&r.lhs, m) {
                            continue;
                        }
                        // The rule applied as often as `m` holds its left side: each
                        // single step only adds the right side, so the rule applies at
                        // every intermediate monomial. Without a count clamp only (a
                        // clamp acts between the steps).
                        if identity_clamp {
                            let q = r
                                .lhs
                                .iter()
                                .map(|&(g, k)| m_count(m, g) / k)
                                .min()
                                .unwrap_or(1);
                            if q > 1
                                && let Some(qa) = m_scale(&r.lhs, q)
                                && let Some(qb) = m_scale(&r.rhs, q)
                                && let Some(n) = m_add(&m_sub(m, &qa), &qb)
                            {
                                out.push((n, Some(i)));
                            }
                        }
                        if let Some(mut n) = m_add(&m_sub(m, &r.lhs), &r.rhs) {
                            if lean_steps {
                                n = self.mirror_lean_clamp(op, &n);
                            } else {
                                count_clamp.apply(&mut n);
                            }
                            out.push((n, Some(i)));
                        }
                    }
                    self.mirror_inverse_steps(&rel, m, out);
                },
            )
        };
        let show = |why: &str| {
            format!(
                "{goal:?} is no Normalize reduct of {start:?} under the round-start rules ({why})"
            )
        };
        let used = match search(&rows) {
            Reach::Found(used) => used,
            Reach::NotFound => return Err(show("no derivation exists")),
            Reach::Budget => {
                return Err(show(&format!(
                    "the search visited {SEARCH_CAP} monomials without reaching it"
                )));
            }
        };
        if used
            .iter()
            .all(|&i| self.mirror_rule_current(&table.rules[i]))
        {
            return Ok(false);
        }
        let current: Vec<usize> = rows
            .iter()
            .copied()
            .filter(|&i| self.mirror_rule_current(&table.rules[i]))
            .collect();
        Ok(!matches!(search(&current), Reach::Found(_)))
    }

    /// `goal` is a `Normalize` reduct of the Lean side `lean`, or failing that of the side
    /// `built` the engine built, by `Rw` steps or failing that by the engine's steps. The
    /// first derivation found decides the notes.
    fn mirror_normalize_any(
        &self,
        table: &RoundTable<Cfg::G, Cfg::O>,
        op: Cfg::O,
        lean: &Mono<Cfg::G>,
        built: Option<&Mono<Cfg::G>>,
        goal: &Mono<Cfg::G>,
        notes: &mut Vec<Note>,
    ) -> Result<(), String> {
        // `(start, Rw steps, the engine's side, the clamp of the Lean side)`.
        let mut tries = vec![
            (lean.clone(), true, false, false),
            (lean.clone(), false, false, false),
        ];
        if let Some(built) = built.filter(|b| *b != lean) {
            tries.push((built.clone(), true, true, false));
            tries.push((built.clone(), false, true, false));
        }
        let clamped = self.mirror_lean_clamp(op, lean);
        if clamped != *lean && Some(&clamped) != built {
            tries.push((clamped.clone(), true, false, true));
            tries.push((clamped, false, false, true));
        }
        let mut errors = Vec::new();
        for (start, lean_steps, unclamped, clamped_side) in tries {
            match self.mirror_normalize(table, op, &start, goal, lean_steps) {
                Ok(stale) => {
                    add_note(notes, Note::StaleRule, stale);
                    add_note(notes, Note::EngineSteps, !lean_steps);
                    add_note(notes, Note::FromUnclampedPair, unclamped);
                    add_note(notes, Note::ClampedSide, clamped_side);
                    return Ok(());
                }
                Err(e) => errors.push(format!(
                    "{} steps: {e}",
                    if lean_steps { "Rw" } else { "engine" }
                )),
            }
        }
        Err(errors.join("; "))
    }

    /// `id` is the class of the node holding `reduct`: `Materialize st reduct _ id`,
    /// with the reduct read through the union-find and up to law instances.
    /// `Ok(true)` when the node does not hold the reduct as spelled.
    fn mirror_materialized(
        &self,
        op: Cfg::O,
        reduct: &Mono<Cfg::G>,
        id: Cfg::G,
    ) -> Result<bool, String> {
        let unit = self.unit_node(op).map(|u| self.classes.find_const(u));
        let cls = self.classes.find_const(id);
        // What the class of `id` holds: the monomial of `id` when it is a node of `op`,
        // the class itself (the atomic node `({c}, c)`), and nothing for the unit class.
        let mut holds: Vec<Mono<Cfg::G>> = Vec::new();
        if self.mirror_is_node_of(id, op) {
            holds.push(self.mirror_node_monomial(id));
        }
        holds.push(vec![(cls, 1)]);
        if unit == Some(cls) {
            holds.push(Vec::new());
        }
        let read = self.mirror_through_find(op, reduct);
        if holds.contains(&read) {
            return Ok(read != *reduct);
        }
        let clamp = self.mirror_clamp(op);
        let rel = self.mirror_inverse(op);
        let reach = m_reach(
            &read,
            |m| holds.contains(m),
            |m, out| {
                if let Some(u) = unit
                    && m_count(m, u) != 0
                {
                    out.push((m.iter().copied().filter(|p| p.0 != u).collect(), None));
                }
                let mut c = m.clone();
                clamp.apply(&mut c);
                if c != *m {
                    out.push((c, None));
                }
                self.mirror_inverse_steps(&rel, m, out);
            },
        );
        match reach {
            Reach::Found(_) => Ok(true),
            _ => Err(format!(
                "{id:?} is not the class of a node holding {reduct:?}: read through the \
                 union-find the reduct is {read:?}, the class holds {holds:?}, and no law \
                 instance takes one to the other"
            )),
        }
    }

    fn mirror_rule<'t>(
        &self,
        table: &'t RoundTable<Cfg::G, Cfg::O>,
        op: Cfg::O,
        node: Cfg::G,
    ) -> Result<&'t RuleRow<Cfg::G, Cfg::O>, String> {
        let i = table
            .rules
            .binary_search_by(|r| r.node.cmp(&node))
            .map_err(|_| {
                format!("node {node:?} is no active oriented rule at the start of the round")
            })?;
        let r = &table.rules[i];
        if r.op != op {
            return Err(format!("the rule of node {node:?} is of another operator"));
        }
        Ok(r)
    }

    fn mirror_check(
        &self,
        why: &MergeWhy<Cfg::G, Cfg::O>,
        a: Cfg::G,
        b: Cfg::G,
        table: Option<&RoundTable<Cfg::G, Cfg::O>>,
    ) -> Result<(Kind, Vec<Note>), String> {
        let same = |x: Cfg::G, y: Cfg::G| self.classes.find_const(x) == self.classes.find_const(y);
        let mut notes: Vec<Note> = Vec::new();
        match why {
            MergeWhy::Pair {
                op,
                origin,
                pair,
                reducts,
            } => {
                let op = *op;
                let table = table.ok_or("a pair merge outside a completion round")?;
                let clamp = self.mirror_clamp(op);
                let rel = self.mirror_inverse(op);
                let clamped = |m: Option<Mono<Cfg::G>>| -> Result<Mono<Cfg::G>, String> {
                    let mut m = m.ok_or("a count of the pair exceeds 128 bits")?;
                    clamp.apply(&mut m);
                    Ok(m)
                };
                let one = |g: Cfg::G| vec![(g, 1u128)];
                // The pair as the Lean definition gives it, from the checker's rules.
                let (kind, model, sources): (Kind, (Mono<Cfg::G>, Mono<Cfg::G>), Vec<Cfg::G>) =
                    match *origin {
                        PairWhy::Superpose { r1, r2 } => {
                            let (x, y) = (
                                self.mirror_rule(table, op, r1)?,
                                self.mirror_rule(table, op, r2)?,
                            );
                            let lcm = m_max(&x.lhs, &y.lhs);
                            (
                                Kind::Superpose,
                                (
                                    clamped(m_add(&m_sub(&lcm, &x.lhs), &x.rhs))?,
                                    clamped(m_add(&m_sub(&lcm, &y.lhs), &y.rhs))?,
                                ),
                                vec![r1, r2],
                            )
                        }
                        PairWhy::Idem { rule, a: x } => {
                            let r = self.mirror_rule(table, op, rule)?;
                            if clamp != CountClamp::Idempotent {
                                return Err(
                                    "an idempotence pair of an operator that is not idempotent"
                                        .into(),
                                );
                            }
                            if m_count(&r.lhs, x) == 0 {
                                return Err(format!("{x:?} is not in the rule's left side"));
                            }
                            (
                                Kind::AxiomIdem,
                                (clamped(m_add(&r.rhs, &one(x)))?, r.rhs.clone()),
                                vec![rule],
                            )
                        }
                        PairWhy::Nil { rule, a: x } => {
                            let r = self.mirror_rule(table, op, rule)?;
                            let CountClamp::Nilpotent(k) = clamp else {
                                return Err(
                                    "a nilpotence pair of an operator that is not nilpotent".into(),
                                );
                            };
                            let m = m_count(&r.lhs, x);
                            if m == 0 || m > k {
                                return Err(format!(
                                    "{x:?} has count {m} in the rule's left side, order {k}"
                                ));
                            }
                            (
                                Kind::AxiomNil,
                                (
                                    clamped(m_add(&r.rhs, &m_rep(x, k - m)))?,
                                    m_sub(&r.lhs, &m_rep(x, m)),
                                ),
                                vec![rule],
                            )
                        }
                        PairWhy::InvLeft { rule, a: x, y } => {
                            let r = self.mirror_rule(table, op, rule)?;
                            if m_count(&r.lhs, x) == 0 {
                                return Err(format!("{x:?} is not in the rule's left side"));
                            }
                            let key = (self.classes.find_const(x), self.classes.find_const(y));
                            if rel.binary_search(&key).is_err() {
                                return Err(format!(
                                    "no inverse node of {x:?} is in the class of {y:?}"
                                ));
                            }
                            (
                                Kind::AxiomInvLeft,
                                (clamped(m_add(&r.rhs, &one(y)))?, m_sub(&r.lhs, &one(x))),
                                vec![rule],
                            )
                        }
                        PairWhy::InvRight { rule, x, y } => {
                            let r = self.mirror_rule(table, op, rule)?;
                            if m_count(&r.lhs, y) == 0 {
                                return Err(format!("{y:?} is not in the rule's left side"));
                            }
                            let key = (self.classes.find_const(x), self.classes.find_const(y));
                            if rel.binary_search(&key).is_err() {
                                return Err(format!(
                                    "no inverse node of {x:?} is in the class of {y:?}"
                                ));
                            }
                            (
                                Kind::AxiomInvRight,
                                (clamped(m_add(&r.rhs, &one(x)))?, m_sub(&r.lhs, &one(y))),
                                vec![rule],
                            )
                        }
                        PairWhy::C1 { .. } | PairWhy::C2 { .. } => {
                            if !self.mirror_cancellative(op) {
                                return Err(
                                    "a cancel pair of an operator that is not cancellative".into(),
                                );
                            }
                            let (direct, constant, (left, right), sources) = match *origin {
                                PairWhy::C1 { rule } => {
                                    let r = self.mirror_rule(table, op, rule)?;
                                    let common = m_min(&r.lhs, &r.rhs);
                                    (
                                        Kind::CancelC1,
                                        Kind::CancelC1Constant,
                                        (m_sub(&r.lhs, &common), m_sub(&r.rhs, &common)),
                                        vec![rule],
                                    )
                                }
                                PairWhy::C2 { r1, r2 } => {
                                    let (x, y) = (
                                        self.mirror_rule(table, op, r1)?,
                                        self.mirror_rule(table, op, r2)?,
                                    );
                                    let overflow = "a count of the pair exceeds 128 bits";
                                    let lefts = m_add(&x.lhs, &y.lhs).ok_or(overflow)?;
                                    let rights = m_add(&x.rhs, &y.rhs).ok_or(overflow)?;
                                    let common = m_min(&lefts, &rights);
                                    (
                                        Kind::CancelC2,
                                        Kind::CancelC2Constant,
                                        (m_sub(&lefts, &common), m_sub(&rights, &common)),
                                        vec![r1, r2],
                                    )
                                }
                                _ => unreachable!(),
                            };
                            if pair.0 == left && pair.1 == right {
                                (direct, (left, right), sources)
                            } else {
                                // `CancelPair.constant`: the right side emptied, and the
                                // pair is `(M + {g}, {g})` for a child class `g`.
                                let g = match pair.1.as_slice() {
                                    [(g, 1)] if right.is_empty() => *g,
                                    _ => {
                                        return Err(format!(
                                            "the pair is neither the cancel pair ({left:?}, {right:?}) nor its closure by a constant"
                                        ));
                                    }
                                };
                                if !table.children.contains(&(op, g)) {
                                    return Err(format!(
                                        "{g:?} is no child of a node of the operator"
                                    ));
                                }
                                let with_g = m_add(&left, &one(g))
                                    .ok_or("a count of the pair exceeds 128 bits")?;
                                (constant, (with_g, one(g)), sources)
                            }
                        }
                    };
                if *pair != model {
                    return Err(format!("the pair is {pair:?}, the model's is {model:?}"));
                }
                // The Lean pair: `Laws.clamp` on the sides the definition clamps (both
                // sides of `criticalPair`, the first side of an `AxiomPair`, no side of a
                // `CancelPair`).
                let (clamp1, clamp2) = match origin {
                    PairWhy::Superpose { .. } => (true, true),
                    PairWhy::C1 { .. } | PairWhy::C2 { .. } => (false, false),
                    _ => (true, false),
                };
                let lean = |m: &Mono<Cfg::G>, on: bool| {
                    if on {
                        self.mirror_lean_clamp(op, m)
                    } else {
                        m.clone()
                    }
                };
                let lean_pair = (lean(&model.0, clamp1), lean(&model.1, clamp2));
                add_note(&mut notes, Note::PairClamped, lean_pair != model);
                for s in sources {
                    let r = self.mirror_rule(table, op, s)?;
                    add_note(&mut notes, Note::StaleRule, !self.mirror_rule_current(r));
                }
                for (lean_side, built, reduct) in [
                    (&lean_pair.0, &model.0, &reducts.0),
                    (&lean_pair.1, &model.1, &reducts.1),
                ] {
                    self.mirror_normalize_any(
                        table,
                        op,
                        lean_side,
                        Some(built),
                        reduct,
                        &mut notes,
                    )?;
                }
                add_note(
                    &mut notes,
                    Note::Respelled,
                    self.mirror_materialized(op, &reducts.0, a)?,
                );
                add_note(
                    &mut notes,
                    Note::Respelled,
                    self.mirror_materialized(op, &reducts.1, b)?,
                );
                Ok((kind, notes))
            }
            MergeWhy::NormalForm { op, node, reduct } => {
                let table = table.ok_or("a normal-form merge outside a completion round")?;
                let i = table
                    .active
                    .binary_search_by(|r| r.0.cmp(node))
                    .map_err(|_| {
                        format!("node {node:?} is no active node at the start of the round")
                    })?;
                let (_, node_op, monomial) = &table.active[i];
                if node_op != op {
                    return Err(format!("node {node:?} is of another operator"));
                }
                self.mirror_normalize_any(table, *op, monomial, None, reduct, &mut notes)?;
                add_note(
                    &mut notes,
                    Note::Respelled,
                    self.mirror_materialized(*op, reduct, a)?,
                );
                if !same(b, *node) {
                    return Err(format!("{b:?} is not the class of node {node:?}"));
                }
                Ok((Kind::NormalForm, notes))
            }
            MergeWhy::InverseRepair { op, node, reduct } => {
                if !self.mirror_is_node_of(*node, *op) {
                    return Err(format!("{node:?} is no node of the operator"));
                }
                let rel = self.mirror_inverse(*op);
                // The repair runs after the round's merges and before the next
                // recanonization: the node's monomial and the reduct are read through
                // the union-find as it stands.
                let start = self.mirror_node_monomial(*node);
                let goal = self.mirror_through_find(*op, reduct);
                let reach = m_reach(
                    &start,
                    |m| *m == goal,
                    |m, out| self.mirror_inverse_steps(&rel, m, out),
                );
                if !matches!(reach, Reach::Found(_)) {
                    return Err(format!(
                        "{goal:?} is not reached from the node's monomial {start:?} by removing inverse pairs"
                    ));
                }
                add_note(
                    &mut notes,
                    Note::Respelled,
                    self.mirror_materialized(*op, reduct, a)?,
                );
                if !same(b, *node) {
                    return Err(format!("{b:?} is not the class of node {node:?}"));
                }
                Ok((Kind::InverseRepair, notes))
            }
            MergeWhy::InverseLaw { op, rule } => {
                let op = *op;
                let inv = self
                    .inverse_op(op)
                    .ok_or("an inverse-law merge of an operator without an inverse")?;
                // `(node, class of its child)` for every stored inverse node.
                let nodes = self.inverse_nodes(inv);
                let child_of = |node: Cfg::G| -> Result<Cfg::G, String> {
                    nodes
                        .iter()
                        .find(|p| p.0 == node)
                        .map(|p| p.1)
                        .ok_or_else(|| format!("{node:?} is no inverse node"))
                };
                let unit = || -> Result<Cfg::G, String> {
                    self.unit_node(op)
                        .ok_or_else(|| "the operator has no unit".to_string())
                };
                let joins =
                    |x: Cfg::G, y: Cfg::G| (same(a, x) && same(b, y)) || (same(a, y) && same(b, x));
                let order = || -> Result<u128, String> {
                    match self.mirror_clamp(op) {
                        CountClamp::Nilpotent(k) => Ok(k),
                        _ => Err("the operator is not nilpotent".to_string()),
                    }
                };
                match *rule {
                    InvRule::R1Inj => {
                        let found = nodes.iter().any(|&(n1, x1)| {
                            nodes.iter().any(|&(n2, x2)| same(n1, n2) && joins(x1, x2))
                        });
                        if !found {
                            return Err("no two inverse nodes of one class have the merged classes as children".into());
                        }
                        Ok((Kind::InvR1Inj, notes))
                    }
                    InvRule::R1Inv { node } => {
                        let x = child_of(node)?;
                        let found = nodes
                            .iter()
                            .any(|&(inner, z)| same(inner, x) && joins(node, z));
                        if !found {
                            return Err(format!(
                                "the child of {node:?} holds no inverse node whose child is the other merged class"
                            ));
                        }
                        Ok((Kind::InvR1Inv, notes))
                    }
                    InvRule::R2InvUnit { node } => {
                        let (x, u) = (child_of(node)?, unit()?);
                        if !same(node, u) || !joins(x, u) {
                            return Err(format!(
                                "{node:?} is not in the unit class, or the merge is not of its child and the unit"
                            ));
                        }
                        Ok((Kind::InvR2InvUnit, notes))
                    }
                    InvRule::R2UnitInv { node } => {
                        let (x, u) = (child_of(node)?, unit()?);
                        if !same(x, u) || !joins(node, u) {
                            return Err(format!(
                                "the child of {node:?} is not in the unit class, or the merge is not of the node and the unit"
                            ));
                        }
                        Ok((Kind::InvR2UnitInv, notes))
                    }
                    InvRule::R4 { node } => {
                        let (x, k) = (child_of(node)?, order()?);
                        unit()?;
                        add_note(
                            &mut notes,
                            Note::Respelled,
                            self.mirror_materialized(op, &m_rep(x, k - 1), a)?,
                        );
                        if !same(b, node) {
                            return Err(format!("{b:?} is not the class of {node:?}"));
                        }
                        Ok((Kind::InvR4, notes))
                    }
                    InvRule::R5 { node } => {
                        let (x, k) = (child_of(node)?, order()?);
                        unit()?;
                        let y = self.classes.find_const(node);
                        add_note(
                            &mut notes,
                            Note::Respelled,
                            self.mirror_materialized(op, &m_rep(y, k - 1), a)?,
                        );
                        if !same(b, x) {
                            return Err(format!("{b:?} is not the class of the child of {node:?}"));
                        }
                        Ok((Kind::InvR5, notes))
                    }
                }
            }
            MergeWhy::Lattice { .. } => unreachable!("checked by mirror_check_lattice"),
        }
    }

    /// The rows `lattice_round` reads for `op` (`engineRows`): `e_c − vec M` for every
    /// node `(M, c)` of `op`, retired ones included, with columns indexed by class, and
    /// the law rows `e_u`, `k·e_a`, `e_x + e_{inv x}`.
    fn mirror_lattice_basis(&self, op: Cfg::O) -> Basis<Cfg::G> {
        let mut cols: HashMap<Cfg::G, usize> = HashMap::new();
        let col = |g: Cfg::G, cols: &mut HashMap<Cfg::G, usize>| {
            let n = cols.len();
            *cols.entry(g).or_insert(n)
        };
        let mut sparse: Vec<Vec<(usize, BigInt)>> = Vec::new();
        let ids: Vec<Cfg::G> = self.completion_node_ids().collect();
        for node in ids {
            if self.node_op(node) != op {
                continue;
            }
            let mut row = vec![(
                col(self.classes.find_const(node), &mut cols),
                BigInt::from(1),
            )];
            for (g, k) in self.mirror_node_monomial(node) {
                row.push((col(g, &mut cols), -BigInt::from(k)));
            }
            sparse.push(row);
        }
        if let Some(u) = self.unit_node(op) {
            sparse.push(vec![(
                col(self.classes.find_const(u), &mut cols),
                BigInt::from(1),
            )]);
        }
        for (x, y) in self.mirror_inverse(op) {
            sparse.push(vec![
                (col(x, &mut cols), BigInt::from(1)),
                (col(y, &mut cols), BigInt::from(1)),
            ]);
        }
        let n = cols.len();
        if let CountClamp::Nilpotent(k) = self.mirror_clamp(op) {
            for j in 0..n {
                sparse.push(vec![(j, BigInt::from(k))]);
            }
        }
        let mut pivots: Vec<Option<Vec<BigInt>>> = vec![None; n];
        for row in sparse {
            let mut dense = vec![BigInt::zero(); n];
            for (j, v) in row {
                dense[j] += v;
            }
            basis_insert(&mut pivots, dense);
        }
        Basis { cols, pivots }
    }

    /// `lattice_merge_sound`: `e_a − e_b` is in the lattice of the rows of `op`, and
    /// `=_E` cancels (the operator is cancellative, or a group of finite exponent).
    ///
    /// The rows are read in the state the merge is applied to, columns indexed by the
    /// classes as they stand: an earlier merge of the same pass joins two columns, which
    /// is the partition row `e_c − e_d` of `engineRows`.
    fn mirror_check_lattice(
        &self,
        op: Cfg::O,
        a: Cfg::G,
        b: Cfg::G,
    ) -> Result<(Kind, Vec<Note>), String> {
        let group = matches!(self.mirror_clamp(op), CountClamp::Nilpotent(_))
            && self.unit_node(op).is_some();
        if !self.mirror_cancellative(op) && !group {
            return Err("a lattice merge of an operator whose theory does not cancel".into());
        }
        let basis = self.mirror_lattice_basis(op);
        let (a, b) = (self.classes.find_const(a), self.classes.find_const(b));
        let (Some(&i), Some(&j)) = (basis.cols.get(&a), basis.cols.get(&b)) else {
            return Err("a merged class is no column of the operator's rows".into());
        };
        let mut v = vec![BigInt::zero(); basis.pivots.len()];
        v[i] += 1;
        v[j] -= 1;
        if !basis_member(&basis.pivots, v) {
            return Err(
                "the two classes do not differ by a member of the lattice of the operator's rows"
                    .into(),
            );
        }
        Ok((Kind::Lattice, Vec::new()))
    }
}
