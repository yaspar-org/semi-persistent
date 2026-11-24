import SemperProofs.EMatch.Engine.Rounds.Round

/-!
# Splicing a nested same-operator child at build: the key `add` stores

`add` of an associative operator splices a child whose class is a pure
same-operator sequence (`flatten_seq_children`, `egraph.rs`): the child is
replaced by the stored children of the class's least sequence node. Those
stored children are canonical for the union-find of the last `rebuild`,
not for the live one: a `union` applied earlier in the same round
(`egraph.rs`, merges recorded in the union-find only) leaves them stale
until the next rebuild. The AC and ACI twins (`flatten_mset_children`,
`flatten_ac_children`) splice a `min_monomial` node's stored children the
same way.

The engine pushed the spliced elements as stored. The node was then keyed
by a non-canonical child list, and `add` registered no use for a stale
child (`repr_id` of an absorbed id is `None`), so no rebuild ever
recanonicalized it: the rebuilt graph reads the node through `find` with
the canonical content, while a later `add` of the canonical spelling
probes the hash-cons with the canonical key and misses. Two nodes of equal
content then sit in two classes, against `Round.WF.dedup`
(`seq_hashcons_miss_min.egg`).

This file models the build key and the store:

* `normalizeSeq`: the fixed build, every spliced element `find`'d;
  `normalizeSeqRaw`: the unfixed one.
* `recanon`: the rebuild's recanonicalization of a stored sequence.
* `normalizeSeq_canonical`, `recanon_normalizeSeq`: the fixed key is
  canonical, so `add` and recanonicalization compute the same normal form
  (`recanon_normalizeSeqRaw`: the raw key differs from it only by `find`).
* `addSeq` and `readGraph`: a hash-cons store keyed exactly, and the graph
  the dump reads from it. `addSeq_preserves` keeps the store's two
  invariants (canonical keys, one id per key); `dedup_of_inv` derives
  `Round.WF.dedup`'s statement from them: equal normal forms are one node,
  hence one class.
* `raw_breaks_dedup`: the counter-model of the unfixed build, the shape of
  the reproducer (a class holding `Cat(a, a)` with `a` merged into `c`,
  `Cat(k, k)` built raw, then `Cat(c, c, c, c)` built): the read graph has
  two nodes of equal content in two classes.

One splice level is modelled (the engine iterates to a fixpoint; each
level emits through the same `find`). Positions on and off the spine of
`:assoc-left`/`:assoc-right` differ only in which children `pure` answers
for, which the model leaves to `pure`.
-/

namespace Semper.EMatch.SeqSplice

open Semper.EMatch

/-- The live union-find: an idempotent representative map. -/
structure UF where
  find : C → C
  idem : ∀ x, find (find x) = find x

/-- For a class, the stored children of its least pure same-operator
sequence node, if the class is one (`pure_seq_node`). The list is the
stored one, which may predate the live union-find. -/
abbrev Pure := C → Option (List C)

/-- One child of the fixed build: spliced elements are `find`'d. -/
def spliceOne (u : UF) (pure : Pure) (x : C) : List C :=
  match pure (u.find x) with
  | some cs => cs.map u.find
  | none => [u.find x]

/-- One child of the unfixed build: spliced elements pushed as stored. -/
def spliceOneRaw (u : UF) (pure : Pure) (x : C) : List C :=
  match pure (u.find x) with
  | some cs => cs
  | none => [u.find x]

/-- The key the fixed `add` stores for a sequence node. -/
def normalizeSeq (u : UF) (pure : Pure) (xs : List C) : List C :=
  xs.flatMap (spliceOne u pure)

/-- The key the unfixed `add` stored. -/
def normalizeSeqRaw (u : UF) (pure : Pure) (xs : List C) : List C :=
  xs.flatMap (spliceOneRaw u pure)

/-- Recanonicalization of a stored sequence at rebuild (`OrderedCanon`,
plain mode): every child `find`'d, order kept. -/
def recanon (u : UF) (cs : List C) : List C := cs.map u.find

/-- Every element is a representative. -/
def Canonical (u : UF) (cs : List C) : Prop := ∀ c ∈ cs, u.find c = c

theorem map_eq_self_iff {f : C → C} : ∀ {l : List C}, l.map f = l ↔ ∀ x ∈ l, f x = x
  | [] => by simp
  | a :: l => by simp [map_eq_self_iff]

theorem recanon_eq_self_iff (u : UF) (cs : List C) :
    recanon u cs = cs ↔ Canonical u cs :=
  map_eq_self_iff

theorem spliceOne_canonical (u : UF) (pure : Pure) (x : C) :
    Canonical u (spliceOne u pure x) := by
  unfold spliceOne
  split
  · intro c hc
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
    exact u.idem d
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact u.idem x

/-- The fixed key is canonical. -/
theorem normalizeSeq_canonical (u : UF) (pure : Pure) (xs : List C) :
    Canonical u (normalizeSeq u pure xs) := by
  intro c hc
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 hc
  exact spliceOne_canonical u pure x c hx

/-- `add` and recanonicalization compute the same normal form: the key the
fixed `add` stores is a fixpoint of the rebuild. -/
theorem recanon_normalizeSeq (u : UF) (pure : Pure) (xs : List C) :
    recanon u (normalizeSeq u pure xs) = normalizeSeq u pure xs :=
  (recanon_eq_self_iff u _).2 (normalizeSeq_canonical u pure xs)

/-- The raw key differs from the normal form only by `find`: a
recanonicalization would repair it, if one ran. -/
theorem recanon_normalizeSeqRaw (u : UF) (pure : Pure) (xs : List C) :
    recanon u (normalizeSeqRaw u pure xs) = normalizeSeq u pure xs := by
  unfold recanon normalizeSeqRaw normalizeSeq
  rw [List.map_flatMap]
  congr 1
  funext x
  unfold spliceOneRaw spliceOne
  split <;> simp [u.idem]

/-- On a store whose spliced sources are already canonical (after a
rebuild, before any union), the two builds agree. -/
theorem normalizeSeqRaw_eq_of_canonical (u : UF) (pure : Pure) (xs : List C)
    (h : ∀ c cs, pure c = some cs → Canonical u cs) :
    normalizeSeqRaw u pure xs = normalizeSeq u pure xs := by
  unfold normalizeSeqRaw normalizeSeq
  congr 1
  funext x
  unfold spliceOneRaw spliceOne
  split
  · next cs hcs => exact ((recanon_eq_self_iff u cs).2 (h _ _ hcs)).symm
  · rfl

/-! ## The store -/

/-- A hash-cons store of one sequence operator: node ids with their keys,
probed by exact key (`VariableArityCache::probe`). -/
abbrev Store := List (NodeId × List C)

/-- The store's invariants after a rebuild: every key is canonical, and a
key names one id (the hash-cons). -/
structure Store.Inv (u : UF) (s : Store) : Prop where
  canon : ∀ p ∈ s, Canonical u p.2
  inj : ∀ p ∈ s, ∀ q ∈ s, p.2 = q.2 → p.1 = q.1

/-- `add` of a key: the probe's hit, or a fresh id appended. -/
def addKey (s : Store) (fresh : NodeId) (k : List C) : NodeId × Store :=
  match s.find? (fun p => p.2 == k) with
  | some p => (p.1, s)
  | none => (fresh, (fresh, k) :: s)

/-- The fixed `add` of a sequence term. -/
def addSeq (u : UF) (pure : Pure) (s : Store) (fresh : NodeId) (xs : List C) :
    NodeId × Store :=
  addKey s fresh (normalizeSeq u pure xs)

/-- The unfixed `add`. -/
def addSeqRaw (u : UF) (pure : Pure) (s : Store) (fresh : NodeId) (xs : List C) :
    NodeId × Store :=
  addKey s fresh (normalizeSeqRaw u pure xs)

theorem addKey_preserves (u : UF) (s : Store) (fresh : NodeId) (k : List C)
    (hs : Store.Inv u s) (hk : Canonical u k) :
    Store.Inv u (addKey s fresh k).2 := by
  unfold addKey
  split
  · exact hs
  · next hnone =>
    have hnk : ∀ p ∈ s, p.2 ≠ k := by
      intro p hp hpk
      have := List.find?_eq_none.1 hnone p hp
      simp [hpk] at this
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hk
      · exact hs.canon p hp
    · intro p hp q hq hpq
      rcases List.mem_cons.1 hp with rfl | hp <;> rcases List.mem_cons.1 hq with rfl | hq
      · rfl
      · exact absurd hpq.symm (hnk q hq)
      · exact absurd hpq (hnk p hp)
      · exact hs.inj p hp q hq hpq

/-- The fixed `add` keeps the store's invariants. -/
theorem addSeq_preserves (u : UF) (pure : Pure) (s : Store) (fresh : NodeId) (xs : List C)
    (hs : Store.Inv u s) :
    Store.Inv u (addSeq u pure s fresh xs).2 :=
  addKey_preserves u s fresh _ hs (normalizeSeq_canonical u pure xs)

/-- The probe hits an existing node of the same normal form. -/
theorem addSeq_hit (u : UF) (pure : Pure) (s : Store) (fresh : NodeId) (xs : List C)
    (hs : Store.Inv u s) (p : NodeId × List C) (hp : p ∈ s)
    (hk : p.2 = normalizeSeq u pure xs) :
    (addSeq u pure s fresh xs).1 = p.1 := by
  unfold addSeq addKey
  split
  · next q hq =>
    have hqmem := List.mem_of_find?_eq_some hq
    have hqk : q.2 = normalizeSeq u pure xs := by
      simpa using List.find?_some hq
    exact hs.inj q hqmem p hp (hqk.trans hk.symm)
  · next hnone =>
    have := List.find?_eq_none.1 hnone p hp
    simp [hk] at this

/-- The graph the dump reads from a store: each node's children read
through `find` (`dump-egraph` prints `find` of every stored child), the
class of a node given by `cls`. -/
def readGraph (u : UF) (op : Sym) (cls : NodeId → C) (s : Store) : Graph where
  nodes := s.map (fun p => (p.1, ⟨op, .seq (recanon u p.2)⟩))
  find := cls

/-- `Round.WF.dedup`'s statement for a graph. -/
def Dedup (G : Graph) : Prop :=
  ∀ id₁ id₂ n, (id₁, n) ∈ G.nodes → (id₂, n) ∈ G.nodes → G.find id₁ = G.find id₂

/-- Equal normal forms imply one class: on a store with canonical keys and
one id per key, two nodes the dump reads with equal content are one node,
whatever the class map. -/
theorem dedup_of_inv (u : UF) (op : Sym) (cls : NodeId → C) (s : Store)
    (hs : Store.Inv u s) : Dedup (readGraph u op cls s) := by
  intro id₁ id₂ n h₁ h₂
  simp only [readGraph, List.mem_map] at h₁ h₂
  obtain ⟨p, hp, hpe⟩ := h₁
  obtain ⟨q, hq, hqe⟩ := h₂
  simp only [Prod.mk.injEq] at hpe hqe
  obtain ⟨rfl, hpn⟩ := hpe
  obtain ⟨rfl, hqn⟩ := hqe
  have hrec : recanon u p.2 = recanon u q.2 := by
    have := hpn.trans hqn.symm
    simp only [Node.mk.injEq, Children.seq.injEq, true_and] at this
    exact this
  rw [(recanon_eq_self_iff u _).2 (hs.canon p hp),
    (recanon_eq_self_iff u _).2 (hs.canon q hq)] at hrec
  show cls p.1 = cls q.1
  rw [hs.inj p hp q hq hrec]

/-! ## Counter-model of the unfixed build

The reproducer's shape. Class `5` holds `Cat(0, 0)` as stored before the
union of `0` into `7` (the live `find` maps `0` to `7`), so `5` is a pure
`Cat` class whose stored children are stale. The rule builds `Cat(k, k)`
for `k = 5` (node `1`, put in class `7` by the rule's union), then the
check builds `Cat(c, c, c, c)` for `c = 7` (node `2`, a fresh class). -/

/-- `find`: `0` merged into `7`. -/
def cmUF : UF where
  find x := if x = 0 then 7 else x
  idem x := by by_cases h : x = 0 <;> simp [h]

/-- Class `5` is the pure `Cat` class with stale stored children `[0, 0]`. -/
def cmPure : Pure := fun c => if c = 5 then some [0, 0] else none

/-- Node `1`, built raw from `Cat(k, k)`, then node `2` from
`Cat(c, c, c, c)`: the second probe misses. -/
def cmStore : Store :=
  (addSeqRaw cmUF cmPure (addSeqRaw cmUF cmPure [] 1 [5, 5]).2 2 [7, 7, 7, 7]).2

/-- Node `1` in class `7` (the rule's union), node `2` in its own class. -/
def cmCls : NodeId → C := fun i => if i = 1 then 7 else i

theorem cmStore_eq : cmStore = [(2, [7, 7, 7, 7]), (1, [0, 0, 0, 0])] := by
  decide

/-- The raw key holds a stale child. -/
theorem raw_key_not_canonical :
    ¬ Canonical cmUF (normalizeSeqRaw cmUF cmPure [5, 5]) := by
  intro h
  have := h 0 (by decide)
  simp [cmUF] at this

/-- The fixed build of `Cat(k, k)` is the key `Cat(c, c, c, c)` probes. -/
theorem fixed_key : normalizeSeq cmUF cmPure [5, 5] = [7, 7, 7, 7] := by
  decide

/-- The unfixed build breaks `Round.WF.dedup`: the read graph holds two
nodes of content `Cat(7, 7, 7, 7)` in classes `7` and `2`. -/
theorem raw_breaks_dedup : ¬ Dedup (readGraph cmUF 0 cmCls cmStore) := by
  intro h
  have h₁ : (1, (⟨0, .seq [7, 7, 7, 7]⟩ : Node)) ∈ (readGraph cmUF 0 cmCls cmStore).nodes := by
    rw [cmStore_eq]; decide
  have h₂ : (2, (⟨0, .seq [7, 7, 7, 7]⟩ : Node)) ∈ (readGraph cmUF 0 cmCls cmStore).nodes := by
    rw [cmStore_eq]; decide
  have := h 1 2 _ h₁ h₂
  simp [readGraph, cmCls] at this

/-- The fixed build on the same history keeps one node: the check's probe
hits node `1`. -/
theorem fixed_keeps_one :
    (addSeq cmUF cmPure (addSeq cmUF cmPure [] 1 [5, 5]).2 2 [7, 7, 7, 7]).1 = 1 := by
  decide

end Semper.EMatch.SeqSplice
