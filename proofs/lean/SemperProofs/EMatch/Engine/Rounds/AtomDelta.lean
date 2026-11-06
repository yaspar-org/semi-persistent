import SemperProofs.EMatch.Engine.Rounds.Round
import SemperProofs.EMatch.Engine.Lower

/-!
# Per-atom stability across a round

An atom's satisfaction (`AtomSat`) reads the graph through three things
only: the existence of its node, the node's stored content, and the node's
representative. The shallow pattern of an atom has variable arguments, so
`MatchN G a.shallow n σ` does not depend on `G` at all
(`matchN_shallow_iff`): a plain atom reads the tuple of child classes, a
commutative atom the sorted pair, an associative atom the sequence
(prefix/suffix rests included), an AC atom the multiset (counts and
multiset rest), an ACI atom the set (set rest). The lookups of the
lowering (`byChildPos`, `byContains`, `byRepr`, `byOp`) are abstracted by
`plan_matches`, which is why the per-atom argument needs no lookup-level
reasoning: a `byChildPos`/`byContains` key is a child class stored in the
node, and a change of it is a change of the stored node (recanonicalized,
hence touched), or of the class variable it is compared with, which is
some other atom's representative (absorbed, hence in the merge delta).

`atomSat_before_of_not_new` is the per-atom lemma: an atom satisfied after
the round at a node that is not new was satisfied before the round by the
same binding. `qsat_eq_iff` says an equality constraint between two class
variables is graph-independent.
-/

namespace Semper.EMatch

/-- The shallow pattern's match relation does not read the graph. -/
theorem matchN_shallow_iff (G G' : Graph) (a : RAtom) (n : Node) (σ : Binding) :
    MatchN G a.shallow n σ ↔ MatchN G' a.shallow n σ := by
  rcases a with ⟨nv, op, shape⟩
  cases shape with
  | plain cs => simp only [RAtom.shallow]; rw [matchN_plain_vars, matchN_plain_vars]
  | comm x y => simp only [RAtom.shallow]; rw [matchN_comm_vars, matchN_comm_vars]
  | assoc pre fx suf => simp only [RAtom.shallow]; rw [matchN_assoc_vars, matchN_assoc_vars]
  | ac es rest => simp only [RAtom.shallow]; rw [matchN_ac_vars, matchN_ac_vars]
  | aci es rest => simp only [RAtom.shallow]; rw [matchN_aci_vars, matchN_aci_vars]

/-- `AtomSat` at a node present in both graphs with the same content and
the same representative transfers between the graphs. -/
theorem atomSat_transfer {G G' : Graph} {σ : Binding} {a : RAtom}
    (h : AtomSat G σ a)
    (hstable : ∀ id n, σ.node a.node = some id → (id, n) ∈ G.nodes →
      (id, n) ∈ G'.nodes ∧ G'.find id = G.find id) :
    AtomSat G' σ a := by
  obtain ⟨id, n, hid, hmem, hcls, hop, hm⟩ := h
  obtain ⟨hmem', hfind⟩ := hstable id n hid hmem
  exact ⟨id, n, hid, hmem', by rw [hfind]; exact hcls, hop, (matchN_shallow_iff G G' a n σ).1 hm⟩

/-- The per-atom lemma (tracking on): an atom satisfied after the round at
a node that is not new was satisfied before the round. -/
theorem atomSat_before_of_not_new {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {σ : Binding} {a : RAtom} (h : AtomSat R.after σ a)
    (hold : ∀ id, σ.node a.node = some id → R.isNew id = false) :
    AtomSat R.before σ a := by
  refine atomSat_transfer h ?_
  intro id n hid hmem
  exact Round.stable_of_not_new hwf htr hmem (hold id hid)

/-- An equality constraint between two class variables is graph-independent. -/
theorem qsat_eq_iff (G G' : Graph) (σ : Binding) (x y : Var) :
    QSat G σ (.eq x y) ↔ QSat G' σ (.eq x y) := Iff.rfl

end Semper.EMatch
