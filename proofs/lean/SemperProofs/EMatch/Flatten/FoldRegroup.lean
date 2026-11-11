import SemperProofs.EMatch.Flatten.FoldEnum
import SemperProofs.EMatch.Flatten.RegroupLaws

/-!
# `:flatten` on folds: regrouped views are the node's fold

`regroup_step_sound_left` and `regroup_step_sound_right` (`RegroupSound.lean`)
prove one regrouping of a fold sound: replacing a prefix of a left fold, or a
suffix of a right fold, by the class of an `f`-member over it keeps the fold's
term. This file carries that to every view the enumeration with regrouping
records for a fold, and to the declarative chains of `RegroupChain.lean`:

* `regroupsTo_left_sound`, `regroupsTo_right_sound`: the declarative step
  `RegroupsTo` on the spine keeps the fold;
* `regroupStep_left_sound`, `regroupChain_left_sound` (and `_right_`): a
  record step and a chain of steps keep the fold;
* `reach_lfold_left`, `reach_rfold_right`: every record reachable from the
  walk's records of a fold node denotes the node's fold, by `otLeft_sound`
  on the walk's records (through `rawNodeD_left_sound`, `FoldEnum.lean`) and
  the step soundness;
* `regroup_views_sound_left`, `regroupSkip_views_sound_left` (and `_right`):
  every view of `enumerateR` and of the engine's `enumerateRSkip` for a
  laws-free fold denotes the node's fold, in every magma with a consistent
  denotation; `regroup_chain_left_sound`, `regroup_chain_right_sound`
  are the same for the chains `regroup_match_iff` characterizes the matches by;
* `reach_den_assoc_dir`, `regroup_views_sound_assoc_laws_dir`,
  `regroupSkip_views_sound_assoc_laws_dir`: the monoid soundness of
  `RegroupLaws.lean`, proved there for `Dir.both`, holds for every direction
  (a fold's views are among the `:assoc` views, `rawNodeD_sub_both`), under
  the laws;
* `baseRecsR_left_views_iff`, `baseRecsR_right_views_iff`: the walk records
  that start the chains of `regroup_match_iff_laws` for a fold are the
  normal forms of the spine views, so that theorem characterizes the fold
  matches with `OTLeft`/`OTRight` at the base and prefix/suffix steps
  (`regroupsTo_left_iff`, `regroupsTo_right_iff`).

The fold soundness is laws-free: the engine declares no law on a fold (laws
need `:comm`, `sortcheck.rs`), and the model's only `:assoc` law, an
identity, has no reading in an arbitrary magma. Under an identity the monoid
theorems (`_dir`) apply, in which a fold reads as an associative product.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## The declarative steps keep the fold -/

/-- **Regrouping a prefix of a left fold keeps the left fold**, declaratively. -/
theorem regroupsTo_left_sound {M : Type*} [Mul M] {ctx : Ctx}
    {den : C → M} (hc : ConsistentL ctx den)
    {id : NodeId} {m : Node} {g : C} {cs : List C} (hm : ctx.IsMember id m g)
    (hcs : m.children = .seq cs) {w w' : List (C × Nat)}
    (h : RegroupsTo .assoc .left w g (kids .assoc m.children) w') :
    lfold ((w'.map Prod.fst).map den) = lfold ((w.map Prod.fst).map den) := by
  rw [regroupsTo_left_iff] at h
  obtain ⟨-, -, hrun, rfl⟩ := h
  have hlen : (kids .assoc m.children).length = cs.length := by rw [hcs, kids_seq]; simp [withK]
  rw [hlen, hcs, kids_seq, withK_map_fst] at hrun
  rw [hlen]
  have hl : lfold (((w.take cs.length).map Prod.fst).map den) = some (den g) := by
    rw [hrun]; exact hc id m g cs hm hcs
  calc lfold ((((g, 1) :: w.drop cs.length).map Prod.fst).map den)
      = lfold (den g :: ((w.drop cs.length).map Prod.fst).map den) := by simp
    _ = lfold (((w.take cs.length).map Prod.fst).map den ++
          ((w.drop cs.length).map Prod.fst).map den) := lfold_splice hl _
    _ = lfold ((w.map Prod.fst).map den) := by
          rw [← List.map_append, ← List.map_append, List.take_append_drop]

/-- **Regrouping a suffix of a right fold keeps the right fold**, declaratively. -/
theorem regroupsTo_right_sound {M : Type*} [Mul M] {ctx : Ctx}
    {den : C → M} (hc : ConsistentR ctx den)
    {id : NodeId} {m : Node} {g : C} {cs : List C} (hm : ctx.IsMember id m g)
    (hcs : m.children = .seq cs) {w w' : List (C × Nat)}
    (h : RegroupsTo .assoc .right w g (kids .assoc m.children) w') :
    rfold ((w'.map Prod.fst).map den) = rfold ((w.map Prod.fst).map den) := by
  rw [regroupsTo_right_iff] at h
  obtain ⟨-, -, hrun, rfl⟩ := h
  have hlen : (kids .assoc m.children).length = cs.length := by rw [hcs, kids_seq]; simp [withK]
  rw [hlen, hcs, kids_seq, withK_map_fst] at hrun
  rw [hlen]
  have hr : rfold (((w.drop (w.length - cs.length)).map Prod.fst).map den) = some (den g) := by
    rw [hrun]; exact hc id m g cs hm hcs
  calc rfold (((w.take (w.length - cs.length) ++ [(g, 1)]).map Prod.fst).map den)
      = rfold (((w.take (w.length - cs.length)).map Prod.fst).map den ++ [den g]) := by simp
    _ = rfold (((w.take (w.length - cs.length)).map Prod.fst).map den ++
          ((w.drop (w.length - cs.length)).map Prod.fst).map den) := rfold_splice hr _
    _ = rfold ((w.map Prod.fst).map den) := by
          rw [← List.map_append, ← List.map_append, List.take_append_drop]

/-- A record step of a left fold keeps the left fold. -/
theorem regroupStep_left_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {r r' : RecR} (h : RegroupStep ctx .left r r') :
    lfold ((r'.1.map Prod.fst).map den) = lfold ((r.1.map Prod.fst).map den) := by
  cases h with
  | mk hm _ hto =>
      obtain ⟨cs, hcs⟩ := hs _ _ _ hm
      rw [hκ] at hto
      exact regroupsTo_left_sound hc hm hcs hto

theorem regroupStep_right_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentR ctx den) {r r' : RecR} (h : RegroupStep ctx .right r r') :
    rfold ((r'.1.map Prod.fst).map den) = rfold ((r.1.map Prod.fst).map den) := by
  cases h with
  | mk hm _ hto =>
      obtain ⟨cs, hcs⟩ := hs _ _ _ hm
      rw [hκ] at hto
      exact regroupsTo_right_sound hc hm hcs hto

/-- **A chain of regroupings of a left fold keeps the left fold.** -/
theorem regroupChain_left_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {r₀ r : RecR} (h : RegroupChain ctx .left r₀ r) :
    lfold ((r.1.map Prod.fst).map den) = lfold ((r₀.1.map Prod.fst).map den) := by
  induction h with
  | refl => rfl
  | tail _ hs' ih => rw [regroupStep_left_sound hκ hs hc hs', ih]

theorem regroupChain_right_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentR ctx den) {r₀ r : RecR} (h : RegroupChain ctx .right r₀ r) :
    rfold ((r.1.map Prod.fst).map den) = rfold ((r₀.1.map Prod.fst).map den) := by
  induction h with
  | refl => rfl
  | tail _ hs' ih => rw [regroupStep_right_sound hκ hs hc hs', ih]

/-! ## The walk's records of a fold -/

/-- The views of the walk's records are the views of the fold enumerator. -/
theorem baseRecsR_views_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node}
    {w : List (C × Nat)} :
    (∃ r ∈ baseRecsR ctx dir laws n, r.1 = w) ↔ w ∈ (enumerateLD ctx dir laws n).map Prod.fst := by
  unfold baseRecsR enumerateLD
  rw [map_fst_enumerateFromL, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact ⟨r', hr', rfl⟩
  · rintro ⟨r', hr', rfl⟩
    exact ⟨RecL.toR r', List.mem_map.2 ⟨r', hr', rfl⟩, rfl⟩

/-- **The walk records of a left fold are the normal forms of the spine views**:
the records the chains of `regroup_match_iff` and `regroup_match_iff_laws`
start from, at the level of views. -/
theorem baseRecsR_left_views_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {laws : Laws} {n : Node} {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} :
    (∃ r ∈ baseRecsR ctx .left laws n, r.1 = w) ↔
      ∃ v, OTLeft ctx ∅ cs v ∧ normalize .assoc laws (withK 1 v) = .node w :=
  baseRecsR_views_iff.trans (enumerateLD_left_iff hκ hs hn)

theorem baseRecsR_right_views_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {laws : Laws} {n : Node} {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} :
    (∃ r ∈ baseRecsR ctx .right laws n, r.1 = w) ↔
      ∃ v, OTRight ctx ∅ cs v ∧ normalize .assoc laws (withK 1 v) = .node w :=
  baseRecsR_views_iff.trans (enumerateLD_right_iff hκ hs hn)

/-- A walk record of a laws-free left fold denotes the node's left fold. -/
theorem baseRecsR_left_lfold {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {r : RecR} (h : r ∈ baseRecsR ctx .left Laws.free n) :
    lfold ((r.1.map Prod.fst).map den) = lfold (cs.map den) := by
  obtain ⟨v, ht, hnorm⟩ := (baseRecsR_left_views_iff hκ hs hn).1 ⟨r, h, rfl⟩
  rw [normalize_free_assoc hnorm, withK_map_fst]
  exact otLeft_sound hc ht

theorem baseRecsR_right_rfold {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentR ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {r : RecR} (h : r ∈ baseRecsR ctx .right Laws.free n) :
    rfold ((r.1.map Prod.fst).map den) = rfold (cs.map den) := by
  obtain ⟨v, ht, hnorm⟩ := (baseRecsR_right_views_iff hκ hs hn).1 ⟨r, h, rfl⟩
  rw [normalize_free_assoc hnorm, withK_map_fst]
  exact otRight_sound hc ht

/-! ## Every reachable record denotes the fold -/

/-- **Every record reachable from the walk's records of a left fold denotes
the node's left fold.** -/
theorem reach_lfold_left {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {r : RecR}
    (h : Reach ctx .left Laws.free (baseRecsR ctx .left Laws.free n) r) :
    lfold ((r.1.map Prod.fst).map den) = lfold (cs.map den) := by
  refine reach_induction (P := fun r => lfold ((r.1.map Prod.fst).map den) = lfold (cs.map den))
    (fun r hr => baseRecsR_left_lfold hκ hs hc hn hr) ?_ h
  intro r r' hr h'
  obtain ⟨g, grp, raw, hgg, hraw, hnorm, -⟩ := mem_regroupRec h'
  obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
  rw [hκ] at hraw hnorm
  rw [normalize_free_assoc hnorm, regroup_step_sound_left hc hm hraw, hr]

theorem reach_rfold_right {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentR ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {r : RecR}
    (h : Reach ctx .right Laws.free (baseRecsR ctx .right Laws.free n) r) :
    rfold ((r.1.map Prod.fst).map den) = rfold (cs.map den) := by
  refine reach_induction (P := fun r => rfold ((r.1.map Prod.fst).map den) = rfold (cs.map den))
    (fun r hr => baseRecsR_right_rfold hκ hs hc hn hr) ?_ h
  intro r r' hr h'
  obtain ⟨g, grp, raw, hgg, hraw, hnorm, -⟩ := mem_regroupRec h'
  obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
  rw [hκ] at hraw hnorm
  rw [normalize_free_assoc hnorm, regroup_step_sound_right hc hm hraw, hr]

/-- **The views with regrouping of a left fold denote the node's left fold**
(`regroup_views_sound_assoc` for a fold, in every magma). -/
theorem regroup_views_sound_left {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {limit : Nat} {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .left Laws.free limit n) :
    lfold ((w.map Prod.fst).map den) = lfold (cs.map den) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateR h
  exact reach_lfold_left hκ hs hc hn hr

/-- The same for the engine's regrouping loop. -/
theorem regroupSkip_views_sound_left {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {limit : Nat} {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkip ctx .left Laws.free limit n) :
    lfold ((w.map Prod.fst).map den) = lfold (cs.map den) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateRSkip h
  exact reach_lfold_left hκ hs hc hn hr

/-- **The views with regrouping of a right fold denote the node's right fold.** -/
theorem regroup_views_sound_right {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentR ctx den) {limit : Nat} {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .right Laws.free limit n) :
    rfold ((w.map Prod.fst).map den) = rfold (cs.map den) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateR h
  exact reach_rfold_right hκ hs hc hn hr

theorem regroupSkip_views_sound_right {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentR ctx den) {limit : Nat} {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkip ctx .right Laws.free limit n) :
    rfold ((w.map Prod.fst).map den) = rfold (cs.map den) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateRSkip h
  exact reach_rfold_right hκ hs hc hn hr

/-- **The chains of `regroup_match_iff` for a left fold end on views of the
node's left fold.** -/
theorem regroup_chain_left_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {r₀ r : RecR} (h₀ : r₀ ∈ baseRecsR ctx .left Laws.free n)
    (h : RegroupChain ctx .left r₀ r) :
    lfold ((r.1.map Prod.fst).map den) = lfold (cs.map den) := by
  rw [regroupChain_left_sound hκ hs hc h]
  exact baseRecsR_left_lfold hκ hs hc hn h₀

theorem regroup_chain_right_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentR ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {r₀ r : RecR} (h₀ : r₀ ∈ baseRecsR ctx .right Laws.free n)
    (h : RegroupChain ctx .right r₀ r) :
    rfold ((r.1.map Prod.fst).map den) = rfold (cs.map den) := by
  rw [regroupChain_right_sound hκ hs hc h]
  exact baseRecsR_right_rfold hκ hs hc hn h₀

/-! ## The monoid soundness holds for every direction -/

section AssocDir

variable {M : Type*} [Monoid M]

/-- Every record reachable from the walk's records of an `:assoc` node, in
any fold direction, denotes the node in a monoid, under the laws
(`reach_den_assoc` for any direction). -/
theorem reach_den_assoc_dir {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M}
    (hc : ConsistentA ctx den) {laws : Laws} (hl : LawsModelA laws den) {dir : Dir} {n : Node}
    {r : RecR} (h : Reach ctx dir laws (baseRecsR ctx dir laws n) r) :
    denA den r.1 = denA den (kids .assoc n.children) := by
  refine reach_induction (P := fun r => denA den r.1 = denA den (kids .assoc n.children)) ?_ ?_ h
  · intro r hr
    obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both (baseRecsR_sub_both hr)
    rw [hκ] at hn
    have h1 := otl_den_assoc hκ hc hv
    rw [hκ] at h1
    rw [denA_normalize hl hn, h1]
  · intro r r' hr h'
    obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_regroupRec h'
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [hκ] at hraw hn
    rw [regroup_step_sound_assoc_laws hc hl hm hraw hn, hr]

/-- **The views with regrouping of an `:assoc` operator or a fold denote the
node in a monoid, under an identity** (`regroup_views_sound_assoc_laws` for
any direction). -/
theorem regroup_views_sound_assoc_laws_dir {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M}
    (hc : ConsistentA ctx den) {laws : Laws} (hl : LawsModelA laws den) {dir : Dir}
    {limit : Nat} {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx dir laws limit n) :
    denA den w = denA den (kids .assoc n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateR h
  exact reach_den_assoc_dir hκ hc hl hr

theorem regroupSkip_views_sound_assoc_laws_dir {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M}
    (hc : ConsistentA ctx den) {laws : Laws} (hl : LawsModelA laws den) {dir : Dir}
    {limit : Nat} {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkip ctx dir laws limit n) :
    denA den w = denA den (kids .assoc n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateRSkip h
  exact reach_den_assoc_dir hκ hc hl hr

end AssocDir

end Semper.EMatch.Flatten
