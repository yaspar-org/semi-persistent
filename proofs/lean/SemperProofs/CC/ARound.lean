import SemperProofs.CC.ARound.Basic
import SemperProofs.CC.ARound.Choice
import SemperProofs.CC.ARound.Store
import SemperProofs.CC.ARound.Nested

/-!
# A-only inter-reduction (`a_round`)

The model of `egraph.rs`, `fn a_round`, and of the build-time splicing
`flatten_seq_children` it relies on (design `06-ac-congruence-closure.md`
§14, `05-algebraic-operators.md` "A-Only Operators").

* `ARound/Basic.lean`: the fold semantics `den`, the step `ARStep` with the
  spine restriction of commit `7beed39f`, its soundness per direction
  (`rewrite_left_sound`, `rewrite_right_sound`, `rewrite_both_sound`), the
  counter-models off the spine (`left_off_spine_unsound`,
  `right_off_spine_unsound`), theory equality `Theq`, and the invariant I2
  over a node set (`aRound_sound`).
* `ARound/Choice.lean`: orientation and the least spelling under `shortlex`
  (`isLeastSpelling_exists`, `isLeastSpelling_unique`, `rule_of_ne_least`);
  an oriented rewrite decreases the sequence (`rewriteAt_shortlex`) and
  rewriting terminates (`orientedRewrite_wf`); the engine's choice of the
  first allowed offset and of the first rule with an occurrence is an
  `ARStep` and exists whenever one does (`engineRewrite_aRStep`,
  `engineRewrite_complete`, `chooseOffset_first`, `firstRule_aRStep`,
  `firstRule_complete`).
* `ARound/Store.lean`: the hash-consed node store; an `a_round` merge,
  whether `add` mints a node or returns an existing one, preserves I2
  (`aRoundH_sound`), and repeated merges from a finite node set terminate
  (`aRoundH_wf`, `aRoundH_chain_bound`).
* `ARound/Nested.lean`: `f`-node children; splicing on the spine preserves
  the denotation (`splice_den_left`, `splice_den_right`, `splice_den_both`),
  `a_round` on spliced sequences is sound (`aRound_spliced_sound`), the
  rewritten sequence needs no splicing (`aRStep_spineImpure`), and splicing
  off the spine of a fold is unsound (`splice_off_spine_unsound_left`,
  `splice_off_spine_unsound_right`).

## Not modelled

* Recanonicalization. Sequences are compared as stored; the engine compares
  children after `find`, and rebuild recanonicalizes nodes and merges those
  that collide. The `shortlex` order on canonical ids is therefore not stable
  across merges in the engine; termination here uses only that an oriented
  rewrite does not lengthen a sequence and copies existing elements, over a
  fixed alphabet. A proof with recanonicalization needs the alphabet of
  canonical ids, which shrinks, and the congruence merges of rebuild in the
  same potential.
* The joint fixpoint. Termination is of `a_round` merges alone; the
  completion loop interleaves them with AC rounds and congruence, and their
  joint termination is not proved here.
* Degenerate sequences: `add` returns the child's class for a one-element
  sequence (`nary_canon`); here every sequence is a node.
* Why stored spines hold no pure class (purity of a class only closes, so a
  child not spliced at build is never spliced later): `aRStep_spineImpure`
  takes it as a hypothesis.
-/
