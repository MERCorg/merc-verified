import MercVerified.Signatures.Refinement
/-!
# Proofs for the `strong_bisim_sigref` correctness contract

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

`strong_bisim_sigref_correct` proves the `StrongBisimSigrefCorrectSpec`
contract stated in `MercVerified/Signatures/Refinement.lean`. The
`example` right after it pins the theorem's exact closed signature (no extra
hypotheses, no narrowed generality) against that spec: `lake build` fails if
a regeneration of this theorem drifts from the pinned shape, forcing a
deliberate, reviewed change to the pin instead of a silent contract change.

Its proof is not yet done: it requires unfolding the translated `do`-blocks of
`strong_bisim_sigref`/`signature_refinement` down to the `run_worklist_loop`
call and a hand-written contract axiom for it (mirroring what the old
whole-function axiom stated) - left as `sorry` for now.

The other two lemmas below are supporting/derived results (not part of the
pinned contract):
- `stable_implies_strong_fixpoint` - a stable partition witnesses the
  strong-bisimulation `FixPoint` semantics: states in the same block are
  related by `StrongFixPoint` (proved from the definitions, independent of
  `strong_bisim_sigref_correct`);
- `strong_bisim_sigref_same_block_strong_fixpoint` - combining the two: the
  partition that `strong_bisim_sigref` returns puts `StrongFixPoint`-related
  states in one block.
-/

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open merc_reduction.signature_refinement (strong_bisim_sigref)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)
open verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem (toLTS)

namespace MercVerified.Signatures.Proofs

theorem strong_bisim_sigref_correct
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    StrongBisimSigrefCorrectSpec TLInst sys timing := by
  sorry

/-- Contract pin (human-reviewed): fails to compile if
    `strong_bisim_sigref_correct`'s signature drifts from
    `StrongBisimSigrefCorrectSpec` (e.g. gains an unapproved extra
    hypothesis). See the module doc comment. -/
example : ∀ {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing),
    StrongBisimSigrefCorrectSpec TLInst sys timing :=
  strong_bisim_sigref_correct

/-- Any partition that is stable for the strong signature witnesses the
    `StrongFixPoint` semantic: two states that end up in the same block are
    strong-bisimulation fixpoint related (take the stable partition itself as
    the witness). -/
theorem stable_implies_strong_fixpoint
    {State : Type u} {Label : Type v} (lts : Cslib.LTS State Label)
    {Block : Type u} (partition : State → Block)
    (hstable : IsStable (fun s => StrongSignature lts s partition) partition) :
    ∀ s s', partition s = partition s' → StrongFixPoint lts s s' := by
  intro s s' h
  unfold StrongFixPoint FixPoint
  refine ⟨Block, partition, ?_, h⟩
  simpa using hstable

/-- States that the `strong_bisim_sigref` refinement places in the same block
    are related by the strong-bisimulation `StrongFixPoint` semantics. -/
theorem strong_bisim_sigref_same_block_strong_fixpoint
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      strong_bisim_sigref
          (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
          sys timing = ok (sys, partition) ∧
      ∀ s s', blockOf s = blockOf s' → StrongFixPoint (toLTS TLInst sys) s s' := by
  have hspec := strong_bisim_sigref_correct TLInst sys timing
  unfold StrongBisimSigrefCorrectSpec at hspec
  rcases hspec with ⟨partition, blockOf, hret, hcoh, hstab⟩
  refine ⟨partition, blockOf, ?_, ?_⟩
  · simpa using hret
  · intro s s' hbb
    exact stable_implies_strong_fixpoint (toLTS TLInst sys) blockOf hstab s s' hbb

end MercVerified.Signatures.Proofs
