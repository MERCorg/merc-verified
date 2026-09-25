import MercVerified.Signatures.Refinement
import Signatures.Proofs.Signature_Proofs
/-!
# Proofs for the `strong_bisim_sigref` correctness contract

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

`strong_bisim_sigref_correct_general` proves the `StrongBisimSigrefCorrectSpec`
contract stated in `MercVerified/Signatures/Refinement.lean`, generically for
any `LTS` trait implementor. `strong_bisim_sigref_correct` specializes it to
`SimpleLabelledTransitionSystem`. Their contract pins (the `example`s
re-stating their exact closed signatures, so `lake build` fails if a
regeneration drifts from the pinned shape) live in the human-vetted
`MercVerified/Signatures/Refinement_Pins.lean`, not in this file.

The proof unfolds the translated `do`-blocks of `strong_bisim_sigref` /
`signature_refinement` down to the `run_worklist_loop` call, using:
- the success-spec contract axioms for the opaque Aeneas externals in
  `MercVerified/Code/FunsExternal.lean` (`IncomingTransitions::new`,
  `Timing::measure`, `HashMap::len`, `Vec::resize_with`, `Vec::default`,
  `TagIndex::new`), plus `BlockPartition::new` (positive element count);
- the `hne : LTSInst.NonEmpty sys` hypothesis (for `SimpleLabelledTransitionSystem`,
  discharged by the domain axiom `slts_num_of_states_pos` - never empty,
  mirroring the Rust `initial_state ∈ transitions` invariant), without which
  `BlockPartition::new`'s `assert!(num_of_elements > 0)` fails;
- the hand-written `run_worklist_loop` contract axiom `run_worklist_loop_spec`
  (declared in `MercVerified/Basic.lean`, where `toLTS` is defined, generic
  over any `LTS` implementor), which provides the partition coherence,
  `IsStable` (soundness) and `StrongFixPoint` completeness conjuncts of the
  spec.

The remaining lemmas below are supporting/derived results (not part of the
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
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open verified.merc_reduction.signature_refinement (strong_bisim_sigref strong_signature_refinement)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)
open verified.merc_lts.lts.LTS (toLTS)

namespace MercVerified.Signatures.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- The translated `FnMut` instance used by `strong_signature_refinement`'s
    `resize_with` call. -/
noncomputable abbrev resizeFnMut {L Label : Type} (LTSInst : LTS L Label) :=
  verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag
    LTSInst

/-- The translated `FnOnce` instance whose `call_once` runs
    `signature_refinement`. -/
noncomputable abbrev fnOnceInst {L Label : Type} (LTSInst : LTS L Label) :=
  verified.merc_reduction.signature_refinement.strong_bisim_sigref.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition
    LTSInst

/-- `FromVecArray::from` always succeeds. -/
private theorem FromVecArray_from_ok {T : Type} {N : Std.Usize} (a : Array T N) :
    ∃ v : alloc.vec.Vec T, alloc.vec.FromVecArray.from a = ok v := by
  have hbnd : a.val.length ≤ Usize.max := by scalar_tac
  rw [alloc.vec.FromVecArray.from]
  refine ⟨alloc.vec.Vec.from a.val hbnd, ?_⟩
  rfl

/-- The translated `BlockPartitionBuilder::default` always succeeds. -/
private theorem BlockPartitionBuilder_default_ok :
    ∃ bpb : verified.merc_reduction.block_partition.BlockPartitionBuilder,
      verified.merc_reduction.block_partition.BlockPartitionBuilder.Insts.CoreDefaultDefault.default = ok bpb := by
  rw [verified.merc_reduction.block_partition.BlockPartitionBuilder.Insts.CoreDefaultDefault.default]
  rcases (alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec (TagIndex Std.Usize BlockTag)) with ⟨b0, hb0⟩
  rcases (alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec Std.Usize) with ⟨b1, hb1⟩
  rw [hb0, hb1]
  simp

/-- The `strong_signature_refinement` call at the heart of `strong_bisim_sigref`,
    on the strong-bisimulation specialization, succeeds for every non-empty
    system and produces a partition satisfying the coherence / stability /
    completeness clauses of `StrongBisimSigrefCorrectSpec`. -/
private theorem signature_refinement_spec
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L)
    (incoming : merc_lts.incoming_transitions.IncomingTransitions)
    (n : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n)
    (hnpos : 0 < n.val) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      verified.merc_reduction.signature_refinement.strong_signature_refinement LTSInst
        sys incoming = ok partition ∧
      (∀ s b, (s, b) ∈ List.zip partition.elements.val partition.element_to_block.val → blockOf s = b) ∧
      IsStable (fun s => StrongSignature (toLTS LTSInst sys) s blockOf) blockOf ∧
      ∀ s s', StrongFixPoint (toLTS LTSInst sys) s s' → blockOf s = blockOf s' := by
  rcases (alloc.vec.Vec.resize_with_spec Global (resizeFnMut LTSInst)
      (alloc.vec.Vec.new (TagIndex Std.Usize BlockTag)) n ()) with ⟨state_to_key, hstate_to_key⟩
  rcases (BlockPartition.new_spec n hnpos) with ⟨bp, hbp⟩
  rcases (merc_utilities.tagged_index.TagIndex.new_spec (T := Std.Usize) BlockTag 0#usize) with ⟨ti, hti⟩
  rcases (FromVecArray_from_ok (Array.make 1#usize [ti])) with ⟨v, hv⟩
  rcases (alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec
      ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag))) with ⟨v1, hv1⟩
  rcases (BlockPartitionBuilder_default_ok) with ⟨bpb, hbpb⟩
  let ctx0 : verified.merc_reduction.signature_refinement.WorklistContextStrong :=
    { partition := bp, worklist := v,
      states := alloc.vec.Vec.new (TagIndex Std.Usize StateTag),
      builder := v1, split_builder := bpb, state_to_key := state_to_key }
  rcases (run_worklist_loop_spec LTSInst sys incoming ctx0)
    with ⟨ctx, blockOf, hloop, hcohloop, hstabloop, hcomplloop⟩
  refine ⟨ctx.partition, blockOf, ?_, hcohloop, hstabloop, hcomplloop⟩
  unfold verified.merc_reduction.signature_refinement.strong_signature_refinement
  rw [hns]
  simp
  rw [hstate_to_key]
  simp
  rw [hbp]
  simp
  rw [hti]
  simp
  rw [hv]
  simp
  rw [hv1]
  simp
  rw [hbpb]
  simp
  rw [hloop]
  simp

/-- Contract pin theorem: for any `LTS` trait implementor `L`/`LTSInst` with a
    non-empty state space (`hne`), `strong_bisim_sigref` returns a partition
    of the input LTS that is stable for the strong signature (sound) and
    complete w.r.t. `StrongFixPoint`, and whose block map agrees with the
    concrete `BlockPartition` representation. -/
theorem strong_bisim_sigref_correct_general
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hne : LTSInst.NonEmpty sys) (timing : Timing) :
    StrongBisimSigrefCorrectSpec LTSInst sys hne timing := by
  unfold StrongBisimSigrefCorrectSpec
  rcases hne with ⟨n, hns, hnpos⟩
  rcases (merc_lts.incoming_transitions.IncomingTransitions.new_spec LTSInst sys)
    with ⟨incoming, hincoming⟩
  rcases (merc_utilities.timing.Timing.measure_spec (fnOnceInst LTSInst) timing (toStr "reduction") (sys, incoming))
    with ⟨partition, hmeasure, hcall⟩
  rcases (signature_refinement_spec LTSInst sys incoming n hns hnpos)
    with ⟨partition', blockOf, hsr, hcoh, hstab, hcomplete⟩
  have hcall' :
      verified.merc_reduction.signature_refinement.strong_signature_refinement LTSInst
        sys incoming = ok partition := by
    rw [fnOnceInst] at hcall
    dsimp at hcall
    rw [verified.merc_reduction.signature_refinement.strong_bisim_sigref.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition.call_once] at hcall
    simpa using hcall
  have hp' : partition' = partition := by
    exact Result.ok_injective (hsr.symm.trans hcall')
  have hcoh' : ∀ s b, (s, b) ∈ List.zip partition.elements.val partition.element_to_block.val → blockOf s = b := by
    intro s b hz
    exact hcoh s b (by simpa [hp'] using hz)
  refine ⟨partition, blockOf, ?_, hcoh', hstab, hcomplete⟩
  unfold strong_bisim_sigref
  rw [hincoming]
  simp
  rw [hmeasure]
  simp

/-- `SimpleLabelledTransitionSystem` satisfies the `LTS.NonEmpty` requirement
    (via `slts_num_of_states_pos`), so its correctness result is a corollary
    of the generic `strong_bisim_sigref_correct_general`. -/
theorem strong_bisim_sigref_correct
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    StrongBisimSigrefCorrectSpec
      (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys
      (slts_num_of_states_pos TLInst sys) timing :=
  strong_bisim_sigref_correct_general
    (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys
    (slts_num_of_states_pos TLInst sys) timing

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
      ∀ s s', blockOf s = blockOf s' → StrongFixPoint (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) s s' := by
  have hspec := strong_bisim_sigref_correct TLInst sys timing
  unfold StrongBisimSigrefCorrectSpec at hspec
  rcases hspec with ⟨partition, blockOf, hret, hcoh, hstab, _hcomplete⟩
  refine ⟨partition, blockOf, ?_, ?_⟩
  · simpa using hret
  · intro s s' hbb
    exact stable_implies_strong_fixpoint (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) blockOf hstab s s' hbb

/-- The partition that `strong_bisim_sigref` returns puts exactly the
    `StrongFixPoint`-related (equivalently, by `StrongFixPoint.bisimilarity` /
    `Cslib.LTS.Bisimilarity.strongFixPoint`, the bisimilar) states in the same
    block: soundness from `stable_implies_strong_fixpoint`, completeness from
    the spec's own completeness conjunct. -/
theorem strong_bisim_sigref_same_block_iff_strong_fixpoint
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      strong_bisim_sigref
          (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
          sys timing = ok (sys, partition) ∧
      ∀ s s', blockOf s = blockOf s' ↔ StrongFixPoint (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) s s' := by
  have hspec := strong_bisim_sigref_correct TLInst sys timing
  unfold StrongBisimSigrefCorrectSpec at hspec
  rcases hspec with ⟨partition, blockOf, hret, hcoh, hstab, hcomplete⟩
  refine ⟨partition, blockOf, ?_, ?_⟩
  · simpa using hret
  · intro s s'
    exact ⟨stable_implies_strong_fixpoint (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) blockOf hstab s s', hcomplete s s'⟩

/-- The headline strong-bisimilarity statement: `strong_bisim_sigref`'s block
    map is exactly the strong bisimilarity relation. This is the *full*
    strong-bisimilarity reachable from `StrongBisimSigrefCorrectSpec`: two
    states are placed in the same block by the translated refinement iff they
    are strongly bisimilar in the `toLTS` view of the
    `SimpleLabelledTransitionSystem`. The right-to-left direction is the spec's
    `StrongFixPoint`-completeness conjunct chained through
    `Cslib.LTS.Bisimilarity.strongFixPoint`; the left-to-right is the spec's
    `IsStable` conjunct witnessed through `stable_implies_strong_fixpoint` and
    `StrongFixPoint.bisimilarity`. -/
theorem strong_bisim_sigref_same_block_iff_bisimilar
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      strong_bisim_sigref
          (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
          sys timing = ok (sys, partition) ∧
      ∀ s s', blockOf s = blockOf s' ↔
        Cslib.LTS.Bisimilarity (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys)
          (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) s s' := by
  obtain ⟨partition, blockOf, hret, hiff⟩ :=
    strong_bisim_sigref_same_block_iff_strong_fixpoint TLInst sys timing
  refine ⟨partition, blockOf, hret, ?_⟩
  intro s s'
  have hss' : blockOf s = blockOf s' ↔
      StrongFixPoint (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) s s' := hiff s s'
  constructor
  · intro hab
    exact StrongFixPoint.bisimilarity (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) (hss'.1 hab)
  · intro hb
    exact hss'.2 (Cslib.LTS.Bisimilarity.strongFixPoint (toLTS (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys) hb)

end MercVerified.Signatures.Proofs
