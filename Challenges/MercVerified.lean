import MercVerified.Refinement.Refinement

/-!
# Comparator challenge: the verified Rust code (human-vetted)

The headline contract theorems about the Aeneas translation in `MercVerified/`, stated with `sorry`
against the human-vetted spec files only (`MercVerified/Refinement/Refinement.lean`,
`MercVerified/Lts/Lts.lean`). `lake comparator` (configured by `comparator_MercVerified.json`, which also lists the trusted Aeneas boundary axioms of `MercVerified/Code/`)
checks that the solution module (`MercVerified`) proves each of them with the same statement,
using only the axioms listed there, and replays the proofs through the kernel. This replaces the
former `example` pins in `MercVerified/Refinement/Pins/Refinement_Pins.lean`.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open verified.merc_reduction.signature_refinement (strong_bisim_sigref)
open MercVerified.Lts (toLTS)
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

/-- `strong_bisim_sigref` is correct: its partition is stable and coarser than every strong
    fixpoint (`StrongBisimSigrefCorrectSpec`). -/
theorem strong_bisim_sigref_correct
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (timing : Timing) :
    StrongBisimSigrefCorrectSpec LTSInst sys hwf hfit timing := sorry

/-- Usability: the block map of `strong_bisim_sigref` is exactly strong bisimilarity (in the
    `toLTS` view) on the real states. -/
theorem strong_bisim_sigref_same_block_iff_bisimilar
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (timing : Timing) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      strong_bisim_sigref
          LTSInst
          sys timing = ok (sys, partition) ∧
      ∀ n, LTSInst.num_of_states sys = ok n →
        ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
          (blockOf s = blockOf s' ↔
            Cslib.LTS.Bisimilarity (toLTS LTSInst sys)
              (toLTS LTSInst sys) s s') := sorry

/-- `branching_bisim_sigref_impl` is correct on a preprocessed LTS
    (`BranchingBisimSigrefImplCorrectSpec`). -/
theorem branching_bisim_sigref_impl_correct
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (hasm : BranchingLtsAssumptions LTSInst sys) (timing : Timing) :
    BranchingBisimSigrefImplCorrectSpec LTSInst sys hwf hfit hasm timing := sorry

/-- `branching_bisim_sigref` (with preprocessing, `divergence_preserving = false`) is correct
    (`BranchingBisimSigrefCorrectSpec`). -/
theorem branching_bisim_sigref_correct {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (state : TagIndex Std.Usize StateTag)
    (hstate : ∀ n, LTSInst.num_of_states sys = ok n → state.index.val < n.val)
    (timing : merc_utilities.timing.Timing) :
    BranchingBisimSigrefCorrectSpec LTSInst sys hwf hass state hstate timing := sorry

end MercVerified.Refinement.Proofs
