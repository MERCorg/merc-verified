import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Refinement_Proofs
import MercVerified.Refinement.Proofs.BranchingTop_Proofs

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel LTS)
open MercVerified.Refinement (StrongBisimSigrefCorrectSpec)

-- Contract pin: fails to compile if `strong_bisim_sigref_correct`'s signature drifts.
example : ∀ {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (timing : Timing),
    StrongBisimSigrefCorrectSpec LTSInst sys hwf hfit timing :=
  MercVerified.Refinement.Proofs.strong_bisim_sigref_correct

-- Usability pin: the spec's block map is exactly strong bisimilarity (in the `toLTS` view) on the
-- real states, so `StrongBisimSigrefCorrectSpec` can be used to prove strong bisimilarity between
-- the elements of a block (and, conversely, bisimilar states share a block).
example : ∀ {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (_hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (_hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (timing : Timing),
    ∃ (partition : verified.merc_reduction.block_partition.BlockPartition)
      (blockOf : TagIndex Std.Usize StateTag →
        TagIndex Std.Usize verified.merc_collections.indexed_partition.BlockTag),
      verified.merc_reduction.signature_refinement.strong_bisim_sigref LTSInst sys timing
          = ok (sys, partition) ∧
      ∀ n, LTSInst.num_of_states sys = ok n →
        ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
          (blockOf s = blockOf s' ↔
            Cslib.LTS.Bisimilarity (MercVerified.Lts.toLTS LTSInst sys)
              (MercVerified.Lts.toLTS LTSInst sys) s s') :=
  MercVerified.Refinement.Proofs.strong_bisim_sigref_same_block_iff_bisimilar

-- Contract pin: fails to compile if `branching_bisim_sigref_impl_correct`'s signature drifts.
example : ∀ {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (hasm : MercVerified.Refinement.BranchingLtsAssumptions LTSInst sys) (timing : Timing),
    MercVerified.Refinement.BranchingBisimSigrefImplCorrectSpec LTSInst sys hwf hfit hasm timing :=
  MercVerified.Refinement.Proofs.branching_bisim_sigref_impl_correct
