import MercVerified.Basic
import MercVerified.Signatures.StrongSignature

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open verified.merc_reduction.signature_refinement (strong_bisim_sigref)
open verified.merc_lts.lts.LTS (toLTS)

namespace MercVerified.Signatures

/-- Correctness of `strong_bisim_sigref` for any `LTS` trait implementor `L` (via its dictionary
    `LTSInst`), given the requirement that isn't implied by the trait's type signature alone:
    well-formedness (`hwf`, see `LTS.WellFormed`: a non-empty state space on which
    `outgoing_transitions` succeeds with in-range targets). `SimpleLabelledTransitionSystem`
    satisfies `hwf` via `slts_wellFormed` (`MercVerified/Basic.lean`), making its correctness result
    (`Proofs.strong_bisim_sigref_correct`) a corollary of this general spec's proof
    (`Proofs.strong_bisim_sigref_correct_general`). -/
def StrongBisimSigrefCorrectSpec
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (_hwf : LTSInst.WellFormed sys) (timing : Timing) : Prop :=
  ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
    strong_bisim_sigref LTSInst sys timing = ok (sys, partition) ∧
    (∀ s b, (s, b) ∈ List.zip partition.elements.val partition.element_to_block.val →
        blockOf s = b) ∧
    (∀ n, LTSInst.num_of_states sys = ok n →
        ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val → s ∈ partition.elements.val) ∧
    IsStable (fun s => StrongSignature (toLTS LTSInst sys) s blockOf) blockOf ∧
    ∀ s s', StrongFixPoint (toLTS LTSInst sys) s s' → blockOf s = blockOf s'

end MercVerified.Signatures
