import MercVerified.Lts.Lts

open Aeneas Aeneas.Std Result
open merc_utilities.timing (Timing)
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open verified.merc_reduction.signature_refinement (strong_bisim_sigref)
open MercVerified.Lts (toLTS)

namespace MercVerified.Refinement

/-- Correctness of `strong_bisim_sigref` for any `LTS` trait implementor `L` (via its dictionary
    `LTSInst`), given the requirement that isn't implied by the trait's type signature alone:
    well-formedness (`hwf`, see `LTS.WellFormed`: a non-empty state space on which
    `outgoing_transitions` succeeds with in-range targets). Showing that a concrete implementor
    (e.g. `LabelledTransitionSystem`) satisfies `hwf` is a separate concern
    (see `docs/axiom-audit-plan.md`). Proved by `Proofs.strong_bisim_sigref_correct`.

    `element_to_block` is indexed by the *state* (`element_to_block[s]` is the block of state `s`;
    `elements` is a permutation of the states, so its positions carry no such meaning), hence the
    coherence clause reads it at `s.index`. Only the `n` real states `s.index < n` are constrained:
    `WellFormed` says nothing about the transitions of indices `≥ n`, so stability and completeness
    are stated for in-range states only. -/
def StrongBisimSigrefCorrectSpec
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (_hwf : MercVerified.Lts.WellFormed LTSInst sys) (timing : Timing) : Prop :=
  ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
    strong_bisim_sigref LTSInst sys timing = ok (sys, partition) ∧
    (∀ s b, s ∈ partition.elements.val →
        partition.element_to_block.val[s.index.val]? = some b → blockOf s = b) ∧
    (∀ n, LTSInst.num_of_states sys = ok n →
        ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val → s ∈ partition.elements.val) ∧
    (∀ n, LTSInst.num_of_states sys = ok n →
        ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
          blockOf s = blockOf s' →
          StrongSignature (toLTS LTSInst sys) s blockOf =
            StrongSignature (toLTS LTSInst sys) s' blockOf) ∧
    ∀ n, LTSInst.num_of_states sys = ok n →
      ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
        StrongFixPoint (toLTS LTSInst sys) s s' → blockOf s = blockOf s'

end MercVerified.Refinement
