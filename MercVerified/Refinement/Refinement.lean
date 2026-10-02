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

/-- The state count `n` is small enough (`n * (n + 2) ≤ Usize::MAX`) that the
    signature-refinement loop's iteration counter, which can reach roughly `n * (n + 1)`, never
    overflows. This is a requirement of `strong_bisim_sigref` only, hence separate from
    `MercVerified.Lts.WellFormed`. -/
def StateCountFits {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  ∀ n : Std.Usize, LTSInst.num_of_states sys = ok n → n.val * (n.val + 2) ≤ Std.Usize.max

/-- Well-formedness of the `BlockPartition` returned by a refinement, relative to the block map
    `blockOf` that interprets it:
    * coherence: `element_to_block` is indexed by the *state* (`element_to_block[s]` is the block of
      state `s`; `elements` is a permutation of the states, so its positions carry no such meaning),
      hence it is read at `s.index`, and it agrees with `blockOf` on every element;
    * coverage: every real state `s.index < n` occurs in `elements`. -/
def PartitionWellFormed
    {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (partition : BlockPartition)
    (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag) : Prop :=
  (∀ s b, s ∈ partition.elements.val →
      partition.element_to_block.val[s.index.val]? = some b → blockOf s = b) ∧
  (∀ n, LTSInst.num_of_states sys = ok n →
      ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val → s ∈ partition.elements.val)

/-- Correctness of `strong_bisim_sigref` for any `LTS` trait implementor `L` (via its dictionary
    `LTSInst`), given the requirement that isn't implied by the trait's type signature alone:
    well-formedness (`hwf`, see `LTS.WellFormed`: a non-empty state space on which
    `outgoing_transitions` succeeds with in-range targets) and a state count small enough for the
    loop counter not to overflow (`hfit`, see `StateCountFits`). Showing that a concrete implementor
    (e.g. `LabelledTransitionSystem`) satisfies `hwf` is a separate concern
    (see `docs/axiom-audit-plan.md`). Proved by `Proofs.strong_bisim_sigref_correct`.

    `element_to_block` is indexed by the *state* (`element_to_block[s]` is the block of state `s`;
    `elements` is a permutation of the states, so its positions carry no such meaning), hence the
    coherence clause reads it at `s.index`. Only the `n` real states `s.index < n` are constrained:
    `WellFormed` says nothing about the transitions of indices `≥ n`, so stability and completeness
    are stated for in-range states only. -/
def StrongBisimSigrefCorrectSpec
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (_hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (_hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (timing : Timing) : Prop :=
  ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
    strong_bisim_sigref LTSInst sys timing = ok (sys, partition) ∧
    PartitionWellFormed LTSInst sys partition blockOf ∧
    (∀ n, LTSInst.num_of_states sys = ok n →
        ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
          blockOf s = blockOf s' →
          StrongSignature (toLTS LTSInst sys) s blockOf =
            StrongSignature (toLTS LTSInst sys) s' blockOf) ∧
    ∀ n, LTSInst.num_of_states sys = ok n →
      ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
        StrongFixPoint (toLTS LTSInst sys) s s' → blockOf s = blockOf s'

end MercVerified.Refinement
