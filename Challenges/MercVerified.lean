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

/-- **The Rust `strong_bisim_sigref` is correct.** Let `LTSInst` implement the Rust `LTS` trait
and let `sys` be well-formed (`hwf`: a non-empty state space on which `outgoing_transitions`
succeeds with in-range targets) with a state count that fits the loop counter (`hfit`). Then for
any `timing` the call succeeds and returns a `BlockPartition` with a block map that is coherent
with `element_to_block` on the real states, stable, and coarser than every strong fixpoint. See
`StrongBisimSigrefCorrectSpec` (`MercVerified/Refinement/Refinement.lean`). -/
theorem strong_bisim_sigref_correct
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (timing : Timing) :
    StrongBisimSigrefCorrectSpec LTSInst sys hwf hfit timing := sorry

/-- **The partition of `strong_bisim_sigref` is strong bisimilarity.** Under the hypotheses of
`strong_bisim_sigref_correct` (`hwf`, `hfit`), the call returns `ok (sys, partition)` with a block
map `blockOf` such that two real states (index below the state count) get the same block iff they
are strongly bisimilar in the `toLTS` view of `sys`. -/
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

/-- **The Rust `branching_bisim_sigref_impl` is correct on a preprocessed LTS.** Let `LTSInst`
implement the Rust `LTS` trait and let `sys` be well-formed (`hwf`) with a state count that fits
the loop counter (`hfit`), and assume `sys` already satisfies `BranchingLtsAssumptions` (the output
of preprocessing). Then the call returns a `BlockPartition` covering all real states whose blocks
are exactly the branching bisimilarity classes of the real states, in the `toLTS` view. That
preprocessing establishes the assumptions is not covered here (see
`branching_bisim_sigref_correct`). See `BranchingBisimSigrefImplCorrectSpec`
(`MercVerified/Refinement/Refinement.lean`). -/
theorem branching_bisim_sigref_impl_correct
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (hasm : BranchingLtsAssumptions LTSInst sys) (timing : Timing) :
    BranchingBisimSigrefImplCorrectSpec LTSInst sys hwf hfit hasm timing := sorry

/-- **The Rust `branching_bisim_sigref` (with preprocessing) is correct.** Let `sys` be a
well-formed system of an `LTS` implementor that satisfies `PreprocessAssumptions`, and `state` a
real state (`hstate`). With `divergence_preserving = false` and any `timing`, the call succeeds and
returns the preprocessed LTS `R`, the image `state'` of `state` and a partition of `R`.

The preprocessing is correct: `R` is well-formed, fits the counter and satisfies
`BranchingLtsAssumptions`, and the map `f` to τ-SCCs is a branching bisimulation with
`state' = f state`. The partition is exactly branching bisimilarity of `R`, so branching
bisimilarity of the input can be read off the output. See `BranchingBisimSigrefCorrectSpec`
(`MercVerified/Refinement/Refinement.lean`). -/
theorem branching_bisim_sigref_correct {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (state : TagIndex Std.Usize StateTag)
    (hstate : ∀ n, LTSInst.num_of_states sys = ok n → state.index.val < n.val)
    (timing : merc_utilities.timing.Timing) :
    BranchingBisimSigrefCorrectSpec LTSInst sys hwf hass state hstate timing := sorry

end MercVerified.Refinement.Proofs
