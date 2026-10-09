import MercVerified.Lts.Lts
import Sigref.Scc

open Aeneas Aeneas.Std Result
open merc_utilities.timing (Timing)
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open verified.merc_reduction.signature_refinement (strong_bisim_sigref branching_bisim_sigref_impl branching_bisim_sigref)
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

/-- What `branching_bisim_sigref_impl` needs of its input beyond `WellFormed`: it is the output of
    `tau_cycle_elimination_and_reorder`, so
    * label index `0` is the hidden label (`is_hidden_label`), and every label of a transition is
      below `num_of_labels`;
    * the τ-transitions (label index `0`) go to a state with a smaller index (topological order;
      together with this, the LTS has no τ-cycles). -/
def BranchingLtsAssumptions {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  (∃ nl : Std.Usize, LTSInst.num_of_labels sys = ok nl ∧
    (∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0))) ∧
    ∀ s μ s', MercVerified.Lts.tr LTSInst sys s μ s' → μ.index.val < nl.val) ∧
  (∀ s μ t, MercVerified.Lts.tr LTSInst sys s μ t → μ.index.val = 0 → t.index.val < s.index.val)

/-- Correctness of `branching_bisim_sigref_impl` for any `LTS` trait implementor `L` whose state
    space is well-formed (`hwf`), fits the loop counter (`hfit`) and satisfies
    `BranchingLtsAssumptions`: it returns a `BlockPartition` (coherent with `blockOf`, covering all
    real states) whose blocks are exactly the branching bisimilarity classes of the real states, in
    the `toLTS` view. Proved by `Proofs.branching_bisim_sigref_impl_correct`.

    Additionally `element_to_block` has an entry for every real state, so `blockOf` is determined
    on the real states (`PartitionWellFormed` alone only constrains entries that exist).

    Scope: this is about `branching_bisim_sigref_impl` (the `lean`-feature variant of the
    Rust code) on an LTS that is already preprocessed. That `tau_cycle_elimination_and_reorder`
    produces an LTS satisfying `BranchingLtsAssumptions` and preserves branching bisimilarity,
    and that `LabelledTransitionSystem` satisfies `WellFormed`, are not covered here. For
    `divergence_preserving` the statement is about the relabelled LTS. -/
def BranchingBisimSigrefImplCorrectSpec
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (_hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (_hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (_hasm : BranchingLtsAssumptions LTSInst sys) (timing : Timing) : Prop :=
  ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
    branching_bisim_sigref_impl LTSInst sys timing = ok partition ∧
    PartitionWellFormed LTSInst sys partition blockOf ∧
    (∀ n, LTSInst.num_of_states sys = ok n →
      ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val →
        ∃ b, partition.element_to_block.val[s.index.val]? = some b) ∧
    ∀ n, LTSInst.num_of_states sys = ok n →
      ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
        (blockOf s = blockOf s' ↔ BranchingBisimilarity (toLTS LTSInst sys) s s')

/-- What `tau_cycle_elimination_and_reorder` needs of its input beyond `WellFormed`:
    * `is_hidden_label` is "label index `0`";
    * the labels are non-empty, the first one is the τ label (`is_tau_label`), and `clone` of a label
      returns it (the quotient copies the label vector);
    * every transition label is below the number of labels;
    * the state count fits (`StateCountFits`) and the initial state is a real state. -/
def PreprocessAssumptions {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  (∀ l : TagIndex Std.Usize LabelTag,
    LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0))) ∧
  (∃ sl : Slice Label, LTSInst.labels sys = ok sl ∧ 1 ≤ sl.val.length ∧
    (∃ t, sl.val[0]? = some t ∧ LTSInst.TransitionLabelInst.is_tau_label t = ok true) ∧
    ∀ s μ t, MercVerified.Lts.tr LTSInst sys s μ t → μ.index.val < sl.val.length) ∧
  (∀ x : Label, LTSInst.TransitionLabelInst.corecloneCloneInst.clone x = ok x) ∧
  StateCountFits LTSInst sys ∧
  (∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
    ∃ i, LTSInst.initial_state_index sys = ok i ∧ i.index.val < n.val)

/-- Correctness of `branching_bisim_sigref` for `divergence_preserving = false`. The call succeeds
    and returns the preprocessed LTS `R`, the image `state'` of `state` and a partition of `R`:
    * the preprocessing is correct: `R` is `WellFormed`, fits the loop counter and satisfies
      `BranchingLtsAssumptions`, and the map `f` (state ↦ its τ-SCC, renumbered topologically) is a
      branching bisimulation between the input and `R`, with `state' = f state`;
    * the partition is the branching bisimilarity of `R` (as in `BranchingBisimSigrefImplCorrectSpec`).
    Hence `state` and `s` are branching bisimilar in the input iff `state'` and `f s` are in `R`
    (composing with the cross bisimulation). Proved by `Proofs.branching_bisim_sigref_correct`. -/
def BranchingBisimSigrefCorrectSpec
    {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (_hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (_hass : PreprocessAssumptions LTSInst sys)
    (state : TagIndex Std.Usize StateTag) (timing : Timing) : Prop :=
  ∃ (R : verified.merc_lts.labelled_transition_system.LabelledTransitionSystem Label)
    (state' : TagIndex Std.Usize StateTag) (partition : BlockPartition)
    (f : ℕ → ℕ) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
    branching_bisim_sigref LTSInst sys state false timing = ok (R, state', partition) ∧
    (∀ n, LTSInst.num_of_states sys = ok n → state.index.val < n.val →
      state'.index.val = f state.index.val) ∧
    Sigref.IsCrossBB (toLTS LTSInst sys)
      (toLTS (verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS
        LTSInst.TransitionLabelInst) R)
      (fun s s' => (∃ n, LTSInst.num_of_states sys = ok n ∧ s.index.val < n.val) ∧
        s'.index.val = f s.index.val) ∧
    (let I := verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS
        LTSInst.TransitionLabelInst
     MercVerified.Lts.WellFormed I R ∧ StateCountFits I R ∧ BranchingLtsAssumptions I R ∧
     PartitionWellFormed I R partition blockOf ∧
     (∀ n, I.num_of_states R = ok n →
       ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val →
         ∃ b, partition.element_to_block.val[s.index.val]? = some b) ∧
     ∀ n, I.num_of_states R = ok n →
       ∀ s s' : TagIndex Std.Usize StateTag, s.index.val < n.val → s'.index.val < n.val →
         (blockOf s = blockOf s' ↔ BranchingBisimilarity (toLTS I R) s s'))

end MercVerified.Refinement
