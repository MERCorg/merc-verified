import Signatures.BranchingBisimilarity
import Signatures.Signature

-- Import the generated Lean code
import MercVerified.Code.Funs
import MercVerified.Code.FunsExternal_Template
import MercVerified.Code.FunsExternal
import MercVerified.Code.FunsExternalSpecs
import MercVerified.Code.Types
import MercVerified.Code.TypesExternal_Template
import MercVerified.Code.TypesExternal

/-!
# Bridge: an `LTS` trait implementor as a cslib `LTS`

We view any Aeneas-translated implementor `L` of the `merc_lts::lts::LTS` trait (dictionary-passed
as `LTSInst : verified.merc_lts.lts.LTS L Label`) as an `LTS` (in the sense of
`Cslib.Foundations.Semantics.LTS.Basic`). The states are the `TagIndex Usize StateTag` indices
addressed by the implementation, and the labels are the `TagIndex Usize LabelTag` *label indices*
stored in each `Transition`. There is a transition `s →[μ] s'` iff
`LTSInst.outgoing_transitions sys s` succeeds and the resulting vector contains the transition
record `⟨μ, s'⟩`.
-/

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (Transition StateTag LabelTag TransitionLabel LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_lts.labelled_transition_system (LabelledTransitionSystem)

namespace verified.merc_lts.lts.LTS

/-- The transition relation induced by an `LTS` implementor's concrete representation:
    `s →[μ] s'` iff `LTSInst.outgoing_transitions sys s` succeeds with a vector that contains the
    transition `{ label := μ, to := s' }`. -/
def tr {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L)
    (s : TagIndex Std.Usize StateTag)
    (μ : TagIndex Std.Usize LabelTag)
    (s' : TagIndex Std.Usize StateTag) : Prop :=
  ∃ ts : alloc.vec.Vec Transition,
    LTSInst.outgoing_transitions sys s = ok ts
      ∧ ({ label := μ, «to» := s' } : Transition) ∈ ts.val

/-- The cslib `LTS` view of an `LTS` trait implementor. States are state-tagged usize indices;
    labels are label-tagged usize indices. -/
def toLTS {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L) :
    Cslib.LTS (TagIndex Std.Usize StateTag) (TagIndex Std.Usize LabelTag) where
  Tr := tr LTSInst sys

@[simp] theorem toLTS_Tr {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L)
    (s : TagIndex Std.Usize StateTag)
    (μ : TagIndex Std.Usize LabelTag)
    (s' : TagIndex Std.Usize StateTag) :
    (toLTS LTSInst sys).Tr s μ s' ↔ tr LTSInst sys s μ s' := Iff.rfl

/-- The one semantic requirement on an `LTS` implementor that the strong-bisimulation refinement
    algorithm's correctness needs beyond the trait's type signature: a non-empty state space
    (needed for `BlockPartition::new`'s `assert!(num_of_elements > 0)`). Not derivable from the
    trait interface alone - it is a property of a specific implementor's invariants (see
    `lts_wellFormed` below for the witness that `LabelledTransitionSystem`
    satisfies it). -/
def NonEmpty {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  ∃ n : Std.Usize, LTSInst.num_of_states sys = ok n ∧ 0 < n.val

/-- Well-formedness of an `LTS` implementor's concrete representation: a non-empty state space
    of `n` states in which `outgoing_transitions` succeeds on every state `< n` and only yields
    transitions whose target is again `< n`. The trait's type signature does not imply any of
    this (`outgoing_transitions` may `fail`, and its targets are arbitrary indices), so
    algorithms over `LTS` implementors are only trusted under this hypothesis. -/
def WellFormed {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  LTSInst.NonEmpty sys ∧
  ∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
    ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val →
      ∃ ts : alloc.vec.Vec Transition,
        LTSInst.outgoing_transitions sys s = ok ts ∧ ∀ t ∈ ts.val, t.to.index.val < n.val

end verified.merc_lts.lts.LTS

/-- The Rust method `is_hidden_label` declares the hidden (τ) label to be
    the tagged index `TagIndex::new(0)`. -/
def tauLabelIndex : TagIndex Std.Usize LabelTag := { index := 0#usize, marker := () }

noncomputable instance : Cslib.HasTau (TagIndex Std.Usize LabelTag) where
  τ := tauLabelIndex

/-- `BlockPartition::new` succeeds for a positive number of elements (the
    translated `assert!(num_of_elements > 0)` holds exactly when
    `0 < num_of_elements`); stated here (not in `Code/FunsExternal.lean`)
    because the def it characterizes is generated code. -/
axiom BlockPartition.new_spec
  (num_of_elements : Std.Usize) (hpos : 0 < num_of_elements.val) :
  ∃ bp, verified.merc_reduction.block_partition.BlockPartition.new num_of_elements = ok bp

/-- The translated `LabelledTransitionSystem` is well-formed: Rust's `assert_valid`
    (`labelled_transition_system.rs:365-447`, run by every safe constructor -
    `from_raw_parts`, `new`, `relabel`, ... - so no reachable instance skips it)
    checks exactly the invariant needed here: `states` has one entry per state
    plus a sentinel (`states[num_of_states] = num_of_transitions`), every
    transition's target is `< num_of_states`, and `initial_state.value() <
    num_of_states` (which alone forces the state space to be non-empty, since
    indices start at `0`). Hence `outgoing_transitions` (a plain slice read
    within the checked `[states[i], states[i+1])` range) succeeds on every
    state `< n` with in-range targets.

    This is the witness that `LabelledTransitionSystem`'s `LTS` instance satisfies the
    `LTS.WellFormed` requirement, making `strong_bisim_sigref_correct` (in
    `MercVerified/Signatures/Proofs/Refinement_Proofs.lean`) a corollary of the generic
    `strong_bisim_sigref_correct_general`. -/
axiom lts_wellFormed {Label : Type}
    (TLInst : verified.merc_lts.lts.TransitionLabel Label)
    (sys : LabelledTransitionSystem Label) :
    (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).WellFormed sys
