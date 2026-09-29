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
open merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (Transition StateTag LabelTag TransitionLabel LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)

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
    `slts_num_of_states_pos` below for the witness that `SimpleLabelledTransitionSystem`
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
    ∀ s : TagIndex Std.Usize StateTag, s.val < n.val →
      ∃ ts : alloc.vec.Vec Transition,
        LTSInst.outgoing_transitions sys s = ok ts ∧ ∀ t ∈ ts.val, t.to.val < n.val

end verified.merc_lts.lts.LTS

/-- The Rust method `is_hidden_label` declares the hidden (τ) label to be
    the tagged index `TagIndex::new(0)`. Since `TagIndex` is modelled
    axiomatically by Aeneas, we postulate the corresponding element here so
    that the cslib `HasTau` class can be instantiated, making the LTS usable
    with weak/branching bisimilarity. -/
axiom tauLabelIndex : TagIndex Std.Usize LabelTag

noncomputable instance : Cslib.HasTau (TagIndex Std.Usize LabelTag) where
  τ := tauLabelIndex

/-- `BlockPartition::new` succeeds for a positive number of elements (the
    translated `assert!(num_of_elements > 0)` holds exactly when
    `0 < num_of_elements`); stated here (not in `Code/FunsExternal.lean`)
    because the def it characterizes is generated code. -/
axiom BlockPartition.new_spec
  (num_of_elements : Std.Usize) (hpos : 0 < num_of_elements.val) :
  ∃ bp, verified.merc_reduction.block_partition.BlockPartition.new num_of_elements = ok bp

/-- The translated `SimpleLabelledTransitionSystem` is well-formed: Rust's type invariant is that
    `transitions` has exactly the keys `0..n` (`n = transitions.len()`, and `n ≥ 1` since the
    constructor keeps `initial_state` in the map) and every transition target is such a key.
    Hence `outgoing_transitions` (a `HashMap::get(..).expect(..)`) succeeds on every state `< n`
    with in-range targets, and the state space is non-empty (otherwise the translated
    `BlockPartition::new` `assert!(num_of_elements > 0)` would fail).

    This is the witness that `SimpleLabelledTransitionSystem`'s `LTS` instance satisfies the
    `LTS.WellFormed` requirement, making `strong_bisim_sigref_correct` (in
    `MercVerified/Signatures/Proofs/Refinement_Proofs.lean`) a corollary of the generic
    `strong_bisim_sigref_correct_general`. -/
axiom slts_wellFormed {Label : Type}
    (TLInst : verified.merc_lts.lts.TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) :
    (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).WellFormed sys
