import Signatures.BranchingBisimilarity
import Signatures.Signature

-- Import the generated Lean code
import MercVerified.Code.Funs
import MercVerified.Code.FunsExternal_Template
import MercVerified.Code.FunsExternal
import MercVerified.Code.Types
import MercVerified.Code.TypesExternal_Template
import MercVerified.Code.TypesExternal

/-!
# Bridge: `SimpleLabelledTransitionSystem` as a cslib `LTS`

We view the Aeneas-translated `SimpleLabelledTransitionSystem Label` as an
`LTS` (in the sense of `Cslib.Foundations.Semantics.LTS.Basic`). The states are
the `TagIndex Usize StateTag` indices addressed by the implementation, and the
labels are the `TagIndex Usize LabelTag` *label indices* stored in each
`Transition`. There is a transition `s →[μ] s'` iff `outgoing_transitions sys s`
succeeds and the resulting vector contains the transition record
`⟨μ, s'⟩`.
-/

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (Transition StateTag LabelTag TransitionLabel)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)

namespace verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem

/-- The transition relation induced by the concrete representation:
    `s →[μ] s'` iff `outgoing_transitions sys s` succeeds with a vector that
    contains the transition `{ label := μ, to := s' }`. -/
def tr {Label : Type}
    (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label)
    (s : TagIndex Std.Usize StateTag)
    (μ : TagIndex Std.Usize LabelTag)
    (s' : TagIndex Std.Usize StateTag) : Prop :=
  ∃ ts : alloc.vec.Vec Transition,
    SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions
        TLInst sys s = ok ts
      ∧ ({ label := μ, «to» := s' } : Transition) ∈ ts.val

/-- The cslib `LTS` view of a `SimpleLabelledTransitionSystem`.
    States are state-tagged usize indices; labels are label-tagged usize indices. -/
def toLTS {Label : Type}
    (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) :
    Cslib.LTS (TagIndex Std.Usize StateTag) (TagIndex Std.Usize LabelTag) where
  Tr := tr TLInst sys

@[simp] theorem toLTS_Tr {Label : Type}
    (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label)
    (s : TagIndex Std.Usize StateTag)
    (μ : TagIndex Std.Usize LabelTag)
    (s' : TagIndex Std.Usize StateTag) :
    (toLTS TLInst sys).Tr s μ s' ↔ tr TLInst sys s μ s' := Iff.rfl

end verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem

/-- The Rust method `is_hidden_label` declares the hidden (τ) label to be
    the tagged index `TagIndex::new(0)`. Since `TagIndex` is modelled
    axiomatically by Aeneas, we postulate the corresponding element here so
    that the cslib `HasTau` class can be instantiated, making the LTS usable
    with weak/branching bisimilarity. -/
axiom tauLabelIndex : TagIndex Std.Usize LabelTag

noncomputable instance : Cslib.HasTau (TagIndex Std.Usize LabelTag) where
  τ := tauLabelIndex
