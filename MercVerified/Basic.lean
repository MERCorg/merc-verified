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
the usize indices addressed by the implementation, and the labels are the usize
*label indices* stored in each `Transition`. There is a transition
`s →[μ] s'` iff `outgoing_transitions sys s` succeeds and the resulting vector
contains the transition record `⟨μ, s'⟩`.
-/

open Aeneas Aeneas.Std Result

namespace verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem

/-- The transition relation induced by the concrete representation:
    `s →[μ] s'` iff `outgoing_transitions sys s` succeeds with a vector that
    contains the transition `{ label := μ, to := s' }`. -/
def tr {Label : Type}
    (sys : SimpleLabelledTransitionSystem Label)
    (s : Std.Usize) (μ : Std.Usize) (s' : Std.Usize) : Prop :=
  ∃ ts : alloc.vec.Vec Transition,
    sys.outgoing_transitions s = ok ts
      ∧ ({ label := μ, «to» := s' } : Transition) ∈ ts.val

/-- The cslib `LTS` view of a `SimpleLabelledTransitionSystem`.
    States are usize indices; labels are usize label-indices. -/
def toLTS {Label : Type}
    (sys : SimpleLabelledTransitionSystem Label) : Cslib.LTS Std.Usize Std.Usize where
  Tr := sys.tr

@[simp] theorem toLTS_Tr {Label : Type}
    (sys : SimpleLabelledTransitionSystem Label)
    (s μ s' : Std.Usize) :
    sys.toLTS.Tr s μ s' ↔ sys.tr s μ s' := Iff.rfl

end verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem

/-- The Rust method `is_hidden_label` declares the hidden (τ) label to be
    index `0`. We mirror this with the cslib `HasTau` class so that the LTS
    can be used with weak/branching bisimilarity. -/
instance : Cslib.HasTau Std.Usize where
  τ := 0#usize
