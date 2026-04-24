import MercVerified

/-- The implementation of the LTS -/
structure LabelledTransitionSystem (State Label : Type) where
  Outgoing : (s : State) → (Label × State) → Prop

/-- An implementation of the signature computation for a labelled transition system. -/
def compute_signature (lts: LabelledTransitionSystem State Label) (s: State) : Set (Label × State) :=
  { (μ, s') | lts.Outgoing s (μ, s') }
