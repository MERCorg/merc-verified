import Signatures.BranchingBisimilarity
import Signatures.Signature


-- The implementation of an LTS -
structure LabelledTransitionSystem (State Label : Type) where
  Outgoing : (s : State) → (Label × State) → Prop

-- An implementation of the signature computation for a labelled transition system.
def compute_signature (lts: LabelledTransitionSystem State Label) (s: State) : Set (Label × State) :=
  { (μ, s') | lts.Outgoing s (μ, s') }

def refines (lts: LabelledTransitionSystem State Label) (s: State) (partition: State → Block) : Set (Label × Block) :=
  { (μ, α) | ∃ s', lts.Outgoing s (μ, s') ∧ partition s' = α }
