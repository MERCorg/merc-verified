import Signatures.BranchingBisimilarity
import Signatures.Signature

-- The implementation of an LTS -
structure LabelledTransitionSystem (State Label : Type) where
  Outgoing : (s : State) → (Label × State) → Prop
