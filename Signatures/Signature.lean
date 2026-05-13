module

public import Cslib.Foundations.Semantics.LTS.Basic

-- Signatures are a way to capture the observable behavior of a state in an LTS.
def StrongSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block): Set (Label × Block)
  := { (μ, α) | ∃ s', lts.Tr s μ s' ∧ partition s' = α }
