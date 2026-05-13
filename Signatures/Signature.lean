module

public import Cslib.Foundations.Semantics.LTS.Basic

-- Signatures are a way to capture the observable behavior of a state in an LTS.
def StrongSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block): Set (Label × Block)
  := { (μ, α) | ∃ s', lts.Tr s μ s' ∧ partition s' = α }


-- Refine a partition by splitting blocks where states have different signatures.
def refinePartition (lts : Cslib.LTS State Label) (partition : State → Block) : State → Block
  := fun s => (partition s, StrongSignature lts s partition)
