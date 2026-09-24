import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Bisimulation

import Signatures.BranchingBisimilarity
import Signatures.Signature
import Signatures.Proofs.Signature_Proofs

-- Contract pin: fails to compile if `IsStable.bisimilarity`'s signature drifts.
example (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => StrongSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    Cslib.LTS.Bisimilarity lts lts s₁ s₂ :=
  IsStable.bisimilarity lts partition h hRel

-- Contract pin: fails to compile if `StrongFixPoint.bisimilarity`'s signature drifts.
example (lts : Cslib.LTS State Label)
    {s s' : State} (h : StrongFixPoint lts s s') :
    Cslib.LTS.Bisimilarity lts lts s s' :=
  StrongFixPoint.bisimilarity lts h

-- Contract pin: fails to compile if `Cslib.LTS.Bisimilarity.strongFixPoint`'s signature drifts.
example (lts : Cslib.LTS State Label)
    {s s' : State} (h : Cslib.LTS.Bisimilarity lts lts s s') :
    StrongFixPoint lts s s' :=
  Cslib.LTS.Bisimilarity.strongFixPoint lts h

-- Contract pin: fails to compile if `IsStable.branchingBisimilarity`'s signature drifts.
example [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => BranchingSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ :=
  IsStable.branchingBisimilarity lts partition h hRel
