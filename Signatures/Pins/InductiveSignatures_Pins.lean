import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Bisimulation
import Signatures.BranchingBisimilarity
import Signatures.Signature
import Signatures.InductiveSignatures
import Signatures.Proofs.InductiveSignatures_Proofs

-- Contract pin: fails to compile if `IsStable.branchingBisimilarity_inductive`'s signature drifts.
example [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    (hStable : IsStable sigFn partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ :=
  IsStable.branchingBisimilarity_inductive hWF partition sigHash sigFn hFix hStable hRel

-- Contract pin: fails to compile if `InductiveBranchingFixPoint.branchingBisimilarity`'s
-- signature drifts.
example [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s s' : State} (h : InductiveBranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' :=
  InductiveBranchingFixPoint.branchingBisimilarity hWF h

-- Contract pin: fails to compile if `BranchingBisimilarity.inductiveBranchingFixPoint`'s
-- signature drifts.
example {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s₁ s₂ : State} (h : BranchingBisimilarity lts s₁ s₂) :
    InductiveBranchingFixPoint lts s₁ s₂ :=
  BranchingBisimilarity.inductiveBranchingFixPoint hWF h
