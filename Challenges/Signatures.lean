import MercLib.LTS.BranchingBisimilarity
import MercLib.Signatures.Signature
import MercLib.Signatures.InductiveSignatures

/-!
# Comparator challenge: signature-based partition refinement (human-vetted)

The headline theorems of `MercLib/Signatures/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Signatures

open MercLib.LTS

/-! ## Strong signatures -/

/-- States in the same block of a partition that is stable w.r.t. the strong signature are
    bisimilar. -/
theorem IsStable.bisimilarity (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => StrongSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    Cslib.LTS.Bisimilarity lts lts s₁ s₂ := sorry

/-- States related by the strong signature fixed point are bisimilar. -/
theorem StrongFixPoint.bisimilarity (lts : Cslib.LTS State Label)
    {s s' : State} (h : StrongFixPoint lts s s') :
    Cslib.LTS.Bisimilarity lts lts s s' := sorry

/-- Bisimilar states are related by the strong signature fixed point; with
    `StrongFixPoint.bisimilarity` the fixed point is exactly bisimilarity. -/
theorem strongFixPoint (lts : Cslib.LTS State Label)
    {s s' : State} (h : Cslib.LTS.Bisimilarity lts lts s s') :
    StrongFixPoint lts s s' := sorry

/-! ## Branching signatures -/

/-- States in the same block of a partition that is stable w.r.t. the branching signature are
    branching bisimilar. -/
theorem IsStable.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => BranchingSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ := sorry

/-- States related by the branching signature fixed point are branching bisimilar. -/
theorem BranchingFixPoint.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {s s' : State} (h : BranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' := sorry

/-- Branching bisimilar states are related by the branching signature fixed point; with
    `BranchingFixPoint.branchingBisimilarity` the fixed point is exactly branching bisimilarity. -/
theorem BranchingBisimilarity.branchingFixPoint [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {s s' : State} (h : BranchingBisimilarity lts s s') :
    BranchingFixPoint lts s s' := sorry

/-! ## Inductive (τ-loop-free) branching signatures -/

/-- On a τ-loop-free LTS, states in the same block of a partition that is stable w.r.t. a fixed
    point of the inductive signature `Sig` are branching bisimilar. -/
theorem IsStable.branchingBisimilarity_inductive [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    (hStable : IsStable sigFn partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ := sorry

/-- On a τ-loop-free LTS, states related by the inductive branching fixed point are branching
    bisimilar. -/
theorem InductiveBranchingFixPoint.branchingBisimilarity [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s s' : State} (h : InductiveBranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' := sorry

/-- On a τ-loop-free LTS, branching bisimilar states are related by the inductive branching fixed
    point; so that fixed point is exactly branching bisimilarity. -/
theorem BranchingBisimilarity.inductiveBranchingFixPoint.{u, v}
    {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s₁ s₂ : State} (h : BranchingBisimilarity lts s₁ s₂) :
    InductiveBranchingFixPoint lts s₁ s₂ := sorry

end MercLib.Signatures
