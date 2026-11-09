import MercLib.Theory.LTS.BranchingBisimilarity
import MercLib.Theory.Signatures.Signature
import MercLib.Theory.Signatures.InductiveSignatures

/-!
# Comparator challenge: signature-based partition refinement (human-vetted)

The headline theorems of `MercLib/Theory/Signatures/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Signatures

open MercLib.LTS

/-! ## Strong signatures -/

/-- **Stable partitions are bisimulations (strong).** If a partition (`State → Block`) of an LTS
is stable for the strong signature (states in one block have the same signature: the set of
`(label, target block)` pairs), then any two states in the same block are strongly bisimilar. -/
theorem IsStable.bisimilarity (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => StrongSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    Cslib.LTS.Bisimilarity lts lts s₁ s₂ := sorry

/-- **The strong signature fixed point is sound.** States related by the strong signature fixed
point (`StrongFixPoint`) of an LTS are strongly bisimilar. -/
theorem StrongFixPoint.bisimilarity (lts : Cslib.LTS State Label)
    {s s' : State} (h : StrongFixPoint lts s s') :
    Cslib.LTS.Bisimilarity lts lts s s' := sorry

/-- **The strong signature fixed point is complete.** Strongly bisimilar states of an LTS are
related by `StrongFixPoint`. With `StrongFixPoint.bisimilarity`, the fixed point is exactly strong
bisimilarity. -/
theorem strongFixPoint (lts : Cslib.LTS State Label)
    {s s' : State} (h : Cslib.LTS.Bisimilarity lts lts s s') :
    StrongFixPoint lts s s' := sorry

/-! ## Branching signatures -/

/-- **Stable partitions are branching bisimulations.** If a partition of an LTS with a silent
action is stable for the branching signature, then any two states in the same block are branching
bisimilar. -/
theorem IsStable.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => BranchingSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ := sorry

/-- **The branching signature fixed point is sound.** In an LTS with a silent action, states
related by `BranchingFixPoint` are branching bisimilar. -/
theorem BranchingFixPoint.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {s s' : State} (h : BranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' := sorry

/-- **The branching signature fixed point is complete.** In an LTS with a silent action, branching
bisimilar states are related by `BranchingFixPoint`. With the soundness theorem, the fixed point is
exactly branching bisimilarity. -/
theorem BranchingBisimilarity.branchingFixPoint [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {s s' : State} (h : BranchingBisimilarity lts s s') :
    BranchingFixPoint lts s s' := sorry

/-! ## Inductive (τ-loop-free) branching signatures -/

/-- **Stable partitions for the inductive signature are branching bisimulations.** Let `lts` be
τ-loop-free and `sigFn` a fixed point of the inductive branching signature `Sig` (with hash
`sigHash`) that is stable for a partition. Then any two states in the same block are branching
bisimilar. -/
theorem IsStable.branchingBisimilarity_inductive [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    (hStable : IsStable sigFn partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ := sorry

/-- **The inductive branching fixed point is sound.** In a τ-loop-free LTS, states related by
`InductiveBranchingFixPoint` are branching bisimilar. -/
theorem InductiveBranchingFixPoint.branchingBisimilarity [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s s' : State} (h : InductiveBranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' := sorry

/-- **The inductive branching fixed point is complete.** In a τ-loop-free LTS, branching
bisimilar states are related by `InductiveBranchingFixPoint`. With the soundness theorem, that
fixed point is exactly branching bisimilarity. -/
theorem BranchingBisimilarity.inductiveBranchingFixPoint.{u, v}
    {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s₁ s₂ : State} (h : BranchingBisimilarity lts s₁ s₂) :
    InductiveBranchingFixPoint lts s₁ s₂ := sorry

end MercLib.Signatures
