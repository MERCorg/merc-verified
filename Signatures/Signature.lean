module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
import Signatures.BranchingBisimilarity

-- Signatures are a way to capture the observable behavior of a state in an LTS.
def StrongSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block): Set (Label × Block)
  := { (μ, α) | ∃ s', lts.Tr s μ s' ∧ partition s' = α }

-- Refines the given LTS and partition based on the signature function
def Refine (lts : Cslib.LTS State Label) (partition : State → Block): (State → Set (Label × Block)) :=
  fun s => StrongSignature lts s partition

-- Branching signature: for each state, the set of (intermediate-block, label, successor-block) triples
-- reachable via τ-steps followed by a single transition. The intermediate block is needed to
-- verify the branching bisimulation condition r s1 s2' (the state reached before the matching step).
def BranchingSignature [Cslib.HasTau Label] (lts : Cslib.LTS State Label) (s : State)
    (partition : State → Block) : Set (Block × Label × Block) :=
  { (β, μ, α) | ∃ s' s'', lts.τSTr s s' ∧ lts.Tr s' μ s'' ∧ partition s' = β ∧ partition s'' = α }

-- A partition is stable w.r.t. a signature if same-block states always have the same signature
def IsStable (sig : State → Sig) (partition : State → Block) : Prop :=
  ∀ s s', partition s = partition s' → sig s = sig s'

-- The coarsest partition stable w.r.t. a signature: states are equivalent iff
-- no stable partition separates them
def FixPoint (sig : State → Sig) : State → State → Prop :=
  fun s s' => ∀ (Block : Type) (partition : State → Block), IsStable sig partition → partition s = partition s'

-- Homogeneous branching bisimulation: the single-LTS variant of LTS.IsBranchingBisimulation
abbrev IsHomBranchingBisimulation [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (r : State → State → Prop) : Prop :=
  LTS.IsBranchingBisimulation lts r

-- If a partition is stable w.r.t. the StrongSignature (i.e., it is a fixed point of refinement),
-- then same-block states form a bisimulation. This is the classical partition refinement result.
theorem IsStable.isHomBisimulation (lts : Cslib.LTS State Label)
    (partition : State → Block) (h : IsStable (Refine lts partition) partition) :
    Cslib.LTS.IsHomBisimulation lts (fun s s' => partition s = partition s') := by
  intro s₁ s₂ hRel μ
  have hSigEq : Refine lts partition s₁ = Refine lts partition s₂ := h s₁ s₂ hRel
  constructor
  · intro t₁ hTr₁
    have hmem : (μ, partition t₁) ∈ Refine lts partition s₁ := ⟨t₁, hTr₁, rfl⟩
    rw [hSigEq] at hmem
    obtain ⟨t₂, hTr₂, hEq⟩ := hmem
    exact ⟨t₂, hTr₂, hEq.symm⟩
  · intro t₂ hTr₂
    have hmem : (μ, partition t₂) ∈ Refine lts partition s₂ := ⟨t₂, hTr₂, rfl⟩
    rw [← hSigEq] at hmem
    obtain ⟨t₁, hTr₁, hEq⟩ := hmem
    exact ⟨t₁, hTr₁, hEq⟩

-- If a partition is stable w.r.t. the BranchingSignature (i.e., it is a fixed point of branching
-- refinement), then same-block states form a branching bisimulation.
-- Key: BranchingSignature encodes (intermediate-block, label, successor-block) triples reachable
-- via τ*-paths, so stability directly supplies the τ-prefix and matching transition required by
-- the branching bisimulation condition.
theorem IsStable.isHomBranchingBisimulation [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => BranchingSignature lts s partition) partition) :
    IsHomBranchingBisimulation lts (fun s s' => partition s = partition s') := by
  unfold IsHomBranchingBisimulation LTS.IsBranchingBisimulation
  intro s₁ s₂ hRel μ
  constructor
  · intro t₁ hTr₁
    -- (partition s₁, μ, partition t₁) is in s₁'s signature via the reflexive τ-path
    have hmem : (partition s₁, μ, partition t₁) ∈ BranchingSignature lts s₁ partition :=
      ⟨s₁, t₁, Relation.ReflTransGen.refl, hTr₁, rfl, rfl⟩
    rw [show BranchingSignature lts s₁ partition = BranchingSignature lts s₂ partition from h s₁ s₂ hRel] at hmem
    obtain ⟨u, u', hτ, hTr, hβ, hα⟩ := hmem
    -- s₂ -τ*-> u with partition u = partition s₁; u -μ-> u' with partition u' = partition t₁
    exact Or.inr ⟨u, u', (Cslib.LTS.sTr_τSTr lts).mpr hτ, hTr, hβ.symm, hα.symm⟩
  · intro t₂ hTr₂
    -- Use partition s₁ = partition s₂ to anchor the element in s₂'s signature
    have hmem : (partition s₁, μ, partition t₂) ∈ BranchingSignature lts s₂ partition :=
      ⟨s₂, t₂, Relation.ReflTransGen.refl, hTr₂, hRel.symm, rfl⟩
    rw [← show BranchingSignature lts s₁ partition = BranchingSignature lts s₂ partition from h s₁ s₂ hRel] at hmem
    obtain ⟨u, u', hτ, hTr, hβ, hα⟩ := hmem
    exact Or.inr ⟨u, u', (Cslib.LTS.sTr_τSTr lts).mpr hτ, hTr, hβ.trans hRel, hα⟩

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp
