module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation

-- Signatures are a way to capture the observable behavior of a state in an LTS.
def StrongSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block): Set (Label × Block)
  := { (μ, α) | ∃ s', lts.Tr s μ s' ∧ partition s' = α }

-- Refines the given LTS and partition based on the signature function
def Refine (lts : Cslib.LTS State Label) (partition : State → Block): (State → Set (Label × Block)) :=
  fun s => StrongSignature lts s partition

-- A partition is stable w.r.t. a signature if same-block states always have the same signature
def IsStable (sig : State → Sig) (partition : State → Block) : Prop :=
  ∀ s s', partition s = partition s' → sig s = sig s'

-- The coarsest partition stable w.r.t. a signature: states are equivalent iff
-- no stable partition separates them
def FixPoint (sig : State → Sig) : State → State → Prop :=
  fun s s' => ∀ (Block : Type) (partition : State → Block), IsStable sig partition → partition s = partition s'

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
