module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
import Signatures.BranchingBisimilarity

-- Signatures are a way to capture the observable behavior of a state in an LTS.
def StrongSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block): Set (Label × Block)
  := { (μ, α) | ∃ s', lts.Tr s μ s' ∧ partition s' = α }

-- Branching signature: for each state, the set of (intermediate-block, label, successor-block) triples
-- reachable via τ-steps followed by a single non-inert transition. The intermediate block is needed
-- to verify the branching bisimulation condition r s1 s2' (the state reached before the matching
-- step). Inert τ-transitions (μ = τ with α = β) are excluded so that branching-bisimilar states
-- have equal signatures, making the bisim-class partition stable.
def BranchingSignature [Cslib.HasTau Label] (lts : Cslib.LTS State Label) (s : State)
    (partition : State → Block) : Set (Block × Label × Block) :=
  { (β, μ, α) | ∃ s' s'', lts.τSTr s s' ∧ lts.Tr s' μ s'' ∧ partition s' = β ∧ partition s'' = α
                ∧ (μ ≠ Cslib.HasTau.τ ∨ α ≠ β) }

-- A partition is stable w.r.t. a signature if same-block states always have the same signature
def IsStable (sig : State → Sig) (partition : State → Block) : Prop :=
  ∀ s s', partition s = partition s' → sig s = sig s'

-- The coarsest partition stable w.r.t. the StrongSignature: states are related iff some stable
-- partition keeps them in the same block. (Existential form — the previous ∀ form was degenerate,
-- collapsing to Eq via the always-stable discrete partition.) `Block` shares State's universe so
-- witnesses like `Quotient ...` fit.
def StrongFixPoint.{u, v} {State : Type u} {Label : Type v} (lts : Cslib.LTS State Label) :
    State → State → Prop :=
  fun s s' => ∃ (Block : Type u) (partition : State → Block),
    IsStable (fun x => StrongSignature lts x partition) partition ∧ partition s = partition s'

-- The coarsest partition stable w.r.t. the BranchingSignature (inert-τ excluded).
def BranchingFixPoint.{u, v} {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    (lts : Cslib.LTS State Label) : State → State → Prop :=
  fun s s' => ∃ (Block : Type u) (partition : State → Block),
    IsStable (fun x => BranchingSignature lts x partition) partition ∧ partition s = partition s'

-- Homogeneous branching bisimulation: the single-LTS variant of LTS.IsBranchingBisimulation
abbrev IsHomBranchingBisimulation [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (r : State → State → Prop) : Prop :=
  LTS.IsBranchingBisimulation lts r

-- If a partition is stable w.r.t. the StrongSignature (i.e., it is a fixed point of refinement),
-- then same-block states form a bisimulation. This is the classical partition refinement result.
theorem IsStable.isHomBisimulation (lts : Cslib.LTS State Label)
    (partition : State → Block) (h : IsStable (fun s => StrongSignature lts s partition) partition) :
    Cslib.LTS.IsHomBisimulation lts (fun s s' => partition s = partition s') := by
  intro s₁ s₂ hRel μ
  have hSigEq : StrongSignature lts s₁ partition = StrongSignature lts s₂ partition := h s₁ s₂ hRel
  constructor
  · intro t₁ hTr₁
    have hmem : (μ, partition t₁) ∈ StrongSignature lts s₁ partition := ⟨t₁, hTr₁, rfl⟩
    rw [hSigEq] at hmem
    obtain ⟨t₂, hTr₂, hEq⟩ := hmem
    exact ⟨t₂, hTr₂, hEq.symm⟩
  · intro t₂ hTr₂
    have hmem : (μ, partition t₂) ∈ StrongSignature lts s₂ partition := ⟨t₂, hTr₂, rfl⟩
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
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₁ = partition s₁
    · -- Inert τ-step: mimic by doing nothing.
      exact Or.inl ⟨hInert.1, hInert.2.trans hRel⟩
    · -- Non-inert: the triple is in the signature, transport it via stability.
      have hNonInert : μ ≠ Cslib.HasTau.τ ∨ partition t₁ ≠ partition s₁ := by tauto
      have hmem : (partition s₁, μ, partition t₁) ∈ BranchingSignature lts s₁ partition :=
        ⟨s₁, t₁, Relation.ReflTransGen.refl, hTr₁, rfl, rfl, hNonInert⟩
      rw [show BranchingSignature lts s₁ partition = BranchingSignature lts s₂ partition from h s₁ s₂ hRel] at hmem
      obtain ⟨u, u', hτ, hTr, hβ, hα, _⟩ := hmem
      exact Or.inr ⟨u, u', (Cslib.LTS.sTr_τSTr lts).mpr hτ, hTr, hβ.symm, hα.symm⟩
  · intro t₂ hTr₂
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₂ = partition s₂
    · exact Or.inl ⟨hInert.1, hRel.trans hInert.2.symm⟩
    · have hNonInert : μ ≠ Cslib.HasTau.τ ∨ partition t₂ ≠ partition s₁ := by
        rcases (Classical.em (μ = Cslib.HasTau.τ)) with hμ | hμ
        · right
          intro heq
          exact hInert ⟨hμ, heq.trans hRel⟩
        · exact Or.inl hμ
      have hmem : (partition s₁, μ, partition t₂) ∈ BranchingSignature lts s₂ partition :=
        ⟨s₂, t₂, Relation.ReflTransGen.refl, hTr₂, hRel.symm, rfl, hNonInert⟩
      rw [← show BranchingSignature lts s₁ partition = BranchingSignature lts s₂ partition from h s₁ s₂ hRel] at hmem
      obtain ⟨u, u', hτ, hTr, hβ, hα, _⟩ := hmem
      exact Or.inr ⟨u, u', (Cslib.LTS.sTr_τSTr lts).mpr hτ, hTr, hβ.trans hRel, hα⟩

-- Same-block states under a StrongSignature-stable partition are bisimilar: bisimilarity is the
-- largest bisimulation, and the same-block relation is a bisimulation by IsStable.isHomBisimulation.
theorem IsStable.bisimilarity (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => StrongSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    Cslib.LTS.Bisimilarity lts lts s₁ s₂ :=
  ⟨fun a b => partition a = partition b, hRel, h.isHomBisimulation lts partition⟩

-- Same-block states under a BranchingSignature-stable partition are branching bisimilar.
theorem IsStable.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => BranchingSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ :=
  ⟨fun a b => partition a = partition b, hRel, h.isHomBranchingBisimulation lts partition⟩

-- The coarsest StrongSignature-stable partition is contained in bisimilarity: FixPoint-related
-- states are bisimilar. Partition-independent statement — the witness partition is existentially
-- bound in StrongFixPoint.
theorem StrongFixPoint.bisimilarity (lts : Cslib.LTS State Label)
    {s s' : State} (h : StrongFixPoint lts s s') :
    Cslib.LTS.Bisimilarity lts lts s s' := by
  obtain ⟨_, partition, hStable, hEq⟩ := h
  exact IsStable.bisimilarity lts partition hStable hEq

-- The coarsest BranchingSignature-stable partition is contained in branching bisimilarity.
theorem BranchingFixPoint.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {s s' : State} (h : BranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' := by
  obtain ⟨_, partition, hStable, hEq⟩ := h
  exact IsStable.branchingBisimilarity lts partition hStable hEq

-- Reverse direction (strong): bisimilarity implies StrongFixPoint. We use the bisim quotient
-- as the witness partition. Together with StrongFixPoint.bisimilarity, this makes
-- StrongFixPoint = Bisimilarity.
theorem Cslib.LTS.Bisimilarity.strongFixPoint (lts : Cslib.LTS State Label)
    {s s' : State} (h : Cslib.LTS.Bisimilarity lts lts s s') :
    StrongFixPoint lts s s' := by
  let bisimSetoid : Setoid State :=
    ⟨fun a b => Cslib.LTS.Bisimilarity lts lts a b, Cslib.LTS.HomBisimilarity.eqv⟩
  refine ⟨Quotient bisimSetoid, Quotient.mk bisimSetoid, ?_, ?_⟩
  · -- Stability: bisimilar states have equal StrongSignatures w.r.t. the bisim quotient.
    intro a b hab
    have hAB : Cslib.LTS.Bisimilarity lts lts a b := Quotient.exact hab
    ext ⟨μ, α⟩
    constructor
    · rintro ⟨c, hTr, hC⟩
      obtain ⟨r, hrAB, hrBis⟩ := hAB
      obtain ⟨d, hTrD, hrCD⟩ := (hrBis hrAB μ).1 c hTr
      have hcd : Cslib.LTS.Bisimilarity lts lts c d := ⟨r, hrCD, hrBis⟩
      exact ⟨d, hTrD, (Quotient.sound hcd).symm.trans hC⟩
    · rintro ⟨d, hTr, hD⟩
      obtain ⟨r, hrBA, hrBis⟩ := Cslib.LTS.Bisimilarity.symm hAB
      obtain ⟨c, hTrC, hrDC⟩ := (hrBis hrBA μ).1 d hTr
      have hdc : Cslib.LTS.Bisimilarity lts lts d c := ⟨r, hrDC, hrBis⟩
      exact ⟨c, hTrC, (Quotient.sound hdc).symm.trans hD⟩
  · exact Quotient.sound h
