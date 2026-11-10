module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import MercLib.Theory.LTS.BranchingBisimilarity
public import MercLib.Theory.Signatures.Signature
public import MercLib.Theory.LTS.Proofs.BranchingBisimilarity_Transitivity_Proofs
import all MercLib.Theory.LTS.Proofs.BranchingBisimilarity_Transitivity_Proofs

@[expose] public section SignatureProofs

namespace MercLib.Signatures

open MercLib.LTS

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The "headline"
theorems below are stated in `Challenges/Signatures.lean` (human-vetted). -/

-- If a partition is stable w.r.t. the StrongSignature (i.e., it is a fixed point of refinement),
-- then same-block states form a bisimulation. This is the classical partition refinement result.
private theorem IsStable.isHomBisimulation (lts : Cslib.LTS State Label)
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
private theorem IsStable.isHomBranchingBisimulation [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => BranchingSignature lts s partition) partition) :
    IsHomBranchingBisimulation lts (fun s s' => partition s = partition s') := by
  unfold IsHomBranchingBisimulation IsBranchingBisimulation
  intro s₁ s₂ hRel μ
  constructor
  · intro t₁ hTr₁
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₁ = partition s₁
    · -- Inert τ-step: mimic by doing nothing.
      exact Or.inl ⟨hInert.1, hInert.2.trans hRel⟩
    · -- Non-inert: the triple is in the signature, transport it via stability.
      have hmem : (partition s₁, μ, partition t₁) ∈ BranchingSignature lts s₁ partition :=
        ⟨s₁, t₁, Relation.ReflTransGen.refl, Or.inl hTr₁, rfl, rfl⟩
      rw [show BranchingSignature lts s₁ partition = BranchingSignature lts s₂ partition from h s₁ s₂ hRel] at hmem
      obtain ⟨u, u', hτ, hTr | ⟨hμ, rfl⟩, hβ, hα⟩ := hmem
      · exact Or.inr ⟨u, u', (Cslib.LTS.sTr_τSTr_iff lts).mpr hτ, hTr, hβ.symm, hα.symm⟩
      · exact absurd ⟨hμ, hα.symm.trans hβ⟩ hInert
  · intro t₂ hTr₂
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₂ = partition s₂
    · exact Or.inl ⟨hInert.1, hRel.trans hInert.2.symm⟩
    · have hmem : (partition s₁, μ, partition t₂) ∈ BranchingSignature lts s₂ partition :=
        ⟨s₂, t₂, Relation.ReflTransGen.refl, Or.inl hTr₂, hRel.symm, rfl⟩
      rw [← show BranchingSignature lts s₁ partition = BranchingSignature lts s₂ partition from h s₁ s₂ hRel] at hmem
      obtain ⟨u, u', hτ, hTr | ⟨hμ, rfl⟩, hβ, hα⟩ := hmem
      · exact Or.inr ⟨u, u', (Cslib.LTS.sTr_τSTr_iff lts).mpr hτ, hTr, hβ.trans hRel, hα⟩
      · exact absurd ⟨hμ, hα.symm.trans (hβ.trans hRel)⟩ hInert

-- If a partition is stable w.r.t. SplitSignature, then same-block states form a bisimulation.
-- Proof mirrors IsStable.isHomBisimulation but uses congr_fun to apply the per-label equality.
private theorem IsStable.isHomBisimulation_ofSplit (lts : Cslib.LTS State Label)
    (partition : State → Block) (h : IsStable (fun s => SplitSignature lts s partition) partition) :
    Cslib.LTS.IsHomBisimulation lts (fun s s' => partition s = partition s') := by
  intro s₁ s₂ hRel μ
  have hSigEq : SplitSignature lts s₁ partition = SplitSignature lts s₂ partition := h s₁ s₂ hRel
  constructor
  · intro t₁ hTr₁
    have hmem : partition t₁ ∈ SplitSignature lts s₁ partition μ := ⟨t₁, hTr₁, rfl⟩
    rw [congr_fun hSigEq μ] at hmem
    obtain ⟨t₂, hTr₂, hEq⟩ := hmem
    exact ⟨t₂, hTr₂, hEq.symm⟩
  · intro t₂ hTr₂
    have hmem : partition t₂ ∈ SplitSignature lts s₂ partition μ := ⟨t₂, hTr₂, rfl⟩
    rw [← congr_fun hSigEq μ] at hmem
    obtain ⟨t₁, hTr₁, hEq⟩ := hmem
    exact ⟨t₁, hTr₁, hEq⟩

-- Same-block states under a SplitSignature-stable partition are bisimilar.
private theorem IsStable.bisimilarity_ofSplit (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => SplitSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    Cslib.LTS.Bisimilarity lts lts s₁ s₂ :=
  ⟨fun a b => partition a = partition b, hRel, IsStable.isHomBisimulation_ofSplit lts partition h⟩

-- Same-block states under a StrongSignature-stable partition are bisimilar: bisimilarity is the
-- largest bisimulation, and the same-block relation is a bisimulation by IsStable.isHomBisimulation.
theorem IsStable.bisimilarity (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => StrongSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    Cslib.LTS.Bisimilarity lts lts s₁ s₂ :=
  ⟨fun a b => partition a = partition b, hRel, IsStable.isHomBisimulation lts partition h⟩

-- The coarsest StrongSignature-stable partition is contained in bisimilarity: FixPoint-related
-- states are bisimilar. Partition-independent statement — the witness partition is existentially
-- bound in StrongFixPoint.
theorem StrongFixPoint.bisimilarity (lts : Cslib.LTS State Label)
    {s s' : State} (h : StrongFixPoint lts s s') :
    Cslib.LTS.Bisimilarity lts lts s s' := by
  obtain ⟨_, partition, hStable, hEq⟩ := h
  exact IsStable.bisimilarity lts partition hStable hEq

-- Reverse direction (strong): bisimilarity implies StrongFixPoint. We use the bisim quotient
-- as the witness partition. Together with StrongFixPoint.bisimilarity, this makes
-- StrongFixPoint = Bisimilarity.
theorem strongFixPoint (lts : Cslib.LTS State Label)
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

-- SplitFixPoint implies bisimilarity.
private theorem SplitFixPoint.bisimilarity (lts : Cslib.LTS State Label)
    {s s' : State} (h : SplitFixPoint lts s s') :
    Cslib.LTS.Bisimilarity lts lts s s' := by
  obtain ⟨_, partition, hStable, hEq⟩ := h
  exact IsStable.bisimilarity_ofSplit lts partition hStable hEq

-- Reverse direction (split): bisimilarity implies SplitFixPoint. Uses the bisim quotient as the
-- witness partition, with SplitSignature stability proved via funext + set extensionality.
-- Together with SplitFixPoint.bisimilarity, this makes SplitFixPoint = Bisimilarity.
private theorem splitFixPoint (lts : Cslib.LTS State Label)
    {s s' : State} (h : Cslib.LTS.Bisimilarity lts lts s s') :
    SplitFixPoint lts s s' := by
  let bisimSetoid : Setoid State :=
    ⟨fun a b => Cslib.LTS.Bisimilarity lts lts a b, Cslib.LTS.HomBisimilarity.eqv⟩
  refine ⟨Quotient bisimSetoid, Quotient.mk bisimSetoid, ?_, ?_⟩
  · intro a b hab
    have hAB : Cslib.LTS.Bisimilarity lts lts a b := Quotient.exact hab
    funext μ; ext α
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

-- Membership bridge: (μ, α) is in the strong signature iff α is in the split signature at μ.
-- The two presentations encode the same transitions; this is the definitional connection.
private theorem StrongSignature_mem_iff_SplitSignature (lts : Cslib.LTS State Label) (s : State)
    (partition : State → Block) {μ : Label} {α : Block} :
    (μ, α) ∈ StrongSignature lts s partition ↔ α ∈ SplitSignature lts s partition μ :=
  Iff.rfl

-- Stability w.r.t. SplitSignature iff stability w.r.t. StrongSignature: direct proof via the
-- membership bridge, without going through bisimilarity.
private theorem IsStable_SplitSignature_iff_StrongSignature (lts : Cslib.LTS State Label)
    (partition : State → Block) :
    IsStable (fun s => SplitSignature lts s partition) partition ↔
    IsStable (fun s => StrongSignature lts s partition) partition := by
  simp only [IsStable]
  constructor
  · intro h s s' heq
    ext ⟨μ, α⟩
    exact (StrongSignature_mem_iff_SplitSignature lts s partition).trans
      ((Set.ext_iff.mp (congr_fun (h s s' heq) μ) α).trans
       (StrongSignature_mem_iff_SplitSignature lts s' partition).symm)
  · intro h s s' heq
    funext μ; ext α
    exact (StrongSignature_mem_iff_SplitSignature lts s partition).symm.trans
      ((Set.ext_iff.mp (h s s' heq) (μ, α)).trans
       (StrongSignature_mem_iff_SplitSignature lts s' partition))

-- SplitFixPoint and StrongFixPoint are equivalent: direct proof via stability equivalence,
-- witnessing that the same partition works for both.
private theorem SplitFixPoint_iff_StrongFixPoint (lts : Cslib.LTS State Label) {s s' : State} :
    SplitFixPoint lts s s' ↔ StrongFixPoint lts s s' := by
  constructor
  · rintro ⟨Block, partition, hStable, hEq⟩
    exact ⟨Block, partition,
      (IsStable_SplitSignature_iff_StrongSignature lts partition).mp hStable, hEq⟩
  · rintro ⟨Block, partition, hStable, hEq⟩
    exact ⟨Block, partition,
      (IsStable_SplitSignature_iff_StrongSignature lts partition).mpr hStable, hEq⟩

-- SplitFixPoint and StrongFixPoint are equal as binary relations: the split-signature fixpoint
-- characterizes exactly the same equivalence as the strong-signature fixpoint.
private theorem SplitFixPoint_eq_StrongFixPoint (lts : Cslib.LTS State Label) :
    SplitFixPoint lts = StrongFixPoint lts :=
  funext fun _ => funext fun _ => propext (SplitFixPoint_iff_StrongFixPoint lts)

-- Same-block states under a BranchingSignature-stable partition are branching bisimilar.
theorem IsStable.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (partition : State → Block)
    (h : IsStable (fun s => BranchingSignature lts s partition) partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ :=
  ⟨fun a b => partition a = partition b, hRel, IsStable.isHomBranchingBisimulation lts partition h⟩

-- The coarsest BranchingSignature-stable partition is contained in branching bisimilarity.
theorem BranchingFixPoint.branchingBisimilarity [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {s s' : State} (h : BranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' := by
  obtain ⟨_, partition, hStable, hEq⟩ := h
  exact IsStable.branchingBisimilarity lts partition hStable hEq

-- Reverse direction (branching): branching bisimilarity implies BranchingFixPoint, with the
-- ≈br-quotient as the witness partition.
theorem BranchingBisimilarity.branchingFixPoint [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {s s' : State} (h : BranchingBisimilarity lts s s') :
    BranchingFixPoint lts s s' := by
  let brSetoid : Setoid State :=
    ⟨fun a b => BranchingBisimilarity lts a b,
     ⟨BranchingBisimilarity.refl,
      fun {_ _} => BranchingBisimilarity.symm,
      fun {_ _ _} => BranchingBisimilarity.trans⟩⟩
  refine ⟨Quotient brSetoid, Quotient.mk brSetoid, ?_, ?_⟩
  · -- Stability: branching-bisimilar states have equal BranchingSignatures w.r.t. the quotient.
    intro a b hab
    have hAB : BranchingBisimilarity lts a b := Quotient.exact hab
    -- Helper: same direction once, then mirror via symmetry of ≈br.
    have aux : ∀ {x y : State}, BranchingBisimilarity lts x y →
        BranchingSignature lts x (Quotient.mk brSetoid) ⊆
          BranchingSignature lts y (Quotient.mk brSetoid) := by
      rintro x y hxy ⟨β, μ, α⟩ ⟨u, u', hτPath, hStep, hβEq, hαEq⟩
      obtain ⟨r, hrXY, hrBis⟩ := hxy
      -- Stutter through τ-path to find matching y-side state.
      obtain ⟨v, hPathYV, hrUV⟩ :=
        IsBranchingBisimulation.stutter hrBis hrXY hτPath
      have hUV : Quotient.mk brSetoid v = β := by
        rw [← hβEq]
        exact (Quotient.sound (s := brSetoid) ⟨r, hrUV, hrBis⟩).symm
      rcases hStep with hTr | ⟨hμτ, rfl⟩
      · -- Apply BB on (u, v) for u →μ→ u'.
        rcases (hrBis hrUV μ).1 _ hTr with ⟨hμτ, hrU'V⟩ | ⟨w, w', hSTrVw, hTrW, hrUW, hrU'W'⟩
        · -- Matched by doing nothing: the reflexive triple at v.
          refine ⟨v, v, hPathYV, Or.inr ⟨hμτ, rfl⟩, hUV, ?_⟩
          rw [← hαEq]
          exact (Quotient.sound (s := brSetoid) ⟨r, hrU'V, hrBis⟩).symm
        · -- Real τ*-prefix + μ-step on the y-side, matching the triple.
          refine ⟨w, w', ?_, Or.inl hTrW, ?_, ?_⟩
          · exact hPathYV.trans ((Cslib.LTS.sTr_τSTr_iff lts).mp hSTrVw)
          · rw [← hβEq]
            exact (Quotient.sound (s := brSetoid) ⟨r, hrUW, hrBis⟩).symm
          · rw [← hαEq]
            exact (Quotient.sound (s := brSetoid) ⟨r, hrU'W', hrBis⟩).symm
      · -- The reflexive triple of x is the reflexive triple at v.
        exact ⟨v, v, hPathYV, Or.inr ⟨hμτ, rfl⟩, hUV, hβEq.symm.trans (hαEq) ▸ hUV⟩
    exact Set.eq_of_subset_of_subset (aux hAB) (aux (BranchingBisimilarity.symm hAB))
  · exact Quotient.sound h

end MercLib.Signatures

end SignatureProofs
