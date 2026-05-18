module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Signatures.BranchingBisimilarity
public import Signatures.Signature
public import Signatures.InductiveSignatures

@[expose] public section InductiveSignaturesProofs

/-! ## Inductive signatures and branching bisimilarity for τ-loop-free LTSs

The `Sig` operator is a one-step recurrence. Its full fixed point exists when the
inert τ-relation is well-founded (no infinite τ-chains, hence no τ-loops). For such LTSs,
a partition stable under the fixed point induces a branching bisimulation.
-/

/-- Witness extraction for a fixed point of `Sig` under τ-loop-freedom.

If `sigFn` is a fixed point of `Sig` and the LTS is τ-loop-free, then every non-inert element
`(μ, Sum.inl α) ∈ sigFn s` is *realized* by an actual transition: there is an inert τ*-path
`s →τ*→ s'` (staying in `partition s`'s block) followed by a transition `s' →μ→ t` with
`partition t = α`.

Proof: well-founded induction on `s` via the τ-relation. If `Sig` delegates at `s` (to some
inert τ-successor `s_chosen`), the element lies in `sigFn s_chosen`; apply the IH and prepend
the τ-step. Otherwise `sigFn s = PreSig s`, and the first PreSig branch supplies the witness
directly (the inert-τ branch is excluded because it is tagged `Sum.inr`). -/
theorem Sig.exists_witness_of_inl [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) (partition : State → Block)
    {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s) :
    ∀ s μ α, (μ, Sum.inl α) ∈ sigFn s →
      ∃ s' t, lts.τSTr s s' ∧ partition s' = partition s ∧
              lts.Tr s' μ t ∧ partition t = α := by
  intro s
  induction s using WellFounded.induction hWF with
  | _ s ih =>
    intro μ α hmem
    by_cases hDeleg : ∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ partition s = partition s' ∧
                PreSig lts partition sigHash s ⊆
                  sigFn s' ∪ {(Cslib.HasTau.τ, Sum.inr (sigHash s'))}
    · -- Delegation case: sigFn s = sigFn hDeleg.choose
      have hEq : sigFn s = sigFn hDeleg.choose := by
        rw [hFix s, Sig, dif_pos hDeleg]
      rw [hEq] at hmem
      obtain ⟨hτ, hπ, _⟩ := hDeleg.choose_spec
      obtain ⟨s', t, hτPath, hπs', hStep, hπt⟩ := ih hDeleg.choose hτ μ α hmem
      exact ⟨s', t, Relation.ReflTransGen.head hτ hτPath, hπs'.trans hπ.symm, hStep, hπt⟩
    · -- No-delegation case: sigFn s = PreSig s
      have hEq : sigFn s = PreSig lts partition sigHash s := by
        rw [hFix s, Sig, dif_neg hDeleg]
      rw [hEq] at hmem
      rcases hmem with ⟨a, s', hStep, _, hPair⟩ | ⟨s', _, _, hPair⟩
      · -- Visible/non-inert PreSig branch — direct witness.
        obtain ⟨rfl, hSum⟩ := Prod.mk.inj hPair
        cases Sum.inl.inj hSum
        exact ⟨s, s', Relation.ReflTransGen.refl, rfl, hStep, rfl⟩
      · -- Inert-τ PreSig branch is tagged Sum.inr, contradicting Sum.inl.
        exact nomatch (Prod.mk.inj hPair).2

/-- If a partition is stable w.r.t. a fixed point `sigFn` of the inductive `Sig` operator
(in a τ-loop-free LTS), then same-block states form a branching bisimulation.

The argument: for inert τ-moves the matching state does nothing (Or.inl). For non-inert moves
on the left, the witness `(μ, Sum.inl (partition t)) ∈ sigFn s₁` lifts via stability to
`sigFn s₂`; the previous lemma realizes it as an inert τ*-path on the right followed by a
matching transition, giving Or.inr. The symmetric direction is identical. -/
theorem IsStable.isHomBranchingBisimulation_inductive [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    (hStable : IsStable sigFn partition) :
    IsHomBranchingBisimulation lts (fun s s' => partition s = partition s') := by
  -- Inert/non-inert membership helper for the PreSig left branch.
  have hPreSigMem : ∀ {s t μ}, lts.Tr s μ t → (μ ≠ Cslib.HasTau.τ ∨ partition s ≠ partition t) →
      (μ, Sum.inl (partition t)) ∈ PreSig lts partition sigHash s := by
    intro s t μ hTr hSide
    exact Or.inl ⟨μ, t, hTr, hSide, rfl⟩
  -- The PreSig element survives the (possible) delegation step: it lands in sigFn s itself.
  have hInSigFn : ∀ {s t μ}, lts.Tr s μ t → (μ ≠ Cslib.HasTau.τ ∨ partition s ≠ partition t) →
      (μ, Sum.inl (partition t)) ∈ sigFn s := by
    intro s t μ hTr hSide
    have hMem : (μ, Sum.inl (partition t)) ∈ PreSig lts partition sigHash s :=
      hPreSigMem hTr hSide
    by_cases hDeleg : ∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ partition s = partition s' ∧
                PreSig lts partition sigHash s ⊆
                  sigFn s' ∪ {(Cslib.HasTau.τ, Sum.inr (sigHash s'))}
    · have hEq : sigFn s = sigFn hDeleg.choose := by
        rw [hFix s, Sig, dif_pos hDeleg]
      rw [hEq]
      obtain ⟨_, _, hSub⟩ := hDeleg.choose_spec
      rcases hSub hMem with h | h
      · exact h
      · exact nomatch (Prod.mk.inj (Set.mem_singleton_iff.mp h)).2
    · have hEq : sigFn s = PreSig lts partition sigHash s := by
        rw [hFix s, Sig, dif_neg hDeleg]
      rw [hEq]; exact hMem
  intro s₁ s₂ hRel μ
  refine ⟨?_, ?_⟩
  · intro t₁ hTr₁
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₁ = partition s₁
    · exact Or.inl ⟨hInert.1, hInert.2.trans hRel⟩
    · have hSide : μ ≠ Cslib.HasTau.τ ∨ partition s₁ ≠ partition t₁ := by
        rcases Classical.em (μ = Cslib.HasTau.τ) with hμ | hμ
        · exact Or.inr fun h => hInert ⟨hμ, h.symm⟩
        · exact Or.inl hμ
      have hMem1 : (μ, Sum.inl (partition t₁)) ∈ sigFn s₁ := hInSigFn hTr₁ hSide
      have hMem2 : (μ, Sum.inl (partition t₁)) ∈ sigFn s₂ := by
        rw [← hStable s₁ s₂ hRel]; exact hMem1
      obtain ⟨s₂', t₂, hτPath, hπs₂', hStep, hπt₂⟩ :=
        Sig.exists_witness_of_inl hWF partition sigHash sigFn hFix s₂ μ (partition t₁) hMem2
      refine Or.inr ⟨s₂', t₂, (Cslib.LTS.sTr_τSTr lts).mpr hτPath, hStep, ?_, hπt₂.symm⟩
      exact hRel.trans hπs₂'.symm
  · intro t₂ hTr₂
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₂ = partition s₂
    · exact Or.inl ⟨hInert.1, hRel.trans hInert.2.symm⟩
    · have hSide : μ ≠ Cslib.HasTau.τ ∨ partition s₂ ≠ partition t₂ := by
        rcases Classical.em (μ = Cslib.HasTau.τ) with hμ | hμ
        · exact Or.inr fun h => hInert ⟨hμ, h.symm⟩
        · exact Or.inl hμ
      have hMem2 : (μ, Sum.inl (partition t₂)) ∈ sigFn s₂ := hInSigFn hTr₂ hSide
      have hMem1 : (μ, Sum.inl (partition t₂)) ∈ sigFn s₁ := by
        rw [hStable s₁ s₂ hRel]; exact hMem2
      obtain ⟨s₁', t₁, hτPath, hπs₁', hStep, hπt₁⟩ :=
        Sig.exists_witness_of_inl hWF partition sigHash sigFn hFix s₁ μ (partition t₂) hMem1
      refine Or.inr ⟨s₁', t₁, (Cslib.LTS.sTr_τSTr lts).mpr hτPath, hStep, hπs₁'.trans hRel, hπt₁⟩

/-- Same-block states under a Sig-fixed-point stable partition (in a τ-loop-free LTS) are
branching bisimilar. -/
theorem IsStable.branchingBisimilarity_inductive [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    (hStable : IsStable sigFn partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ :=
  ⟨fun a b => partition a = partition b, hRel,
    IsStable.isHomBranchingBisimulation_inductive hWF partition sigHash sigFn hFix hStable⟩

end InductiveSignaturesProofs
