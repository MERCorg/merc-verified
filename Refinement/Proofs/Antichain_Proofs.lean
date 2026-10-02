module

public import Refinement.Semantics
public import Refinement.Product
public import Refinement.Antichain

open Cslib (LTS HasTau)

@[expose] public section AntichainProofs

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). -/

@[refl] theorem ProductLE.refl (p : Set State1 × State2) : ProductLE p p := ⟨rfl, le_refl _⟩

theorem ProductLE.trans {p q r : Set State1 × State2}
    (h1 : ProductLE p q) (h2 : ProductLE q r) : ProductLE p r :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- A member of an antichain is (trivially) contained in it. -/
theorem AntichainMem.self {A : Set (Set State1 × State2)} {x : Set State1 × State2}
    (hx : x ∈ A) : AntichainMem A x :=
  ⟨x, hx, .refl x⟩

/-- `AntichainMem` is monotone in the antichain argument. -/
theorem AntichainMem.mono {A A' : Set (Set State1 × State2)} (hAA' : A ⊆ A')
    {x : Set State1 × State2} (hx : AntichainMem A x) : AntichainMem A' x :=
  let ⟨y, hyA, hyx⟩ := hx
  ⟨y, hAA' hyA, hyx⟩

/-- **Lemma 5.3.** Inserting a new element into an antichain does not remove anything that was
    already contained. (The paper states this with the extra hypothesis `y ∉ A` in the
    `AntichainMem` sense, matching the only context it's ever applied in - after a failed
    membership test - but the proof below does not actually need it.) -/
theorem AntichainMem.insert_of_not_mem {A : Set (Set State1 × State2)} {x y : Set State1 × State2}
    (hx : AntichainMem A x) (_hy : ¬ AntichainMem A y) :
    AntichainMem (AntichainInsert A y) x := by
  by_cases hyx : ProductLE y x
  · exact ⟨y, Or.inl rfl, hyx⟩
  · obtain ⟨z, hzA, hzx⟩ := hx
    have hyz : ¬ ProductLE y z := fun h => hyx (h.trans hzx)
    exact ⟨z, Or.inr ⟨hzA, hyz⟩, hzx⟩

theorem normTr_isMonotone [HasTau Label] (lts : LTS State Label) :
    IsMonotoneNormalForm (NormTr lts) := by
  rintro U V a V' hUV ⟨hvis, rfl⟩
  exact ⟨{ t | ∃ s ∈ U, WeakTr lts s [a] t }, ⟨hvis, rfl⟩,
    fun t ⟨s, hs, hst⟩ => ⟨s, hUV hs, hst⟩⟩

theorem fdrNormTr_isMonotone [HasTau Label] (lts : LTS State Label) :
    IsMonotoneNormalForm (FdrNormTr lts) := by
  rintro U V a V' hUV ⟨hvis, hnd, rfl⟩
  refine ⟨{ t | ∃ s ∈ U, WeakTr lts s [a] t }, ⟨hvis, ?_, rfl⟩,
    fun t ⟨s, hs, hst⟩ => ⟨s, hUV hs, hst⟩⟩
  exact fun ⟨s, hs, hds⟩ => hnd ⟨s, hUV hs, hds⟩

/-- **Lemma 5.7**, multi-step: `L1 ⋉ L2` states ordered by `ProductLE` simulate each other's
    moves, staying ordered. Needs only `IsMonotoneNormalForm L1`, so it applies uniformly to the
    `norm`/`normfdr` products of Theorems 3.11/3.14 and 3.24. -/
theorem IsMonotoneNormalForm.simulate [HasTau Label]
    {L1 : LTS (Set State1) Label} (hmono : IsMonotoneNormalForm L1) (lts2 : LTS State2 Label)
    {p q : Set State1 × State2} (hpq : ProductLE p q) {σ : List Label} {q' : Set State1 × State2}
    (h : (product L1 lts2).MTr q σ q') :
    ∃ p', (product L1 lts2).MTr p σ p' ∧ ProductLE p' q' := by
  obtain ⟨hpq2, hpq1⟩ := hpq
  induction h generalizing p with
  | refl => exact ⟨p, .refl, hpq2, hpq1⟩
  | @stepL q μ mid μs' q' hstep _ ih =>
    rcases hstep with ⟨hτ, hmid1, hstep2⟩ | ⟨hvis, hstep1, hstep2⟩
    · obtain ⟨pmid, hpmid, hpmidle⟩ := ih (p := (p.1, mid.2)) rfl (by rw [hmid1]; exact hpq1)
      refine ⟨pmid, Cslib.LTS.MTr.stepL ?_ hpmid, hpmidle⟩
      exact Or.inl ⟨hτ, rfl, by rw [hpq2]; exact hstep2⟩
    · obtain ⟨U', hU'step, hU'le⟩ := hmono hpq1 hstep1
      obtain ⟨pmid, hpmid, hpmidle⟩ := ih (p := (U', mid.2)) rfl hU'le
      refine ⟨pmid, Cslib.LTS.MTr.stepL ?_ hpmid, hpmidle⟩
      exact Or.inr ⟨hvis, hU'step, by rw [hpq2]; exact hstep2⟩

/-- **Proposition 5.8.** Anti-monotonicity of reachability: from a `ProductLE`-smaller start, any
    state reachable from a bigger one is matched by a smaller-or-equal reachable state. -/
theorem productLE_canReach [HasTau Label]
    {L1 : LTS (Set State1) Label} (hmono : IsMonotoneNormalForm L1) (lts2 : LTS State2 Label)
    {p q q' : Set State1 × State2} (hpq : ProductLE p q)
    (h : (product L1 lts2).CanReach q q') :
    ∃ p', (product L1 lts2).CanReach p p' ∧ ProductLE p' q' := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨p', hp', hple⟩ := hmono.simulate lts2 hpq h
  exact ⟨p', ⟨σ, hp'⟩, hple⟩

/-- **Lemma 5.9** for TR-witnesses: anti-monotonicity under `ProductLE`. -/
theorem IsTRWitness.antitone {U V : Set State1} {s t : State2}
    (hle : ProductLE (U, s) (V, t)) (hwit : IsTRWitness V t) : IsTRWitness U s :=
  Set.subset_eq_empty hle.2 hwit

/-- **Lemma 5.9** for SF-witnesses: anti-monotonicity under `ProductLE`. -/
theorem IsSFWitness.antitone [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) {U V : Set State1} {s t : State2}
    (hle : ProductLE (U, s) (V, t)) (hwit : IsSFWitness lts1 lts2 V t) :
    IsSFWitness lts1 lts2 U s := by
  obtain ⟨hs, hU⟩ := hle
  subst hs
  rcases hwit with hV | ⟨hstable, hnsub⟩
  · exact Or.inl (Set.subset_eq_empty hU hV)
  · refine Or.inr ⟨hstable, fun hsub => hnsub ?_⟩
    exact hsub.trans (fun _ ⟨s', hs', hstab, hX⟩ => ⟨s', hU hs', hstab, hX⟩)

/-- **Lemma 5.9** for FD-witnesses: anti-monotonicity under `ProductLE`. -/
theorem IsFDWitness.antitone [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) {U V : Set State1} {s t : State2}
    (hle : ProductLE (U, s) (V, t)) (hwit : IsFDWitness lts1 lts2 V t) :
    IsFDWitness lts1 lts2 U s := by
  obtain ⟨hs, hU⟩ := hle
  subst hs
  obtain ⟨hVnd, hdisj⟩ := hwit
  refine ⟨fun ⟨u, hu, hdu⟩ => hVnd ⟨u, hU hu, hdu⟩, ?_⟩
  rcases hdisj with hV | ⟨hstable, hnsub⟩ | hsdiv
  · exact Or.inl (Set.subset_eq_empty hU hV)
  · refine Or.inr (Or.inl ⟨hstable, fun hsub => hnsub ?_⟩)
    exact hsub.trans (fun _ ⟨s', hs', hstab, hX⟩ => ⟨s', hU hs', hstab, hX⟩)
  · exact Or.inr (Or.inr hsdiv)

end AntichainProofs
