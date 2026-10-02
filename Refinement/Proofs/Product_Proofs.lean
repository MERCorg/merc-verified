module

public import Refinement.Semantics
public import Refinement.Product
public import Refinement.Proofs.Semantics_Proofs

open Cslib (LTS HasTau)

@[expose] public section ProductProofs

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorem below live in `Refinement/Pins/Product_Pins.lean`. -/

/-- Two states of a product are related by `CanReach` whenever one is, composed transitively
    (`Cslib.LTS.CanReach` has no transitivity lemma of its own). -/
theorem Cslib.LTS.CanReach.trans {lts : LTS State Label} {s t u : State}
    (h1 : lts.CanReach s t) (h2 : lts.CanReach t u) : lts.CanReach s u := by
  obtain ⟨μs1, h1⟩ := h1
  obtain ⟨μs2, h2⟩ := h2
  exact ⟨μs1 ++ μs2, Cslib.LTS.MTr.comp lts h1 h2⟩

/-- Lemmas 3.4/3.5 combined into a single closed form: the normal form's multistep transition
    relation from `NormInit lts s1` along `ρ` reaches exactly the `ρ`-weak-derivatives of `s1`. -/
theorem normTr_image [HasTau Label] (lts : LTS State Label) (s1 : State) :
    ∀ {ρ : List Label} {U : Set State},
      (NormTr lts).MTr (NormInit lts s1) ρ U → U = { t | WeakTr lts s1 ρ t } := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
    intro U h
    exact (Cslib.LTS.MTr.nil_eq _ h).symm ▸ rfl
  | append_singleton ρ' a ih =>
    intro U h
    obtain ⟨V, hV1, hV2⟩ := (Cslib.LTS.MTr.append_iff _).mp h
    have hVeq := ih hV1
    subst hVeq
    have hUa := (Cslib.LTS.MTr.singleton_iff _ _ _ _).mp hV2
    obtain ⟨_, hUeq⟩ := hUa
    rw [hUeq]
    ext t
    constructor
    · rintro ⟨v, hv, hvt⟩
      exact hv.comp hvt
    · intro ht
      obtain ⟨v, hv1, hv2⟩ := ht.splitAppend
      exact ⟨v, hv1, hv2⟩

/-- Lemma analogous to the content used in the proofs of Lemmas 3.9/3.10 (unzip direction): any
    reachable state of `L1 ⋉ L2` is reached via a weak trace `ρ` that is simultaneously a
    multistep trace of `L1` and a weak trace of `L2` from the chosen states. Stated for a generic
    `L1 : LTS (Set State1) Label` so it serves both `NormTr lts1` (Theorems 3.11, 3.14) and
    `FdrNormTr lts1` (Theorem 3.24) without re-proving. -/
theorem product_unzip [HasTau Label]
    (L1 : LTS (Set State1) Label) (lts2 : LTS State2 Label) {p q : Set State1 × State2}
    {μs : List Label} (h : (product L1 lts2).MTr p μs q) :
    ∃ ρ : List Label, L1.MTr p.1 ρ q.1 ∧ WeakTr lts2 p.2 ρ q.2 := by
  induction h with
  | refl => exact ⟨[], .refl, .refl _⟩
  | @stepL p μ mid μs' q hstep _ ih =>
    obtain ⟨ρ', hρ'1, hρ'2⟩ := ih
    rcases hstep with ⟨hτ, hmid1, hstep2⟩ | ⟨hvis, hstep1, hstep2⟩
    · exact ⟨ρ', hmid1 ▸ hρ'1, (WeakTr.tau hstep2).comp hρ'2⟩
    · exact ⟨μ :: ρ', Cslib.LTS.MTr.stepL hstep1 hρ'1, (WeakTr.vis hvis hstep2).comp hρ'2⟩

/-- Zip direction: an `L1`-trace and a matching weak trace of `L2` glue into a reachable pair of
    `L1 ⋉ L2`. Generic in `L1 : LTS (Set State1) Label` for the same reason as `product_unzip`. -/
theorem product_zip [HasTau Label]
    (L1 : LTS (Set State1) Label) (lts2 : LTS State2 Label) {s0 s : State2} {ρ : List Label}
    (h2 : WeakTr lts2 s0 ρ s) :
    ∀ {U0 U : Set State1}, L1.MTr U0 ρ U →
      (product L1 lts2).CanReach (U0, s0) (U, s) := by
  induction h2 with
  | refl s0 =>
    intro U0 U h1
    obtain rfl := Cslib.LTS.MTr.nil_eq L1 h1
    exact ⟨[], Cslib.LTS.MTr.refl⟩
  | @tau s0 s htau =>
    intro U0 U h1
    obtain rfl := Cslib.LTS.MTr.nil_eq L1 h1
    have hstep : (product L1 lts2).Tr (U0, s0) HasTau.τ (U0, s) :=
      Or.inl ⟨rfl, rfl, htau⟩
    exact ⟨[HasTau.τ], .stepL hstep .refl⟩
  | @vis s0 s a hvis htr =>
    intro U0 U h1
    have hUtr := (Cslib.LTS.MTr.singleton_iff _ _ _ _).mp h1
    have hstep : (product L1 lts2).Tr (U0, s0) a (U, s) :=
      Or.inr ⟨hvis, hUtr, htr⟩
    exact ⟨[a], .stepL hstep .refl⟩
  | comp _ _ ih1 ih2 =>
    intro U0 U h1
    obtain ⟨V, hV1, hV2⟩ := h1.split
    exact (ih1 hV1).trans (ih2 hV2)

/-- The normal form's transition relation is total on visible-only label sequences: every state
    has *some* `ρ`-derivative (possibly `∅`), for any sequence of visible labels `ρ`. -/
theorem normTr_total [HasTau Label] (lts : LTS State Label) (U0 : Set State) :
    ∀ {ρ : List Label}, (∀ μ ∈ ρ, IsVisible μ) → ∃ U, (NormTr lts).MTr U0 ρ U := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro _; exact ⟨U0, .refl⟩
  | append_singleton ρ' a ih =>
    intro hvis
    obtain ⟨U, hU⟩ := ih (fun μ hμ => hvis μ (List.mem_append_left _ hμ))
    have ha : IsVisible a := hvis a (List.mem_append_right _ (List.mem_singleton_self a))
    refine ⟨{ t | ∃ s ∈ U, WeakTr lts s [a] t }, (Cslib.LTS.MTr.append_iff _).mpr ?_⟩
    exact ⟨U, hU, (Cslib.LTS.MTr.singleton_iff _ _ _ _).mpr ⟨ha, rfl⟩⟩

/-- **Theorem 3.11.** Trace refinement holds iff no TR-witness is reachable in `norm(L1) ⋉ L2`. -/
theorem traceRefines_iff_not_reachable_trWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑tr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsTRWitness U s := by
  constructor
  · intro href ⟨U, s, ⟨μs, hreach⟩, hwit⟩
    have hunz : ∃ ρ : List Label, (NormTr lts1).MTr (NormInit lts1 s1) ρ U ∧ WeakTr lts2 s2 ρ s :=
      product_unzip (NormTr lts1) lts2 hreach
    obtain ⟨ρ, hρ1, hρ2⟩ := hunz
    have hρ2' : ρ ∈ weaktraces lts2 s2 := ⟨s, hρ2⟩
    have hρ1' : ρ ∉ weaktraces lts1 s1 := by
      have := normTr_image lts1 s1 hρ1
      rw [hwit] at this
      simp only [weaktraces, Set.mem_setOf_eq]
      rw [eq_comm, Set.eq_empty_iff_forall_notMem] at this
      exact fun ⟨t, ht⟩ => this t ht
    exact hρ1' (href hρ2')
  · intro hnwit ρ hρ
    obtain ⟨s, hs⟩ := hρ
    by_contra hnotin
    apply hnwit
    refine ⟨∅, s, ?_, rfl⟩
    obtain ⟨U, hU⟩ := normTr_total lts1 (NormInit lts1 s1) hs.visible
    have hUeq : U = ∅ := by
      rw [normTr_image lts1 s1 hU]
      exact Set.eq_empty_iff_forall_notMem.mpr fun t ht => hnotin ⟨t, ht⟩
    exact hUeq ▸ product_zip (NormTr lts1) lts2 hs hU

/-- **Theorem 3.14.** Stable failures refinement holds iff no SF-witness is reachable in
    `norm(L1) ⋉ L2`. -/
theorem stableFailuresRefines_iff_not_reachable_sfWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑sfr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsSFWitness lts1 lts2 U s := by
  constructor
  · rintro ⟨hfail, htr⟩ ⟨U, s, ⟨μs, hreach⟩, hwit⟩
    have hunz : ∃ ρ : List Label, (NormTr lts1).MTr (NormInit lts1 s1) ρ U ∧ WeakTr lts2 s2 ρ s :=
      product_unzip (NormTr lts1) lts2 hreach
    obtain ⟨ρ, hρ1, hρ2⟩ := hunz
    rcases hwit with hU | ⟨hstable, hnsub⟩
    · exact (traceRefines_iff_not_reachable_trWitness lts1 s1 lts2 s2).mp htr
        ⟨U, s, ⟨μs, hreach⟩, hU⟩
    · obtain ⟨X, hXmem, hXnot⟩ := Set.not_subset.mp hnsub
      have hfailure2 : (ρ, X) ∈ failures lts2 s2 := ⟨s, hρ2, hstable, hXmem⟩
      obtain ⟨t, ht1, ht2, ht3⟩ := hfail hfailure2
      have htU : t ∈ U := (normTr_image lts1 s1 hρ1) ▸ ht1
      exact hXnot ⟨t, htU, ht2, ht3⟩
  · intro hnwit
    have htr : TraceRefines lts1 s1 lts2 s2 :=
      (traceRefines_iff_not_reachable_trWitness lts1 s1 lts2 s2).mpr
        (fun ⟨U, s, hreach, hU⟩ => hnwit ⟨U, s, hreach, Or.inl hU⟩)
    refine ⟨?_, htr⟩
    rintro ⟨ρ, X⟩ ⟨s, hρ2, hstable, hXmem⟩
    dsimp only at hρ2 hXmem ⊢
    obtain ⟨U, hU⟩ := normTr_total lts1 (NormInit lts1 s1) hρ2.visible
    by_contra hnotfail
    have himg := normTr_image lts1 s1 hU
    have hXnot : X ∉ refusals lts1 U := by
      rintro ⟨t, htU, htstable, htX⟩
      rw [himg] at htU
      exact hnotfail ⟨t, htU, htstable, htX⟩
    have hwit : IsSFWitness lts1 lts2 U s := Or.inr ⟨hstable, fun hsub => hXnot (hsub hXmem)⟩
    exact hnwit ⟨U, s, product_zip (NormTr lts1) lts2 hρ2 hU, hwit⟩

/-- Lemma 3.17/3.18 combined into a closed form for `FdrNormTr`, exactly as `normTr_image` is for
    `NormTr`: the proof only ever uses the equational component of `(FdrNormTr lts).Tr`, so it
    goes through unchanged (the divergence guard only affects *whether* a transition exists, not
    what the reached set equals when one does). -/
theorem fdrNormTr_image [HasTau Label] (lts : LTS State Label) (s1 : State) :
    ∀ {ρ : List Label} {U : Set State},
      (FdrNormTr lts).MTr (NormInit lts s1) ρ U → U = { t | WeakTr lts s1 ρ t } := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
    intro U h
    exact (Cslib.LTS.MTr.nil_eq _ h).symm ▸ rfl
  | append_singleton ρ' a ih =>
    intro U h
    obtain ⟨V, hV1, hV2⟩ := (Cslib.LTS.MTr.append_iff _).mp h
    have hVeq := ih hV1
    subst hVeq
    obtain ⟨_, _, hUeq⟩ := (Cslib.LTS.MTr.singleton_iff _ _ _ _).mp hV2
    rw [hUeq]
    ext t
    constructor
    · rintro ⟨v, hv, hvt⟩
      exact hv.comp hvt
    · intro ht
      obtain ⟨v, hv1, hv2⟩ := ht.splitAppend
      exact ⟨v, hv1, hv2⟩

/-- Whenever `FdrNormTr` succeeds in reaching `U` via the whole of `ρ = ρ' ++ σ` with `U` itself
    non-divergent, it also succeeds reaching some `V` via just the prefix `ρ'`, with `V` itself
    non-divergent: either `σ = []` and `V = U`, or `σ` is nonempty and non-divergence of its
    source `V` is exactly `FdrNormTr`'s guard on the first step of `σ`. -/
theorem fdrNormTr_prefix_not_divergent [HasTau Label] (lts : LTS State Label)
    {ρ ρ' σ : List Label} {U0 U : Set State}
    (h : (FdrNormTr lts).MTr U0 ρ U) (hρ : ρ = ρ' ++ σ) (hUnd : ¬ SetDivergent lts U) :
    ∃ V, (FdrNormTr lts).MTr U0 ρ' V ∧ ¬ SetDivergent lts V := by
  subst hρ
  obtain ⟨V, hV1, hV2⟩ := (Cslib.LTS.MTr.append_iff _).mp h
  refine ⟨V, hV1, ?_⟩
  cases σ with
  | nil =>
    obtain rfl := Cslib.LTS.MTr.nil_eq (FdrNormTr lts) hV2
    exact hUnd
  | cons b σ' =>
    obtain ⟨mid, hstep, _⟩ := Cslib.LTS.MTr.cons_iff.mp hV2
    exact hstep.2.1

/-- **Lemma 3.19 analogue.** If the FDR normal form reaches a non-divergent `U` via the whole of
    `ρ`, then `ρ` is not a divergence of `L1`: no prefix of `ρ` can reach a divergent state,
    since every such prefix's normal-form image is non-divergent by
    `fdrNormTr_prefix_not_divergent`. -/
theorem fdrNormTr_not_divergences [HasTau Label] (lts : LTS State Label) (s1 : State)
    {ρ : List Label} {U : Set State}
    (h : (FdrNormTr lts).MTr (NormInit lts s1) ρ U) (hUnd : ¬ SetDivergent lts U) :
    ρ ∉ divergences lts s1 := by
  rintro ⟨_, ρ', σ, hρ, t, hwt, hdt⟩
  obtain ⟨V, hV1, hVnd⟩ := fdrNormTr_prefix_not_divergent lts h hρ hUnd
  apply hVnd
  rw [fdrNormTr_image lts s1 hV1]
  exact ⟨t, hwt, hdt⟩

/-- **Theorem 3.24, forward direction (Lemma 3.22 analogue).** -/
theorem failuresDivergencesRefines_of_not_reachable_fdWitness_aux [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hfailBot : failuresBot lts2 s2 ⊆ failuresBot lts1 s1)
    (hdiv : divergences lts2 s2 ⊆ divergences lts1 s1) :
    ¬ ∃ U s, (product (FdrNormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
      IsFDWitness lts1 lts2 U s := by
  rintro ⟨U, s, ⟨μs, hreach⟩, hUndiv, hdisj⟩
  have hunz : ∃ ρ : List Label,
      (FdrNormTr lts1).MTr (NormInit lts1 s1) ρ U ∧ WeakTr lts2 s2 ρ s :=
    product_unzip (FdrNormTr lts1) lts2 hreach
  obtain ⟨ρ, hρ1, hρ2⟩ := hunz
  have hρnd : ρ ∉ divergences lts1 s1 := fdrNormTr_not_divergences lts1 s1 hρ1 hUndiv
  have himg := fdrNormTr_image lts1 s1 hρ1
  rcases hdisj with hUempty | ⟨hstable, hnsub⟩ | hsdiv
  · -- U = ∅
    by_cases hsd : lts2.Divergent s
    · exact hρnd (hdiv ⟨hρ2.visible, ρ, [], (List.append_nil ρ).symm, s, hρ2, hsd⟩)
    · obtain ⟨t, hτt, htstable⟩ := not_divergent_has_stable (lts := lts2) hsd
      have hwt : WeakTr lts2 s2 ρ t :=
        (List.append_nil ρ) ▸ hρ2.comp (WeakTr.of_τSTr hτt)
      have hfail2 : (ρ, (∅ : Set Label)) ∈ failuresBot lts2 s2 :=
        Or.inl ⟨t, hwt, htstable, Set.empty_subset _⟩
      rcases hfailBot hfail2 with hf | hd
      · obtain ⟨t', ht1, _, _⟩ := hf
        have htU : t' ∈ U := by rw [himg]; exact ht1
        rw [hUempty] at htU
        exact htU
      · exact hρnd hd
  · -- refusal mismatch
    obtain ⟨X, hXmem, hXnot⟩ := Set.not_subset.mp hnsub
    have hfail2 : (ρ, X) ∈ failuresBot lts2 s2 := Or.inl ⟨s, hρ2, hstable, hXmem⟩
    rcases hfailBot hfail2 with hf | hd
    · obtain ⟨t, ht1, ht2, ht3⟩ := hf
      have htU : t ∈ U := by rw [himg]; exact ht1
      exact hXnot ⟨t, htU, ht2, ht3⟩
    · exact hρnd hd
  · exact hρnd (hdiv ⟨hρ2.visible, ρ, [], (List.append_nil ρ).symm, s, hρ2, hsdiv⟩)

/-- For any visible-only `ρ`, the FDR normal form either processes all of `ρ` successfully, or
    gets stuck exactly at a divergent intermediate set reached via some prefix of `ρ`. Needed for
    the reverse direction of Theorem 3.24, where `normTr_total`'s unconditional totality
    (available for plain `NormTr`) no longer holds. -/
theorem fdrNormTr_reach_or_stuck [HasTau Label] (lts1 : LTS State1 Label) (s1 : State1) :
    ∀ {ρ : List Label}, (∀ μ ∈ ρ, IsVisible μ) →
      ∃ ρ' U, (∃ σ, ρ = ρ' ++ σ) ∧ (FdrNormTr lts1).MTr (NormInit lts1 s1) ρ' U ∧
        (ρ' = ρ ∨ SetDivergent lts1 U) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro _; exact ⟨[], NormInit lts1 s1, ⟨[], rfl⟩, .refl, Or.inl rfl⟩
  | append_singleton ρ0 a ih =>
    intro hvis
    obtain ⟨ρ', U, ⟨σ, hσ⟩, hmtr, hdisj⟩ := ih (fun μ hμ => hvis μ (List.mem_append_left _ hμ))
    rcases hdisj with heq | hdiv
    · have hmtr0 : (FdrNormTr lts1).MTr (NormInit lts1 s1) ρ0 U := heq ▸ hmtr
      by_cases hdU : SetDivergent lts1 U
      · exact ⟨ρ0, U, ⟨[a], rfl⟩, hmtr0, Or.inr hdU⟩
      · have ha : IsVisible a := hvis a (List.mem_append_right _ (List.mem_singleton_self a))
        have hstep : (FdrNormTr lts1).Tr U a { t | ∃ s ∈ U, WeakTr lts1 s [a] t } :=
          ⟨ha, hdU, rfl⟩
        exact ⟨ρ0 ++ [a], { t | ∃ s ∈ U, WeakTr lts1 s [a] t }, ⟨[], by rw [List.append_nil]⟩,
          (Cslib.LTS.MTr.append_iff _).mpr
            ⟨U, hmtr0, (Cslib.LTS.MTr.singleton_iff _ _ _ _).mpr hstep⟩,
          Or.inl rfl⟩
    · exact ⟨ρ', U, ⟨σ ++ [a], by rw [hσ, List.append_assoc]⟩, hmtr, Or.inr hdiv⟩

/-- **Theorem 3.24, reverse direction (Lemma 3.23 analogue).** -/
theorem failuresDivergencesRefines_of_not_reachable_fdWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hnwit : ¬ ∃ U s, (product (FdrNormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
      IsFDWitness lts1 lts2 U s) :
    (s1 ⊑fdr[lts1,lts2] s2) := by
  have hdiv : divergences lts2 s2 ⊆ divergences lts1 s1 := by
    rintro ν ⟨hvisν, ρ0, σ, hν, t, hwt, hdt⟩
    obtain ⟨ρ'', U, ⟨σ'', hσ''⟩, hmtr, hdisj⟩ := fdrNormTr_reach_or_stuck lts1 s1 hwt.visible
    by_cases hdU : SetDivergent lts1 U
    · obtain ⟨u, huU, hdu⟩ := hdU
      rw [fdrNormTr_image lts1 s1 hmtr] at huU
      refine ⟨hvisν, ρ'', σ'' ++ σ, ?_, u, huU, hdu⟩
      rw [hν, hσ'', List.append_assoc]
    · have heq : ρ'' = ρ0 := hdisj.resolve_right hdU
      subst heq
      exfalso
      exact hnwit ⟨U, t, product_zip (FdrNormTr lts1) lts2 hwt hmtr, hdU, Or.inr (Or.inr hdt)⟩
  refine ⟨?_, hdiv⟩
  rintro ⟨ρ, X⟩ hp
  rcases hp with hf | hd
  · obtain ⟨s, hρ2, hstable, hXmem⟩ := hf
    obtain ⟨ρ'', U, ⟨σ'', hσ''⟩, hmtr, hdisj⟩ := fdrNormTr_reach_or_stuck lts1 s1 hρ2.visible
    by_cases hdU : SetDivergent lts1 U
    · obtain ⟨u, huU, hdu⟩ := hdU
      rw [fdrNormTr_image lts1 s1 hmtr] at huU
      exact Or.inr (show ρ ∈ divergences lts1 s1 from ⟨hρ2.visible, ρ'', σ'', hσ'', u, huU, hdu⟩)
    · have heq : ρ'' = ρ := hdisj.resolve_right hdU
      subst heq
      by_contra hnotfail
      have hXnotin : X ∉ refusals lts1 U := by
        rintro ⟨t', ht'U, ht'stable, ht'X⟩
        apply hnotfail
        refine Or.inl ⟨t', ?_, ht'stable, ht'X⟩
        rw [fdrNormTr_image lts1 s1 hmtr] at ht'U
        exact ht'U
      exact hnwit ⟨U, s, product_zip (FdrNormTr lts1) lts2 hρ2 hmtr, hdU,
        Or.inr (Or.inl ⟨hstable, fun hsub => hXnotin (hsub hXmem)⟩)⟩
  · exact Or.inr (hdiv hd)

/-- **Theorem 3.24.** Failures-divergences refinement holds iff no FD-witness is reachable in
    `normfdr(L1) ⋉ L2`. -/
theorem failuresDivergencesRefines_iff_not_reachable_fdWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑fdr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (FdrNormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsFDWitness lts1 lts2 U s :=
  ⟨fun ⟨hb, hd⟩ => failuresDivergencesRefines_of_not_reachable_fdWitness_aux lts1 s1 lts2 s2 hb hd,
    failuresDivergencesRefines_of_not_reachable_fdWitness lts1 s1 lts2 s2⟩

end ProductProofs
