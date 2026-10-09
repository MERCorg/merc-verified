module

public import Refinement.Semantics
public import Refinement.Product
public import Refinement.Antichain
public import Refinement.Algorithm
public import Refinement.ImpossibleFutures
public import Refinement.Proofs.Semantics_Proofs
public import Refinement.Proofs.Product_Proofs
public import Refinement.Proofs.Antichain_Proofs
public import Refinement.Proofs.Algorithm_Proofs

open Cslib (LTS HasTau)

@[expose] public section ImpossibleFuturesProofs

namespace Refinement

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems below live in `Refinement/Pins/ImpossibleFutures_Pins.lean`.

This file proves Lemma 4 (`not_impossibleFuturesRefines_iff`), Theorem 2 (Lemmas 7 and 8,
`impossibleFuturesRefines_iff_not_reachable_ifWitness`), the antitonicity of (stable) IF-witnesses
(Lemma 9), the two Algorithm 4 corollaries built on `foundWitness_iff_exists_witness_finite`,
Lemma 10 (`IsIFWitness.of_tau_step`) together with its stable-witness consequence of Section 4.2,
and Lemma 11 (`impossibleFutures_eq_of_tauCycle`). -/

/-- **Lemma 4** (in this package's orientation): impossible futures refinement fails iff some weak
    trace `ρ` of the implementation reaches a state `s` such that every `ρ`-derivative `t` of the
    specification has a weak trace that `s` lacks. -/
theorem not_impossibleFuturesRefines_iff [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    ¬ (s1 ⊑if[lts1,lts2] s2) ↔
      ∃ ρ s, WeakTr lts2 s2 ρ s ∧
        ∀ t, WeakTr lts1 s1 ρ t → ¬ weaktraces lts1 t ⊆ weaktraces lts2 s := by
  constructor
  · intro h
    change ¬ (impossibleFutures lts2 s2 ⊆ impossibleFutures lts1 s1) at h
    rw [Set.not_subset] at h
    obtain ⟨⟨ρ, X⟩, hmem, hnotmem⟩ := h
    have h1 : ∃ s, WeakTr lts2 s2 ρ s ∧ X ∩ weaktraces lts2 s = ∅ := hmem
    have h2 : ¬ ∃ t, WeakTr lts1 s1 ρ t ∧ X ∩ weaktraces lts1 t = ∅ := hnotmem
    obtain ⟨s, hws, hemp⟩ := h1
    rw [Set.eq_empty_iff_forall_notMem] at hemp
    refine ⟨ρ, s, hws, fun t ht hsub => ?_⟩
    have hne : X ∩ weaktraces lts1 t ≠ ∅ :=
      fun hempty => h2 ⟨t, ht, hempty⟩
    obtain ⟨w, ⟨hwx, hwt⟩⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact hemp w ⟨hwx, hsub hwt⟩
  · rintro ⟨ρ, s, hws, hall⟩
    change ¬ (impossibleFutures lts2 s2 ⊆ impossibleFutures lts1 s1)
    rw [Set.not_subset]
    refine ⟨(ρ, {w | ∃ t, WeakTr lts1 s1 ρ t ∧ w ∈ weaktraces lts1 t ∧
        w ∉ weaktraces lts2 s}), ?_, ?_⟩
    · refine ⟨s, hws, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]
      rintro w ⟨⟨t, _, _, hnot⟩, hws⟩
      exact hnot hws
    · intro hmem
      obtain ⟨t, ht, hemp⟩ := hmem
      rw [Set.eq_empty_iff_forall_notMem] at hemp
      refine hall t ht ?_
      intro w hw
      by_contra hn
      exact hemp w ⟨⟨t, ht, hw, hn⟩, hw⟩

/-- **Theorem 2** (Lemmas 7 and 8). Impossible futures refinement holds iff no IF-witness is
    reachable in `norm(L1) ⋉ L2`. -/
theorem impossibleFuturesRefines_iff_not_reachable_ifWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsIFWitness lts1 lts2 U s := by
  constructor
  · intro hIF ⟨U, s, hreach, hwit⟩
    obtain ⟨μs, hmtr⟩ := hreach
    obtain ⟨ρ, hρ1, hρ2⟩ := product_unzip (NormTr lts1) lts2 hmtr
    have hUeq : U = { t | WeakTr lts1 s1 ρ t } := normTr_image lts1 s1 hρ1
    exfalso
    refine ((not_impossibleFuturesRefines_iff lts1 s1 lts2 s2).mpr ⟨ρ, s, hρ2, ?_⟩) hIF
    intro t ht hsub
    have htU : t ∈ U := by rw [hUeq]; exact ht
    rcases hwit with hU | hmem
    · rw [hU] at htU
      exact (Set.mem_empty_iff_false t).mp htU
    · exact hmem t htU hsub
  · intro hnwit
    by_contra hnotIF
    obtain ⟨ρ, s, hρ2, hall⟩ := (not_impossibleFuturesRefines_iff lts1 s1 lts2 s2).mp hnotIF
    obtain ⟨U, hU⟩ := normTr_total lts1 (NormInit lts1 s1) hρ2.visible
    have hUeq : U = { t | WeakTr lts1 s1 ρ t } := normTr_image lts1 s1 hU
    have hwit : IsIFWitness lts1 lts2 U s := by
      refine Or.inr fun t ht hsub => hall t ?_ hsub
      rw [hUeq] at ht
      exact ht
    exact hnwit ⟨U, s, product_zip (NormTr lts1) lts2 hρ2 hU, hwit⟩

/-- **Lemma 9**: anti-monotonicity of IF-witnesses under `ProductLE`. -/
theorem IsIFWitness.antitone [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) {U V : Set State1} {s t : State2}
    (hle : ProductLE (U, s) (V, t)) (hwit : IsIFWitness lts1 lts2 V t) :
    IsIFWitness lts1 lts2 U s := by
  obtain ⟨hs, hUV⟩ := hle
  subst hs
  rcases hwit with hV | hmem
  · exact Or.inl (Set.subset_eq_empty hUV hV)
  · exact Or.inr (fun u hu hsub => hmem u (hUV hu) hsub)

/-- Anti-monotonicity for the stable-only witness test of Algorithm 6. -/
theorem IsStableIFWitness.antitone [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) {U V : Set State1} {s t : State2}
    (hle : ProductLE (U, s) (V, t)) (hwit : IsStableIFWitness lts1 lts2 V t) :
    IsStableIFWitness lts1 lts2 U s := by
  obtain ⟨hs, hUV⟩ := hle
  subst hs
  rcases hwit with hV | ⟨hstable, hmem⟩
  · exact Or.inl (Set.subset_eq_empty hUV hV)
  · exact Or.inr ⟨hstable, fun u hu hsub => hmem u (hUV hu) hsub⟩

/-- **Algorithm 4** (and Algorithm 2, which differs only in not pruning): the antichain-based
    exploration finds an IF-witness iff impossible futures refinement fails. -/
theorem impossibleFuturesRefines_iff_not_foundWitness [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 (IsIFWitness lts1 lts2) (NormInit lts1 s1, s2) := by
  rw [impossibleFuturesRefines_iff_not_reachable_ifWitness,
    foundWitness_iff_exists_witness_finite (normTr_isMonotone lts1)
      (fun hle hwit => IsIFWitness.antitone lts1 lts2 hle hwit), Prod.exists]

/-- **Lemma 10**: IF-witnesses survive implementation `τ`-steps of the product. -/
theorem IsIFWitness.of_tau_step [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) {U : Set State1} {s s' : State2}
    (hstep : lts2.Tr s HasTau.τ s') (hwit : IsIFWitness lts1 lts2 U s) :
    IsIFWitness lts1 lts2 U s' := by
  rcases hwit with hU | hmem
  · exact Or.inl hU
  · refine Or.inr fun t ht hsub => hmem t ht ?_
    intro ρ hρ
    obtain ⟨u, hu⟩ := hsub hρ
    exact ⟨u, (WeakTr.tau hstep).comp hu⟩

/-- Lemma 10, multi-step: IF-witnesses survive `τ*`-paths of the implementation. -/
theorem IsIFWitness.of_τSTr [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) {U : Set State1} {s t : State2}
    (hτ : lts2.τSTr s t) (hwit : IsIFWitness lts1 lts2 U s) :
    IsIFWitness lts1 lts2 U t := by
  induction hτ with
  | refl => exact hwit
  | tail _ hstep ih => exact IsIFWitness.of_tau_step lts1 lts2 hstep ih

/-- Reachable IF-witnesses can be taken stable when the implementation is convergent
    (consequence of Lemma 10), so the weak trace comparison only has to be made at stable
    implementation states. -/
theorem reachable_ifWitness_iff_reachable_stableIFWitness [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (hconv : Convergent lts2)
    (p0 : Set State1 × State2) :
    (∃ U s, (product (NormTr lts1) lts2).CanReach p0 (U, s) ∧ IsIFWitness lts1 lts2 U s) ↔
      ∃ U s, (product (NormTr lts1) lts2).CanReach p0 (U, s) ∧ IsStableIFWitness lts1 lts2 U s := by
  constructor
  · rintro ⟨U, s, hreach, hwit⟩
    obtain ⟨t, hτ, hstab⟩ := not_divergent_has_stable (hconv s)
    have hstep : (product (NormTr lts1) lts2).CanReach (U, s) (U, t) :=
      product_zip (NormTr lts1) lts2 (WeakTr.of_τSTr hτ) Cslib.LTS.MTr.refl
    have hwit' := IsIFWitness.of_τSTr lts1 lts2 hτ hwit
    refine ⟨U, t, canReach_trans hreach hstep, ?_⟩
    rcases hwit' with hU | hmem
    · exact Or.inl hU
    · exact Or.inr ⟨hstab, hmem⟩
  · rintro ⟨U, s, hreach, hwit⟩
    refine ⟨U, s, hreach, ?_⟩
    rcases hwit with hU | ⟨_, hmem⟩
    · exact Or.inl hU
    · exact Or.inr hmem

/-- Algorithm 4 with the stable-only witness test (the delayed check of Section 4.2). -/
theorem impossibleFuturesRefines_iff_not_foundStableWitness [HasTau Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hconv : Convergent lts2) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 (IsStableIFWitness lts1 lts2) (NormInit lts1 s1, s2) := by
  rw [impossibleFuturesRefines_iff_not_reachable_ifWitness,
    reachable_ifWitness_iff_reachable_stableIFWitness lts1 lts2 hconv,
    foundWitness_iff_exists_witness_finite (normTr_isMonotone lts1)
      (fun hle hwit => IsStableIFWitness.antitone lts1 lts2 hle hwit), Prod.exists]

/-- **Lemma 11**: states on a common `τ`-cycle of the implementation have the same weak
    impossible futures. -/
theorem impossibleFutures_eq_of_tauCycle [HasTau Label]
    (lts : LTS State Label) {s s' : State}
    (h1 : WeakTr lts s [] s') (h2 : WeakTr lts s' [] s) :
    impossibleFutures lts s = impossibleFutures lts s' := by
  ext p
  constructor
  · rintro ⟨t, ht, hemp⟩
    exact ⟨t, h2.comp ht, hemp⟩
  · rintro ⟨t, ht, hemp⟩
    exact ⟨t, h1.comp ht, hemp⟩

/-- **Lemma 11** (as stated in the paper): collapsing a `τ`-cycle of the implementation preserves
    impossible futures refinement. -/
theorem impossibleFuturesRefines_iff_of_tauCycle [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) {s2 s2' : State2}
    (h1 : WeakTr lts2 s2 [] s2') (h2 : WeakTr lts2 s2' [] s2) :
    (s1 ⊑if[lts1,lts2] s2) ↔ (s1 ⊑if[lts1,lts2] s2') := by
  change impossibleFutures lts2 s2 ⊆ impossibleFutures lts1 s1 ↔
    impossibleFutures lts2 s2' ⊆ impossibleFutures lts1 s1
  rw [impossibleFutures_eq_of_tauCycle lts2 h1 h2]

end Refinement

end ImpossibleFuturesProofs
