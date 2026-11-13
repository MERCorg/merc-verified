module

public import MercLib.Theory.CoupledSim.FixedPoint
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Basic.Finite.Prod

open Cslib (LTS HasTau)

@[expose] public section FixedPointProofs

namespace MercLib.CoupledSim

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The "headline"
theorems below are stated in `Challenges/CoupledSim.lean` (human-vetted). -/

/-! ## Helper lemmas about simulations

These mirror (private) lemmas of `CoupledSimilarity_Proofs`; `Proofs/` files do not import
other `Proofs/` files, so the needed ones are repeated here (in the `Aux` namespace to keep the
names apart). -/

namespace Aux

/-- A delay step is a weak step. -/
private theorem dtr_sttr [HasTau Label] {lts : LTS State Label}
    {s s' : State} {μ : Label} (h : DTr lts s μ s') : lts.STr s μ s' := by
  cases h with
  | tau => exact LTS.STr.refl
  | vis _ hτ htr => exact LTS.STr.tr hτ htr LTS.τSTr.refl

/-- A strong `τ`-step is a `τ`-reachability step. -/
private theorem τSTr_of_tr [HasTau Label] {lts : LTS State Label} {s s' : State}
    (h : lts.Tr s HasTau.τ s') : lts.τSTr s s' :=
  Relation.ReflTransGen.single (show LTS.Tr.toRelation lts HasTau.τ s s' from h)

/-- Prepending `τ`-steps before a weak step keeps it a weak step. -/
private theorem stτhead [HasTau Label] {lts : LTS State Label}
    {s s' s'' : State} {μ : Label} (hτ : lts.τSTr s s') (h : lts.STr s' μ s'') :
    lts.STr s μ s'' := by
  cases h with
  | refl => exact (LTS.sTr_τSTr_iff lts).mpr hτ
  | tr hτ1 htr hτ2 => exact LTS.STr.tr (Relation.ReflTransGen.trans hτ hτ1) htr hτ2

/-- Appending `τ`-steps after a weak step keeps it a weak step. -/
private theorem stτtail [HasTau Label] {lts : LTS State Label}
    {s s' s'' : State} {μ : Label} (h : lts.STr s μ s') (hτ : lts.τSTr s' s'') :
    lts.STr s μ s'' := by
  cases h with
  | refl => exact (LTS.sTr_τSTr_iff lts).mpr hτ
  | tr hτ1 htr hτ2 => exact LTS.STr.tr hτ1 htr (Relation.ReflTransGen.trans hτ2 hτ)

/-- Stuttering lemma: a weak simulation can answer every `τ`-reachability challenge. -/
private theorem weakSim_stutter [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : IsWeakSimulation lts r)
    {s s' t : State} (hst : r s t) (hτ : lts.τSTr s s') :
    ∃ t', lts.τSTr t t' ∧ r s' t' := by
  induction hτ with
  | refl => exact ⟨t, Relation.ReflTransGen.refl, hst⟩
  | tail _ hLast ih =>
    obtain ⟨tPrev, hPath, hrPrev⟩ := ih
    obtain ⟨t', hr', hsTr⟩ := hr hrPrev HasTau.τ _ hLast
    exact ⟨t', Relation.ReflTransGen.trans hPath ((LTS.sTr_τSTr_iff lts).mp hsTr), hr'⟩

/-- A weak simulation can answer every weak-step challenge. -/
private theorem weakSim_sttr [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : IsWeakSimulation lts r)
    {s s' t : State} {μ : Label} (hst : r s t) (h : lts.STr s μ s') :
    ∃ t', r s' t' ∧ lts.STr t μ t' := by
  cases h with
  | refl => exact ⟨t, hst, LTS.STr.refl⟩
  | tr hτ1 htr hτ2 =>
    obtain ⟨t1, hPath1, hr1⟩ := weakSim_stutter hr hst hτ1
    obtain ⟨t2, hr2, hsTr2⟩ := hr hr1 μ _ htr
    obtain ⟨t3, hPath3, hr3⟩ := weakSim_stutter hr hr2 hτ2
    exact ⟨t3, hr3, stτtail (stτhead hPath1 hsTr2) hPath3⟩

/-- Symmetric composition of two relations: `symComp r₁ r₂ p q` holds if `p` and `q` are related
through some intermediate state via `r₁` then `r₂`, or via `r₂` then `r₁`. -/
private def symComp (r₁ r₂ : State → State → Prop) (p q : State) : Prop :=
  ∃ u, (r₁ p u ∧ r₂ u q) ∨ (r₂ p u ∧ r₁ u q)

/-- Weak simulations compose: the symmetric composition of `r₁` and `r₂` is again a weak
simulation. -/
private theorem isWeakSimulation_trans_comp [HasTau Label] {lts : LTS State Label}
    {r₁ r₂ : State → State → Prop} (h₁ : IsWeakSimulation lts r₁) (h₂ : IsWeakSimulation lts r₂) :
    IsWeakSimulation lts (symComp r₁ r₂) := by
  rintro p q ⟨u, ⟨h1u, h2u⟩ | ⟨h2u, h1u⟩⟩ μ p' htr
  · obtain ⟨u1, hu1', hsTr⟩ := h₁ h1u μ p' htr
    obtain ⟨q', hq', hsTr'⟩ := weakSim_sttr h₂ h2u hsTr
    refine ⟨q', ?_, hsTr'⟩
    show ∃ u, (r₁ p' u ∧ r₂ u q') ∨ (r₂ p' u ∧ r₁ u q')
    exact ⟨u1, Or.inl ⟨hu1', hq'⟩⟩
  · obtain ⟨u1, hu1', hsTr⟩ := h₂ h2u μ p' htr
    obtain ⟨q', hq', hsTr'⟩ := weakSim_sttr h₁ h1u hsTr
    refine ⟨q', ?_, hsTr'⟩
    show ∃ u, (r₁ p' u ∧ r₂ u q') ∨ (r₂ p' u ∧ r₁ u q')
    exact ⟨u1, Or.inr ⟨hu1', hq'⟩⟩

/-- **Lemma 4 of [Bisping2019]** (as a relation property): `τ`-reachability is a coupled
simulation — the relation `λ p q, q ⇒τ* p` is a coupled simulation. -/
private theorem tauReach_isCoupledSimulation [HasTau Label] (lts : LTS State Label) :
    IsCoupledSimulation lts (fun p q => lts.τSTr q p) := by
  constructor
  · rintro p q hτ μ p' htr
    refine ⟨p', ?_, LTS.STr.tr hτ htr LTS.τSTr.refl⟩
    exact LTS.τSTr.refl
  · rintro p q hτ
    refine ⟨p, hτ, ?_⟩
    exact LTS.τSTr.refl

/-- **Lemma 4 of [Bisping2019]**: if `q ⇒ p`, then `p ≼cs[lts] q`. -/
private theorem preorder_of_tauReach [HasTau Label] {lts : LTS State Label} {p q : State}
    (h : lts.τSTr q p) : p ≼cs[lts] q := by
  refine ⟨fun p q => lts.τSTr q p, tauReach_isCoupledSimulation lts, ?_⟩
  exact h

/-- **Lemma 2 of [Bisping2019]** (transitivity): the coupled simulation preorder is transitive. -/
private theorem preorder_trans [HasTau Label] {lts : LTS State Label}
    {p q r : State} (h1 : p ≼cs[lts] q) (h2 : q ≼cs[lts] r) : p ≼cs[lts] r := by
  obtain ⟨R1, hR1, hR1pq⟩ := h1
  obtain ⟨R2, hR2, hR2qr⟩ := h2
  refine ⟨symComp R1 R2, ⟨?_, ?_⟩, ?_⟩
  · exact isWeakSimulation_trans_comp hR1.1 hR2.1
  · rintro a b ⟨u, ⟨h1u, h2u⟩ | ⟨h2u, h1u⟩⟩
    · obtain ⟨u1, hτ1, hu1⟩ := hR1.2 h1u
      obtain ⟨b1, hτ2, hb1⟩ := weakSim_stutter hR2.1 h2u hτ1
      obtain ⟨b2, hτ3, hb2⟩ := hR2.2 hb1
      refine ⟨b2, Relation.ReflTransGen.trans hτ2 hτ3, u1, ?_⟩
      exact Or.inr ⟨hb2, hu1⟩
    · obtain ⟨u1, hτ1, hu1⟩ := hR2.2 h2u
      obtain ⟨b1, hτ2, hb1⟩ := weakSim_stutter hR1.1 h1u hτ1
      obtain ⟨b2, hτ3, hb2⟩ := hR1.2 hb1
      refine ⟨b2, Relation.ReflTransGen.trans hτ2 hτ3, u1, ?_⟩
      exact Or.inl ⟨hb2, hu1⟩
  · exact ⟨q, Or.inl ⟨hR1pq, hR2qr⟩⟩

/-- **τ-challenges are trivial for the preorder**: from `p ⇒τ* p'` and `p ≼cs[lts] q` follows
`p' ≼cs[lts] q`. -/
private theorem preorder_tau_challenge_trivial [HasTau Label] {lts : LTS State Label}
    {p p' q : State} (hτ : lts.τSTr p p') (h : p ≼cs[lts] q) : p' ≼cs[lts] q :=
  preorder_trans (preorder_of_tauReach hτ) h

/-- **Lemma 1 of [Bisping2019]** (direction 1): the coupled simulation preorder itself is a
coupled delay simulation. -/
private theorem coupledSimPreorder_isCD [HasTau Label] (lts : LTS State Label) :
    IsCoupledDelaySimulation lts (CoupledSimulationPreorder lts) := by
  constructor
  · rintro p q ⟨r, hr, hpq⟩ μ p' htr
    by_cases hμ : μ = HasTau.τ
    · subst hμ
      refine ⟨q, preorder_tau_challenge_trivial (τSTr_of_tr htr) ⟨r, hr, hpq⟩, DTr.tau⟩
    · obtain ⟨v, hv, hsTr⟩ := hr.1 hpq μ p' htr
      cases hsTr with
      | refl => exact absurd rfl hμ
      | tr hτ1 htr' hτ2 =>
        refine ⟨_, ⟨?_, DTr.vis hμ hτ1 htr'⟩⟩
        exact preorder_trans ⟨r, hr, hv⟩ (preorder_of_tauReach hτ2)
  · rintro p q ⟨r, hr, hpq⟩
    obtain ⟨q', hτ, hq'⟩ := hr.2 hpq
    exact ⟨q', hτ, ⟨r, hr, hq'⟩⟩

end Aux

/-! ## Basic properties of `fpStep` -/

/-- `fpStep` is monotone. -/
private theorem fpStep_mono [HasTau Label] {lts : LTS State Label} {r₁ r₂ : State → State → Prop}
    (h : ∀ ⦃p q⦄, r₁ p q → r₂ p q) : ∀ ⦃p q⦄, fpStep lts r₁ p q → fpStep lts r₂ p q := by
  rintro p q ⟨hpq, hsim, hcoup⟩
  refine ⟨h hpq, ?_, ?_⟩
  · rintro μ p' htr
    obtain ⟨q', hq', hd⟩ := hsim μ p' htr
    exact ⟨q', h hq', hd⟩
  · obtain ⟨q', hτ, hq'⟩ := hcoup
    exact ⟨q', hτ, h hq'⟩

/-- A relation is a fixed point of `fpStep` iff it is a coupled delay simulation (Sect. 3 of
[Bisping2019]). -/
private theorem fpStep_self_iff_cds [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} : fpStep lts r = r ↔ IsCoupledDelaySimulation lts r := by
  constructor
  · intro h
    have hcl : ∀ ⦃p q⦄, r p q → fpStep lts r p q := by
      intro p q hpq
      rw [h]
      exact hpq
    refine ⟨?_, ?_⟩
    · rintro p q hpq μ p' htr
      exact (hcl hpq).2.1 μ p' htr
    · rintro p q hpq
      exact (hcl hpq).2.2
  · intro h
    funext p q
    exact propext ⟨fun hc => hc.1, fun hpq => ⟨hpq, h.1 hpq, h.2 hpq⟩⟩

/-- A coupled delay simulation is a coupled simulation. -/
private theorem cds_isCoupledSimulation [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (h : IsCoupledDelaySimulation lts r) :
    IsCoupledSimulation lts r :=
  ⟨fun p q hpq μ p' htr => by
    obtain ⟨q', hq', hd⟩ := h.1 hpq μ p' htr
    exact ⟨q', hq', Aux.dtr_sttr hd⟩, h.2⟩

/-! ## The greatest fixed point characterizes the preorder (Lemma 7) -/

/-- **Lemma 7 of [Bisping2019]**: the greatest fixed points of `fpStep` are exactly the relations
equivalent to the coupled simulation preorder. -/
theorem gfp_iff_preorder [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) :
    IsGreatestFixedPt lts r ↔ ∀ p q, r p q ↔ p ≼cs[lts] q := by
  constructor
  · rintro ⟨hfix, hgreat⟩ p q
    constructor
    · intro hpq
      exact ⟨r, cds_isCoupledSimulation (fpStep_self_iff_cds.mp hfix), hpq⟩
    · intro hpre
      have hufix : fpStep lts (CoupledSimulationPreorder lts) = CoupledSimulationPreorder lts :=
        (fpStep_self_iff_cds).mpr (Aux.coupledSimPreorder_isCD lts)
      exact hgreat (CoupledSimulationPreorder lts) hufix hpre
  · intro hiff
    refine ⟨(fpStep_self_iff_cds).mpr ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rintro p q hpq μ p' htr
        obtain ⟨q', hq', hd⟩ := (Aux.coupledSimPreorder_isCD lts).1 ((hiff p q).mp hpq) μ p' htr
        exact ⟨q', ⟨(hiff p' q').mpr hq', hd⟩⟩
      · rintro p q hpq
        obtain ⟨q', hτ, hq'⟩ := (Aux.coupledSimPreorder_isCD lts).2 ((hiff p q).mp hpq)
        exact ⟨q', hτ, (hiff q' p).mpr hq'⟩
    · intro s hs p q hspq
      exact (hiff p q).mpr ⟨s, cds_isCoupledSimulation (fpStep_self_iff_cds.mp hs), hspq⟩

/-! ## The iteration (Lemma 8 and Theorem 2) -/

/-- Each iteration step applies `fpStep` to the previous iterate. -/
private theorem fpIter_succ [HasTau Label] (lts : LTS State Label) (n : ℕ) :
    fpIter lts (n + 1) = fpStep lts (fpIter lts n) := by
  show (fpStep lts)^[n + 1] (fun _ _ => True) = fpStep lts ((fpStep lts)^[n] (fun _ _ => True))
  rw [Function.iterate_succ_apply']

/-- Each iteration step of `fpIter` contracts the relation. -/
private theorem fpIter_step_le [HasTau Label] (lts : LTS State Label) {n : ℕ} {p q : State}
    (h : fpIter lts (n + 1) p q) : fpIter lts n p q := by
  rw [fpIter_succ lts n] at h
  exact h.1

/-- `fpIter` is antitone in the iteration index. -/
private theorem fpIter_antitone [HasTau Label] (lts : LTS State Label) :
    ∀ {n m : ℕ}, n ≤ m → ∀ {p q : State}, fpIter lts m p q → fpIter lts n p q := by
  intro n m hnm
  induction hnm with
  | refl => intro p q h; exact h
  | step _ ih => intro p q h; exact ih (fpIter_step_le lts h)

/-- The extension of a relation to a set of pairs. -/
private def relExt (r : State → State → Prop) : Set (State × State) := {x | r x.1 x.2}

/-- `relExt` is injective. -/
private theorem relExt_injective {State : Type*} :
    Function.Injective
      (fun (r : State → State → Prop) => ({x : State × State | r x.1 x.2} : Set (State × State))) := by
  intro r₁ r₂ hext
  funext p q
  exact congrArg (fun (s : Set (State × State)) => (p, q) ∈ s) hext

/-- **Lemma 8 of [Bisping2019]**: on finite state spaces, the iteration of `fpStep` stabilizes. -/
private theorem exists_fpIter_fixed [HasTau Label] [Finite State] (lts : LTS State Label) :
    ∃ n, fpIter lts n = fpIter lts (n + 1) := by
  by_contra hcon
  -- if the iteration never stabilizes, the extensions of the iterates form an injective
  -- sequence of subsets of the finite set `State × State`
  have hinj : Function.Injective (fun n : ℕ => relExt (fpIter lts n)) := by
    intro i j hij
    rcases Nat.lt_trichotomy i j with h | h | h
    · have hij' : fpIter lts i = fpIter lts j := relExt_injective hij
      have hstep : fpIter lts (i + 1) = fpIter lts j := by
        funext p q
        exact propext ⟨fun hpq => by rw [← hij']; exact fpIter_step_le lts hpq,
          fun hpq => fpIter_antitone lts (Nat.succ_le_of_lt h) hpq⟩
      exact absurd ⟨i, hij'.trans hstep.symm⟩ hcon
    · exact h
    · have hji' : fpIter lts j = fpIter lts i := (relExt_injective hij).symm
      have hstep : fpIter lts (j + 1) = fpIter lts i := by
        funext p q
        exact propext ⟨fun hpq => by rw [← hji']; exact fpIter_step_le lts hpq,
          fun hpq => fpIter_antitone lts (Nat.succ_le_of_lt h) hpq⟩
      exact absurd ⟨j, hji'.trans hstep.symm⟩ hcon
  have hrange : (Set.range (fun n : ℕ => relExt (fpIter lts n))).Finite :=
    Set.Finite.subset
      (Set.Finite.powerset (Set.finite_univ : (Set.univ : Set (State × State)).Finite))
      (by rw [Set.range_subset_iff]; intro n; exact Set.subset_univ _)
  exact Set.infinite_range_of_injective hinj hrange

/-- Every fixed point of `fpStep` is contained in every iterate. -/
private theorem fixedPoint_subset_fpIter [HasTau Label] (lts : LTS State Label)
    {u : State → State → Prop} (hu : fpStep lts u = u) :
    ∀ (k : ℕ) {p q : State}, u p q → fpIter lts k p q := by
  intro k
  induction k with
  | zero => intro p q h; exact trivial
  | succ k ih =>
    intro p q h
    rw [fpIter_succ lts k]
    exact fpStep_mono (fun a b hab => ih hab) (by rw [hu]; exact h)

/-- **Theorem 2 of [Bisping2019]**: on finite state spaces, the fixed-point iteration returns the
coupled simulation preorder. -/
theorem exists_fpIter_eq_preorder [HasTau Label] [Finite State] (lts : LTS State Label) :
    ∃ n, ∀ p q, fpIter lts n p q ↔ p ≼cs[lts] q := by
  obtain ⟨n, hn⟩ := exists_fpIter_fixed lts
  have hfix : fpStep lts (fpIter lts n) = fpIter lts n := by
    rw [← fpIter_succ lts n, hn]
  refine ⟨n, (gfp_iff_preorder lts (fpIter lts n)).mp ⟨hfix, ?_⟩⟩
  intro s hs p q hspq
  exact fixedPoint_subset_fpIter lts hs n hspq

end MercLib.CoupledSim
