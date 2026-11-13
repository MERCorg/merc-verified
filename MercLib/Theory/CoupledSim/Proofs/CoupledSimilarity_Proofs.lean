module

public import MercLib.Theory.CoupledSim.CoupledSimilarity

open Cslib (LTS HasTau)

@[expose] public section CoupledSimilarityProofs

namespace MercLib.CoupledSim

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The "headline"
theorems below are stated in `Challenges/CoupledSim.lean` (human-vetted). -/

/-! ## Helper lemmas about weak and delay steps -/

/-- A delay step is a weak step. -/
private theorem DTr.sttr [HasTau Label] {lts : LTS State Label}
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
private theorem IsWeakSimulation.stutter [HasTau Label] {lts : LTS State Label}
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
private theorem IsWeakSimulation.sttr [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : IsWeakSimulation lts r)
    {s s' t : State} {μ : Label} (hst : r s t) (h : lts.STr s μ s') :
    ∃ t', r s' t' ∧ lts.STr t μ t' := by
  cases h with
  | refl => exact ⟨t, hst, LTS.STr.refl⟩
  | tr hτ1 htr hτ2 =>
    obtain ⟨t1, hPath1, hr1⟩ := hr.stutter hst hτ1
    obtain ⟨t2, hr2, hsTr2⟩ := hr hr1 μ _ htr
    obtain ⟨t3, hPath3, hr3⟩ := hr.stutter hr2 hτ2
    exact ⟨t3, hr3, stτtail (stτhead hPath1 hsTr2) hPath3⟩

/-! ## Transitivity of weak simulations -/

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
    obtain ⟨q', hq', hsTr'⟩ := h₂.sttr h2u hsTr
    refine ⟨q', ?_, hsTr'⟩
    show ∃ u, (r₁ p' u ∧ r₂ u q') ∨ (r₂ p' u ∧ r₁ u q')
    exact ⟨u1, Or.inl ⟨hu1', hq'⟩⟩
  · obtain ⟨u1, hu1', hsTr⟩ := h₂ h2u μ p' htr
    obtain ⟨q', hq', hsTr'⟩ := h₁.sttr h1u hsTr
    refine ⟨q', ?_, hsTr'⟩
    show ∃ u, (r₁ p' u ∧ r₂ u q') ∨ (r₂ p' u ∧ r₁ u q')
    exact ⟨u1, Or.inr ⟨hu1', hq'⟩⟩

/-! ## Coupled simulations -/

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
theorem preorder_of_tauReach [HasTau Label] {lts : LTS State Label} {p q : State}
    (h : lts.τSTr q p) : p ≼cs[lts] q := by
  refine ⟨fun p q => lts.τSTr q p, tauReach_isCoupledSimulation lts, ?_⟩
  exact h

/-- **Lemma 2 of [Bisping2019]** (reflexivity): the coupled simulation preorder is reflexive. -/
theorem CoupledSimulationPreorder.refl [HasTau Label] (lts : LTS State Label) (s : State) :
    s ≼cs[lts] s :=
  preorder_of_tauReach LTS.τSTr.refl

/-! ## Transitivity of the coupled simulation preorder -/

/-- **Lemma 2 of [Bisping2019]** (transitivity): the coupled simulation preorder is transitive. -/
theorem CoupledSimulationPreorder.trans [HasTau Label] {lts : LTS State Label} {p q r : State}
    (h1 : p ≼cs[lts] q) (h2 : q ≼cs[lts] r) : p ≼cs[lts] r := by
  obtain ⟨R1, hR1, hR1pq⟩ := h1
  obtain ⟨R2, hR2, hR2qr⟩ := h2
  refine ⟨symComp R1 R2, ⟨?_, ?_⟩, ?_⟩
  · exact isWeakSimulation_trans_comp hR1.1 hR2.1
  · rintro a b ⟨u, ⟨h1u, h2u⟩ | ⟨h2u, h1u⟩⟩
    · obtain ⟨u1, hτ1, hu1⟩ := hR1.2 h1u
      obtain ⟨b1, hτ2, hb1⟩ := hR2.1.stutter h2u hτ1
      obtain ⟨b2, hτ3, hb2⟩ := hR2.2 hb1
      refine ⟨b2, Relation.ReflTransGen.trans hτ2 hτ3, u1, ?_⟩
      exact Or.inr ⟨hb2, hu1⟩
    · obtain ⟨u1, hτ1, hu1⟩ := hR2.2 h2u
      obtain ⟨b1, hτ2, hb1⟩ := hR1.1.stutter h1u hτ1
      obtain ⟨b2, hτ3, hb2⟩ := hR1.2 hb1
      refine ⟨b2, Relation.ReflTransGen.trans hτ2 hτ3, u1, ?_⟩
      exact Or.inl ⟨hb2, hu1⟩
  · exact ⟨q, Or.inl ⟨hR1pq, hR2qr⟩⟩

/-- **τ-challenges are trivial for the preorder**: from `p ⇒τ* p'` and `p ≼cs[lts] q` follows
`p' ≼cs[lts] q`. -/
private theorem preorder_tau_challenge_trivial [HasTau Label] {lts : LTS State Label}
    {p p' q : State} (hτ : lts.τSTr p p') (h : p ≼cs[lts] q) : p' ≼cs[lts] q :=
  CoupledSimulationPreorder.trans (preorder_of_tauReach hτ) h

/-! ## The preorder is a coupled delay simulation (Lemma 1) -/

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
        exact CoupledSimulationPreorder.trans ⟨r, hr, hv⟩ (preorder_of_tauReach hτ2)
  · rintro p q ⟨r, hr, hpq⟩
    obtain ⟨q', hτ, hq'⟩ := hr.2 hpq
    exact ⟨q', hτ, ⟨r, hr, hq'⟩⟩

/-- **Lemma 1 of [Bisping2019]**: `p ≼cs[lts] q` precisely if there is a coupled delay
simulation `r` such that `r p q`. -/
theorem cds_iff_preorder [HasTau Label] {lts : LTS State Label} {p q : State} :
    p ≼cs[lts] q ↔ ∃ r, IsCoupledDelaySimulation lts r ∧ r p q := by
  constructor
  · intro h
    exact ⟨CoupledSimulationPreorder lts, coupledSimPreorder_isCD lts, h⟩
  · rintro ⟨r, hr, hpq⟩
    refine ⟨r, ⟨fun p q hpq μ p' htr => ?_, hr.2⟩, hpq⟩
    obtain ⟨q', hq', hd⟩ := hr.1 hpq μ p' htr
    exact ⟨q', hq', DTr.sttr hd⟩

/-- **Corollary 1 of [Bisping2019]**: states on a `τ`-cycle are coupled similar. -/
theorem tauCycle_coupledSimilarity [HasTau Label] {lts : LTS State Label} {p q : State}
    (h1 : lts.τSTr p q) (h2 : lts.τSTr q p) : p ≡cs[lts] q :=
  ⟨preorder_of_tauReach h2, preorder_of_tauReach h1⟩

/-! ## Coinductive characterization (Lemma 3) -/

/-- The relation used for the coinductive characterization of the preorder: a pair satisfies the
coinductive rule of Lemma 3, or is already related by the preorder. -/
private def coindRel [HasTau Label] (lts : LTS State Label) (a b : State) : Prop :=
  ((∀ μ a', lts.Tr a μ a' → ∃ q', DTr lts b μ q' ∧ a' ≼cs[lts] q') ∧
    ∃ q', lts.τSTr b q' ∧ q' ≼cs[lts] a) ∨ a ≼cs[lts] b

/-- **Lemma 3 of [Bisping2019]**: the coupled simulation preorder can be characterized
coinductively: `p ≼cs[lts] q` iff every strong step of `p` can be answered by a delay step of
`q` into a related pair, and `q` can catch up to `p` by `τ`-steps into a related pair. -/
theorem preorder_coinductive_iff [HasTau Label] {lts : LTS State Label} {p q : State} :
    p ≼cs[lts] q ↔
      ((∀ μ p', lts.Tr p μ p' → ∃ q', DTr lts q μ q' ∧ p' ≼cs[lts] q') ∧
        ∃ q', lts.τSTr q q' ∧ q' ≼cs[lts] p) := by
  constructor
  · intro h
    obtain ⟨hsim, hcpl⟩ := coupledSimPreorder_isCD lts
    exact ⟨fun μ p' htr => by obtain ⟨q', hq', hd⟩ := hsim h μ p' htr; exact ⟨q', hd, hq'⟩,
      hcpl h⟩
  · rintro ⟨hsim, hcpl⟩
    refine ⟨coindRel lts, ⟨?_, ?_⟩, ?_⟩
    · rintro a b (⟨hs, _⟩ | hpre) μ a' htr
      · obtain ⟨q', hd, hq'⟩ := hs μ a' htr
        refine ⟨q', ?_, DTr.sttr hd⟩
        exact Or.inr hq'
      · obtain ⟨r, hr, hab⟩ := hpre
        obtain ⟨q', hq', hsTr⟩ := hr.1 hab μ a' htr
        refine ⟨q', ?_, hsTr⟩
        exact Or.inr ⟨r, hr, hq'⟩
    · rintro a b (⟨_, hc⟩ | hpre)
      · obtain ⟨q', hτ, hq'⟩ := hc
        refine ⟨q', hτ, ?_⟩
        exact Or.inr hq'
      · obtain ⟨r, hr, hab⟩ := hpre
        obtain ⟨q', hτ, hq'⟩ := hr.2 hab
        refine ⟨q', hτ, ?_⟩
        exact Or.inr ⟨r, hr, hq'⟩
    · exact Or.inl ⟨hsim, hcpl⟩

/-! ## τ-loop ignorance (Lemma 5) -/

/-- The relation witnessing Lemma 5: the identity on all states, plus the pair `(p, q)` and its
swap. -/
private def tauLoopRel (p q : State) (x y : State) : Prop :=
  x = y ∨ (x = p ∧ y = q) ∨ (x = q ∧ y = p)

/-- **Lemma 5 of [Bisping2019]**: if `p` and `q` have exactly the same outgoing transitions,
except that `p` has an additional `τ`-loop, then `p ≡cs[lts] q`. -/
theorem tauLoopIgnorance [HasTau Label] {lts : LTS State Label} {p q : State}
    (h : ∀ ⦃α p'⦄, lts.Tr p α p' ↔ (lts.Tr q α p' ∨ (α = HasTau.τ ∧ p' = p))) :
    p ≡cs[lts] q := by
  have hRsim : IsCoupledSimulation lts (tauLoopRel p q) := by
    constructor
    · rintro x y (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) μ x' htr
      · refine ⟨x', ?_, LTS.STr.single htr⟩
        exact Or.inl rfl
      · rcases h.mp htr with hq' | ⟨hμτ, hx'p⟩
        · refine ⟨x', ?_, LTS.STr.single hq'⟩
          exact Or.inl rfl
        · subst hμτ
          subst hx'p
          refine ⟨y, ?_, LTS.STr.refl⟩
          exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · refine ⟨x', ?_, LTS.STr.single (h.mpr (Or.inl htr))⟩
        exact Or.inl rfl
    · rintro x y (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · refine ⟨x, LTS.τSTr.refl, ?_⟩
        exact Or.inl rfl
      · refine ⟨y, LTS.τSTr.refl, ?_⟩
        exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · refine ⟨y, LTS.τSTr.refl, ?_⟩
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  refine ⟨?_, ?_⟩
  · refine ⟨tauLoopRel p q, hRsim, ?_⟩
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · refine ⟨tauLoopRel p q, hRsim, ?_⟩
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

end MercLib.CoupledSim
