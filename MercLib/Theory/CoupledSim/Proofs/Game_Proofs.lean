module

public import MercLib.Theory.CoupledSim.Game

open Cslib (LTS HasTau)

@[expose] public section GameProofs

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

/-- A coupled delay simulation is a coupled simulation. -/
private theorem cds_isCoupledSimulation [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (h : IsCoupledDelaySimulation lts r) :
    IsCoupledSimulation lts r :=
  ⟨fun p q hpq μ p' htr => by
    obtain ⟨q', hq', hd⟩ := h.1 hpq μ p' htr
    exact ⟨q', hq', dtr_sttr hd⟩, h.2⟩

end Aux

/-! ## Unfolding the defender's winning region -/

/-- The defender's winning region is a fixed point of `defenderStep` (coinduction principle:
`DefenderWinning` is the greatest fixed point of `defenderHom`). -/
private theorem defenderWinning_unfold [HasTau Label] (lts : LTS State Label) :
    defenderStep lts (DefenderWinning lts) = DefenderWinning lts :=
  (defenderHom lts).map_gfp

/-- At an attacker node, membership in the winning region means coping with every attacker
move. -/
private theorem dw_att [HasTau Label] (lts : LTS State Label) {p q : State}
    (h : DefenderWinning lts (.att p q)) :
    ∀ n', CSGameMoves lts (.att p q) n' → DefenderWinning lts n' := by
  have hstep : defenderStep lts (DefenderWinning lts) (.att p q) := by
    rw [defenderWinning_unfold lts]
    exact h
  exact hstep

/-- At a simulation defender node, membership in the winning region yields a successor move. -/
private theorem dw_sim [HasTau Label] (lts : LTS State Label) {a : Label} {p' q : State}
    (h : DefenderWinning lts (.sim a p' q)) :
    ∃ n', CSGameMoves lts (.sim a p' q) n' ∧ DefenderWinning lts n' := by
  have hstep : defenderStep lts (DefenderWinning lts) (.sim a p' q) := by
    rw [defenderWinning_unfold lts]
    exact h
  exact hstep

/-- At a coupling defender node, membership in the winning region yields a catch-up move. -/
private theorem dw_cpl [HasTau Label] (lts : LTS State Label) {p q : State}
    (h : DefenderWinning lts (.cpl p q)) :
    ∃ q', lts.τSTr q q' ∧ DefenderWinning lts (.att q' p) := by
  have hstep : defenderStep lts (DefenderWinning lts) (.cpl p q) := by
    rw [defenderWinning_unfold lts]
    exact h
  exact hstep

/-! ## The game characterisation (Theorem 3) -/

/-- The relation on states induced by the defender's winning region: `a` and `b` are related iff
the defender wins the game at the attacker position `att a b`. -/
private def winRel [HasTau Label] (lts : LTS State Label) (a b : State) : Prop :=
  DefenderWinning lts (.att a b)

/-- **Theorem 3 of [Bisping2019]** (direction ⇒): the relation induced by the defender's winning
region is a coupled delay simulation. -/
private theorem winRel_isCDS [HasTau Label] (lts : LTS State Label) :
    IsCoupledDelaySimulation lts (winRel lts) := by
  refine ⟨?_, ?_⟩
  · rintro a b hab μ b' htr
    by_cases hμ : μ = HasTau.τ
    · subst hμ
      exact ⟨b, dw_att lts hab (.att b' b) ⟨htr, rfl⟩, DTr.tau⟩
    · obtain ⟨n', hmove, hdw⟩ :=
        dw_sim lts (dw_att lts hab (.sim μ b' b) ⟨htr, hμ, rfl⟩)
      cases n' with
      | att p2 q2 =>
        obtain ⟨heq, hd⟩ := hmove
        subst heq
        exact ⟨q2, hdw, hd⟩
      | sim a2 p2 q2 => exact (hmove : False).elim
      | cpl p2 q2 => exact (hmove : False).elim
  · rintro a b hab
    obtain ⟨q', hτ, hdw⟩ := dw_cpl lts (dw_att lts hab (.cpl a b) ⟨rfl, rfl⟩)
    exact ⟨q', hτ, hdw⟩

/-- **Theorem 3 of [Bisping2019]** (direction ⇒): if the defender wins the game at `att p q`,
then `p ≼cs[lts] q`. -/
private theorem preorder_of_defenderWinning [HasTau Label] (lts : LTS State Label) {p q : State}
    (h : DefenderWinning lts (.att p q)) : p ≼cs[lts] q :=
  ⟨winRel lts, Aux.cds_isCoupledSimulation (winRel_isCDS lts), h⟩

/-- The canonical candidate winning region derived from the coupled simulation preorder. -/
private def preorderWinning [HasTau Label] (lts : LTS State Label) : CSGameNode lts → Prop :=
  fun n =>
    match n with
    | .att p q => p ≼cs[lts] q
    | .sim a p' q => ∃ q', DTr lts q a q' ∧ p' ≼cs[lts] q'
    | .cpl p q => ∃ q', lts.τSTr q q' ∧ q' ≼cs[lts] p

/-- The candidate region is a post-fixpoint of `defenderStep` (the positional strategy of
Lemma 10 of [Bisping2019]). -/
private theorem preorderWinning_postfix [HasTau Label] (lts : LTS State Label) :
    preorderWinning lts ≤ defenderStep lts (preorderWinning lts) := by
  rintro n hn
  cases n with
  | att p q =>
    intro n' hmove
    cases n' with
    | sim μ b' b =>
      obtain ⟨htr, hμ, heq⟩ := hmove
      subst heq
      obtain ⟨q2, hpq2, hd⟩ := (Aux.coupledSimPreorder_isCD lts).1 hn μ b' htr
      exact ⟨q2, hd, hpq2⟩
    | att p' q' =>
      obtain ⟨htr, heq⟩ := hmove
      subst heq
      exact Aux.preorder_tau_challenge_trivial (Aux.τSTr_of_tr htr) hn
    | cpl p' q' =>
      obtain ⟨heq1, heq2⟩ := hmove
      subst heq1
      subst heq2
      exact (Aux.coupledSimPreorder_isCD lts).2 hn
  | sim a p' q =>
    obtain ⟨q', hd, hpq⟩ := hn
    exact ⟨.att p' q', ⟨rfl, hd⟩, hpq⟩
  | cpl p q => exact hn

/-- **Theorem 3 of [Bisping2019]** (direction ⇐): if `p ≼cs[lts] q`, the defender wins the game
at `att p q`. -/
private theorem defenderWinning_of_preorder [HasTau Label] (lts : LTS State Label) {p q : State}
    (h : p ≼cs[lts] q) : DefenderWinning lts (.att p q) :=
  (OrderHom.le_gfp (defenderHom lts) (preorderWinning_postfix lts)) (.att p q) h

/-- **Theorem 3 of [Bisping2019]**: the defender wins the coupled simulation game at `att p q`
precisely if `p ≼cs[lts] q`. -/
theorem defenderWinning_iff_preorder [HasTau Label] (lts : LTS State Label) (p q : State) :
    DefenderWinning lts (.att p q) ↔ p ≼cs[lts] q :=
  ⟨preorder_of_defenderWinning lts, defenderWinning_of_preorder lts⟩

end MercLib.CoupledSim
