import Sigref.SigE
import Sigref.SigData
import Sigref.RelBisim
import Sigref.Proofs.SigData_Proofs
import Sigref.Proofs.RelBisim_Proofs

/-!
# Proofs: SigE

`Sig`-equality is `E π`: witness lemma, non-absorbed normal form and the two inclusions.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/SigE_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label] {lts : LTS State Label} {π : Setoid State}

namespace SigData

variable (d : SigData lts π)

/-- The local pre-signature of `s` (inert τ-steps tagged by the hash of their target). -/
def PS (s : State) : Set (Label × (Quotient π ⊕ d.Tag)) :=
  PreSig lts (Quotient.mk π) d.sigHash s

theorem ps_inl {s x : State} {a : Label} (hTr : lts.Tr s a x) (hN : a ≠ HasTau.τ ∨ ¬ π.r s x) :
    (a, Sum.inl (Quotient.mk π x)) ∈ d.PS s := by
  refine Or.inl ⟨a, x, hTr, ?_, rfl⟩
  rcases hN with h | h
  · exact Or.inl h
  · exact Or.inr (fun h' => h (Quotient.exact h'))

theorem ps_inr {s x : State} (hTr : lts.Tr s HasTau.τ x) (hπ : π.r s x) :
    (HasTau.τ, Sum.inr (d.sigHash x)) ∈ d.PS s :=
  Or.inr ⟨x, hTr, Quotient.sound hπ, rfl⟩

theorem ps_inl_elim {s : State} {a : Label} {α : Quotient π}
    (h : (a, Sum.inl α) ∈ d.PS s) :
    ∃ x, lts.Tr s a x ∧ (a ≠ HasTau.τ ∨ ¬ π.r s x) ∧ α = Quotient.mk π x := by
  rcases h with ⟨a', x, hTr, hN, he⟩ | ⟨x, _, _, he⟩
  · have h1 : a = a' := congrArg Prod.fst he
    have h2 : α = Quotient.mk π x := Sum.inl.inj (congrArg Prod.snd he)
    subst h1
    refine ⟨x, hTr, ?_, h2⟩
    rcases hN with h | h
    · exact Or.inl h
    · exact Or.inr (fun h' => h (Quotient.sound h'))
  · exact absurd (congrArg Prod.snd he) (by simp)

theorem ps_inr_elim {s : State} {a : Label} {c : d.Tag}
    (h : (a, Sum.inr c) ∈ d.PS s) :
    a = HasTau.τ ∧ ∃ x, lts.Tr s HasTau.τ x ∧ π.r s x ∧ c = d.sigHash x := by
  rcases h with ⟨a', x, _, _, he⟩ | ⟨x, hTr, hπ, he⟩
  · exact absurd (congrArg Prod.snd he) (by simp)
  · have h1 : a = HasTau.τ := congrArg Prod.fst he
    have h2 : c = d.sigHash x := Sum.inr.inj (congrArg Prod.snd he)
    exact ⟨h1, x, hTr, Quotient.exact hπ, h2⟩

/-- Absorption: `a` is an inert successor of `s` whose signature absorbs the local one of `s`. -/
def Absorbs (s a : State) : Prop :=
  lts.Tr s HasTau.τ a ∧ π.r s a ∧ d.PS s ⊆ d.sigFn a ∪ {(HasTau.τ, Sum.inr (d.sigHash a))}

/-- Either `s` is not absorbed and its signature is the local one, or it equals that of an absorber. -/
theorem sig_cases (s : State) :
    ((∀ a, ¬ d.Absorbs s a) ∧ d.sigFn s = d.PS s) ∨ ∃ a, d.Absorbs s a ∧ d.sigFn s = d.sigFn a := by
  have hfix := d.hFix s
  unfold Sig at hfix
  by_cases hc : ∃ a, lts.Tr s HasTau.τ a ∧ Quotient.mk π s = Quotient.mk π a ∧
      PreSig lts (Quotient.mk π) d.sigHash s ⊆ d.sigFn a ∪ {(HasTau.τ, Sum.inr (d.sigHash a))}
  · rw [dif_pos hc] at hfix
    obtain ⟨h1, h2, h3⟩ := hc.choose_spec
    exact Or.inr ⟨hc.choose, ⟨h1, Quotient.exact h2, h3⟩, hfix⟩
  · rw [dif_neg hc] at hfix
    refine Or.inl ⟨fun a ⟨h1, h2, h3⟩ => hc ⟨a, h1, Quotient.sound h2, h3⟩, hfix⟩

/-- The local signature's `inl` entries are always in the signature. -/
theorem ps_inl_sub {s : State} {a : Label} {α : Quotient π} (h : (a, Sum.inl α) ∈ d.PS s) :
    (a, Sum.inl α) ∈ d.sigFn s := by
  rcases d.sig_cases s with ⟨_, he⟩ | ⟨a', ha, he⟩
  · rw [he]; exact h
  · rw [he]
    rcases ha.2.2 h with h' | h'
    · exact h'
    · exact absurd (congrArg Prod.snd h') (by simp)

/-- Local `inr` entries are in the signature unless they are the absorber's own tag. -/
theorem ps_inr_cases {s : State} {c : d.Tag} (h : (HasTau.τ, Sum.inr c) ∈ d.PS s) :
    (HasTau.τ, Sum.inr c) ∈ d.sigFn s ∨
      ∃ a, d.Absorbs s a ∧ d.sigFn s = d.sigFn a ∧ c = d.sigHash a := by
  rcases d.sig_cases s with ⟨_, he⟩ | ⟨a', ha, he⟩
  · exact Or.inl (by rw [he]; exact h)
  · rcases ha.2.2 h with h' | h'
    · exact Or.inl (by rw [he]; exact h')
    · exact Or.inr ⟨a', ha, he, Sum.inr.inj (congrArg Prod.snd h')⟩

/-- **Witness lemma**: every entry of `σ s` is a *local* entry of some inert-reachable state with
the same signature. -/
theorem witness (hWF : TauLoopFree lts) (s : State) :
    ∀ e, e ∈ d.sigFn s → ∃ s', InertReach lts π s s' ∧ d.sigFn s' = d.sigFn s ∧ e ∈ d.PS s' := by
  induction s using hWF.induction with
  | _ s ih =>
    intro e he
    rcases d.sig_cases s with ⟨_, hs⟩ | ⟨a, ha, hs⟩
    · exact ⟨s, Relation.ReflTransGen.refl, rfl, by rw [hs] at he; exact he⟩
    · rw [hs] at he
      obtain ⟨s', hIR, hσ, hmem⟩ := ih a ha.1 e he
      exact ⟨s', Relation.ReflTransGen.head ⟨ha.1, ha.2.1⟩ hIR, hσ.trans hs.symm, hmem⟩

/-- **Equal signatures imply `E π`.** -/
theorem sig_E (hWF : TauLoopFree lts) {s t : State} (hπ : π.r s t)
    (h : d.sigFn s = d.sigFn t) : E lts π s t := by
  refine E_coind lts π (fun s t => π.r s t ∧ d.sigFn s = d.sigFn t)
    (fun s t h => ⟨π.symm h.1, h.2.symm⟩) ?_ s t ⟨hπ, h⟩
  rintro s t ⟨hπ, hσ⟩
  refine ⟨hπ, fun a s1 hTr => ?_⟩
  by_cases hin : a = HasTau.τ ∧ π.r s s1
  · obtain ⟨rfl, hπ1⟩ := hin
    rcases d.ps_inr_cases (d.ps_inr hTr hπ1) with hmem | ⟨b, hb, hσb, hc⟩
    · obtain ⟨t', hIR, hσt', hmem'⟩ := d.witness hWF t _ (hσ ▸ hmem)
      obtain ⟨_, u, hTr', hπu, hu⟩ := d.ps_inr_elim hmem'
      have hπt' : π.r s t' := π.trans hπ (InertReach.rel lts π hIR)
      exact Or.inr ⟨t', u, hIR, ⟨hπt', hσ.trans hσt'.symm⟩, hTr',
        Or.inl ⟨rfl, hπ1, π.trans (π.symm hπ1) (π.trans hπt' hπu),
          (d.hCoh s1 u).1 hu⟩⟩
    · have hσ1 : d.sigFn s1 = d.sigFn t := ((d.hCoh s1 b).1 hc).trans (hσb.symm.trans hσ)
      exact Or.inl ⟨rfl, hπ1, π.trans (π.symm hπ1) hπ, hσ1⟩
  · have hmem := d.ps_inl_sub (d.ps_inl hTr (not_and_or.1 hin))
    obtain ⟨t', hIR, hσt', hmem'⟩ := d.witness hWF t _ (hσ ▸ hmem)
    obtain ⟨y, hTr', _, hq⟩ := d.ps_inl_elim hmem'
    exact Or.inr ⟨t', y, hIR, ⟨π.trans hπ (InertReach.rel lts π hIR), hσ.trans hσt'.symm⟩, hTr',
      Or.inr ⟨not_and_or.1 hin, Quotient.exact hq⟩⟩

/-- Every state has an inert-reachable, non-absorbed state with the same signature. -/
theorem normal_form (hWF : TauLoopFree lts) (s : State) :
    ∃ s', InertReach lts π s s' ∧ d.sigFn s' = d.sigFn s ∧ ∀ a, ¬ d.Absorbs s' a := by
  induction s using hWF.induction with
  | _ s ih =>
    rcases d.sig_cases s with ⟨hna, _⟩ | ⟨a, ha, hs⟩
    · exact ⟨s, Relation.ReflTransGen.refl, rfl, hna⟩
    · obtain ⟨s', hIR, hσ, hna⟩ := ih a ha.1
      exact ⟨s', Relation.ReflTransGen.head ⟨ha.1, ha.2.1⟩ hIR, hσ.trans hs.symm, hna⟩

theorem sig_eq_PS {s : State} (h : ∀ a, ¬ d.Absorbs s a) : d.sigFn s = d.PS s := by
  rcases d.sig_cases s with ⟨_, he⟩ | ⟨a, ha, _⟩
  · exact he
  · exact absurd ha (h a)

variable [Finite State]

/-- **`E π` implies equal signatures** (for a τ-loop-free LTS). Strong induction along a total
order extending the τ-order: states are replaced by non-absorbed representatives of their inert
class, whose local signatures must coincide because an `E`-related inert successor would absorb. -/
theorem E_sig (hWF : TauLoopFree lts) {x y : State} (hE : E lts π x y) :
    d.sigFn x = d.sigFn y := by
  obtain ⟨lt, hlt, htot, hmono, htrans⟩ := exists_tau_order lts hWF
  have le_IR : ∀ {s s' : State}, InertReach lts π s s' → s' = s ∨ lt s' s := by
    intro s s' h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
      rcases ih with rfl | h
      · exact Or.inr (hmono _ _ hstep.1)
      · exact Or.inr (htrans _ _ _ (hmono _ _ hstep.1) h)
  have MC : ∀ m, ∀ x y, E lts π x y → (x = m ∨ lt x m) → (y = m ∨ lt y m) →
      d.sigFn x = d.sigFn y := by
    intro m
    induction m using hlt.induction with
    | _ m ih =>
      intro x y hE hx hy
      have lt_m : ∀ {p q : State}, lt p q → (q = m ∨ lt q m) → lt p m := by
        intro p q hpq hq
        rcases hq with rfl | h
        · exact hpq
        · exact htrans _ _ _ hpq h
      have le_m : ∀ {p q : State}, (q = m ∨ lt q m) → (p = q ∨ lt p q) → (p = m ∨ lt p m) := by
        intro p q hq hp
        rcases hp with rfl | h
        · exact hq
        · exact Or.inr (lt_m h hq)
      have IH' : ∀ p q, E lts π p q → lt p m → lt q m → d.sigFn p = d.sigFn q := by
        intro p q hpq hp hq
        by_cases hne : p = q
        · rw [hne]
        rcases htot p q hne with h | h
        · exact ih q hq p q hpq (Or.inr h) (Or.inl rfl)
        · exact ih p hp p q hpq (Or.inl rfl) (Or.inr h)
      have Abs : ∀ p a, (p = m ∨ lt p m) → lts.Tr p HasTau.τ a → π.r p a → E lts π p a →
          d.Absorbs p a := by
        intro p a hp hTr hπ hEpa
        have hap_m : lt a m := lt_m (hmono p a hTr) hp
        refine ⟨hTr, hπ, ?_⟩
        rintro ⟨b, α | c⟩ he
        · obtain ⟨y, hTry, hN, hα⟩ := d.ps_inl_elim he
          rcases E_step lts π hEpa hTry with ⟨hb, hπy, _⟩ | ⟨a', y1, hIR, hEa', hTr', hcase⟩
          · exfalso
            rcases hN with h | h
            · exact h hb
            · exact h hπy
          · rcases hcase with ⟨hb, hπy, _⟩ | ⟨_, hπy1⟩
            · exfalso
              rcases hN with h | h
              · exact h hb
              · exact h hπy
            · have hπa' : π.r p a' := hEa'.1
              have hN' : b ≠ HasTau.τ ∨ ¬ π.r a' y1 := by
                rcases hN with h | h
                · exact Or.inl h
                · exact Or.inr (fun h' => h (π.trans hπa' (π.trans h' (π.symm hπy1))))
              have hmem := d.ps_inl_sub (d.ps_inl hTr' hN')
              have hlta' : lt a' m := by
                rcases le_IR hIR with h | h
                · rw [h]; exact hap_m
                · exact htrans _ _ _ h hap_m
              have hσ : d.sigFn a = d.sigFn a' :=
                IH' a a' (E.trans lts π (E.symm lts π hEpa) hEa') hap_m hlta'
              refine Or.inl ?_
              rw [hσ, hα.trans (Quotient.sound hπy1)]
              exact hmem
        · obtain ⟨hb, u, hTru, hπu, hc⟩ := d.ps_inr_elim he
          subst hb
          have hum : lt u m := lt_m (hmono p u hTru) hp
          rcases E_step lts π hEpa hTru with ⟨_, _, hEu⟩ | ⟨a', u1, hIR, hEa', hTr', hcase⟩
          · refine Or.inr ?_
            have hh : d.sigHash u = d.sigHash a := (d.hCoh u a).2 (IH' u a hEu hum hap_m)
            rw [hc, hh]; rfl
          · rcases hcase with ⟨_, _, hEu1⟩ | ⟨hne, _⟩
            · have hπa' : π.r p a' := hEa'.1
              have hlta' : lt a' m := by
                rcases le_IR hIR with h | h
                · rw [h]; exact hap_m
                · exact htrans _ _ _ h hap_m
              have hu1m : lt u1 m := htrans _ _ _ (hmono a' u1 hTr') hlta'
              have hh : d.sigHash u = d.sigHash u1 := (d.hCoh u u1).2 (IH' u u1 hEu1 hum hu1m)
              have hπa'u1 : π.r a' u1 := π.trans (π.symm hπa') (π.trans hπu hEu1.1)
              have hmem := d.ps_inr hTr' hπa'u1
              have hσa : d.sigFn a = d.sigFn a' :=
                IH' a a' (E.trans lts π (E.symm lts π hEpa) hEa') hap_m hlta'
              rcases d.ps_inr_cases hmem with hm | ⟨a'', ha'', hσa', hc'⟩
              · refine Or.inl ?_
                rw [hσa, hc, hh]; exact hm
              · refine Or.inr ?_
                have h1 : d.sigFn u1 = d.sigFn a'' := (d.hCoh u1 a'').1 hc'
                have h2 : d.sigFn u1 = d.sigFn a := h1.trans (hσa'.symm.trans hσa.symm)
                have h3 : d.sigHash u1 = d.sigHash a := (d.hCoh u1 a).2 h2
                rw [hc, hh, h3]; rfl
            · exfalso
              rcases hne with h | h
              · exact h rfl
              · exact h hπu
      have sub : ∀ p q, (p = m ∨ lt p m) → (q = m ∨ lt q m) → E lts π p q →
          (∀ a, ¬ d.Absorbs p a) → (∀ a, ¬ d.Absorbs q a) → d.PS p ⊆ d.PS q := by
        intro p q hp hq hEpq hnp hnq
        have triv : ∀ q', InertReach lts π q q' → E lts π p q' → q' = q := by
          intro q' hIR hEq'
          rcases hIR.cases_head with h | ⟨q1, hstep, hrest⟩
          · exact h.symm
          · exfalso
            have hEq1 : E lts π p q1 :=
              E_stutter lts π hWF hEpq (Relation.ReflTransGen.single hstep) hrest hEq'
            exact hnq q1 (Abs q q1 hq hstep.1 hstep.2
              (E.trans lts π (E.symm lts π hEpq) hEq1))
        rintro ⟨b, α | c⟩ he
        · obtain ⟨y, hTry, hN, hα⟩ := d.ps_inl_elim he
          rcases E_step lts π hEpq hTry with ⟨hb, hπy, _⟩ | ⟨q', y1, hIR, hEq', hTr', hcase⟩
          · exfalso
            rcases hN with h | h
            · exact h hb
            · exact h hπy
          · rcases hcase with ⟨hb, hπy, _⟩ | ⟨_, hπy1⟩
            · exfalso
              rcases hN with h | h
              · exact h hb
              · exact h hπy
            · have hqq := triv q' hIR hEq'
              rw [hqq] at hTr' hEq'
              have hN' : b ≠ HasTau.τ ∨ ¬ π.r q y1 := by
                rcases hN with h | h
                · exact Or.inl h
                · exact Or.inr (fun h' => h (π.trans hEq'.1 (π.trans h' (π.symm hπy1))))
              rw [hα.trans (Quotient.sound hπy1)]
              exact d.ps_inl hTr' hN'
        · obtain ⟨hb, u, hTru, hπu, hc⟩ := d.ps_inr_elim he
          subst hb
          rcases E_step lts π hEpq hTru with ⟨_, _, hEu⟩ | ⟨q', u1, hIR, hEq', hTr', hcase⟩
          · exfalso
            exact hnp u (Abs p u hp hTru hπu (E.trans lts π hEpq (E.symm lts π hEu)))
          · rcases hcase with ⟨_, _, hEu1⟩ | ⟨hne, _⟩
            · have hqq := triv q' hIR hEq'
              rw [hqq] at hTr' hEq'
              have hum : lt u m := lt_m (hmono p u hTru) hp
              have hu1m : lt u1 m := lt_m (hmono q u1 hTr') hq
              have hh : d.sigHash u = d.sigHash u1 := (d.hCoh u u1).2 (IH' u u1 hEu1 hum hu1m)
              have hπ : π.r q u1 := π.trans (π.symm hEq'.1) (π.trans hπu hEu1.1)
              rw [hc, hh]
              exact d.ps_inr hTr' hπ
            · exfalso
              rcases hne with h | h
              · exact h rfl
              · exact h hπu
      obtain ⟨x', hIRx, hσx, hnax⟩ := d.normal_form hWF x
      obtain ⟨y', hIRy, hσy, hnay⟩ := d.normal_form hWF y
      have hx' := le_m hx (le_IR hIRx)
      have hy' := le_m hy (le_IR hIRy)
      have hExx' : E lts π x x' := d.sig_E hWF (InertReach.rel lts π hIRx) hσx.symm
      have hEyy' : E lts π y y' := d.sig_E hWF (InertReach.rel lts π hIRy) hσy.symm
      have hE' : E lts π x' y' :=
        E.trans lts π (E.symm lts π hExx') (E.trans lts π hE hEyy')
      have h1 := sub x' y' hx' hy' hE' hnax hnay
      have h2 := sub y' x' hy' hx' (E.symm lts π hE') hnay hnax
      have hPS : d.PS x' = d.PS y' := Set.Subset.antisymm h1 h2
      rw [← hσx, ← hσy, d.sig_eq_PS hnax, d.sig_eq_PS hnay, hPS]
  by_cases hxy : x = y
  · rw [hxy]
  · rcases htot x y hxy with h | h
    · exact MC y x y hE (Or.inr h) (Or.inl rfl)
    · exact MC x x y hE (Or.inl rfl) (Or.inr h)

/-- **`Sig`-equality is `E π`**: for `π`-related states of a finite τ-loop-free LTS, equal
signatures hold exactly when the states are `E π`-related. -/
theorem sig_iff_E (hWF : TauLoopFree lts) {s t : State} (hπ : π.r s t) :
    d.sigFn s = d.sigFn t ↔ E lts π s t :=
  ⟨d.sig_E hWF hπ, d.E_sig hWF⟩
end SigData

/-- Headline: signature equality is `E π`. -/
theorem sigEqualIffRelBisim [Finite State] {lts : LTS State Label} {π : Setoid State}
    (d : SigData lts π) : SigEqualIffRelBisim lts π d :=
  fun hWF _ _ hπ => SigData.sig_iff_E d hWF hπ

end Sigref
