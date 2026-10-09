import Sigref.Proofs.SigE_Proofs

/-!
# Proofs: absorption

A state whose local signature is absorbed by an inert τ-successor is `E π`-related to that
successor, whichever absorber the (non-deterministic) `choose` of `Sig` picked.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label] {lts : LTS State Label} {π : Setoid State}

namespace SigData

variable (d : SigData lts π)

/-- The matching condition of `E π` for two `π`-related states with equal signatures
(the core of `sig_E`, with the relation `σ`-equality made explicit). -/
theorem sig_match (hWF : TauLoopFree lts) {s t : State} (hπ : π.r s t)
    (hσ : d.sigFn s = d.sigFn t) {a : Label} {s1 : State} (hTr : lts.Tr s a s1) :
    (a = HasTau.τ ∧ π.r s s1 ∧ d.sigFn s1 = d.sigFn t) ∨
    ∃ t' t1, InertReach lts π t t' ∧ π.r s t' ∧ d.sigFn s = d.sigFn t' ∧ lts.Tr t' a t1 ∧
      ((a = HasTau.τ ∧ π.r s s1 ∧ π.r s1 t1 ∧ d.sigFn s1 = d.sigFn t1) ∨
        ((a ≠ HasTau.τ ∨ ¬ π.r s s1) ∧ π.r s1 t1)) := by
  by_cases hin : a = HasTau.τ ∧ π.r s s1
  · obtain ⟨rfl, hπ1⟩ := hin
    rcases d.ps_inr_cases (d.ps_inr hTr hπ1) with hmem | ⟨b, hb, hσb, hc⟩
    · obtain ⟨t', hIR, hσt', hmem'⟩ := d.witness hWF t _ (hσ ▸ hmem)
      obtain ⟨_, u, hTr', hπu, hu⟩ := d.ps_inr_elim hmem'
      have hπt' : π.r s t' := π.trans hπ (InertReach.rel lts π hIR)
      exact Or.inr ⟨t', u, hIR, hπt', hσ.trans hσt'.symm, hTr',
        Or.inl ⟨rfl, hπ1, π.trans (π.symm hπ1) (π.trans hπt' hπu), (d.hCoh s1 u).1 hu⟩⟩
    · have hσ1 : d.sigFn s1 = d.sigFn t := ((d.hCoh s1 b).1 hc).trans (hσb.symm.trans hσ)
      exact Or.inl ⟨rfl, hπ1, hσ1⟩
  · have hmem := d.ps_inl_sub (d.ps_inl hTr (not_and_or.1 hin))
    obtain ⟨t', hIR, hσt', hmem'⟩ := d.witness hWF t _ (hσ ▸ hmem)
    obtain ⟨y, hTr', _, hq⟩ := d.ps_inl_elim hmem'
    exact Or.inr ⟨t', y, hIR, π.trans hπ (InertReach.rel lts π hIR), hσ.trans hσt'.symm, hTr',
      Or.inr ⟨not_and_or.1 hin, Quotient.exact hq⟩⟩

/-- **An absorbing inert successor is `E π`-related.** -/
theorem absorbs_E (hWF : TauLoopFree lts) {z a : State} (hA : d.Absorbs z a) :
    E lts π z a := by
  obtain ⟨hza, hπza, hsub⟩ := hA
  let R : State → State → Prop := fun x y =>
    (π.r x y ∧ d.sigFn x = d.sigFn y) ∨
    (x = z ∧ π.r z y ∧ d.sigFn y = d.sigFn a) ∨
    (y = z ∧ π.r z x ∧ d.sigFn x = d.sigFn a)
  have hRs : ∀ x y, R x y → R y x := by
    rintro x y (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨π.symm h1, h2.symm⟩
    · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  refine E_coind lts π R hRs ?_ z a (Or.inr (Or.inl ⟨rfl, hπza, rfl⟩))
  rintro x y (⟨hπ, hσ⟩ | ⟨hx, hπ, hσ⟩ | ⟨hy, hπ, hσ⟩)
  · refine ⟨hπ, fun a' s1 hTr => ?_⟩
    rcases d.sig_match hWF hπ hσ hTr with ⟨h1, h2, h3⟩ | ⟨t', t1, hIR, h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2, Or.inl ⟨π.trans (π.symm h2) hπ, h3⟩⟩
    · refine Or.inr ⟨t', t1, hIR, Or.inl ⟨h1, h2⟩, h3, ?_⟩
      rcases h4 with ⟨e1, e2, e3, e4⟩ | h4
      · exact Or.inl ⟨e1, e2, Or.inl ⟨e3, e4⟩⟩
      · exact Or.inr h4
  · subst x
    -- the pair `(z, y)` with `σ y = σ a`
    refine ⟨hπ, fun a' z1 hTr => ?_⟩
    by_cases hin : a' = HasTau.τ ∧ π.r z z1
    · obtain ⟨rfl, hπ1⟩ := hin
      rcases hsub (d.ps_inr hTr hπ1) with hmem | hmem
      · obtain ⟨y', hIR, hσy', hmem'⟩ := d.witness hWF y _ (hσ ▸ hmem)
        obtain ⟨_, u, hTr', hπu, hu⟩ := d.ps_inr_elim hmem'
        have hπy' : π.r z y' := π.trans hπ (InertReach.rel lts π hIR)
        refine Or.inr ⟨y', u, hIR, Or.inr (Or.inl ⟨rfl, hπy', hσy'.trans hσ⟩), hTr',
          Or.inl ⟨rfl, hπ1, Or.inl ⟨π.trans (π.symm hπ1) (π.trans hπy' hπu),
            (d.hCoh z1 u).1 hu⟩⟩⟩
      · have hh : d.sigHash z1 = d.sigHash a := Sum.inr.inj (congrArg Prod.snd hmem)
        exact Or.inl ⟨rfl, hπ1, Or.inl ⟨π.trans (π.symm hπ1) hπ,
          ((d.hCoh z1 a).1 hh).trans hσ.symm⟩⟩
    · have hmem := hsub (d.ps_inl hTr (not_and_or.1 hin))
      have hmem' : (a', Sum.inl (Quotient.mk π z1)) ∈ d.sigFn a := by
        rcases hmem with h | h
        · exact h
        · exact absurd (congrArg Prod.snd h) (by simp)
      obtain ⟨y', hIR, hσy', hmem''⟩ := d.witness hWF y _ (hσ ▸ hmem')
      obtain ⟨x', hTr', _, hq⟩ := d.ps_inl_elim hmem''
      have hπy' : π.r z y' := π.trans hπ (InertReach.rel lts π hIR)
      exact Or.inr ⟨y', x', hIR, Or.inr (Or.inl ⟨rfl, hπy', hσy'.trans hσ⟩), hTr',
        Or.inr ⟨not_and_or.1 hin, Quotient.exact hq⟩⟩
  · subst y
    -- the pair `(x, z)` with `σ x = σ a`
    have hπxa : π.r x a := π.trans (π.symm hπ) hπza
    refine ⟨π.symm hπ, fun a' x1 hTr => ?_⟩
    rcases d.sig_match hWF hπxa hσ hTr with ⟨h1, h2, h3⟩ | ⟨t', t1, hIR, h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2, Or.inr (Or.inr ⟨rfl, π.trans hπ h2, h3⟩)⟩
    · refine Or.inr ⟨t', t1, Relation.ReflTransGen.head ⟨hza, hπza⟩ hIR, Or.inl ⟨h1, h2⟩, h3, ?_⟩
      rcases h4 with ⟨e1, e2, e3, e4⟩ | h4
      · exact Or.inl ⟨e1, e2, Or.inl ⟨e3, e4⟩⟩
      · exact Or.inr h4

end SigData

end Sigref
