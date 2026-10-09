import Sigref.Scc

/-!
# Proofs: the τ-SCC quotient

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/Scc_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

variable {State State' Label : Type} [HasTau Label]

theorem quotientCrossBisimulation (lts : LTS State Label) (blk : State → ℕ) :
    QuotientCrossBisimulation lts blk := by
  intro hs s b hr μ
  subst hr
  constructor
  · intro s' hstep
    by_cases helm : μ = HasTau.τ ∧ blk s = blk s'
    · exact Or.inl ⟨helm.1, helm.2.symm⟩
    · refine Or.inr ⟨blk s, blk s', LTS.STr.refl, ⟨s, s', rfl, rfl, hstep, ?_⟩, rfl, rfl⟩
      exact fun h => helm ⟨h.1, h.2⟩
  · rintro c ⟨s0, t0, h0, h1, hstep, hne⟩
    refine Or.inr ⟨s0, t0, (LTS.sTr_τSTr lts).mpr (hs s s0 h0.symm), hstep, h0, h1⟩

theorem quotientTauAcyclic (lts : LTS State Label) (blk : State → ℕ) (k : ℕ) :
    QuotientTauAcyclic lts blk k := by
  intro ⟨_, _, hiff⟩ b hcyc
  have hs : ∀ s t, blk s = blk t → lts.τSTr s t := fun s t h => ((hiff s t).1 h).1
  -- a quotient τ-step is a τ-step between members of different blocks
  have hedge : ∀ b c, (quotientTau lts blk).Tr b HasTau.τ c →
      ∃ s t, blk s = b ∧ blk t = c ∧ lts.Tr s HasTau.τ t ∧ b ≠ c := by
    rintro b c ⟨s, t, h1, h2, h3, h4⟩
    exact ⟨s, t, h1, h2, h3, fun h => h4 ⟨rfl, h⟩⟩
  -- a quotient τ-path lifts to a τ-path from any member of its source block
  have hlift : ∀ c b, Relation.ReflTransGen (fun b c => (quotientTau lts blk).Tr b HasTau.τ c) c b →
      ∀ t, blk t = c → ∃ s', blk s' = b ∧ lts.τSTr t s' := by
    intro c b h
    induction h with
    | refl => exact fun t ht => ⟨t, ht, Relation.ReflTransGen.refl⟩
    | tail _ hstep ih =>
      intro t ht
      obtain ⟨s', hs', hts'⟩ := ih t ht
      obtain ⟨s2, t2, h2, h3, h4, -⟩ := hedge _ _ hstep
      refine ⟨t2, h3, ?_⟩
      exact (hts'.trans (hs s' s2 (hs'.trans h2.symm))).tail h4
  obtain ⟨c, hbc, hcb⟩ := (Relation.TransGen.head'_iff).1 hcyc
  obtain ⟨s, t, hsb, htc, hst, hne⟩ := hedge _ _ hbc
  obtain ⟨s', hs', hts'⟩ := hlift c b hcb t htc
  have hts : lts.τSTr t s := hts'.trans (hs s' s (hs'.trans hsb.symm))
  have hscc : TauScc lts s t := ⟨Relation.ReflTransGen.single hst, hts⟩
  exact hne (hsb.symm.trans (((hiff s t).2 hscc).trans htc))

end Sigref
