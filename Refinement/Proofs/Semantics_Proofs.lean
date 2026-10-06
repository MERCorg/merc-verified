module

public import Refinement.Semantics

open Cslib (LTS HasTau)

@[expose] public section SemanticsProofs

namespace Refinement

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Helper lemmas about
`WeakTr`'s composability, used throughout `Refinement/Proofs/Product_Proofs.lean`. -/

/-- A weak trace over `a :: ρ'` splits into a weak step over the singleton `[a]` followed by one
    over `ρ'`. The general "split at any prefix" fact also holds but this is the only shape the
    rest of the development needs. -/
theorem WeakTr.splitHead [HasTau Label] {lts : LTS State Label} {s t : State} {ν : List Label}
    (h : WeakTr lts s ν t) : ∀ {a : Label} {ρ' : List Label}, ν = a :: ρ' →
      ∃ u, WeakTr lts s [a] u ∧ WeakTr lts u ρ' t := by
  induction h with
  | refl s => intro a ρ' hν; exact absurd hν (by simp)
  | tau _ => intro a ρ' hν; exact absurd hν (by simp)
  | vis hvis htr =>
    intro a ρ' hν
    obtain ⟨rfl, rfl⟩ := List.cons.injEq .. |>.mp hν
    exact ⟨_, WeakTr.vis hvis htr, WeakTr.refl _⟩
  | comp h1 h2 ih1 ih2 =>
    rename_i ρ σ
    intro a ρ' hν
    cases ρ with
    | nil =>
      simp only [List.nil_append] at hν
      obtain ⟨w, hw1, hw2⟩ := ih2 hν
      exact ⟨w, h1.comp hw1, hw2⟩
    | cons b ρ'' =>
      rw [List.cons_append] at hν
      obtain ⟨rfl, hρ'⟩ := List.cons.injEq .. |>.mp hν
      obtain ⟨w, hw1, hw2⟩ := ih1 rfl
      exact ⟨w, hw1, hρ' ▸ hw2.comp h2⟩

/-- A weak trace over `ρ1 ++ ρ2` splits into a weak step over `ρ1` followed by one over `ρ2`,
    for any way of cutting the list (not just at the head, unlike `WeakTr.splitHead`, which this
    is proved from by induction on `ρ1`). -/
theorem WeakTr.splitAppend [HasTau Label] {lts : LTS State Label} {t : State} :
    ∀ {ρ1 ρ2 : List Label} {s : State}, WeakTr lts s (ρ1 ++ ρ2) t →
      ∃ u, WeakTr lts s ρ1 u ∧ WeakTr lts u ρ2 t := by
  intro ρ1
  induction ρ1 with
  | nil => intro ρ2 s h; exact ⟨s, WeakTr.refl s, h⟩
  | cons b ρ1' ih =>
    intro ρ2 s h
    rw [List.cons_append] at h
    obtain ⟨w, hw1, hw2⟩ := h.splitHead rfl
    obtain ⟨u, hu1, hu2⟩ := ih hw2
    exact ⟨u, hw1.comp hu1, hu2⟩

/-- The `ρ`-image of a set of states under `WeakTr` is already closed under further `ε`-steps:
    extending by `[]` (on the right) never adds anything new. Used to show that every state
    reachable in the normal form (`NormTr`/`FdrNormTr`) is `ε`-saturated. -/
theorem weakImage_eps_closed [HasTau Label] (lts : LTS State Label) (U : Set State)
    (ρ : List Label) :
    { t | ∃ u ∈ { t | ∃ s ∈ U, WeakTr lts s ρ t }, WeakTr lts u [] t } =
      { t | ∃ s ∈ U, WeakTr lts s ρ t } := by
  ext t
  constructor
  · rintro ⟨u, ⟨s, hs, hsu⟩, hut⟩
    exact ⟨s, hs, (List.append_nil ρ) ▸ hsu.comp hut⟩
  · rintro ⟨s, hs, hst⟩
    exact ⟨t, ⟨s, hs, hst⟩, WeakTr.refl t⟩

/-- A `τ*`-path is a weak transition over the empty trace. -/
theorem WeakTr.of_τSTr [HasTau Label] {lts : LTS State Label} {s t : State}
    (h : lts.τSTr s t) : WeakTr lts s [] t := by
  induction h with
  | refl => exact .refl _
  | tail _ hstep ih => exact (List.append_nil ([] : List Label)) ▸ ih.comp (.tau hstep)

/-- Every non-divergent state can reach a stable one by `τ`-steps: if no infinite `τ`-sequence
    exists from `s`, then repeatedly picking an outgoing `τ`-successor (while unstable) cannot go
    on forever, since that would itself witness `s`'s divergence. Needed for the "`U = ∅`" case of
    Theorem 3.24 (an FD-witness there gives no stable implementation state for free, unlike the
    SF-witness case which starts from a `Stable` hypothesis). -/
theorem not_divergent_has_stable [HasTau Label] {lts : LTS State Label} {s : State}
    (h : ¬ lts.Divergent s) : ∃ t, lts.τSTr s t ∧ Stable lts t := by
  by_contra hcon
  push Not at hcon
  apply h
  have hstep : ∀ t : { t // lts.τSTr s t },
      ∃ t' : { t' // lts.τSTr s t' }, lts.Tr t.1 HasTau.τ t'.1 := by
    rintro ⟨t, ht⟩
    have hns : ¬ Stable lts t := hcon t ht
    unfold Stable at hns
    rw [not_not] at hns
    obtain ⟨t', ht'⟩ := hns
    exact ⟨⟨t', ht.tail ht'⟩, ht'⟩
  choose next hnext using hstep
  set ss : ℕ → { t // lts.τSTr s t } := fun i => next^[i] ⟨s, .refl⟩ with hss_def
  have hss_succ : ∀ i, ss (i + 1) = next (ss i) := by
    intro i; simp [hss_def, Function.iterate_succ_apply']
  refine ⟨⟨fun i => (ss i).1⟩, ⟨fun _ => HasTau.τ⟩, ?_, ?_, fun _ => rfl⟩
  · intro i
    show lts.Tr (ss i).1 HasTau.τ (ss (i + 1)).1
    rw [hss_succ i]
    exact hnext (ss i)
  · show (ss 0).1 = s
    simp [hss_def]

end Refinement

end SemanticsProofs
