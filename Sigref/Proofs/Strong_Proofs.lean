import Sigref.Strong
import Sigref.Proofs.Basic_Proofs
import Signatures.Proofs.Signature_Proofs
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import Mathlib.Data.Prod.Lex

/-!
# Proofs: Strong

Proofs for the abstract strong signature refinement: invariant preservation, final result and termination.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/Strong_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

variable {State Label : Type}

theorem strongInv_init (lts : LTS State Label) : StrongInv lts (initConfig State) :=
  ⟨fun _ _ _ => trivial, fun _ _ _ => Iff.rfl, fun _ _ _ hs => absurd trivial hs⟩

/-- Bisimilar states have equal signatures under any coarsening of bisimilarity. -/
theorem sigS_eq_of_bisim (lts : LTS State Label) (π : Setoid State)
    (hR : ∀ s t, LTS.Bisimilarity lts lts s t → π.r s t) {s t : State}
    (h : LTS.Bisimilarity lts lts s t) : sigS lts π s = sigS lts π t := by
  have key : ∀ {s t : State}, LTS.Bisimilarity lts lts s t → ∀ x, x ∈ sigS lts π s → x ∈ sigS lts π t := by
    intro s t h ⟨μ, α⟩ ⟨s', htr, hα⟩
    obtain ⟨t', htr', hb⟩ := (LTS.Bisimilarity.isBisimulation lts lts).follow_fst h htr
    exact ⟨t', htr', hα ▸ (Quotient.sound (π.symm (hR _ _ hb))).symm ▸ rfl⟩
  exact Set.ext fun x => ⟨key h x, key h.symm x⟩

/-- Unfolded form of the relation of the split partition. -/
theorem stepSetoid_r (lts : LTS State Label) (π : Setoid State) (X : Set State) (s0 : State)
    (s t : State) :
    (stepSetoid lts π X s0).r s t ↔
      π.r s t ∧ (s ∈ cls π s0 → ((s ∈ cls π s0 ∩ X ↔ t ∈ cls π s0 ∩ X) ∧
        (s ∈ cls π s0 ∩ X → sigS lts π s = sigS lts π t))) := Iff.rfl

/-- **The invariant is preserved by every step.** This contains the real mathematical content
(soundness `R`, marked-closure `M`, uniformity `U`). -/
theorem strongInv_step (lts : LTS State Label) {c c' : Config State} (inv : StrongInv lts c)
    (hstep : StrongStep lts c c') : StrongInv lts c' := by
  obtain ⟨s0, s1, ⟨d, hdB, hdX⟩, hs1, hπ, hX⟩ := hstep
  obtain ⟨π', X'⟩ := c'
  simp only at hπ hX
  have hr' : ∀ s t, π'.r s t ↔ c.π.r s t ∧ (s ∈ cls c.π s0 → ((s ∈ cls c.π s0 ∩ c.X ↔
      t ∈ cls c.π s0 ∩ c.X) ∧ (s ∈ cls c.π s0 ∩ c.X → sigS lts c.π s = sigS lts c.π t))) := by
    intro s t; rw [hπ]; exact stepSetoid_r lts c.π c.X s0 s t
  have sat := cls_saturated c.π s0
  have hR' : ∀ s t, LTS.Bisimilarity lts lts s t → π'.r s t := by
    intro s t hb
    have hr := inv.R s t hb
    refine (hr' s t).2 ⟨hr, fun hsB => ?_⟩
    have htB := (sat s t hr).1 hsB
    exact ⟨⟨fun ⟨_, hx⟩ => ⟨htB, (inv.M s t hb).1 hx⟩, fun ⟨_, hx⟩ => ⟨hsB, (inv.M s t hb).2 hx⟩⟩,
      fun _ => sigS_eq_of_bisim lts c.π inv.R hb⟩
  have dir : ∀ s t, LTS.Bisimilarity lts lts s t → s ∈ X' → t ∈ X' := by
    intro s t hb hs
    rw [hX] at hs ⊢
    rcases hs with ⟨hsX, hsB⟩ | ⟨μ, u, ⟨huB, hunk⟩, htr⟩
    · exact Or.inl ⟨(inv.M s t hb).1 hsX, fun htB => hsB ((sat s t (inv.R s t hb)).2 htB)⟩
    · obtain ⟨v, htr', hbuv⟩ := (LTS.Bisimilarity.isBisimulation lts lts).follow_fst hb htr
      have huv := hR' u v hbuv
      have hvB : v ∈ cls c.π s0 := (sat u v ((hr' u v).1 huv).1).1 huB
      refine Or.inr ⟨μ, v, ⟨hvB, fun hvk => hunk ?_⟩, htr'⟩
      exact π'.trans hvk (π'.symm huv) |> fun h => by
        have : cls π' s1 = {t | π'.r s1 t} := rfl
        exact h
  have sub : ∀ s t, π'.r s t → s ∉ X' → t ∉ X' →
      ∀ x, x ∈ sigS lts π' s → x ∈ sigS lts π' t := by
    intro s t hst hsX' htX' ⟨μ, α⟩ ⟨u, htr, hα⟩
    have hst' := (hr' s t).1 hst
    have hold : sigS lts c.π s = sigS lts c.π t := by
      by_cases hsB : s ∈ cls c.π s0
      · by_cases hsX : s ∈ c.X
        · exact (hst'.2 hsB).2 ⟨hsB, hsX⟩
        · have htB := (sat s t hst'.1).1 hsB
          have htX : t ∉ c.X := fun htX => hsX ((hst'.2 hsB).1.2 ⟨htB, htX⟩).2
          exact inv.U s t hst'.1 hsX htX
      · have hsX : s ∉ c.X := fun h => hsX' (by rw [hX]; exact Or.inl ⟨h, hsB⟩)
        have htB : t ∉ cls c.π s0 := fun h => hsB ((sat s t hst'.1).2 h)
        have htX : t ∉ c.X := fun h => htX' (by rw [hX]; exact Or.inl ⟨h, htB⟩)
        exact inv.U s t hst'.1 hsX htX
    have hmem : ((μ, Quotient.mk c.π u) : Label × Quotient c.π) ∈ sigS lts c.π s := ⟨u, htr, rfl⟩
    rw [hold] at hmem
    obtain ⟨v, htr', hv⟩ := hmem
    have ruv : c.π.r u v := Quotient.exact hv.symm
    have ruv' : π'.r u v := by
      refine (hr' u v).2 ⟨ruv, fun huB => ?_⟩
      have hvB := (sat u v ruv).1 huB
      have hu : u ∈ cls π' s1 := by
        by_contra hcon
        exact hsX' (by rw [hX]; exact Or.inr ⟨μ, u, ⟨huB, hcon⟩, htr⟩)
      have hv' : v ∈ cls π' s1 := by
        by_contra hcon
        exact htX' (by rw [hX]; exact Or.inr ⟨μ, v, ⟨hvB, hcon⟩, htr'⟩)
      have := π'.trans (π'.symm hu) hv'
      exact (hr' u v).1 this |>.2 huB
    exact ⟨v, htr', (Quotient.sound ruv').symm.trans hα⟩
  exact ⟨hR', fun s t hb => ⟨dir s t hb, dir t s hb.symm⟩,
    fun s t hst hs ht => Set.ext fun x => ⟨sub s t hst hs ht x, sub t s (π'.symm hst) ht hs x⟩⟩

/-- **Final.** With no dirty state left, the partition is exactly bisimilarity. -/
theorem strongInv_final (lts : LTS State Label) {c : Config State} (inv : StrongInv lts c)
    (hX : ∀ s, s ∉ c.X) (s t : State) : c.π.r s t ↔ LTS.Bisimilarity lts lts s t := by
  refine ⟨fun h => ?_, inv.R s t⟩
  refine Signatures.IsStable.bisimilarity lts (Quotient.mk c.π) (fun a b hab => ?_) (Quotient.sound h)
  exact inv.U a b (Quotient.exact hab) (hX a) (hX b)

/-- The termination measure: the size of the relation (decreasing as blocks split), then the number
of dirty states. -/
noncomputable def measure (c : Config State) : Lex (ℕ × ℕ) :=
  toLex (Set.ncard {p : State × State | c.π.r p.1 p.2}, Set.ncard c.X)

/-- Every step strictly decreases the measure. -/
theorem strongStep_measure_lt [Finite State] (lts : LTS State Label) {c c' : Config State}
    (h : StrongStep lts c c') : measure c' < measure c := by
  obtain ⟨s0, s1, ⟨d, hdB, hdX⟩, hs1, hπ, hX⟩ := h
  have hsub : {p : State × State | c'.π.r p.1 p.2} ⊆ {p : State × State | c.π.r p.1 p.2} := by
    intro p hp
    have : (stepSetoid lts c.π c.X s0).r p.1 p.2 := hπ ▸ hp
    exact ((stepSetoid_r lts c.π c.X s0 p.1 p.2).1 this).1
  by_cases heq : ∀ p : State × State, c.π.r p.1 p.2 → c'.π.r p.1 p.2
  · -- no split: the kept part is the whole class, so the dirty states of the class are removed
    have hcls : cls c.π s0 \ cls c'.π s1 = ∅ := by
      ext t
      simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro ht
      have h1 : c.π.r s1 t := c.π.trans (c.π.symm hs1) ht
      exact heq (s1, t) h1
    have hX' : c'.X = c.X \ cls c.π s0 := by
      rw [hX, hcls]
      ext x; simp [predS]
    have hrel : {p : State × State | c'.π.r p.1 p.2} = {p : State × State | c.π.r p.1 p.2} :=
      Set.Subset.antisymm hsub heq
    unfold measure
    rw [hrel]
    refine Prod.Lex.right _ ?_
    rw [hX']
    exact Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.2 ⟨d, hdX, hdB⟩) (Set.toFinite _)
  · push Not at heq
    obtain ⟨p, hp, hnp⟩ := heq
    have hss : {p : State × State | c'.π.r p.1 p.2} ⊂ {p : State × State | c.π.r p.1 p.2} :=
      Set.ssubset_iff_of_subset hsub |>.2 ⟨p, hp, hnp⟩
    exact Prod.Lex.left _ _ (Set.ncard_lt_ncard hss (Set.toFinite _))

/-- **Termination:** on a finite state space every sequence of steps is finite. -/
theorem strongStep_wf [Finite State] (lts : LTS State Label) :
    WellFounded (fun c' c : Config State => StrongStep lts c c') :=
  Subrelation.wf (fun h => strongStep_measure_lt lts h) (InvImage.wf measure wellFounded_lt)
/-- Headline: correctness of the abstract strong signature refinement. -/
theorem strongSigrefCorrect (lts : LTS State Label) : StrongSigrefCorrect lts :=
  ⟨strongInv_init lts, fun _ _ h s => strongInv_step lts h s,
    fun _ h hX => strongInv_final lts h hX⟩

/-- Headline: termination of the abstract strong signature refinement. -/
theorem strongSigrefTerminates [Finite State] (lts : LTS State Label) :
    StrongSigrefTerminates lts :=
  strongStep_wf lts


end Sigref
