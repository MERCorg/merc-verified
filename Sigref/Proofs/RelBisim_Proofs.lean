import Sigref.RelBisim
import Signatures.InductiveSignatures
import Signatures.Proofs.InductiveSignatures_Proofs
import Signatures.Proofs.BranchingBisimilarity_Transitivity_Proofs

/-!
# Proofs: RelBisim

Theory of `E π` (branching bisimilarity relative to a partition): matching condition `E_step`, coinduction `E_coind`, equivalence, stuttering, path lifting, and `↔b ⊆ E π`.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/RelBisim_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label]

variable (lts : LTS State Label) (π : Setoid State)

theorem relLTS_tau_inl {s : State} {z : State ⊕ Unit} :
    (relLTS lts π).Tr (.inl s) HasTau.τ z ↔ ∃ x, z = .inl x ∧ InertTr lts π s x := by
  rcases z with x | u
  · simp only [relLTS]
    constructor
    · rintro ⟨_, h⟩; exact ⟨x, rfl, h⟩
    · rintro ⟨y, hy, h⟩; cases hy; exact ⟨rfl, h⟩
  · simp only [relLTS]
    constructor
    · rintro ⟨a, x, hl, _⟩
      exact absurd (congrArg Prod.snd hl) (by simp [HasTau.τ])
    · rintro ⟨y, hy, _⟩; cases hy

theorem tauSTr_inl {s : State} {z : State ⊕ Unit} (h : (relLTS lts π).τSTr (.inl s) z) :
    ∃ t, z = .inl t ∧ InertReach lts π s t := by
  induction h with
  | refl => exact ⟨s, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨t, rfl, hp⟩ := ih
    obtain ⟨x, rfl, hx⟩ := (relLTS_tau_inl lts π).1 hstep
    exact ⟨x, rfl, hp.tail hx⟩

theorem inertReach_tauSTr {s t : State} (h : InertReach lts π s t) :
    (relLTS lts π).τSTr (.inl s) (.inl t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact ih.tail ((relLTS_tau_inl lts π).2 ⟨_, rfl, hstep⟩)

theorem InertReach.rel {s t : State} (h : InertReach lts π s t) : π.r s t := by
  induction h with
  | refl => exact π.refl _
  | tail _ hstep ih => exact π.trans ih hstep.2

/-- Unfolded matching condition of `E π` (the `relLTS` bisimulation game, transported back to `lts`).
A π-inert τ-step is matched by doing nothing or by an inert path followed by an inert step (with
`E`-related targets); every other step is matched by an inert path followed by a step with
`π`-related target. -/
theorem E_step {s t : State} (h : E lts π s t) {a : Label} {s1 : State} (hTr : lts.Tr s a s1) :
    (a = HasTau.τ ∧ π.r s s1 ∧ E lts π s1 t) ∨
    ∃ t' t1, InertReach lts π t t' ∧ E lts π s t' ∧ lts.Tr t' a t1 ∧
      ((a = HasTau.τ ∧ π.r s s1 ∧ E lts π s1 t1) ∨
        ((a ≠ HasTau.τ ∨ ¬ π.r s s1) ∧ π.r s1 t1)) := by
  obtain ⟨hπ, hbb⟩ := h
  have hc := Signatures.BranchingBisimilarity.isBranchingBisimulation (lts := relLTS lts π) hbb
  by_cases hin : a = HasTau.τ ∧ π.r s s1
  · have edge : (relLTS lts π).Tr (.inl s) HasTau.τ (.inl s1) := by
      refine ⟨rfl, ?_⟩
      rw [hin.1] at hTr
      exact ⟨hTr, hin.2⟩
    rcases (hc HasTau.τ).1 _ edge with ⟨_, hbs1⟩ | ⟨t2', t2'', hSTr, hTr', hb1, hb2⟩
    · exact Or.inl ⟨hin.1, hin.2, π.trans (π.symm hin.2) hπ, hbs1⟩
    · obtain ⟨t', rfl, hIR⟩ := tauSTr_inl lts π ((LTS.sTr_τSTr (relLTS lts π)).mp hSTr)
      obtain ⟨x, rfl, hx⟩ := (relLTS_tau_inl lts π).1 hTr'
      have hst' : π.r s t' := π.trans hπ (InertReach.rel lts π hIR)
      exact Or.inr ⟨t', x, hIR, ⟨hst', hb1⟩, by rw [hin.1]; exact hx.1,
        Or.inl ⟨hin.1, hin.2, π.trans (π.symm hin.2) (π.trans hst' hx.2), hb2⟩⟩
  · have edge : (relLTS lts π).Tr (.inl s) (a, some (Quotient.mk π s1)) (.inr ()) :=
      ⟨a, s1, rfl, hTr, hin⟩
    rcases (hc (a, some (Quotient.mk π s1))).1 _ edge with ⟨hμ, _⟩ | ⟨t2', t2'', hSTr, hTr', hb1, hb2⟩
    · exact absurd (congrArg Prod.snd hμ) (by simp [HasTau.τ])
    · obtain ⟨t', rfl, hIR⟩ := tauSTr_inl lts π ((LTS.sTr_τSTr (relLTS lts π)).mp hSTr)
      rcases t2'' with x0 | u
      · exact absurd (congrArg Prod.snd hTr'.1) (by simp)
      · obtain ⟨a', x, hl, hTrx, _⟩ := hTr'
        have ha : a = a' := congrArg Prod.fst hl
        subst ha
        have hq : Quotient.mk π s1 = Quotient.mk π x := by
          have := congrArg Prod.snd hl
          simpa using this
        exact Or.inr ⟨t', x, hIR, ⟨π.trans hπ (InertReach.rel lts π hIR), hb1⟩, hTrx,
          Or.inr ⟨not_and_or.1 hin, Quotient.exact hq⟩⟩

/-- **Coinduction principle for `E π`**: a symmetric relation satisfying the matching condition of
`E_step` (with itself in place of `E`) is contained in `E π`. -/
theorem E_coind (R : State → State → Prop) (hsymm : ∀ s t, R s t → R t s)
    (hR : ∀ s t, R s t → π.r s t ∧ ∀ a s1, lts.Tr s a s1 →
      ((a = HasTau.τ ∧ π.r s s1 ∧ R s1 t) ∨
       ∃ t' t1, InertReach lts π t t' ∧ R s t' ∧ lts.Tr t' a t1 ∧
         ((a = HasTau.τ ∧ π.r s s1 ∧ R s1 t1) ∨ ((a ≠ HasTau.τ ∨ ¬ π.r s s1) ∧ π.r s1 t1)))) :
    ∀ s t, R s t → E lts π s t := by
  let r' : State ⊕ Unit → State ⊕ Unit → Prop
    | .inl s, .inl t => R s t
    | .inr _, .inr _ => True
    | _, _ => False
  have r'symm : ∀ x y, r' x y → r' y x := by
    intro x y h
    rcases x with s | u <;> rcases y with t | v
    · exact hsymm s t h
    · exact h.elim
    · exact h.elim
    · trivial
  have half : ∀ x y, r' x y → ∀ μ x1, (relLTS lts π).Tr x μ x1 →
      (μ = HasTau.τ ∧ r' x1 y) ∨ ∃ y' y'', (relLTS lts π).STr y HasTau.τ y' ∧
        (relLTS lts π).Tr y' μ y'' ∧ r' x y' ∧ r' x1 y'' := by
    intro x y hxy μ x1 hTr
    rcases x with s | u
    · rcases y with t | v
      · have hRst : R s t := hxy
        obtain ⟨_, hmatch⟩ := hR s t hRst
        rcases x1 with s1 | w
        · obtain ⟨hμ, hin⟩ := hTr
          subst hμ
          rcases hmatch HasTau.τ s1 hin.1 with ⟨_, _, hR1⟩ | ⟨t', t1, hIR, hRt', hTr', hcase⟩
          · exact Or.inl ⟨rfl, hR1⟩
          · rcases hcase with ⟨_, _, hR1⟩ | ⟨hne, _⟩
            · have hst' : π.r s t' := (hR s t' hRt').1
              have hs1t1 : π.r s1 t1 := (hR s1 t1 hR1).1
              refine Or.inr ⟨.inl t', .inl t1, (LTS.sTr_τSTr _).mpr (inertReach_tauSTr lts π hIR),
                ⟨rfl, hTr', π.trans (π.symm hst') (π.trans hin.2 hs1t1)⟩, hRt', hR1⟩
            · rcases hne with h | h
              · exact absurd rfl h
              · exact absurd hin.2 h
        · obtain ⟨a, x, hμ, hTrx, hni⟩ := hTr
          rcases hmatch a x hTrx with ⟨ha, hsx, _⟩ | ⟨t', t1, hIR, hRt', hTr', hcase⟩
          · exact absurd ⟨ha, hsx⟩ hni
          · rcases hcase with ⟨ha, hsx, _⟩ | ⟨_, hxt1⟩
            · exact absurd ⟨ha, hsx⟩ hni
            · have hst' : π.r s t' := (hR s t' hRt').1
              refine Or.inr ⟨.inl t', .inr (), (LTS.sTr_τSTr _).mpr (inertReach_tauSTr lts π hIR),
                ⟨a, t1, ?_, hTr', ?_⟩, hRt', trivial⟩
              · rw [hμ, Quotient.sound hxt1]
              · rintro ⟨ha, hpt⟩
                exact hni ⟨ha, π.trans (π.trans hst' hpt) (π.symm hxt1)⟩
      · exact hxy.elim
    · rcases y with t | v
      · exact hxy.elim
      · exact hTr.elim
  have hbis : LTS.IsBranchingBisimulation (relLTS lts π) r' := by
    intro x y hxy μ
    refine ⟨fun x1 h => half x y hxy μ x1 h, fun y1 h => ?_⟩
    rcases half y x (r'symm x y hxy) μ y1 h with ⟨hμ, h1⟩ | ⟨x', x'', hS, hT, h2, h3⟩
    · exact Or.inl ⟨hμ, r'symm _ _ h1⟩
    · exact Or.inr ⟨x', x'', hS, hT, r'symm _ _ h2, r'symm _ _ h3⟩
  intro s t h
  exact ⟨(hR s t h).1, r', h, hbis⟩

theorem E.refl (s : State) : E lts π s s := ⟨π.refl s, Signatures.BranchingBisimilarity.refl _⟩

theorem E.symm {s t : State} (h : E lts π s t) : E lts π t s :=
  ⟨π.symm h.1, Signatures.BranchingBisimilarity.symm h.2⟩

theorem E.trans {s t u : State} (h1 : E lts π s t) (h2 : E lts π t u) : E lts π s u :=
  ⟨π.trans h1.1 h2.1, Signatures.BranchingBisimilarity.trans h1.2 h2.2⟩

theorem E.rel {s t : State} (h : E lts π s t) : π.r s t := h.1

/-- `E π` as a `Setoid`. -/
def ESetoid : Setoid State := ⟨E lts π, ⟨E.refl lts π, fun h => E.symm lts π h, fun h1 h2 => E.trans lts π h1 h2⟩⟩

/-- The auxiliary LTS is τ-loop-free when `lts` is. -/
theorem tauLoopFree_relLTS (hWF : TauLoopFree lts) : TauLoopFree (relLTS lts π) := by
  have hacc : ∀ s : State, Acc (fun z' z => (relLTS lts π).Tr z HasTau.τ z') (.inl s) := by
    intro s
    induction s using hWF.induction with
    | _ s ih =>
      refine Acc.intro _ (fun z' hz' => ?_)
      obtain ⟨x, rfl, hx⟩ := (relLTS_tau_inl lts π).1 hz'
      exact ih x hx.1
  refine ⟨fun z => ?_⟩
  rcases z with s | u
  · exact hacc s
  · exact Acc.intro _ (fun z' hz' => hz'.elim)

/-- Strong stuttering for `E π` (needs τ-loop-freeness): states on an inert path between two
`E`-related states are `E`-related to both. -/
theorem E_stutter (hWF : TauLoopFree lts) {s t m t' : State} (hst : E lts π s t)
    (h1 : InertReach lts π t m) (h2 : InertReach lts π m t') (hst' : E lts π s t') :
    E lts π s m := by
  have hbb : BranchingBisimilarity (relLTS lts π) (.inl t) (.inl t') :=
    Signatures.BranchingBisimilarity.trans (Signatures.BranchingBisimilarity.symm hst.2) hst'.2
  have hmid := Signatures.BranchingBisimilarity.tauPath_mid (tauLoopFree_relLTS lts π hWF)
    (inertReach_tauSTr lts π h1) (inertReach_tauSTr lts π h2) hbb
  exact ⟨π.trans hst.1 (InertReach.rel lts π h1),
    Signatures.BranchingBisimilarity.trans hst.2 (Signatures.BranchingBisimilarity.symm hmid)⟩

/-- Path lifting: an inert path on one side of an `E`-pair is mimicked on the other side. -/
theorem E_lift {s t d : State} (hst : E lts π s t) (h : InertReach lts π t d) :
    ∃ s', InertReach lts π s s' ∧ E lts π s' d := by
  have hr := Signatures.BranchingBisimilarity.isBranchingBisimulation (lts := relLTS lts π)
  obtain ⟨z, hz, hbz⟩ := Signatures.LTS.IsBranchingBisimulation.stutter hr
    (Signatures.BranchingBisimilarity.symm hst.2) (inertReach_tauSTr lts π h)
  obtain ⟨s', rfl, hIR⟩ := tauSTr_inl lts π hz
  have hπ : π.r s' d := π.trans (π.symm (InertReach.rel lts π hIR))
    (π.trans hst.1 (InertReach.rel lts π h))
  exact ⟨s', hIR, hπ, Signatures.BranchingBisimilarity.symm hbz⟩

/-- A τ-path between branching-bisimilar states is inert whenever branching bisimilarity refines
`π`. -/
theorem inertReach_of_bb (hWF : TauLoopFree lts)
    (hπ : ∀ s t, BranchingBisimilarity lts s t → π.r s t) {t t' : State}
    (hp : lts.τSTr t t') (hb : BranchingBisimilarity lts t t') : InertReach lts π t t' := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w t' hrest hstep ih =>
    have hwt : BranchingBisimilarity lts w t :=
      Signatures.BranchingBisimilarity.tauPath_mid hWF hrest (Relation.ReflTransGen.single hstep) hb
    have htw : BranchingBisimilarity lts t w := Signatures.BranchingBisimilarity.symm hwt
    exact (ih htw).tail ⟨hstep, hπ _ _ (Signatures.BranchingBisimilarity.trans hwt hb)⟩

/-- Branching bisimilarity is contained in `E π` as soon as it is contained in `π`. -/
theorem E_of_bisim (hWF : TauLoopFree lts)
    (hπ : ∀ s t, BranchingBisimilarity lts s t → π.r s t) {s t : State}
    (h : BranchingBisimilarity lts s t) : E lts π s t := by
  refine E_coind lts π (BranchingBisimilarity lts) (fun _ _ => Signatures.BranchingBisimilarity.symm) ?_ s t h
  intro s t h
  refine ⟨hπ s t h, fun a s1 hTr => ?_⟩
  have hc := Signatures.BranchingBisimilarity.isBranchingBisimulation (lts := lts) h
  rcases (hc a).1 s1 hTr with ⟨ha, hb1⟩ | ⟨t', t'', hSTr, hTr', hb1, hb2⟩
  · exact Or.inl ⟨ha, hπ s s1 (Signatures.BranchingBisimilarity.trans h (Signatures.BranchingBisimilarity.symm hb1)), hb1⟩
  · have hp : lts.τSTr t t' := (LTS.sTr_τSTr lts).mp hSTr
    have hIR := inertReach_of_bb lts π hWF hπ hp
      (Signatures.BranchingBisimilarity.trans (Signatures.BranchingBisimilarity.symm h) hb1)
    refine Or.inr ⟨t', t'', hIR, hb1, hTr', ?_⟩
    by_cases hin : a = HasTau.τ ∧ π.r s s1
    · exact Or.inl ⟨hin.1, hin.2, hb2⟩
    · exact Or.inr ⟨not_and_or.1 hin, hπ _ _ hb2⟩

end Sigref
