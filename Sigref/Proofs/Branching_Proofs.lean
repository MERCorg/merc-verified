import Sigref.Branching
import Sigref.Proofs.Strong_Proofs
import Sigref.Proofs.RelBisim_Proofs

/-!
# Proofs: Branching

Proofs for the abstract branching signature refinement: the step lemmas `R'`, `M'`, `U'`, `S'`, the final result, termination, progress and totality.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/Branching_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label]

theorem branchingInv_init (lts : LTS State Label) : BranchingInv lts (initConfig State) := by
  have hY : ∀ s, s ∈ inertClosure lts (initConfig State).π (initConfig State).X :=
    fun s => ⟨s, trivial, Relation.ReflTransGen.refl⟩
  exact ⟨fun _ _ _ => trivial, fun s t _ => ⟨fun _ => hY t, fun _ => hY s⟩,
    fun s _ _ hs => absurd (hY s) hs, fun s _ _ hs => absurd (hY s) hs⟩

section Closure

variable {lts : LTS State Label} {π : Setoid State} {D : Set State}

theorem mem_inertClosure_of_mem {s : State} (h : s ∈ D) : s ∈ inertClosure lts π D :=
  ⟨s, h, Relation.ReflTransGen.refl⟩

theorem inertClosure_head {s s1 : State} (hs : InertTr lts π s s1) (h : s1 ∈ inertClosure lts π D) :
    s ∈ inertClosure lts π D := by
  obtain ⟨d, hd, hp⟩ := h
  exact ⟨d, hd, Relation.ReflTransGen.head hs hp⟩

theorem inertClosure_path {s t : State} (hp : InertReach lts π s t) (h : t ∈ inertClosure lts π D) :
    s ∈ inertClosure lts π D := by
  obtain ⟨d, hd, hq⟩ := h
  exact ⟨d, hd, hp.trans hq⟩

theorem not_inertClosure_path {s t : State} (hp : InertReach lts π s t)
    (h : s ∉ inertClosure lts π D) : t ∉ inertClosure lts π D :=
  fun ht => h (inertClosure_path hp ht)

end Closure

namespace StepFacts

variable {lts : LTS State Label} {c c' : Config State} {s0 s1 : State}
  (f : StepFacts lts c c' s0 s1)

include f

/-- The processed part `D` of the block is exactly its intersection with the dirty closure. -/
theorem D_iff {s : State} :
    s ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X) ↔
      s ∈ cls c.π s0 ∧ s ∈ inertClosure lts c.π c.X := by
  constructor
  · rintro ⟨d, ⟨hdB, hdX⟩, hp⟩
    exact ⟨(cls_saturated c.π s0 s d (InertReach.rel lts c.π hp)).2 hdB, d, hdX, hp⟩
  · rintro ⟨hsB, d, hdX, hp⟩
    exact ⟨d, ⟨(cls_saturated c.π s0 s d (InertReach.rel lts c.π hp)).1 hsB, hdX⟩, hp⟩

theorem le {s t : State} (h : c'.π.r s t) : c.π.r s t := ((f.rel s t).1 h).1

theorem out {s t : State} (hs : s ∉ cls c.π s0) : c'.π.r s t ↔ c.π.r s t := by
  rw [f.rel]
  exact ⟨fun h => h.1, fun h => ⟨h, fun hB => absurd hB hs⟩⟩

/-- The kept part is contained in the block. -/
theorem keep_sub {t : State} (ht : t ∈ cls c'.π s1) : t ∈ cls c.π s0 :=
  (cls_saturated c.π s0 s1 t (f.le ht)).1 f.mem

/-- `U = B \ keep` is a union of `π'`-classes. -/
theorem U_sat {s t : State} (hst : c'.π.r s t) (hs : s ∈ cls c.π s0 \ cls c'.π s1) :
    t ∈ cls c.π s0 \ cls c'.π s1 := by
  refine ⟨(cls_saturated c.π s0 s t (f.le hst)).1 hs.1, fun ht => hs.2 ?_⟩
  exact c'.π.trans ht (c'.π.symm hst)

/-- Inert paths outside the block are unaffected by the split. -/
theorem inertReach_out {t x : State} (ht : t ∉ cls c.π s0) (hp : InertReach lts c.π t x) :
    InertReach lts c'.π t x := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v hrest hstep ih =>
    have hu : u ∉ cls c.π s0 := fun hu =>
      ht ((cls_saturated c.π s0 t u (InertReach.rel lts c.π hrest)).2 hu)
    exact ih.tail ⟨hstep.1, (f.out hu).2 hstep.2⟩

/-- Soundness: branching-bisimilar states stay together. -/
theorem R' (hWF : TauLoopFree lts) (inv : BranchingInv lts c) {s t : State}
    (hb : BranchingBisimilarity lts s t) : c'.π.r s t := by
  rw [f.rel]
  unfold branchRel
  refine ⟨inv.R s t hb, fun hsB => ⟨?_, fun hsD => ?_⟩⟩
  · have htB : t ∈ cls c.π s0 := (cls_saturated c.π s0 s t (inv.R s t hb)).1 hsB
    rw [f.D_iff, f.D_iff]
    exact ⟨fun h => ⟨htB, (inv.M s t hb).1 h.2⟩, fun h => ⟨hsB, (inv.M s t hb).2 h.2⟩⟩
  · exact E_of_bisim lts c.π hWF inv.R hb

/-- Base case of `M'`: a dirty state is mirrored by every bisimilar state. -/
theorem M_base (hWF : TauLoopFree lts) (inv : BranchingInv lts c) {s t : State}
    (hb : BranchingBisimilarity lts s t) (hs : s ∈ c'.X) :
    t ∈ inertClosure lts c'.π c'.X := by
  rw [f.dX] at hs
  rcases hs with ⟨hsX, hsD⟩ | ⟨μ, u, huU, hTr, hμ⟩
  · have hsB : s ∉ cls c.π s0 := fun h => hsD ((f.D_iff).2 ⟨h, mem_inertClosure_of_mem hsX⟩)
    have htY := (inv.M s t hb).1 (mem_inertClosure_of_mem hsX)
    have htB : t ∉ cls c.π s0 := fun h => hsB ((cls_saturated c.π s0 s t (inv.R s t hb)).2 h)
    obtain ⟨x, hxX, hp⟩ := htY
    have hxB : x ∉ cls c.π s0 := fun h =>
      htB ((cls_saturated c.π s0 t x (InertReach.rel lts c.π hp)).2 h)
    have hxD : x ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X) := fun h => hxB ((f.D_iff.1 h).1)
    refine ⟨x, ?_, f.inertReach_out htB hp⟩
    rw [f.dX]; exact Or.inl ⟨hxX, hxD⟩
  · have hc := BranchingBisimilarity.isBranchingBisimulation (lts := lts) hb
    have hst : c'.π.r s t := f.R' hWF inv hb
    rcases (hc μ).1 u hTr with ⟨hμτ, hb1⟩ | ⟨t', t'', hSTr, hTr', hb2, hb3⟩
    · exfalso
      have htU := f.U_sat (f.R' hWF inv hb1) huU
      exact hμ hμτ (f.U_sat (c'.π.symm hst) htU)
    · have hp : lts.τSTr t t' := (LTS.sTr_τSTr lts).mp hSTr
      have hIR : InertReach lts c'.π t t' :=
        inertReach_of_bb lts c'.π hWF (fun a b h => f.R' hWF inv h) hp
          (BranchingBisimilarity.trans (BranchingBisimilarity.symm hb) hb2)
      have ht''U := f.U_sat (f.R' hWF inv hb3) huU
      refine ⟨t', ?_, hIR⟩
      rw [f.dX]
      refine Or.inr ⟨μ, t'', ht''U, hTr', fun hμτ ht'U => ?_⟩
      exact hμ hμτ (f.U_sat (c'.π.symm (f.R' hWF inv hb2)) ht'U)

/-- The effective dirty set is closed under branching bisimilarity. -/
theorem M' (hWF : TauLoopFree lts) (inv : BranchingInv lts c) {s t : State}
    (hb : BranchingBisimilarity lts s t) (hs : s ∈ inertClosure lts c'.π c'.X) :
    t ∈ inertClosure lts c'.π c'.X := by
  obtain ⟨d, hd, hp⟩ := hs
  induction hp using Relation.ReflTransGen.head_induction_on generalizing t with
  | refl => exact f.M_base hWF inv hb hd
  | head hab hrest ih =>
    rename_i a b
    have hc := BranchingBisimilarity.isBranchingBisimulation (lts := lts) hb
    rcases (hc HasTau.τ).1 b hab.1 with ⟨_, hb1⟩ | ⟨t', t'', hSTr, hTr', hb2, hb3⟩
    · exact ih hb1
    · have hp : lts.τSTr t t' := (LTS.sTr_τSTr lts).mp hSTr
      have hIR : InertReach lts c'.π t t' :=
        inertReach_of_bb lts c'.π hWF (fun a b h => f.R' hWF inv h) hp
          (BranchingBisimilarity.trans (BranchingBisimilarity.symm hb) hb2)
      have hπ : c'.π.r t' t'' :=
        c'.π.trans (c'.π.symm (f.R' hWF inv hb2)) (c'.π.trans hab.2 (f.R' hWF inv hb3))
      exact inertClosure_path (hIR.tail ⟨hTr', hπ⟩) (ih hb3)

/-! ### Helper lemmas for `U'` and `S'` -/

/-- Outside the block, `E π'` is contained in `E π`. -/
theorem E_out {u v : State} (hE : E lts c'.π u v) (hu : u ∉ cls c.π s0) : E lts c.π u v := by
  refine E_coind lts c.π (fun u v => E lts c'.π u v ∧ u ∉ cls c.π s0)
    (fun u v h => ⟨E.symm lts c'.π h.1, fun hv =>
      h.2 ((cls_saturated c.π s0 u v (f.le h.1.1)).2 hv)⟩) ?_ u v ⟨hE, hu⟩
  rintro u v ⟨hE, hu⟩
  refine ⟨f.le hE.1, fun a u1 hTr => ?_⟩
  rcases E_step lts c'.π hE hTr with ⟨ha, hπ, hE1⟩ | ⟨v', v1, hIR, hE', hTr', hcase⟩
  · have hπ1 := f.le hπ
    exact Or.inl ⟨ha, hπ1, hE1, fun h => hu ((cls_saturated c.π s0 u u1 hπ1).2 h)⟩
  · have key : ∀ x y, InertReach lts c'.π x y → InertReach lts c.π x y := by
      intro x y h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih => exact ih.tail ⟨hstep.1, f.le hstep.2⟩
    have hIR1 : InertReach lts c.π v v' := key v v' hIR
    refine Or.inr ⟨v', v1, hIR1, ⟨hE', hu⟩, hTr', ?_⟩
    rcases hcase with ⟨ha, hπ, hE1⟩ | ⟨hN, hπ1⟩
    · have hπ' := f.le hπ
      exact Or.inl ⟨ha, hπ', hE1, fun h => hu ((cls_saturated c.π s0 u _ hπ').2 h)⟩
    · refine Or.inr ⟨?_, f.le hπ1⟩
      rcases hN with h | h
      · exact Or.inl h
      · exact Or.inr (fun h' => h ((f.out hu).2 h'))

/-- A clean state outside the block is clean for the old partition too. -/
theorem notY_of_out {s : State} (hs : s ∉ cls c.π s0) (hs' : s ∉ inertClosure lts c'.π c'.X) :
    s ∉ inertClosure lts c.π c.X := by
  rintro ⟨x, hxX, hp⟩
  have hxB : x ∉ cls c.π s0 := fun h =>
    hs ((cls_saturated c.π s0 s x (InertReach.rel lts c.π hp)).2 h)
  have hxD : x ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X) := fun h => hxB ((f.D_iff.1 h).1)
  refine hs' ⟨x, ?_, f.inertReach_out hs hp⟩
  rw [f.dX]; exact Or.inl ⟨hxX, hxD⟩

/-- A state that is clean after the step and was not processed was already clean. -/
theorem notY_of_notD {s : State} (hs' : s ∉ inertClosure lts c'.π c'.X)
    (hD : s ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X)) : s ∉ inertClosure lts c.π c.X := by
  by_cases hB : s ∈ cls c.π s0
  · intro hY; exact hD (f.D_iff.2 ⟨hB, hY⟩)
  · exact f.notY_of_out hB hs'

/-- `E π` for any two clean-after-the-step states of one new block. -/
theorem E_of_clean (inv : BranchingInv lts c) {s t : State} (hst : c'.π.r s t)
    (hs : s ∉ inertClosure lts c'.π c'.X) (ht : t ∉ inertClosure lts c'.π c'.X) :
    E lts c.π s t := by
  have hπ := f.le hst
  have hrel := (f.rel s t).1 hst
  by_cases hD : s ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X)
  · exact (hrel.2 (f.D_iff.1 hD).1).2 hD
  · have htD : t ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X) := by
      intro h
      by_cases hB : s ∈ cls c.π s0
      · exact hD ((hrel.2 hB).1.2 h)
      · exact hB ((cls_saturated c.π s0 s t hπ).2 (f.D_iff.1 h).1)
    exact inv.U s t hπ (f.notY_of_notD hs hD) (f.notY_of_notD ht htD)

/-- Inert steps of a clean (old) state survive the split. -/
theorem inert_pres {u v : State} (hu : u ∉ inertClosure lts c.π c.X) (h : InertTr lts c.π u v) :
    InertTr lts c'.π u v := by
  refine ⟨h.1, ?_⟩
  by_cases hB : u ∈ cls c.π s0
  · have hvY : v ∉ inertClosure lts c.π c.X := fun hv => hu (inertClosure_head h hv)
    have huD : u ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X) := fun hd => hu (f.D_iff.1 hd).2
    have hvD : v ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X) := fun hd => hvY (f.D_iff.1 hd).2
    rw [f.rel]
    exact ⟨h.2, fun _ => ⟨⟨fun a => absurd a huD, fun a => absurd a hvD⟩, fun a => absurd a huD⟩⟩
  · exact (f.out hB).2 h.2

theorem inertReach_pres {u v : State} (hu : u ∉ inertClosure lts c.π c.X)
    (h : InertReach lts c.π u v) : InertReach lts c'.π u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w x hrest hstep ih =>
    exact ih.tail (f.inert_pres (not_inertClosure_path hrest hu) hstep)

/-- A clean state has no edge into `U` except τ-edges starting inside `U`. -/
theorem clean_edge {u u1 : State} {a : Label} (hu : u ∉ inertClosure lts c'.π c'.X)
    (hTr : lts.Tr u a u1) (h1 : u1 ∈ cls c.π s0 \ cls c'.π s1) :
    a = HasTau.τ ∧ u ∈ cls c.π s0 \ cls c'.π s1 := by
  by_contra hcon
  apply hu
  refine ⟨u, ?_, Relation.ReflTransGen.refl⟩
  rw [f.dX]
  exact Or.inr ⟨a, u1, h1, hTr, fun hτ hU => hcon ⟨hτ, hU⟩⟩

/-- Targets of non-inert edges of clean states land in the kept part. -/
theorem tail_keep {u u1 : State} {a : Label} (hu : u ∉ inertClosure lts c'.π c'.X)
    (hTr : lts.Tr u a u1) (hN : a ≠ HasTau.τ ∨ ¬ c.π.r u u1) (hB : u1 ∈ cls c.π s0) :
    u1 ∈ cls c'.π s1 := by
  by_contra hk
  obtain ⟨ha, huU⟩ := f.clean_edge hu hTr ⟨hB, hk⟩
  have hπ : c.π.r u u1 := c.π.trans (c.π.symm huU.1) hB
  rcases hN with h | h
  · exact h ha
  · exact h hπ

/-- Tails of non-inert edges of two clean states are `π'`-related. -/
theorem tails_pi' {u v u1 v1 : State} {a : Label} (hu : u ∉ inertClosure lts c'.π c'.X)
    (hv : v ∉ inertClosure lts c'.π c'.X) (hTu : lts.Tr u a u1) (hTv : lts.Tr v a v1)
    (hNu : a ≠ HasTau.τ ∨ ¬ c.π.r u u1) (hNv : a ≠ HasTau.τ ∨ ¬ c.π.r v v1)
    (h : c.π.r u1 v1) : c'.π.r u1 v1 := by
  by_cases hB : u1 ∈ cls c.π s0
  · have hvB : v1 ∈ cls c.π s0 := (cls_saturated c.π s0 u1 v1 h).1 hB
    exact c'.π.trans (c'.π.symm (f.tail_keep hu hTu hNu hB)) (f.tail_keep hv hTv hNv hvB)
  · exact (f.out hB).2 h

/-- Separation is preserved: a clean and a dirty state of one new block are not `E π'`-related. -/
theorem S' (inv : BranchingInv lts c) {s t : State} (hst : c'.π.r s t)
    (hs : s ∉ inertClosure lts c'.π c'.X) (ht : t ∈ inertClosure lts c'.π c'.X) :
    ¬ E lts c'.π s t := by
  intro hE
  obtain ⟨d', hd', hp⟩ := ht
  obtain ⟨s', hIR, hEs'⟩ := E_lift lts c'.π hE hp
  have hs' : s' ∉ inertClosure lts c'.π c'.X := not_inertClosure_path hIR hs
  rw [f.dX] at hd'
  rcases hd' with ⟨hdX, hdD⟩ | ⟨μ, u, huU, hTr, hμ⟩
  · have hdB : d' ∉ cls c.π s0 := fun h => hdD (f.D_iff.2 ⟨h, mem_inertClosure_of_mem hdX⟩)
    have hs'B : s' ∉ cls c.π s0 := fun h =>
      hdB ((cls_saturated c.π s0 s' d' (f.le hEs'.1)).1 h)
    exact inv.S s' d' (f.le hEs'.1) (f.notY_of_out hs'B hs') (mem_inertClosure_of_mem hdX)
      (f.E_out hEs' hs'B)
  · rcases E_step lts c'.π (E.symm lts c'.π hEs') hTr with
      ⟨hτ, hπ, _⟩ | ⟨s'', u1, hIR', hE'', hTr'', hcase⟩
    · exact hμ hτ (f.U_sat (c'.π.symm hπ) huU)
    · rcases hcase with ⟨hτ, hπ, _⟩ | ⟨_, hπ1⟩
      · exact hμ hτ (f.U_sat (c'.π.symm hπ) huU)
      · have hu1U := f.U_sat hπ1 huU
        have hs''X : s'' ∈ c'.X := by
          rw [f.dX]
          exact Or.inr ⟨μ, u1, hu1U, hTr'', fun hτ hs''U =>
            hμ hτ (f.U_sat (c'.π.symm hE''.1) hs''U)⟩
        exact hs' (inertClosure_path hIR' ⟨s'', hs''X, Relation.ReflTransGen.refl⟩)

/-- Uniformity is preserved: clean states of a new block are `E π'`-related. -/
theorem U' (hWF : TauLoopFree lts) (inv : BranchingInv lts c) {s t : State}
    (hst : c'.π.r s t) (hs : s ∉ inertClosure lts c'.π c'.X)
    (ht : t ∉ inertClosure lts c'.π c'.X) : E lts c'.π s t := by
  let Q : State → State → Prop := fun s t => c'.π.r s t ∧ s ∉ inertClosure lts c'.π c'.X ∧
    t ∉ inertClosure lts c'.π c'.X ∧ E lts c.π s t
  refine E_coind lts c'.π Q ?_ ?_ s t ⟨hst, hs, ht, f.E_of_clean inv hst hs ht⟩
  · rintro u v ⟨h1, h2, h3, h4⟩
    exact ⟨c'.π.symm h1, h3, h2, E.symm lts c.π h4⟩
  rintro s t ⟨hπ', hs, ht, hE⟩
  refine ⟨hπ', fun a s1 hTr => ?_⟩
  have hπst : c.π.r s t := f.le hπ'
  by_cases hD : s ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X)
  · -- Case II: `s` was processed in this step
    have hsB : s ∈ cls c.π s0 := (f.D_iff.1 hD).1
    have hsY : s ∈ inertClosure lts c.π c.X := (f.D_iff.1 hD).2
    have hrel := (f.rel s t).1 hπ'
    have htD : t ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X) := (hrel.2 hsB).1.1 hD
    have htB : t ∈ cls c.π s0 := (f.D_iff.1 htD).1
    have htY : t ∈ inertClosure lts c.π c.X := (f.D_iff.1 htD).2
    rcases E_step lts c.π hE hTr with ⟨ha, hπss1, hE1⟩ | ⟨t', t1, hIR, hEt', hTr', hcase⟩
    · subst ha
      have hs1B : s1 ∈ cls c.π s0 := (cls_saturated c.π s0 s s1 hπss1).1 hsB
      by_cases hπ's1 : c'.π.r s s1
      · have hin' : InertTr lts c'.π s s1 := ⟨hTr, hπ's1⟩
        exact Or.inl ⟨rfl, hπ's1, c'.π.trans (c'.π.symm hπ's1) hπ',
          not_inertClosure_path (Relation.ReflTransGen.single hin') hs, ht, hE1⟩
      · exfalso
        by_cases hs1D : s1 ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X)
        · apply hπ's1
          rw [f.rel]
          exact ⟨hπss1, fun _ => ⟨⟨fun _ => hs1D, fun _ => hD⟩,
            fun _ => E.trans lts c.π hE (E.symm lts c.π hE1)⟩⟩
        · exact inv.S s1 t hE1.1 (fun h => hs1D (f.D_iff.2 ⟨hs1B, h⟩)) htY hE1
    · have ht'B : t' ∈ cls c.π s0 := (cls_saturated c.π s0 s t' hEt'.1).1 hsB
      have ht'Y : t' ∈ inertClosure lts c.π c.X := by
        by_contra h
        exact inv.S t' s (c.π.symm hEt'.1) h hsY (E.symm lts c.π hEt')
      have ht'D : t' ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X) := f.D_iff.2 ⟨ht'B, ht'Y⟩
      have mid : ∀ m, InertReach lts c.π t m → InertReach lts c.π m t' → c'.π.r s m := by
        intro m h1 h2
        have hEsm := E_stutter lts c.π hWF hE h1 h2 hEt'
        have hmD := inertClosure_path h2 ht'D
        rw [f.rel]
        exact ⟨hEsm.1, fun _ => ⟨⟨fun _ => hmD, fun _ => hD⟩, fun _ => hEsm⟩⟩
      have path : ∀ y, InertReach lts c.π t y → InertReach lts c.π y t' →
          InertReach lts c'.π t y := by
        intro y h1
        induction h1 with
        | refl => intro _; exact Relation.ReflTransGen.refl
        | @tail w y hrest hstep ih =>
          intro h2
          have h2w : InertReach lts c.π w t' := Relation.ReflTransGen.head hstep h2
          have hw := mid w hrest h2w
          have hy := mid y (hrest.tail hstep) h2
          exact (ih h2w).tail ⟨hstep.1, c'.π.trans (c'.π.symm hw) hy⟩
      have IR' : InertReach lts c'.π t t' := path t' hIR Relation.ReflTransGen.refl
      have hst' : c'.π.r s t' := mid t' hIR Relation.ReflTransGen.refl
      have ht'Y' := not_inertClosure_path IR' ht
      have Qst' : Q s t' := ⟨hst', hs, ht'Y', hEt'⟩
      rcases hcase with ⟨ha, hπss1, hE1⟩ | ⟨hN, hπ1⟩
      · subst ha
        have hs1B : s1 ∈ cls c.π s0 := (cls_saturated c.π s0 s s1 hπss1).1 hsB
        have ht1B : t1 ∈ cls c.π s0 := (cls_saturated c.π s0 s1 t1 hE1.1).1 hs1B
        have hs1t1 : c'.π.r s1 t1 := by
          by_cases hs1D : s1 ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X)
          · have ht1D : t1 ∈ inertClosure lts c.π (cls c.π s0 ∩ c.X) := by
              by_contra h
              exact inv.S t1 s1 (c.π.symm hE1.1) (fun hy => h (f.D_iff.2 ⟨ht1B, hy⟩))
                (f.D_iff.1 hs1D).2 (E.symm lts c.π hE1)
            rw [f.rel]
            exact ⟨hE1.1, fun _ => ⟨⟨fun _ => ht1D, fun _ => hs1D⟩, fun _ => hE1⟩⟩
          · have ht1D : t1 ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X) := fun h =>
              inv.S s1 t1 hE1.1 (fun hy => hs1D (f.D_iff.2 ⟨hs1B, hy⟩)) (f.D_iff.1 h).2 hE1
            rw [f.rel]
            exact ⟨hE1.1, fun _ => ⟨⟨fun h => absurd h hs1D, fun h => absurd h ht1D⟩,
              fun h => absurd h hs1D⟩⟩
        by_cases hπ's1 : c'.π.r s s1
        · have hin' : InertTr lts c'.π s s1 := ⟨hTr, hπ's1⟩
          have hit' : InertTr lts c'.π t' t1 :=
            ⟨hTr', c'.π.trans (c'.π.symm hst') (c'.π.trans hπ's1 hs1t1)⟩
          exact Or.inr ⟨t', t1, IR', Qst', hTr', Or.inl ⟨rfl, hπ's1, hs1t1,
            not_inertClosure_path (Relation.ReflTransGen.single hin') hs,
            not_inertClosure_path (Relation.ReflTransGen.single hit') ht'Y', hE1⟩⟩
        · exact Or.inr ⟨t', t1, IR', Qst', hTr', Or.inr ⟨Or.inr hπ's1, hs1t1⟩⟩
      · have hNt' : a ≠ HasTau.τ ∨ ¬ c.π.r t' t1 := by
          rcases hN with h | h
          · exact Or.inl h
          · exact Or.inr (fun h' => h (c.π.trans hEt'.1 (c.π.trans h' (c.π.symm hπ1))))
        have hN' : a ≠ HasTau.τ ∨ ¬ c'.π.r s s1 := by
          rcases hN with h | h
          · exact Or.inl h
          · exact Or.inr (fun h' => h (f.le h'))
        exact Or.inr ⟨t', t1, IR', Qst', hTr',
          Or.inr ⟨hN', f.tails_pi' hs ht'Y' hTr hTr' hN hNt' hπ1⟩⟩
  · -- Case I: `s` (and `t`) were not processed
    have htD : t ∉ inertClosure lts c.π (cls c.π s0 ∩ c.X) := by
      intro h
      have hsB : s ∈ cls c.π s0 := (cls_saturated c.π s0 s t hπst).2 (f.D_iff.1 h).1
      exact hD ((((f.rel s t).1 hπ').2 hsB).1.2 h)
    have hsY := f.notY_of_notD hs hD
    have htY := f.notY_of_notD ht htD
    rcases E_step lts c.π hE hTr with ⟨ha, hπss1, hE1⟩ | ⟨t', t1, hIR, hEt', hTr', hcase⟩
    · subst ha
      have hin' := f.inert_pres hsY ⟨hTr, hπss1⟩
      exact Or.inl ⟨rfl, hin'.2, c'.π.trans (c'.π.symm hin'.2) hπ',
        not_inertClosure_path (Relation.ReflTransGen.single hin') hs, ht, hE1⟩
    · have IR' := f.inertReach_pres htY hIR
      have ht'Y := not_inertClosure_path hIR htY
      have ht'Y' := not_inertClosure_path IR' ht
      have hst' : c'.π.r s t' := c'.π.trans hπ' (InertReach.rel lts c'.π IR')
      have Qst' : Q s t' := ⟨hst', hs, ht'Y', hEt'⟩
      rcases hcase with ⟨ha, hπss1, hE1⟩ | ⟨hN, hπ1⟩
      · subst ha
        have hπt't1 : c.π.r t' t1 := c.π.trans (c.π.symm hEt'.1) (c.π.trans hπss1 hE1.1)
        have hin' := f.inert_pres hsY ⟨hTr, hπss1⟩
        have hit' := f.inert_pres ht'Y ⟨hTr', hπt't1⟩
        exact Or.inr ⟨t', t1, IR', Qst', hTr', Or.inl ⟨rfl, hin'.2,
          c'.π.trans (c'.π.symm hin'.2) (c'.π.trans hst' hit'.2),
          not_inertClosure_path (Relation.ReflTransGen.single hin') hs,
          not_inertClosure_path (Relation.ReflTransGen.single hit') ht'Y', hE1⟩⟩
      · have hNt' : a ≠ HasTau.τ ∨ ¬ c.π.r t' t1 := by
          rcases hN with h | h
          · exact Or.inl h
          · exact Or.inr (fun h' => h (c.π.trans hEt'.1 (c.π.trans h' (c.π.symm hπ1))))
        have hN' : a ≠ HasTau.τ ∨ ¬ c'.π.r s s1 := by
          rcases hN with h | h
          · exact Or.inl h
          · exact Or.inr (fun h' => h (f.le h'))
        exact Or.inr ⟨t', t1, IR', Qst', hTr',
          Or.inr ⟨hN', f.tails_pi' hs ht'Y' hTr hTr' hN hNt' hπ1⟩⟩

end StepFacts

/-- **The invariant is preserved by every step.** -/
theorem branchingInv_step (lts : LTS State Label) (hWF : TauLoopFree lts) {c c' : Config State}
    (inv : BranchingInv lts c) (h : BranchingStep lts c c') : BranchingInv lts c' := by
  obtain ⟨s0, s1, f⟩ := h
  exact ⟨fun s t hb => f.R' hWF inv hb,
    fun s t hb => ⟨f.M' hWF inv hb, f.M' hWF inv (BranchingBisimilarity.symm hb)⟩,
    fun s t hst hs ht => f.U' hWF inv hst hs ht,
    fun s t hst hs ht => f.S' inv hst hs ht⟩

/-- An inert path is a τ-path. -/
theorem inertReach_tauPath {lts : LTS State Label} {π : Setoid State} {s t : State}
    (h : InertReach lts π s t) : lts.τSTr s t :=
  Relation.ReflTransGen.mono (fun _ _ h => h.1) h

/-- **Final.** With no dirty state left, the partition is exactly branching bisimilarity. -/
theorem branchingInv_final (lts : LTS State Label) {c : Config State}
    (inv : BranchingInv lts c) (hX : ∀ s, s ∉ c.X) (s t : State) :
    c.π.r s t ↔ BranchingBisimilarity lts s t := by
  refine ⟨fun h => ?_, inv.R s t⟩
  have hY : ∀ s, s ∉ inertClosure lts c.π c.X := fun s ⟨d, hd, _⟩ => hX d hd
  have hE : ∀ s t, c.π.r s t → E lts c.π s t := fun s t h => inv.U s t h (hY s) (hY t)
  have half : ∀ s t, c.π.r s t → ∀ μ s1, lts.Tr s μ s1 →
      (μ = HasTau.τ ∧ c.π.r s1 t) ∨ ∃ t' t'', lts.STr t HasTau.τ t' ∧ lts.Tr t' μ t'' ∧
        c.π.r s t' ∧ c.π.r s1 t'' := by
    intro s t h μ s1 hTr
    rcases E_step lts c.π (hE s t h) hTr with ⟨ha, _, hE1⟩ | ⟨t', t1, hIR, hEt', hTr', hcase⟩
    · exact Or.inl ⟨ha, hE1.1⟩
    · refine Or.inr ⟨t', t1, (LTS.sTr_τSTr lts).mpr (inertReach_tauPath hIR), hTr', hEt'.1, ?_⟩
      rcases hcase with ⟨_, _, hE1⟩ | ⟨_, hπ1⟩
      · exact hE1.1
      · exact hπ1
  refine ⟨c.π.r, h, fun s t h μ => ⟨half s t h μ, fun t1 hTr => ?_⟩⟩
  rcases half t s (c.π.symm h) μ t1 hTr with ⟨ha, h1⟩ | ⟨s', s'', hS, hT, h2, h3⟩
  · exact Or.inl ⟨ha, c.π.symm h1⟩
  · exact Or.inr ⟨s', s'', hS, hT, c.π.symm h2, c.π.symm h3⟩

/-- The termination measure, as for the strong algorithm. -/
theorem branchingStep_measure_lt [Finite State] (lts : LTS State Label) {c c' : Config State}
    (h : BranchingStep lts c c') : measure c' < measure c := by
  obtain ⟨s0, s1, f⟩ := h
  obtain ⟨e, heB, heX⟩ := f.dirty
  have hsub : {p : State × State | c'.π.r p.1 p.2} ⊆ {p : State × State | c.π.r p.1 p.2} :=
    fun p hp => f.le hp
  by_cases heq : ∀ p : State × State, c.π.r p.1 p.2 → c'.π.r p.1 p.2
  · have hcls : cls c.π s0 \ cls c'.π s1 = ∅ := by
      ext t
      simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro ht
      exact heq (s1, t) (c.π.trans (c.π.symm f.mem) ht)
    have hX' : c'.X = c.X \ inertClosure lts c.π (cls c.π s0 ∩ c.X) := by
      rw [f.dX, hcls]
      ext x; simp [predB]
    have hrel : {p : State × State | c'.π.r p.1 p.2} = {p : State × State | c.π.r p.1 p.2} :=
      Set.Subset.antisymm hsub heq
    unfold measure
    rw [hrel]
    refine Prod.Lex.right _ ?_
    rw [hX']
    refine Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.2 ⟨e, heX, ?_⟩) (Set.toFinite _)
    exact ⟨e, ⟨heB, heX⟩, Relation.ReflTransGen.refl⟩
  · push Not at heq
    obtain ⟨p, hp, hnp⟩ := heq
    have hss : {p : State × State | c'.π.r p.1 p.2} ⊂ {p : State × State | c.π.r p.1 p.2} :=
      Set.ssubset_iff_of_subset hsub |>.2 ⟨p, hp, hnp⟩
    exact Prod.Lex.left _ _ (Set.ncard_lt_ncard hss (Set.toFinite _))

/-- **Termination:** on a finite state space every sequence of steps is finite. -/
theorem branchingStep_wf [Finite State] (lts : LTS State Label) :
    WellFounded (fun c' c : Config State => BranchingStep lts c c') :=
  Subrelation.wf (fun h => branchingStep_measure_lt lts h) (InvImage.wf measure wellFounded_lt)

/-- The split relation is an equivalence (this is where transitivity of `E π` is needed). -/
def branchSetoid (lts : LTS State Label) (π : Setoid State) (X : Set State) (s0 : State) :
    Setoid State where
  r := branchRel lts π X s0
  iseqv := by
    have sat := cls_saturated π s0
    refine ⟨fun s => ⟨π.refl s, fun _ => ⟨Iff.rfl, fun _ => E.refl lts π s⟩⟩, ?_, ?_⟩
    · intro s t ⟨hst, h⟩
      refine ⟨π.symm hst, fun ht => ?_⟩
      obtain ⟨h1, h2⟩ := h ((sat s t hst).2 ht)
      exact ⟨h1.symm, fun htD => E.symm lts π (h2 (h1.2 htD))⟩
    · intro s t u ⟨hst, h1⟩ ⟨htu, h2⟩
      refine ⟨π.trans hst htu, fun hs => ?_⟩
      obtain ⟨a1, a2⟩ := h1 hs
      obtain ⟨b1, b2⟩ := h2 ((sat s t hst).1 hs)
      exact ⟨a1.trans b1, fun hsD => E.trans lts π (a2 hsD) (b2 (a1.1 hsD))⟩

/-- **Progress**: a configuration with a dirty state can always take a step. -/
theorem branchingStep_exists (lts : LTS State Label) (c : Config State) {s : State}
    (hs : s ∈ c.X) : ∃ c', BranchingStep lts c c' := by
  let π' := branchSetoid lts c.π c.X s
  refine ⟨⟨π', (c.X \ inertClosure lts c.π (cls c.π s ∩ c.X)) ∪
    predB lts (cls c.π s \ cls π' s)⟩, s, s, ?_⟩
  exact ⟨⟨s, c.π.refl s, hs⟩, c.π.refl s, fun _ _ => Iff.rfl, rfl⟩

/-- Every reachable configuration satisfies the invariant. -/
theorem branchingInv_reach (lts : LTS State Label) (hWF : TauLoopFree lts) {c : Config State}
    (h : Relation.ReflTransGen (BranchingStep lts) (initConfig State) c) : BranchingInv lts c := by
  induction h with
  | refl => exact branchingInv_init lts
  | tail _ hstep ih => exact branchingInv_step lts hWF ih hstep

/-- **Correctness of the abstract branching algorithm**: any run that ends without dirty states
yields exactly branching bisimilarity. -/
theorem branching_run_correct (lts : LTS State Label) (hWF : TauLoopFree lts) {c : Config State}
    (h : Relation.ReflTransGen (BranchingStep lts) (initConfig State) c)
    (hX : ∀ s, s ∉ c.X) (s t : State) : c.π.r s t ↔ BranchingBisimilarity lts s t :=
  branchingInv_final lts (branchingInv_reach lts hWF h) hX s t

/-- **Termination and totality**: on a finite τ-loop-free LTS the algorithm always reaches a
configuration without dirty states, whatever choices it makes, and that configuration is branching
bisimilarity. -/
theorem branching_terminates [Finite State] (lts : LTS State Label) (hWF : TauLoopFree lts) :
    ∃ c, Relation.ReflTransGen (BranchingStep lts) (initConfig State) c ∧ (∀ s, s ∉ c.X) ∧
      ∀ s t, c.π.r s t ↔ BranchingBisimilarity lts s t := by
  have key : ∀ c : Config State, Relation.ReflTransGen (BranchingStep lts) (initConfig State) c →
      ∃ c', Relation.ReflTransGen (BranchingStep lts) (initConfig State) c' ∧ (∀ s, s ∉ c'.X) := by
    intro c
    induction c using (branchingStep_wf lts).induction with
    | _ c ih =>
      intro hc
      by_cases hX : ∀ s, s ∉ c.X
      · exact ⟨c, hc, hX⟩
      · push Not at hX
        obtain ⟨s, hs⟩ := hX
        obtain ⟨c1, h1⟩ := branchingStep_exists lts c hs
        exact ih c1 h1 (hc.tail h1)
  obtain ⟨c, hc, hX⟩ := key _ Relation.ReflTransGen.refl
  exact ⟨c, hc, hX, branching_run_correct lts hWF hc hX⟩
/-- Headline: correctness of the abstract branching signature refinement. -/
theorem branchingSigrefCorrect (lts : LTS State Label) : BranchingSigrefCorrect lts :=
  ⟨branchingInv_init lts, fun hWF _ _ h s => branchingInv_step lts hWF h s,
    fun _ h hX => branchingInv_final lts h hX⟩

/-- Headline: termination of the abstract branching signature refinement. -/
theorem branchingSigrefTerminates [Finite State] (lts : LTS State Label) :
    BranchingSigrefTerminates lts :=
  branchingStep_wf lts

/-- Headline: progress of the abstract branching signature refinement. -/
theorem branchingSigrefProgress (lts : LTS State Label) : BranchingSigrefProgress lts :=
  fun c _ hs => branchingStep_exists lts c hs

/-- Headline: totality of the abstract branching signature refinement. -/
theorem branchingSigrefTotal [Finite State] (lts : LTS State Label) :
    BranchingSigrefTotal lts :=
  fun hWF => branching_terminates lts hWF


end Sigref
