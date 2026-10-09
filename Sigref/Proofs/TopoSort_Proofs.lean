import Sigref.TopoSort
import Mathlib.Order.WellFounded
import Mathlib.Data.Fintype.Card

/-!
# Proofs: the topological sort

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/TopoSort_Pins.lean` (human-vetted).
-/

namespace Sigref.Topo

open Relation

variable {n : ℕ}

theorem pushSuccs_spec (m : Fin n → Option Mark) (ts D : List (Fin n)) (a : Bool) :
    (pushSuccs m ts D a).1 = (ts.filter (fun w => decide (m w = none))).reverse ++ D ∧
    ((pushSuccs m ts D a).2 = true ↔ a = true ∧ ∀ w ∈ ts, m w ≠ some Mark.temp) := by
  induction ts generalizing D a with
  | nil => simp [pushSuccs]
  | cons w ts ih =>
    cases hw : m w with
    | none =>
      obtain ⟨h1, h2⟩ := ih (w :: D) a
      simp only [pushSuccs, hw]
      refine ⟨?_, ?_⟩
      · rw [h1]; simp [hw]
      · rw [h2]; simp [hw]
    | some mk =>
      cases mk with
      | temp =>
        obtain ⟨h1, h2⟩ := ih D false
        simp only [pushSuccs, hw]
        refine ⟨?_, ?_⟩
        · rw [h1]; simp [hw]
        · rw [h2]; simp [hw]
      | perm =>
        obtain ⟨h1, h2⟩ := ih D a
        simp only [pushSuccs, hw]
        refine ⟨?_, ?_⟩
        · rw [h1]; simp [hw]
        · rw [h2]; simp [hw]

/-- The edge relation of the graph. -/
def E (succ : Fin n → List (Fin n)) (a b : Fin n) : Prop := b ∈ succ a

/-- Reflexive-transitive closure of `step`. -/
abbrev Runs (succ : Fin n → List (Fin n)) (c c' : Cfg n) : Prop :=
  ReflTransGen (fun a b => step succ a = some b) c c'

/-- The invariant of the finished states: they are exactly the `Permanent` ones, listed once, and
every successor of a finished state was finished before it. -/
structure Good (succ : Fin n → List (Fin n)) (c : Cfg n) : Prop where
  perm : ∀ a, c.marks a = some Mark.perm ↔ a ∈ c.order
  nodup : c.order.Nodup
  closed : ∀ l1 a l2, c.order = l1 ++ a :: l2 → ∀ b ∈ succ a, b ∈ l1

/-- What a run preserves: the finishing order only grows, the `Temporary` states stay the same. -/
structure Ext (c c' : Cfg n) : Prop where
  prefix_ : c.order <+: c'.order
  temp : ∀ t, c'.marks t = some Mark.temp ↔ c.marks t = some Mark.temp
  idx : c'.idx = c.idx

theorem Ext.refl (c : Cfg n) : Ext c c := ⟨List.prefix_refl _, fun _ => Iff.rfl, rfl⟩

theorem Ext.trans {c1 c2 c3 : Cfg n} (h1 : Ext c1 c2) (h2 : Ext c2 c3) : Ext c1 c3 :=
  ⟨h1.prefix_.trans h2.prefix_, fun t => (h2.temp t).trans (h1.temp t), h2.idx.trans h1.idx⟩

/-- The claim for the visit of `v`. -/
def VisitStmt (succ : Fin n → List (Fin n)) (v : Fin n) : Prop :=
  ∀ (c : Cfg n) (D : List (Fin n)), c.depth = v :: D → Good succ c → c.acyc = true →
    (∀ t, c.marks t = some Mark.temp → TransGen (E succ) t v) →
    ∃ c', Runs succ c c' ∧ c'.depth = D ∧ Good succ c' ∧ Ext c c' ∧
      c'.marks v = some Mark.perm ∧ c'.acyc = true

theorem closed_snoc (succ : Fin n → List (Fin n)) (o : List (Fin n)) (v : Fin n)
    (hc : ∀ l1 a l2, o = l1 ++ a :: l2 → ∀ b ∈ succ a, b ∈ l1) (hv : ∀ b ∈ succ v, b ∈ o) :
    ∀ l1 a l2, o ++ [v] = l1 ++ a :: l2 → ∀ b ∈ succ a, b ∈ l1 := by
  intro l1 a l2 h b hb
  rcases List.eq_nil_or_concat l2 with rfl | ⟨l2', z, rfl⟩
  · have h' : o ++ [v] = l1 ++ [a] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    subst h1
    have : a = v := by simpa using h2.symm
    subst this
    exact hv b hb
  · have h' : o ++ [v] = (l1 ++ a :: l2') ++ [z] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    exact hc l1 a l2' h1 b hb

theorem cands {succ : Fin n → List (Fin n)} (_hA : Acyclic succ) (v : Fin n) (ih : ∀ w, E succ v w → VisitStmt succ w) :
    ∀ (cs : List (Fin n)), (∀ w ∈ cs, E succ v w) → ∀ (c : Cfg n) (D : List (Fin n)),
      c.depth = cs ++ D → Good succ c → c.acyc = true →
      (∀ t, c.marks t = some Mark.temp → t = v ∨ TransGen (E succ) t v) →
      ∃ c', Runs succ c c' ∧ c'.depth = D ∧ Good succ c' ∧ Ext c c' ∧
        (∀ w ∈ cs, c'.marks w = some Mark.perm) ∧ c'.acyc = true := by
  intro cs
  induction cs with
  | nil =>
    intro _ c D hd hg ha _
    exact ⟨c, ReflTransGen.refl, by simpa using hd, hg, Ext.refl c, by simp, ha⟩
  | cons w cs ihc =>
    intro hcs c D hd hg ha hT
    have hw : E succ v w := hcs w (List.mem_cons_self ..)
    have hd' : c.depth = w :: (cs ++ D) := by simpa using hd
    have hTw : ∀ t, c.marks t = some Mark.temp → TransGen (E succ) t w := by
      intro t ht
      rcases hT t ht with rfl | h
      · exact TransGen.single hw
      · exact h.tail hw
    obtain ⟨c1, hr1, hd1, hg1, hx1, hp1, ha1⟩ := ih w hw c (cs ++ D) hd' hg ha hTw
    obtain ⟨c2, hr2, hd2, hg2, hx2, hp2, ha2⟩ := ihc (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
      c1 D hd1 hg1 ha1 (fun t ht => hT t ((hx1.temp t).1 ht))
    refine ⟨c2, hr1.trans hr2, hd2, hg2, hx1.trans hx2, ?_, ha2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hg2.perm x).2 (hx2.prefix_.subset ((hg1.perm x).1 hp1))
    · exact hp2 x hx

theorem acyclic_wf {succ : Fin n → List (Fin n)} (hA : Acyclic succ) : WellFounded (fun b a : Fin n => TransGen (E succ) a b) := by
  haveI : IsTrans (Fin n) (fun b a : Fin n => TransGen (E succ) a b) :=
    ⟨fun a b c hab hbc => TransGen.trans hbc hab⟩
  haveI : Std.Irrefl (fun b a : Fin n => TransGen (E succ) a b) := ⟨fun a h => hA a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

theorem step_none (succ : Fin n → List (Fin n)) (c : Cfg n) (x : Fin n) (D : List (Fin n))
    (hd : c.depth = x :: D) (hm : c.marks x = none) :
    step succ c = some { c with
      marks := Function.update c.marks x (some Mark.temp)
      depth := (pushSuccs (Function.update c.marks x (some Mark.temp)) (succ x) (x :: D) c.acyc).1
      acyc := (pushSuccs (Function.update c.marks x (some Mark.temp)) (succ x) (x :: D) c.acyc).2 } := by
  simp [step, hd, hm]

theorem step_temp (succ : Fin n → List (Fin n)) (c : Cfg n) (x : Fin n) (D : List (Fin n))
    (hd : c.depth = x :: D) (hm : c.marks x = some Mark.temp) :
    step succ c = some {
      marks := Function.update c.marks x (some Mark.perm)
      depth := D
      order := c.order ++ [x]
      acyc := c.acyc
      idx := c.idx } := by
  simp [step, hd, hm]

theorem step_perm (succ : Fin n → List (Fin n)) (c : Cfg n) (x : Fin n) (D : List (Fin n))
    (hd : c.depth = x :: D) (hm : c.marks x = some Mark.perm) :
    step succ c = some { c with depth := D } := by
  simp [step, hd, hm]

theorem visit_all {succ : Fin n → List (Fin n)} (hA : Acyclic succ) : ∀ v, VisitStmt succ v := by
  intro v
  induction v using (acyclic_wf hA).induction with
  | _ v ih =>
  intro c D hd hg hacyc hT
  cases hm : c.marks v with
  | some mk =>
    cases mk with
    | temp => exact absurd (hT v hm) (hA v)
    | perm =>
      refine ⟨{ c with depth := D }, ReflTransGen.single (step_perm succ c v D hd hm), rfl,
        ⟨hg.perm, hg.nodup, hg.closed⟩, ⟨List.prefix_refl _, fun _ => Iff.rfl, rfl⟩, hm, hacyc⟩
  | none =>
    set marks' := Function.update c.marks v (some Mark.temp) with hmarks'
    obtain ⟨hpd, hpa⟩ := pushSuccs_spec marks' (succ v) (v :: D) c.acyc
    set cs := ((succ v).filter (fun w => decide (marks' w = none))).reverse with hcs
    have hcsE : ∀ w ∈ cs, E succ v w := by
      intro w hw
      rw [hcs, List.mem_reverse, List.mem_filter] at hw
      exact hw.1
    have hne : ∀ w ∈ succ v, w ≠ v := fun w hw h => hA v (by subst h; exact TransGen.single hw)
    have hm'w : ∀ w, w ≠ v → marks' w = c.marks w := fun w hw => by
      simp [hmarks', Function.update_of_ne hw]
    have hnoTemp : ∀ w ∈ succ v, c.marks w ≠ some Mark.temp := by
      intro w hw h
      exact hA v (TransGen.head hw (hT w h))
    have hacyc1 : (pushSuccs marks' (succ v) (v :: D) c.acyc).2 = true := by
      rw [hpa.2]
      refine ⟨hacyc, fun w hw => ?_⟩
      rw [hm'w w (hne w hw)]
      exact hnoTemp w hw
    set c1 : Cfg n := { c with
      marks := marks'
      depth := (pushSuccs marks' (succ v) (v :: D) c.acyc).1
      acyc := (pushSuccs marks' (succ v) (v :: D) c.acyc).2 } with hc1
    have hstep1 : step succ c = some c1 := step_none succ c v D hd hm
    have hvnot : v ∉ c.order := fun h => by
      have := (hg.perm v).2 h
      rw [hm] at this; cases this
    have hg1 : Good succ c1 := by
      refine ⟨fun a => ?_, hg.nodup, hg.closed⟩
      show marks' a = some Mark.perm ↔ a ∈ c.order
      by_cases hav : a = v
      · subst hav; simp [hmarks', hvnot]
      · rw [hm'w a hav]; exact hg.perm a
    have hd1 : c1.depth = cs ++ (v :: D) := hpd
    obtain ⟨c2, hr2, hd2, hg2, hx2, hp2, ha2⟩ := cands hA v (fun w hw => ih w (TransGen.single hw))
      cs hcsE c1 (v :: D) hd1 hg1 hacyc1 (by
        intro t ht
        by_cases htv : t = v
        · exact Or.inl htv
        · exact Or.inr (hT t (by rw [← hm'w t htv]; exact ht)))
    have hv2 : c2.marks v = some Mark.temp := (hx2.temp v).2 (by simp [c1, hmarks'])
    have hstep3 := step_temp succ c2 v D hd2 hv2
    set c3 : Cfg n := {
      marks := Function.update c2.marks v (some Mark.perm)
      depth := D
      order := c2.order ++ [v]
      acyc := c2.acyc
      idx := c2.idx } with hc3
    have hv2n : v ∉ c2.order := fun h => by
      have := (hg2.perm v).2 h
      rw [hv2] at this; cases this
    have hsucc : ∀ b ∈ succ v, b ∈ c2.order := by
      intro b hb
      rw [← hg2.perm]
      have hbv := hne b hb
      cases hmb : c.marks b with
      | none =>
        apply hp2
        rw [hcs, List.mem_reverse, List.mem_filter]
        exact ⟨hb, by simp [hm'w b hbv, hmb]⟩
      | some mk =>
        cases mk with
        | temp => exact absurd hmb (hnoTemp b hb)
        | perm =>
          exact (hg2.perm b).2 (hx2.prefix_.subset ((hg.perm b).1 hmb))
    have hg3 : Good succ c3 := by
      refine ⟨fun a => ?_, ?_, closed_snoc succ c2.order v hg2.closed hsucc⟩
      · show Function.update c2.marks v (some Mark.perm) a = some Mark.perm ↔ a ∈ c2.order ++ [v]
        by_cases hav : a = v
        · subst hav; simp
        · rw [Function.update_of_ne hav]; simp [hav, hg2.perm a]
      · show (c2.order ++ [v]).Nodup
        exact List.nodup_append.2 ⟨hg2.nodup, List.nodup_singleton v, fun a ha b hb => by
          rw [List.mem_singleton] at hb; subst hb; intro h; exact hv2n (h ▸ ha)⟩
    refine ⟨c3, ReflTransGen.head hstep1 (hr2.tail hstep3), rfl, hg3, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact (List.prefix_refl c.order).trans (hx2.prefix_.trans (List.prefix_append _ _))
      · intro t
        show Function.update c2.marks v (some Mark.perm) t = some Mark.temp ↔ _
        by_cases htv : t = v
        · subst htv; simp [hm]
        · rw [Function.update_of_ne htv, hx2.temp t]
          show marks' t = some Mark.temp ↔ _
          rw [hm'w t htv]
      · exact hx2.idx
    · show Function.update c2.marks v (some Mark.perm) v = some Mark.perm
      simp
    · exact ha2

/-- The configurations between two roots of the outer loop. -/
structure Root (succ : Fin n → List (Fin n)) (c : Cfg n) : Prop where
  depth : c.depth = []
  good : Good succ c
  acyc : c.acyc = true
  notemp : ∀ a, c.marks a ≠ some Mark.temp
  done : ∀ a : Fin n, a.val < c.idx → c.marks a = some Mark.perm

theorem step_root (succ : Fin n → List (Fin n)) (c : Cfg n) (hd : c.depth = []) (h : c.idx < n)
    (hm : c.marks ⟨c.idx, h⟩ = none) :
    step succ c = some { c with depth := [⟨c.idx, h⟩], idx := c.idx + 1 } := by
  simp [step, hd, h, hm]

theorem step_root_marked (succ : Fin n → List (Fin n)) (c : Cfg n) (hd : c.depth = [])
    (h : c.idx < n) (hm : c.marks ⟨c.idx, h⟩ ≠ none) :
    step succ c = some { c with idx := c.idx + 1 } := by
  simp [step, hd, h, hm]

theorem step_end (succ : Fin n → List (Fin n)) (c : Cfg n) (hd : c.depth = []) (h : ¬ c.idx < n) :
    step succ c = none := by
  simp [step, hd, h]

theorem root_init (succ : Fin n → List (Fin n)) : Root succ (init n) := by
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, rfl, ?_, ?_⟩
  · intro a; simp [init]
  · simp [init]
  · intro l1 a l2 h; simp [init] at h
  · intro a; simp [init]
  · intro a ha; simp [init] at ha

theorem root_progress {succ : Fin n → List (Fin n)} (hA : Acyclic succ) :
    ∀ k, k ≤ n → ∃ c, Runs succ (init n) c ∧ Root succ c ∧ c.idx = k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨init n, ReflTransGen.refl, ⟨rfl, ⟨?_, ?_, ?_⟩, rfl, ?_, ?_⟩, rfl⟩
    · intro a; simp [init]
    · simp [init]
    · intro l1 a l2 h; simp [init] at h
    · intro a; simp [init]
    · intro a ha; simp [init] at ha
  | succ k ih =>
    intro hk
    obtain ⟨c, hr, hroot, hidx⟩ := ih (by omega)
    have hkn : c.idx < n := by omega
    by_cases hm : c.marks ⟨c.idx, hkn⟩ = none
    · set c1 : Cfg n := { c with depth := [⟨c.idx, hkn⟩], idx := c.idx + 1 } with hc1
      have hs1 : step succ c = some c1 := step_root succ c hroot.depth hkn hm
      obtain ⟨c2, hr2, hd2, hg2, hx2, hp2, ha2⟩ := visit_all hA ⟨c.idx, hkn⟩ c1 [] rfl
        ⟨hroot.good.perm, hroot.good.nodup, hroot.good.closed⟩ hroot.acyc (fun t ht => absurd ht (hroot.notemp t))
      refine ⟨c2, (hr.tail hs1).trans hr2, ⟨hd2, hg2, ha2, ?_, ?_⟩, ?_⟩
      · intro a ha; exact hroot.notemp a ((hx2.temp a).1 ha)
      · intro a ha
        have hidx2 : c2.idx = c.idx + 1 := hx2.idx
        rw [hidx2] at ha
        by_cases hak : a.val < c.idx
        · exact (hg2.perm a).2 (hx2.prefix_.subset ((hroot.good.perm a).1 (hroot.done a hak)))
        · have : a = ⟨c.idx, hkn⟩ := Fin.ext (by simp; omega)
          subst this; exact hp2
      · rw [hx2.idx]; simp [hc1, hidx]
    · have hs1 := step_root_marked succ c hroot.depth hkn hm
      have hperm : c.marks ⟨c.idx, hkn⟩ = some Mark.perm := by
        cases h : c.marks ⟨c.idx, hkn⟩ with
        | none => exact absurd h hm
        | some mk => cases mk with
          | temp => exact absurd h (hroot.notemp _)
          | perm => rfl
      refine ⟨{ c with idx := c.idx + 1 }, hr.tail hs1, ⟨hroot.depth, ⟨hroot.good.perm, hroot.good.nodup,
        hroot.good.closed⟩, hroot.acyc, hroot.notemp, ?_⟩, by simp [hidx]⟩
      intro a ha
      show c.marks a = some Mark.perm
      by_cases hak : a.val < c.idx
      · exact hroot.done a hak
      · have : a = ⟨c.idx, hkn⟩ := Fin.ext (by simp at ha ⊢; omega)
        subst this; exact hperm

theorem topoSortCorrect (succ : Fin n → List (Fin n)) : TopoSortCorrect succ := by
  intro hA c hc hterm
  obtain ⟨cn, hrn, hroot, hidx⟩ := root_progress hA n le_rfl
  have hterm_n : step succ cn = none := step_end succ cn hroot.depth (by omega)
  have hru : Relator.RightUnique (fun a b => step succ a = some b) := by
    intro a b b' h h'; rw [h] at h'; exact Option.some.inj h'
  have hceq : c = cn := by
    rcases ReflTransGen.total_of_right_unique hru hc hrn with h | h
    · cases h using ReflTransGen.head_induction_on with
      | refl => rfl
      | head hab _ => rw [hterm] at hab; cases hab
    · cases h using ReflTransGen.head_induction_on with
      | refl => rfl
      | head hab _ => rw [hterm_n] at hab; cases hab
  subst hceq
  refine ⟨hroot.acyc, hroot.good.nodup, fun v => ?_, hroot.good.closed⟩
  exact (hroot.good.perm v).1 (hroot.done v (by rw [hidx]; exact v.2))

theorem filter_none_update (marks : Fin n → Option Mark) (x : Fin n) (mk : Mark)
    (hx : marks x = none) :
    Finset.univ.filter (fun u => Function.update marks x (some mk) u = none) =
      (Finset.univ.filter (fun u => marks u = none)).erase x := by
  ext u
  by_cases hu : u = x
  · subst hu; simp [hx]
  · simp [hu]

theorem filter_none_update_ne (marks : Fin n → Option Mark) (x : Fin n) (mk : Mark)
    (hx : marks x ≠ none) :
    Finset.univ.filter (fun u => Function.update marks x (some mk) u = none) =
      Finset.univ.filter (fun u => marks u = none) := by
  ext u
  by_cases hu : u = x
  · subst hu; simp [hx]
  · simp [Function.update_of_ne hu]

theorem topoSortTerminates (succ : Fin n → List (Fin n)) : TopoSortTerminates succ := by
  intro c c' h
  unfold step at h
  rcases hd : c.depth with _ | ⟨x, D⟩
  · rw [hd] at h
    simp only at h
    by_cases hi : c.idx < n
    · rw [dif_pos hi] at h
      by_cases hm : c.marks ⟨c.idx, hi⟩ = none
      · rw [if_pos hm] at h
        cases h
        unfold measure
        simp [hd]
        omega
      · rw [if_neg hm] at h
        cases h
        unfold measure
        simp [hd]
        omega
    · rw [dif_neg hi] at h; cases h
  · rw [hd] at h
    simp only at h
    cases hm : c.marks x with
    | none =>
      rw [hm] at h
      simp only at h
      cases h
      obtain ⟨hpd, -⟩ := pushSuccs_spec (Function.update c.marks x (some Mark.temp)) (succ x) (x :: D) c.acyc
      unfold measure
      simp only [hd]
      rw [filter_none_update c.marks x Mark.temp hm, hpd]
      have hmem : x ∈ Finset.univ.filter (fun u => c.marks u = none) := by simp [hm]
      rw [Finset.card_erase_of_mem hmem, ← Finset.add_sum_erase _ (fun u => (succ u).length) hmem]
      have hlen : ((succ x).filter (fun w => decide (Function.update c.marks x (some Mark.temp) w = none))).reverse.length
          ≤ (succ x).length := by
        simpa using List.length_filter_le _ _
      have hcard : 0 < (Finset.univ.filter (fun u => c.marks u = none)).card :=
        Finset.card_pos.2 ⟨x, hmem⟩
      simp only [List.length_append, List.length_cons]
      omega
    | some mk =>
      cases mk with
      | temp =>
        rw [hm] at h
        simp only at h
        cases h
        unfold measure
        simp only [hd]
        rw [filter_none_update_ne c.marks x Mark.perm (by simp [hm])]
        simp
      | perm =>
        rw [hm] at h
        simp only at h
        cases h
        unfold measure
        simp [hd]

theorem step_idx_mono {succ : Fin n → List (Fin n)} {c c' : Cfg n} (h : step succ c = some c') :
    c.idx ≤ c'.idx := by
  unfold step at h
  rcases hd : c.depth with _ | ⟨x, D⟩
  · rw [hd] at h
    simp only at h
    by_cases hi : c.idx < n
    · rw [dif_pos hi] at h
      by_cases hm : c.marks ⟨c.idx, hi⟩ = none
      · rw [if_pos hm] at h; cases h; simp
      · rw [if_neg hm] at h; cases h; simp
    · rw [dif_neg hi] at h; cases h
  · rw [hd] at h
    simp only at h
    cases hm : c.marks x with
    | none => rw [hm] at h; simp only at h; cases h; rfl
    | some mk =>
      cases mk <;> (rw [hm] at h; simp only at h; cases h; rfl)

theorem step_nil_idx {succ : Fin n → List (Fin n)} {c c' : Cfg n} (hd : c.depth = [])
    (h : step succ c = some c') : c'.idx = c.idx + 1 := by
  unfold step at h
  rw [hd] at h
  simp only at h
  by_cases hi : c.idx < n
  · rw [dif_pos hi] at h
    by_cases hm : c.marks ⟨c.idx, hi⟩ = none
    · rw [if_pos hm] at h; cases h; rfl
    · rw [if_neg hm] at h; cases h; rfl
  · rw [dif_neg hi] at h; cases h

theorem runs_idx_mono {succ : Fin n → List (Fin n)} {c c' : Cfg n} (h : Runs succ c c') :
    c.idx ≤ c'.idx := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (step_idx_mono hs)

/-- Two configurations with an empty stack that are reached from one configuration and have the same
counter are equal. -/
theorem unique_empty {succ : Fin n → List (Fin n)} {c a b : Cfg n} (ha : Runs succ c a)
    (hb : Runs succ c b) (hda : a.depth = []) (hdb : b.depth = []) (hi : a.idx = b.idx) : a = b := by
  have hru : Relator.RightUnique (fun x y => step succ x = some y) := by
    intro a b b' h h'; rw [h] at h'; exact Option.some.inj h'
  rcases ReflTransGen.total_of_right_unique hru ha hb with h | h
  · cases h using ReflTransGen.head_induction_on with
    | refl => rfl
    | head hab hrest =>
      have h1 := step_nil_idx hda hab
      have h2 := runs_idx_mono hrest
      omega
  · cases h using ReflTransGen.head_induction_on with
    | refl => rfl
    | head hab hrest =>
      have h1 := step_nil_idx hdb hab
      have h2 := runs_idx_mono hrest
      omega

/-- One iteration of the outer loop from a root configuration. -/
theorem root_step {succ : Fin n → List (Fin n)} (hA : Acyclic succ) {c : Cfg n} (hroot : Root succ c)
    (hi : c.idx < n) : ∃ c2, Runs succ c c2 ∧ Root succ c2 ∧ c2.idx = c.idx + 1 := by
  by_cases hm : c.marks ⟨c.idx, hi⟩ = none
  · set c1 : Cfg n := { c with depth := [⟨c.idx, hi⟩], idx := c.idx + 1 } with hc1
    have hs1 : step succ c = some c1 := step_root succ c hroot.depth hi hm
    obtain ⟨c2, hr2, hd2, hg2, hx2, hp2, ha2⟩ := visit_all hA ⟨c.idx, hi⟩ c1 [] rfl
      ⟨hroot.good.perm, hroot.good.nodup, hroot.good.closed⟩ hroot.acyc
      (fun t ht => absurd ht (hroot.notemp t))
    refine ⟨c2, ReflTransGen.head hs1 hr2, ⟨hd2, hg2, ha2, ?_, ?_⟩, ?_⟩
    · intro a ha; exact hroot.notemp a ((hx2.temp a).1 ha)
    · intro a ha
      have hidx2 : c2.idx = c.idx + 1 := hx2.idx
      rw [hidx2] at ha
      by_cases hak : a.val < c.idx
      · exact (hg2.perm a).2 (hx2.prefix_.subset ((hroot.good.perm a).1 (hroot.done a hak)))
      · have : a = ⟨c.idx, hi⟩ := Fin.ext (by simp; omega)
        subst this; exact hp2
    · rw [hx2.idx]
  · have hs1 := step_root_marked succ c hroot.depth hi hm
    have hperm : c.marks ⟨c.idx, hi⟩ = some Mark.perm := by
      cases h : c.marks ⟨c.idx, hi⟩ with
      | none => exact absurd h hm
      | some mk => cases mk with
        | temp => exact absurd h (hroot.notemp _)
        | perm => rfl
    refine ⟨{ c with idx := c.idx + 1 }, ReflTransGen.head hs1 ReflTransGen.refl, ⟨hroot.depth,
      ⟨hroot.good.perm, hroot.good.nodup, hroot.good.closed⟩, hroot.acyc, hroot.notemp, ?_⟩, rfl⟩
    intro a ha
    show c.marks a = some Mark.perm
    by_cases hak : a.val < c.idx
    · exact hroot.done a hak
    · have : a = ⟨c.idx, hi⟩ := Fin.ext (by simp at ha ⊢; omega)
      subst this; exact hperm

end Sigref.Topo
