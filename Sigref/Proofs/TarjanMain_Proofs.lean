import Sigref.Proofs.TarjanFinish_Proofs

/-!
# Proofs: the Tarjan model is correct

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/Tarjan_Pins.lean` (human-vetted).
-/

namespace Sigref.Tarjan

open Relation

variable {n : ℕ}

theorem initNode_work (g : Graph n) (s : Fin n) (c : Ctx n) : (initNode g s c).work = c.work := by
  unfold initNode; split_ifs <;> rfl

theorem initNode_comm (g : Graph n) (s : Fin n) (c : Ctx n) (W : List (Fin n × ℕ)) :
    initNode g s { c with work := W } = { initNode g s c with work := W } := by
  unfold initNode; split_ifs <;> rfl

theorem scan_comm (g : Graph n) (s : Fin n) :
    ∀ (ts : List (Bool × Fin n)) (idx : ℕ) (c : Ctx n) (W : List (Fin n × ℕ)),
      scan g s ts idx { c with work := W } =
        ((scan g s ts idx c).1, (scan g s ts idx c).2.1, { (scan g s ts idx c).2.2 with work := W }) := by
  intro ts
  induction ts with
  | nil => intro idx c W; simp [scan]
  | cons e ts ih =>
    obtain ⟨h, v⟩ := e
    intro idx c W
    cases h with
    | false => simp only [scan, Bool.false_eq_true, if_false]; exact ih _ _ _
    | true =>
      by_cases hd : c.disc v = g.unv
      · simp [scan, hd]
      · by_cases hc : (c.onSt v && decide (c.disc v < c.low s)) = true
        · simp only [scan, if_true, hd, if_false, hc]
          exact ih _ { c with low := Function.update c.low s (c.disc v) } W
        · simp only [scan, if_true, hd, if_false, hc, Bool.false_eq_true]
          exact ih _ c W

/-- The number of unvisited states. -/
def cnt (g : Graph n) (c : Ctx n) : ℕ := (Finset.univ.filter (fun v => c.disc v = g.unv)).card

theorem initNode_ri (g : Graph n) (s : Fin n) (c : Ctx n) : (initNode g s c).ri = c.ri := by
  unfold initNode; split_ifs <;> rfl

theorem cnt_initNode_le {g : Graph n} {c : Ctx n} (h : Inv g c) (s : Fin n) :
    cnt g (initNode g s c) ≤ cnt g c := by
  unfold cnt
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  unfold initNode at hu
  split_ifs at hu with hl
  · by_cases hus : u = s
    · subst hus
      simp at hu
      exact absurd hu h.time_ne_unv
    · simpa [Function.update_of_ne hus] using hu
  · exact hu

theorem finish_fields {s : Fin n} {c c3 : Ctx n} (h : finish s c = some c3) :
    c3.work = c.work ∧ c3.disc = c.disc ∧ c3.ri = c.ri := by
  unfold finish at h
  by_cases hd : c.disc s = c.low s
  · rw [if_pos hd] at h
    cases hpc : popComp s c.eq c.stk c.onSt c.blk with
    | none => simp [hpc] at h
    | some r =>
      simp only [hpc, Option.map_some, Option.some.injEq] at h
      subst h
      rcases hW : c.work with _ | ⟨⟨p, o⟩, W'⟩
      · simp
      · simp only
        split_ifs <;> simp
  · rw [if_neg hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rcases hW : c.work with _ | ⟨⟨p, o⟩, W'⟩
    · simp [hW] at h; subst h; simp [hW]
    · simp only [hW] at h
      split_ifs at h <;> (subst h; simp [hW])

/-- A step with a non-empty work stack succeeds and preserves the invariant. -/
theorem step_cons {g : Graph n} {c : Ctx n} (h : Inv g c) {s : Fin n} {off : ℕ}
    {W : List (Fin n × ℕ)} (hw : c.work = (s, off) :: W) :
    ∃ c', step g c = Out.next c' ∧ Inv g c' ∧ measure g c' < measure g c := by
  have h0 := inv_initNode h hw
  have hw0 : (initNode g s c).work = (s, off) :: W := by rw [initNode_work]; exact hw
  have hsI0 : Init g (initNode g s c) s := by
    unfold initNode Init
    split_ifs with hl
    · show Function.update c.low s c.time s ≠ g.unv
      simp [h.time_ne_unv]
    · exact hl
  have hon : ∀ v, (initNode g s c).disc v = g.unv → (initNode g s c).onSt v = false := by
    intro v hv
    by_contra hcon
    have hcon' : (initNode g s c).onSt v = true := by simpa using hcon
    have := h0.disc_ne_unv (h0.stk_init v ((h0.onSt_iff v).1 hcon'))
    exact this hv
  rcases hscan : scan g s ((g.adj s).drop off) off (initNode g s c) with ⟨ch, off', c2⟩
  have hres : ScanRes g s ((g.adj s).drop off) off (initNode g s c) ch off' c2 := by
    have := scan_spec g s ((g.adj s).drop off) off (initNode g s c) hon
    rw [hscan] at this; exact this
  have hinv := inv_scan h0 hw0 hsI0 hres
  have hstep : step g c = (match ch with
      | some v => Out.next { c2 with work := (v, 0) :: (s, off') :: W }
      | none => (match finish s { c2 with work := W } with
          | none => Out.fail
          | some c3 => Out.next c3)) := by
    unfold step
    rw [hw]
    simp only [initNode_comm, scan_comm, hscan]
    cases ch <;> rfl
  have hri2 : c2.ri = c.ri := by rw [hres.ri, initNode_ri]
  have hcnt0 := cnt_initNode_le h s
  cases ch with
  | some v =>
    refine ⟨_, hstep, by simpa using hinv, ?_⟩
    have hsub : Finset.univ.filter (fun u => c2.disc u = g.unv) ⊂
        Finset.univ.filter (fun u => (initNode g s c).disc u = g.unv) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨v, ?_, ?_⟩
        · simp [(hres.child v rfl).1]
        · simp [(hres.child v rfl).2]
          have := g.unv_gt
          omega
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        by_cases huv : some v = some u
        · exact absurd (by rw [(hres.child u huv).2] at hu; exact hu.symm) (by have := g.unv_gt; omega)
        · rw [← hres.disc_ne u huv]; exact hu
    have hlt : cnt g c2 < cnt g (initNode g s c) := Finset.card_lt_card hsub
    unfold measure
    simp only [List.length_cons, hri2]
    unfold cnt at hlt hcnt0
    rw [hw]
    simp only [List.length_cons]
    omega
  | none =>
    have hoff0 : off ≤ (g.adj s).length := h.work_off s off (by rw [hw]; simp)
    obtain ⟨_, hnone, _⟩ := scanRes_idx hres hoff0
    have hoff' : off' = (g.adj s).length := hnone rfl
    have hV : Inv g { c2 with work := (s, off') :: W } := by simpa using hinv
    obtain ⟨c3, hfin, hc3⟩ := inv_finish hV (s := s) (off' := off') (W := W) rfl
      (by
        have h1 := hres.low_le
        have h2 := h0.low_le s hsI0
        have h3 := h0.disc_lt s hsI0
        have h4 := h0.time_le
        have h5 := g.unv_gt
        show c2.low s ≠ g.unv
        omega) hoff'
    obtain ⟨hw3, hd3, hr3⟩ := finish_fields hfin
    refine ⟨c3, ?_, hc3, ?_⟩
    · rw [hstep]
      simp only
      rw [hfin]
    · have hsub : Finset.univ.filter (fun u => c2.disc u = g.unv) ⊆
          Finset.univ.filter (fun u => (initNode g s c).disc u = g.unv) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        rw [← hres.disc_ne u (by simp)]; exact hu
      have hle : cnt g c2 ≤ cnt g (initNode g s c) := Finset.card_le_card hsub
      unfold measure
      have hd3' : c3.disc = c2.disc := hd3
      have hr3' : c3.ri = c2.ri := hr3
      simp only [hw3, hd3', hr3', hri2]
      unfold cnt at hle hcnt0
      rw [hw]
      simp only [List.length_cons]
      omega

/-- The invariant holds after a step of the root loop. -/
theorem step_nil {g : Graph n} {c : Ctx n} (h : Inv g c) (hw : c.work = []) :
    (step g c = Out.stop ∧ ¬ c.ri < n) ∨
      ∃ c', step g c = Out.next c' ∧ Inv g c' ∧ measure g c' < measure g c := by
  by_cases hri : c.ri < n
  · right
    have hstk : c.stk = [] := by
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨p, off, hp, _⟩ := h.SE x hx
      rw [hw] at hp; simp at hp
    by_cases hlow : c.low ⟨c.ri, hri⟩ = g.unv
    · refine ⟨{ c with work := [(⟨c.ri, hri⟩, 0)], ri := c.ri + 1 }, ?_, ?_, ?_⟩
      · simp [step, hw, hri, hlow]
      · have hrI : ¬ Init g c ⟨c.ri, hri⟩ := fun hh => hh hlow
        refine { h with
          unv_disc := ?_
          work_nodup := ?_
          work_off := ?_
          work_fresh := ?_
          work_disc := ?_
          work_reach := ?_
          work_stk := ?_
          exam_vis := ?_
          K := ?_
          G := ?_
          L := ?_
          SE := ?_
          R := ?_
          ri_le := ?_ }
        · intro v hv
          rcases h.unv_disc v hv with hh | ⟨_, rest, hrest⟩
          · exact Or.inl hh
          · rw [hw] at hrest; simp at hrest
        · simp
        · intro p off2 hp
          simp at hp
          rw [hp.2]; exact Nat.zero_le _
        · intro p off2 hp
          right
          simp at hp
          obtain ⟨rfl, rfl⟩ := hp
          simp
        · simp
        · simp
        · intro p off2 hp hI
          simp at hp
          exact absurd hI (by rw [hp.1]; exact hrI)
        · intro x w hx hex
          by_cases hxr : x = ⟨c.ri, hri⟩
          · exact absurd hx (by rw [hxr]; exact hrI)
          · exact h.exam_vis x w hx ⟨hex.1, fun off2 ho => by rw [hw] at ho; simp at ho⟩
        · intro W1 p off2 W2 hwk hpI
          have : (p, off2) ∈ [(⟨c.ri, hri⟩, 0)] := by
            have hwk' : [((⟨c.ri, hri⟩ : Fin n), 0)] = W1 ++ (p, off2) :: W2 := hwk
            rw [hwk']; simp
          simp at this
          exact absurd hpI (by rw [this.1]; exact hrI)
        · intro p off2 hp hpI
          simp at hp
          exact absurd hpI (by rw [hp.1]; exact hrI)
        · intro v hv hvn
          exact h.L v hv (by rw [hw]; simp)
        · intro x hx
          rw [hstk] at hx; simp at hx
        · intro v hv
          have hv' : v.val < c.ri + 1 := hv
          by_cases hvr : v.val < c.ri
          · rcases h.R v hvr with hh | hh
            · exact Or.inl hh
            · rw [hw] at hh; simp at hh
          · right
            have : v = ⟨c.ri, hri⟩ := Fin.ext (by show v.val = c.ri; omega)
            rw [this]; simp
        · show c.ri + 1 ≤ n
          omega
      · unfold measure
        simp only [hw, List.length_nil, List.length_cons]
        omega
    · refine ⟨{ c with ri := c.ri + 1 }, ?_, ?_, ?_⟩
      · simp [step, hw, hri, hlow]
      · refine { h with R := ?_, ri_le := ?_ }
        · intro v hv
          have hv' : v.val < c.ri + 1 := hv
          by_cases hvr : v.val < c.ri
          · exact h.R v hvr
          · left
            have : v = ⟨c.ri, hri⟩ := Fin.ext (by show v.val = c.ri; omega)
            rw [this]; exact hlow
        · show c.ri + 1 ≤ n
          omega
      · unfold measure
        simp only [hw, List.length_nil]
        omega
  · left
    exact ⟨by simp [step, hw, hri], hri⟩

/-- One step either stops (empty work stack, all roots tried), or moves to a configuration with the
invariant and a smaller measure; it never fails. -/
theorem step_cases {g : Graph n} {c : Ctx n} (h : Inv g c) :
    (step g c = Out.stop ∧ c.work = [] ∧ ¬ c.ri < n) ∨
      ∃ c', step g c = Out.next c' ∧ Inv g c' ∧ measure g c' < measure g c := by
  rcases hw : c.work with _ | ⟨⟨s, off⟩, W⟩
  · rcases step_nil h hw with ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨h1, rfl, h2⟩
    · exact Or.inr h1
  · obtain ⟨c', h1, h2, h3⟩ := step_cons h hw
    exact Or.inr ⟨c', h1, h2, h3⟩

theorem inv_run (g : Graph n) : ∀ c, ReflTransGen (Step g) (init g) c → Inv g c := by
  intro c hc
  induction hc with
  | refl => exact inv_init g
  | tail _ hstep ih =>
    rcases step_cases ih with ⟨h1, _⟩ | ⟨c', h1, h2, _⟩
    · unfold Step at hstep; rw [h1] at hstep; cases hstep
    · unfold Step at hstep
      rw [h1] at hstep
      cases hstep
      exact h2

theorem partition_of_end {g : Graph n} {c : Ctx n} (h : Inv g c) (hw : c.work = [])
    (hri : ¬ c.ri < n) : IsSccPartition g c.blk c.eq := by
  have hstk : c.stk = [] := by
    by_contra hne
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨p, off, hp, _⟩ := h.SE x hx
    rw [hw] at hp; simp at hp
  have hdone : ∀ v, Done g c v := by
    intro v
    have hv : v.val < c.ri := by have := h.ri_le; have := v.2; omega
    refine ⟨?_, by rw [hstk]; simp⟩
    rcases h.R v hv with hh | hh
    · exact hh
    · rw [hw] at hh; simp at hh
  refine ⟨fun v => h.E1 v (hdone v), fun b hb => ?_, fun u v => h.E3 u v (hdone u) (hdone v)⟩
  obtain ⟨v, _, hbv⟩ := h.E4 b hb
  exact ⟨v, hbv⟩

/-- **Correctness of the SCC decomposition.** -/
theorem tarjanCorrect {n : ℕ} (g : Graph n) : TarjanCorrect g := by
  intro c hc
  have h := inv_run g c hc
  rcases step_cases h with ⟨h1, h2, h3⟩ | ⟨c', h1, _⟩
  · exact ⟨fun _ => partition_of_end h h2 h3, (fun e => nomatch h1.symm.trans e)⟩
  · exact ⟨(fun e => nomatch h1.symm.trans e), (fun e => nomatch h1.symm.trans e)⟩

/-- **Termination of the SCC decomposition.** -/
theorem tarjanTerminates {n : ℕ} (g : Graph n) : TarjanTerminates g := by
  intro c hc c' hstep
  have h := inv_run g c hc
  rcases step_cases h with ⟨h1, _⟩ | ⟨c'', h1, _, h3⟩
  · unfold Step at hstep; rw [h1] at hstep; cases hstep
  · unfold Step at hstep
    rw [h1] at hstep
    cases hstep
    exact h3

end Sigref.Tarjan
