import Sigref.Proofs.TarjanInit_Proofs

/-!
# Proofs: scanning the transitions of the top state preserves the invariant

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

namespace Sigref.Tarjan

open Relation

variable {n : ℕ}

/-- The edges examined by the scan are those at the positions `off ≤ i < off'`. -/
theorem scanRes_idx {g : Graph n} {s : Fin n} {off off' : ℕ} {c c2 : Ctx n} {ch : Option (Fin n)}
    (hres : ScanRes g s ((g.adj s).drop off) off c ch off' c2) (hoff : off ≤ (g.adj s).length) :
    off' ≤ (g.adj s).length ∧ (ch = none → off' = (g.adj s).length) ∧
    (∀ i w, off ≤ i → i < off' → (g.adj s)[i]? = some (true, w) →
      c2.disc w ≠ g.unv ∧ (c2.onSt w = true → c2.low s ≤ c2.disc w)) ∧
    (∀ v, ch = some v → (true, v) ∈ g.adj s) ∧
    (c2.low s = c.low s ∨ ∃ w, (true, w) ∈ g.adj s ∧ c.onSt w = true ∧ c.disc w ≠ g.unv ∧
      c2.low s = c.disc w) := by
  obtain ⟨tc, tr, h1, h2, h3, h4, h5, h6⟩ := hres.consumed
  have hlen : (tc ++ tr).length = (g.adj s).length - off := by
    rw [← h1]; simp
  have hlen' : tc.length ≤ (g.adj s).length - off := by
    rw [← hlen]; simp
  refine ⟨by omega, fun hn => ?_, ?_, ?_, ?_⟩
  · have := h3 hn
    subst this
    simp at hlen
    omega
  · intro i w hi1 hi2 hget
    have hm : i - off < tc.length := by omega
    have hmem : (true, w) ∈ tc := by
      have h7 : ((g.adj s).drop off)[i - off]? = some (true, w) := by
        rw [List.getElem?_drop]; have : off + (i - off) = i := by omega
        rw [this]; exact hget
      rw [h1, List.getElem?_append_left hm] at h7
      exact List.mem_of_getElem? h7
    exact h5 w hmem
  · intro v hv
    obtain ⟨pre, hpre⟩ := h4 v hv
    have : (true, v) ∈ tc := by rw [hpre]; simp
    have : (true, v) ∈ (g.adj s).drop off := by rw [h1]; exact List.mem_append_left _ this
    exact List.mem_of_mem_drop this
  · rcases h6 with h6 | ⟨w, hw, hw2⟩
    · exact Or.inl h6
    · refine Or.inr ⟨w, ?_, hw2⟩
      have : (true, w) ∈ (g.adj s).drop off := by rw [h1]; exact List.mem_append_left _ hw
      exact List.mem_of_mem_drop this

theorem inv_scan {g : Graph n} {c : Ctx n} (h : Inv g c) {s : Fin n} {off : ℕ}
    {W : List (Fin n × ℕ)} (hw : c.work = (s, off) :: W) (hsI : Init g c s)
    {ch : Option (Fin n)} {off' : ℕ} {c2 : Ctx n}
    (hres : ScanRes g s ((g.adj s).drop off) off c ch off' c2) :
    Inv g { c2 with work := (ch.toList.map fun v => (v, 0)) ++ (s, off') :: W } := by
  have hmem : (s, off) ∈ c.work := by rw [hw]; simp
  have hoff : off ≤ (g.adj s).length := h.work_off s off hmem
  obtain ⟨hle', hnone, hidx, hedge, hlow⟩ := scanRes_idx hres hoff
  have hInitW : ∀ p off', (p, off') ∈ W → Init g c p := by
    intro p off' hp
    rcases h.work_fresh p off' (by rw [hw]; exact List.mem_cons_of_mem _ hp) with hh | hh
    · exact hh
    · rw [hw] at hh
      simp at hh
      obtain ⟨⟨e1, _⟩, _⟩ := hh
      rw [← e1] at hp
      exact absurd hp (h.head_unique hw off')
  have hWne : ∀ p off', (p, off') ∈ W → p ≠ s := fun p off' hp e =>
    h.head_unique hw off' (e ▸ hp)
  have hunv : ∀ v, ch = some v → c.disc v = g.unv := fun v hv => (hres.child v hv).1
  have hdisc2 : ∀ v, Init g c v → c2.disc v = c.disc v := by
    intro v hv
    apply hres.disc_ne
    intro hc
    have := hunv v hc
    exact h.disc_ne_unv hv this
  have hlowI : ∀ v, Init g c2 v ↔ Init g c v := by
    intro v
    by_cases hvs : v = s
    · subst hvs
      constructor
      · intro _; exact hsI
      · intro _ hh
        have h1 := hres.low_le
        have h2 := h.low_le v hsI
        have h3 := h.disc_lt v hsI
        have h4 := h.time_le
        have h5 := g.unv_gt
        unfold Init at hsI
        omega
    · simp only [Init, hres.low_ne v hvs]
  set pre : List (Fin n × ℕ) := ch.toList.map (fun v => (v, 0)) with hpre
  set c4 : Ctx n := { c2 with work := pre ++ (s, off') :: W } with hc4
  have hchI : ∀ e ∈ pre, ¬ Init g c e.1 ∧ c.disc e.1 = g.unv ∧ c2.disc e.1 = 0 ∧
      (true, e.1) ∈ g.adj s ∧ e.2 = 0 := by
    intro e he
    rw [hpre] at he
    simp only [Option.toList, List.mem_map] at he
    obtain ⟨v, hv, rfl⟩ := he
    have hcv : ch = some v := by
      cases ch with
      | none => simp at hv
      | some w => simp at hv; rw [hv]
    refine ⟨fun hh => h.disc_ne_unv hh (hunv v hcv), hunv v hcv, (hres.child v hcv).2, hedge v hcv, rfl⟩
  have hlen_pre : pre.length ≤ 1 := by
    rw [hpre]; cases ch <;> simp
  have hpre_nodes : ∀ p, p ∈ pre.map Prod.fst → ¬ Init g c p ∧ c.disc p = g.unv := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact ⟨(hchI e he).1, (hchI e he).2.1⟩
  have hwork4 : c4.work = pre ++ (s, off') :: W := rfl
  have hstk4 : c4.stk = c.stk := hres.stk
  have honSt4 : c4.onSt = c.onSt := hres.onSt
  have htime4 : c4.time = c.time := hres.time
  have hblk4 : c4.blk = c.blk := hres.blk
  have heq4 : c4.eq = c.eq := hres.eq
  have hri4 : c4.ri = c.ri := hres.ri
  have hInit4 : ∀ v, Init g c4 v ↔ Init g c v := hlowI
  have hdisc4 : ∀ v, Init g c v → c4.disc v = c.disc v := hdisc2
  have hlow4 : ∀ v, v ≠ s → c4.low v = c.low v := hres.low_ne
  have hlow4s : c4.low s ≤ c.low s := hres.low_le
  have hDone4 : ∀ v, Done g c4 v ↔ Done g c v := by
    intro v; unfold Done; rw [hInit4 v, hstk4]
  have hs_notpre : s ∉ pre.map Prod.fst := fun hh => (hpre_nodes s hh).1 hsI
  -- the examined edges of `s` in the new work stack
  have hExamS : ∀ w, Examined g c4.work s w →
      (∃ i, i < off ∧ (g.adj s)[i]? = some (true, w)) ∨
      (∃ i, off ≤ i ∧ i < off' ∧ (g.adj s)[i]? = some (true, w)) := by
    intro w ⟨_, hh⟩
    obtain ⟨i, hi, hget⟩ := hh off' (by rw [hwork4]; simp)
    by_cases hio : i < off
    · exact Or.inl ⟨i, hio, hget⟩
    · exact Or.inr ⟨i, by omega, hi, hget⟩
  have hExamOld : ∀ x w, x ≠ s → Examined g c4.work x w → Examined g c.work x w := by
    intro x w hxs ⟨hed, hh⟩
    refine ⟨hed, fun off2 ho => hh off2 ?_⟩
    rw [hw] at ho
    rw [hwork4]
    rcases List.mem_cons.mp ho with e | e
    · exact absurd (congrArg Prod.fst e) hxs
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ e)
  have hExamS_old : ∀ w i, i < off → (g.adj s)[i]? = some (true, w) → Examined g c.work s w := by
    intro w i hi hget
    refine ⟨?_, fun off2 ho => ?_⟩
    · exact List.mem_of_getElem? hget
    · rw [hw] at ho
      rcases List.mem_cons.mp ho with e | e
      · have := (Prod.mk.inj e).2
        subst this
        exact ⟨i, hi, hget⟩
      · exact absurd e (h.head_unique hw off2)
  refine
    { time_card := ?_
      disc_lt := ?_
      low_le := ?_
      disc_inj := ?_
      unv_disc := ?_
      onSt_iff := ?_
      stk_nodup := ?_
      stk_init := ?_
      stk_sorted := ?_
      work_nodup := ?_
      work_off := ?_
      work_fresh := ?_
      work_disc := ?_
      work_reach := ?_
      work_stk := ?_
      exam_vis := ?_
      K := ?_
      G := ?_
      E1 := ?_
      E2 := ?_
      E3 := ?_
      E4 := ?_
      F := ?_
      L := ?_
      SE := ?_
      R := ?_
      ri_le := ?_ }
  · -- time_card
    have hset : Finset.univ.filter (fun v => c4.low v ≠ g.unv) =
        Finset.univ.filter (fun v => c.low v ≠ g.unv) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hInit4 v
    rw [hset, htime4]; exact h.time_card
  · -- disc_lt
    intro v hv
    have hv' := (hInit4 v).1 hv
    show c4.disc v < c4.time
    rw [hdisc4 v hv', htime4]; exact h.disc_lt v hv'
  · -- low_le
    intro v hv
    have hv' := (hInit4 v).1 hv
    show c4.low v ≤ c4.disc v
    by_cases hvs : v = s
    · subst hvs; rw [hdisc4 v hv']; exact hlow4s.trans (h.low_le v hv')
    · rw [hlow4 v hvs, hdisc4 v hv']; exact h.low_le v hv'
  · -- disc_inj
    intro u v hu hv huv
    have hu' := (hInit4 u).1 hu
    have hv' := (hInit4 v).1 hv
    exact h.disc_inj u v hu' hv' (by rw [← hdisc4 u hu', ← hdisc4 v hv']; exact huv)
  · -- unv_disc
    intro v hv
    have hvI : ¬ Init g c v := fun hh => hv ((hInit4 v).2 hh)
    by_cases hcv : ch = some v
    · right
      refine ⟨(hres.child v hcv).2, (s, off') :: W, ?_⟩
      rw [hwork4, hpre, hcv]; simp
    · left
      have hne : c4.disc v = c.disc v := hres.disc_ne v hcv
      rw [hne]
      rcases h.unv_disc v hvI with hh | ⟨hh, rest, hrest⟩
      · exact hh
      · exfalso
        rw [hw] at hrest
        have hsv : s = v := congrArg Prod.fst (List.cons.inj hrest).1
        exact hvI (by rw [← hsv]; exact hsI)
  · -- onSt_iff
    intro v; rw [honSt4, hstk4]; exact h.onSt_iff v
  · rw [hstk4]; exact h.stk_nodup
  · intro v hv; rw [hstk4] at hv; exact (hInit4 v).2 (h.stk_init v hv)
  · -- stk_sorted
    rw [hstk4]
    refine h.stk_sorted.imp_of_mem ?_
    intro a b ha hb hab
    show c4.disc b < c4.disc a
    rw [hdisc4 a (h.stk_init a ha), hdisc4 b (h.stk_init b hb)]; exact hab
  · -- work_nodup
    rw [hwork4]
    have hnd := h.work_nodup
    rw [hw] at hnd
    simp only [List.map_cons] at hnd
    simp only [List.map_append, List.map_cons]
    have hnd_pre : (pre.map Prod.fst).Nodup := by
      rw [hpre]; cases ch <;> simp
    refine List.nodup_append.2 ⟨hnd_pre, hnd, ?_⟩
    intro a ha b hb hab
    subst hab
    have hn := hpre_nodes a ha
    rcases List.mem_cons.mp hb with e | e
    · exact hn.1 (e ▸ hsI)
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp e
      exact hn.1 (hInitW e'.1 e'.2 he')
  · -- work_off
    intro p off2 hp
    rw [hwork4] at hp
    rcases List.mem_append.mp hp with hp | hp
    · have h0 : off2 = 0 := (hchI _ hp).2.2.2.2
      rw [h0]; exact Nat.zero_le _
    · rcases List.mem_cons.mp hp with e | e
      · obtain ⟨hps, hoff2⟩ := Prod.mk.inj e
        rw [hps, hoff2]; exact hle'
      · exact h.work_off p off2 (by rw [hw]; exact List.mem_cons_of_mem _ e)
  · -- work_fresh
    intro p off2 hp
    rw [hwork4] at hp ⊢
    rcases List.mem_append.mp hp with hp | hp
    · right
      have hoff0 := (hchI _ hp).2.2.2.2
      refine ⟨?_, hoff0⟩
      rw [hpre] at hp ⊢
      cases ch with
      | none => simp at hp
      | some v =>
        simp only [Option.toList, List.map_cons, List.map_nil, List.mem_singleton] at hp ⊢
        rw [hp]; rfl
    · rcases List.mem_cons.mp hp with e | e
      · have hps : p = s := (Prod.mk.inj e).1
        left; rw [hps]; exact (hInit4 s).2 hsI
      · left; exact (hInit4 p).2 (hInitW p off2 e)
  · -- work_disc
    rw [hwork4]
    have hpw := h.work_disc
    rw [hw] at hpw
    rw [List.pairwise_cons] at hpw
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [hpre]; cases ch <;> simp
    · rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro b hb hIa
        have hbI := hInitW b.1 b.2 hb
        show c4.disc b.1 < c4.disc s
        rw [hdisc4 b.1 hbI, hdisc4 s hsI]
        exact hpw.1 b hb hsI
      · refine hpw.2.imp_of_mem ?_
        intro a b ha hb hab hIa
        have haI := hInitW a.1 a.2 ha
        have hbI := hInitW b.1 b.2 hb
        show c4.disc b.1 < c4.disc a.1
        rw [hdisc4 a.1 haI, hdisc4 b.1 hbI]
        exact hab haI
    · intro a ha b hb hIa
      exact absurd ((hInit4 a.1).1 hIa) (hchI a ha).1
  · -- work_reach
    rw [hwork4]
    have hpw := h.work_reach
    rw [hw] at hpw
    rw [List.pairwise_cons] at hpw
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [hpre]; cases ch <;> simp
    · rw [List.pairwise_cons]
      exact ⟨hpw.1, hpw.2⟩
    · intro a ha b hb
      have hedge' : Reach g s a.1 := ReflTransGen.single (hchI a ha).2.2.2.1
      rcases List.mem_cons.mp hb with e | e
      · rw [e]; exact hedge'
      · exact (hpw.1 b e).trans hedge'
  · -- work_stk
    intro p off2 hp hpI
    rw [hwork4] at hp
    rw [hstk4]
    rcases List.mem_append.mp hp with hp | hp
    · exact absurd ((hInit4 p).1 hpI) (hchI _ hp).1
    · rcases List.mem_cons.mp hp with e | e
      · have hps : p = s := (Prod.mk.inj e).1
        rw [hps]; exact h.work_stk s off hmem hsI
      · exact h.work_stk p off2 (by rw [hw]; exact List.mem_cons_of_mem _ e) ((hInit4 p).1 hpI)
  · -- exam_vis
    intro x w hx hex
    have hx' := (hInit4 x).1 hx
    have hnotunv : ∀ w, c.disc w ≠ g.unv → c4.disc w ≠ g.unv := by
      intro w hw
      by_cases hcw : ch = some w
      · rw [(hres.child w hcw).2]
        have := g.unv_gt
        omega
      · rw [hres.disc_ne w hcw]; exact hw
    by_cases hxs : x = s
    · subst hxs
      rcases hExamS w hex with ⟨i, hi, hget⟩ | ⟨i, hi1, hi2, hget⟩
      · exact hnotunv w (h.exam_vis x w hsI (hExamS_old w i hi hget))
      · exact (hidx i w hi1 hi2 hget).1
    · exact hnotunv w (h.exam_vis x w hx' (hExamOld x w hxs hex))
  · -- K
    intro W1 p off2 W2 hwk hpI x hx hdx w hw' hex
    have hpI' := (hInit4 p).1 hpI
    rw [hstk4] at hx hw'
    have hxI := h.stk_init x hx
    have hwI := h.stk_init w hw'
    rw [hdisc4 p hpI', hdisc4 x hxI] at hdx
    have hlowmap : ∀ q, c.low q ≤ c.disc w → c4.low q ≤ c4.disc w := by
      intro q hq
      rw [hdisc4 w hwI]
      by_cases hqs : q = s
      · rw [hqs] at hq ⊢; exact hlow4s.trans hq
      · rw [hlow4 q hqs]; exact hq
    have hnewS : ∀ i, off ≤ i → i < off' → (g.adj s)[i]? = some (true, w) →
        c4.low s ≤ c4.disc w := by
      intro i hi1 hi2 hget
      exact (hidx i w hi1 hi2 hget).2 (by rw [honSt4]; exact (h.onSt_iff w).2 hw')
    have hdec : (p = s ∧ off2 = off' ∧ W2 = W ∧ W1 = pre) ∨
        (∃ W1', W = W1' ++ (p, off2) :: W2 ∧ W1 = pre ++ (s, off') :: W1') := by
      have hwk' : pre ++ (s, off') :: W = W1 ++ (p, off2) :: W2 := hwk
      rcases List.append_eq_append_iff.mp hwk' with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
      · cases a' with
        | nil =>
          left
          simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at h2
          refine ⟨h2.1.1.symm, h2.1.2.symm, h2.2.symm, by simpa using h1⟩
        | cons e a'' =>
          right
          simp only [List.cons_append, List.cons.injEq] at h2
          refine ⟨a'', h2.2, ?_⟩
          rw [h1, ← h2.1]
      · cases c' with
        | nil =>
          left
          simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at h2
          refine ⟨h2.1.1, h2.1.2, h2.2, by simpa using h1.symm⟩
        | cons e c'' =>
          exfalso
          have hpe : (p, off2) = e := by
            simp only [List.cons_append, List.cons.injEq] at h2; exact h2.1
          have : e ∈ pre := by rw [h1]; simp
          exact (hchI e this).1 (by rw [← hpe]; exact hpI')
    rcases hdec with ⟨hps, hoff2, hW2, hW1⟩ | ⟨W1', hWsplit, hW1⟩
    · -- the top state `s` itself
      subst hW1
      rw [hps] at hdx ⊢
      refine ⟨s, by simp, ?_⟩
      by_cases hxs : x = s
      · subst hxs
        rcases hExamS w hex with ⟨i, hi, hget⟩ | ⟨i, hi1, hi2, hget⟩
        · obtain ⟨q, hq, hql⟩ := h.K [] x off W hw hsI x hx hdx w hw' (hExamS_old w i hi hget)
          have : q = x := by simpa using hq
          rw [this] at hql
          exact hlowmap x hql
        · exact hnewS i hi1 hi2 hget
      · obtain ⟨q, hq, hql⟩ := h.K [] s off W hw hsI x hx hdx w hw' (hExamOld x w hxs hex)
        have : q = s := by simpa using hq
        rw [this] at hql
        exact hlowmap s hql
    · -- deeper in the work stack
      have hcw : c.work = ((s, off) :: W1') ++ (p, off2) :: W2 := by
        rw [hw, hWsplit]; rfl
      have hmapq : ∀ q, q ∈ ((s, off) :: W1').map Prod.fst ++ [p] →
          q ∈ W1.map Prod.fst ++ [p] := by
        intro q hq
        rw [hW1]
        simp only [List.map_cons, List.map_append, List.mem_append, List.mem_cons] at hq ⊢
        tauto
      have hsmem : s ∈ W1.map Prod.fst ++ [p] := by
        rw [hW1]; simp
      by_cases hxs : x = s
      · subst hxs
        rcases hExamS w hex with ⟨i, hi, hget⟩ | ⟨i, hi1, hi2, hget⟩
        · obtain ⟨q, hq, hql⟩ := h.K _ p off2 W2 hcw hpI' x hx hdx w hw' (hExamS_old w i hi hget)
          exact ⟨q, hmapq q hq, hlowmap q hql⟩
        · exact ⟨x, hsmem, hnewS i hi1 hi2 hget⟩
      · obtain ⟨q, hq, hql⟩ := h.K _ p off2 W2 hcw hpI' x hx hdx w hw' (hExamOld x w hxs hex)
        exact ⟨q, hmapq q hq, hlowmap q hql⟩
  · -- G
    intro p off2 hp hpI x hx hdx
    rw [hwork4] at hp
    rw [hstk4] at hx
    have hpI' := (hInit4 p).1 hpI
    have hxI := h.stk_init x hx
    rw [hdisc4 p hpI', hdisc4 x hxI] at hdx
    rcases List.mem_append.mp hp with hp | hp
    · exact absurd hpI' (hchI _ hp).1
    · rcases List.mem_cons.mp hp with e | e
      · have hps : p = s := (Prod.mk.inj e).1
        rw [hps] at hdx ⊢
        exact h.G s off hmem hsI x hx hdx
      · exact h.G p off2 (by rw [hw]; exact List.mem_cons_of_mem _ e) hpI' x hx hdx
  · -- E1
    intro v hv
    rw [hblk4, heq4]; exact h.E1 v ((hDone4 v).1 hv)
  · intro v w hv he
    exact (hDone4 w).2 (h.E2 v w ((hDone4 v).1 hv) he)
  · -- E3
    intro v w hv hw'
    rw [hblk4]; exact h.E3 v w ((hDone4 v).1 hv) ((hDone4 w).1 hw')
  · -- E4
    intro b hb
    rw [heq4] at hb
    obtain ⟨v, hv, hbv⟩ := h.E4 b hb
    exact ⟨v, (hDone4 v).2 hv, by rw [hblk4]; exact hbv⟩
  · -- F
    intro v hv
    rw [hstk4] at hv
    obtain ⟨w, hw', hdw, hr⟩ := h.F v hv
    have hwI := h.stk_init w hw'
    by_cases hvs : v = s
    · subst hvs
      rcases hlow with hl | ⟨w2, hw2e, hw2on, hw2d, hw2l⟩
      · exact ⟨w, by rw [hstk4]; exact hw', by rw [hdisc4 w hwI]; show _ = c2.low v; rw [hl]; exact hdw, hr⟩
      · have hw2s : w2 ∈ c.stk := (h.onSt_iff w2).1 hw2on
        refine ⟨w2, by rw [hstk4]; exact hw2s, ?_, ReflTransGen.single hw2e⟩
        rw [hdisc4 w2 (h.stk_init w2 hw2s)]; exact hw2l.symm
    · exact ⟨w, by rw [hstk4]; exact hw', by rw [hdisc4 w hwI, hlow4 v hvs]; exact hdw, hr⟩
  · -- L
    intro v hv hvn
    rw [hstk4] at hv
    have hvs : v ≠ s := fun e => hvn (by rw [hwork4, e]; simp)
    have hvn' : v ∉ c.work.map Prod.fst := by
      intro hh
      apply hvn
      rw [hwork4]
      rw [hw] at hh
      simp only [List.map_cons, List.mem_cons] at hh
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      rcases hh with hh | hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr hh)
    show c4.low v < c4.disc v
    rw [hlow4 v hvs, hdisc4 v (h.stk_init v hv)]
    exact h.L v hv hvn'
  · -- SE
    intro x hx
    rw [hstk4] at hx
    obtain ⟨p, off2, hp, hpI, hdp⟩ := h.SE x hx
    have hxI := h.stk_init x hx
    rw [hw] at hp
    have hdp' : c4.disc p ≤ c4.disc x := by rw [hdisc4 p hpI, hdisc4 x hxI]; exact hdp
    rcases List.mem_cons.mp hp with e | e
    · have hps : p = s := (Prod.mk.inj e).1
      refine ⟨s, off', by rw [hwork4]; simp, (hInit4 s).2 hsI, ?_⟩
      rw [← hps]; exact hdp'
    · exact ⟨p, off2, by rw [hwork4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ e),
        (hInit4 p).2 hpI, hdp'⟩
  · -- R
    intro v hv
    have hv' : v.val < c.ri := by rw [← hri4]; exact hv
    rcases h.R v hv' with hh | hh
    · exact Or.inl ((hInit4 v).2 hh)
    · rw [hw] at hh
      rcases List.mem_cons.mp hh with e | e
      · have hvs : v = s := (Prod.mk.inj e).1
        left; rw [hvs]; exact (hInit4 s).2 hsI
      · right; rw [hwork4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ e)
  · show c4.ri ≤ n
    rw [hri4]; exact h.ri_le

end Sigref.Tarjan
