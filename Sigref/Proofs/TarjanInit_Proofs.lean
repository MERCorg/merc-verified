import Sigref.Proofs.TarjanInv_Proofs

/-!
# Proofs: initialising the state at the top of the work stack preserves the invariant

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

namespace Sigref.Tarjan

open Relation

variable {n : ℕ}

theorem inv_initNode {g : Graph n} {c : Ctx n} (h : Inv g c) {s : Fin n} {off : ℕ}
    {W : List (Fin n × ℕ)} (hw : c.work = (s, off) :: W) : Inv g (initNode g s c) := by
  by_cases hs : c.low s = g.unv
  · -- the state is fresh
    have hsI : ¬ Init g c s := fun hh => hh hs
    have hmem : (s, off) ∈ c.work := by rw [hw]; simp
    have hfresh : off = 0 := by
      rcases h.work_fresh s off hmem with hh | hh
      · exact absurd hh hsI
      · exact hh.2
    have hsnot : s ∉ c.stk := fun hh => hsI (h.stk_init s hh)
    set c1 : Ctx n := initNode g s c with hc1
    have hc1' : c1 = { c with
      disc := Function.update c.disc s c.time
      low := Function.update c.low s c.time
      time := c.time + 1
      stk := s :: c.stk
      onSt := Function.update c.onSt s true } := by
      simp [hc1, initNode, hs]
    have hlowtime : c.time ≠ g.unv := h.time_ne_unv
    have hI1 : ∀ v, Init g c1 v ↔ (Init g c v ∨ v = s) := by
      intro v
      by_cases hv : v = s
      · subst hv; simp [Init, hc1', hlowtime]
      · simp [Init, hc1', hv]
    have hwork1 : c1.work = c.work := by rw [hc1']
    have hdisc_ne : ∀ v, v ≠ s → c1.disc v = c.disc v := fun v hv => by
      rw [hc1']; simp [Function.update_of_ne hv]
    have hlow_ne : ∀ v, v ≠ s → c1.low v = c.low v := fun v hv => by
      rw [hc1']; simp [Function.update_of_ne hv]
    have hdisc_s : c1.disc s = c.time := by rw [hc1']; simp
    have hlow_s : c1.low s = c.time := by rw [hc1']; simp
    have hstk1 : c1.stk = s :: c.stk := by rw [hc1']
    have htime1 : c1.time = c.time + 1 := by rw [hc1']
    have hblk1 : c1.blk = c.blk := by rw [hc1']
    have heq1 : c1.eq = c.eq := by rw [hc1']
    -- an examined edge of `s` does not exist
    have hnoexam : ∀ w, ¬ Examined g c.work s w := by
      intro w ⟨_, hh⟩
      obtain ⟨i, hi, _⟩ := hh off hmem
      omega
    have hWnode : ∀ p off', (p, off') ∈ c.work → p ≠ s → (p, off') ∈ W := by
      intro p off' hp hps
      rw [hw] at hp
      rcases List.mem_cons.mp hp with hh | hh
      · exact absurd (congrArg Prod.fst hh) hps
      · exact hh
    have hInitW : ∀ p off', (p, off') ∈ W → Init g c p := by
      intro p off' hp
      rcases h.work_fresh p off' (by rw [hw]; exact List.mem_cons_of_mem _ hp) with hh | hh
      · exact hh
      · rw [hw] at hh
        simp at hh
        obtain ⟨⟨e1, _⟩, _⟩ := hh
        rw [← e1] at hp
        exact absurd hp (h.head_unique hw off')
    have hD1 : ∀ v, Done g c1 v ↔ Done g c v := by
      intro v
      constructor
      · rintro ⟨hv, hvn⟩
        have hvs : v ≠ s := fun e => hvn (by rw [hstk1, e]; exact List.mem_cons_self ..)
        exact ⟨((hI1 v).1 hv).resolve_right hvs, fun hh => hvn (by rw [hstk1]; exact List.mem_cons_of_mem _ hh)⟩
      · rintro ⟨hv, hvn⟩
        have hvs : v ≠ s := fun e => hsI (e ▸ hv)
        exact ⟨(hI1 v).2 (Or.inl hv), by rw [hstk1]; simp [hvs, hvn]⟩
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
      have hset : Finset.univ.filter (fun v => c1.low v ≠ g.unv) =
          insert s (Finset.univ.filter (fun v => c.low v ≠ g.unv)) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        exact (hI1 v).trans or_comm
      rw [hset, Finset.card_insert_of_notMem (by simpa [Init] using hsI), ← h.time_card, htime1]
    · -- disc_lt
      intro v hv
      by_cases hvs : v = s
      · subst hvs; rw [hdisc_s, htime1]; omega
      · have hvI : Init g c v := ((hI1 v).1 hv).resolve_right hvs
        rw [hdisc_ne v hvs, htime1]
        have := h.disc_lt v hvI
        omega
    · -- low_le
      intro v hv
      by_cases hvs : v = s
      · subst hvs; rw [hlow_s, hdisc_s]
      · have hvI : Init g c v := ((hI1 v).1 hv).resolve_right hvs
        rw [hlow_ne v hvs, hdisc_ne v hvs]; exact h.low_le v hvI
    · -- disc_inj
      intro u v hu hv huv
      by_cases hus : u = s <;> by_cases hvs : v = s
      · rw [hus, hvs]
      · have hvI : Init g c v := ((hI1 v).1 hv).resolve_right hvs
        rw [hus, hdisc_s, hdisc_ne v hvs] at huv
        exact absurd huv.symm (ne_of_lt (h.disc_lt v hvI))
      · have huI : Init g c u := ((hI1 u).1 hu).resolve_right hus
        rw [hvs, hdisc_s, hdisc_ne u hus] at huv
        exact absurd huv (ne_of_lt (h.disc_lt u huI))
      · have huI : Init g c u := ((hI1 u).1 hu).resolve_right hus
        have hvI : Init g c v := ((hI1 v).1 hv).resolve_right hvs
        rw [hdisc_ne u hus, hdisc_ne v hvs] at huv
        exact h.disc_inj u v huI hvI huv
    · -- unv_disc
      intro v hv
      have hvs : v ≠ s := fun e => hv ((hI1 v).2 (Or.inr e))
      have hvI : ¬ Init g c v := fun hh => hv ((hI1 v).2 (Or.inl hh))
      rw [hdisc_ne v hvs, hwork1]
      rcases h.unv_disc v hvI with hh | ⟨hh, rest, hrest⟩
      · exact Or.inl hh
      · rw [hw] at hrest
        have := List.cons.inj hrest
        exact absurd (congrArg Prod.fst this.1).symm hvs
    · -- onSt_iff
      intro v
      rw [hstk1]
      by_cases hv : v = s
      · subst hv; rw [hc1']; simp
      · have : c1.onSt v = c.onSt v := by rw [hc1']; simp [Function.update_of_ne hv]
        rw [this, h.onSt_iff v]
        simp [hv]
    · -- stk_nodup
      rw [hstk1]; exact List.nodup_cons.2 ⟨hsnot, h.stk_nodup⟩
    · -- stk_init
      intro v hv
      rw [hstk1] at hv
      rcases List.mem_cons.mp hv with hvs | hv
      · exact (hI1 v).2 (Or.inr hvs)
      · exact (hI1 v).2 (Or.inl (h.stk_init v hv))
    · -- stk_sorted
      rw [hstk1]
      refine List.pairwise_cons.2 ⟨?_, ?_⟩
      · intro b hb
        have hbs : b ≠ s := fun e => hsnot (e ▸ hb)
        rw [hdisc_ne b hbs, hdisc_s]
        exact h.disc_lt b (h.stk_init b hb)
      · refine h.stk_sorted.imp_of_mem ?_
        intro a b ha hb hab
        have has : a ≠ s := fun e => hsnot (e ▸ ha)
        have hbs : b ≠ s := fun e => hsnot (e ▸ hb)
        rw [hdisc_ne a has, hdisc_ne b hbs]; exact hab
    · -- work_nodup
      rw [hwork1]; exact h.work_nodup
    · -- work_off
      intro p off' hp; rw [hwork1] at hp; exact h.work_off p off' hp
    · -- work_fresh
      intro p off' hp
      rw [hwork1] at hp ⊢
      rcases h.work_fresh p off' hp with hh | hh
      · exact Or.inl ((hI1 p).2 (Or.inl hh))
      · exact Or.inr hh
    · -- work_disc
      rw [hwork1, hw]
      have hpw := h.work_disc
      rw [hw] at hpw
      rw [List.pairwise_cons] at hpw ⊢
      refine ⟨?_, ?_⟩
      · intro b hb hIa
        have hbI : Init g c b.1 := hInitW b.1 b.2 hb
        have hbs : b.1 ≠ s := fun e => h.head_unique hw b.2 (e ▸ hb)
        rw [hdisc_ne b.1 hbs, hdisc_s]
        exact h.disc_lt b.1 hbI
      · refine hpw.2.imp_of_mem ?_
        intro a b ha hb hab hIa
        have has : a.1 ≠ s := fun e => h.head_unique hw a.2 (e ▸ ha)
        have hbs : b.1 ≠ s := fun e => h.head_unique hw b.2 (e ▸ hb)
        have haI : Init g c a.1 := hInitW a.1 a.2 ha
        rw [hdisc_ne a.1 has, hdisc_ne b.1 hbs]
        exact hab haI
    · -- work_reach
      rw [hwork1]; exact h.work_reach
    · -- work_stk
      intro p off' hp hpI
      rw [hwork1] at hp
      rw [hstk1]
      by_cases hps : p = s
      · rw [hps]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (h.work_stk p off' hp (((hI1 p).1 hpI).resolve_right hps))
    · -- exam_vis
      intro x w hx hex
      rw [hwork1] at hex
      by_cases hxs : x = s
      · subst hxs; exact absurd hex (hnoexam w)
      · have hxI : Init g c x := ((hI1 x).1 hx).resolve_right hxs
        have := h.exam_vis x w hxI hex
        by_cases hws : w = s
        · subst hws; rw [hdisc_s]; exact h.time_ne_unv
        · rw [hdisc_ne w hws]; exact this
    · -- K
      intro W1 p off2 W2 hwk hpI x hx hdx w hw hex
      rw [hwork1] at hwk hex
      rw [hstk1] at hx hw
      rcases List.mem_cons.mp hx with hxs | hx'
      · rw [hxs] at hex; exact absurd hex (hnoexam w)
      · have hxs' : x ≠ s := fun e => hsnot (e ▸ hx')
        by_cases hps : p = s
        · exfalso
          rw [hps, hdisc_s, hdisc_ne x hxs'] at hdx
          have := h.disc_lt x (h.stk_init x hx')
          omega
        · have hpI' : Init g c p := ((hI1 p).1 hpI).resolve_right hps
          rw [hdisc_ne p hps, hdisc_ne x hxs'] at hdx
          rcases List.mem_cons.mp hw with hws | hw'
          · refine ⟨p, by simp, ?_⟩
            rw [hlow_ne p hps, hws, hdisc_s]
            have := h.low_le p hpI'
            have := h.disc_lt p hpI'
            omega
          · have hws' : w ≠ s := fun e => hsnot (e ▸ hw')
            obtain ⟨q, hq, hql⟩ := h.K W1 p off2 W2 hwk hpI' x hx' hdx w hw' hex
            have hqs : q ≠ s := by
              intro e
              rw [e, hs] at hql
              have := h.disc_lt w (h.stk_init w hw')
              have := h.time_le
              have := g.unv_gt
              omega
            exact ⟨q, hq, by rw [hlow_ne q hqs, hdisc_ne w hws']; exact hql⟩
    · -- G
      intro p off2 hp hpI x hx hdx
      rw [hwork1] at hp
      rw [hstk1] at hx
      by_cases hps : p = s
      · rcases List.mem_cons.mp hx with hxs | hx'
        · rw [hps, hxs]
        · exfalso
          have hxs' : x ≠ s := fun e => hsnot (e ▸ hx')
          rw [hps, hdisc_s, hdisc_ne x hxs'] at hdx
          have := h.disc_lt x (h.stk_init x hx')
          omega
      · have hpI' : Init g c p := ((hI1 p).1 hpI).resolve_right hps
        rcases List.mem_cons.mp hx with hxs | hx'
        · rw [hxs]
          have hpW : (p, off2) ∈ W := hWnode p off2 hp hps
          have hpw := h.work_reach
          rw [hw] at hpw
          exact (List.pairwise_cons.1 hpw).1 (p, off2) hpW
        · have hxs' : x ≠ s := fun e => hsnot (e ▸ hx')
          rw [hdisc_ne p hps, hdisc_ne x hxs'] at hdx
          exact h.G p off2 hp hpI' x hx' hdx
    · -- E1
      intro v hv
      rw [hblk1, heq1]; exact h.E1 v ((hD1 v).1 hv)
    · -- E2
      intro v w hv he
      exact (hD1 w).2 (h.E2 v w ((hD1 v).1 hv) he)
    · -- E3
      intro v w hv hw'
      rw [hblk1]; exact h.E3 v w ((hD1 v).1 hv) ((hD1 w).1 hw')
    · -- E4
      intro b hb
      rw [heq1] at hb
      obtain ⟨v, hv, hbv⟩ := h.E4 b hb
      exact ⟨v, (hD1 v).2 hv, by rw [hblk1]; exact hbv⟩
    · -- F
      intro v hv
      rw [hstk1] at hv
      by_cases hvs : v = s
      · subst hvs
        exact ⟨v, by rw [hstk1]; exact List.mem_cons_self .., by rw [hdisc_s, hlow_s], ReflTransGen.refl⟩
      · have hv' : v ∈ c.stk := (List.mem_cons.mp hv).resolve_left hvs
        obtain ⟨w, hw, hdw, hr⟩ := h.F v hv'
        have hws : w ≠ s := fun e => hsnot (e ▸ hw)
        exact ⟨w, by rw [hstk1]; exact List.mem_cons_of_mem _ hw, by rw [hdisc_ne w hws, hlow_ne v hvs]; exact hdw, hr⟩
    · -- L
      intro v hv hvn
      rw [hstk1] at hv
      rw [hwork1] at hvn
      by_cases hvs : v = s
      · exfalso; apply hvn; rw [hvs]; exact List.mem_map.mpr ⟨(s, off), hmem, rfl⟩
      · have hv' : v ∈ c.stk := (List.mem_cons.mp hv).resolve_left hvs
        rw [hlow_ne v hvs, hdisc_ne v hvs]
        exact h.L v hv' hvn
    · -- SE
      intro x hx
      rw [hstk1] at hx
      rcases List.mem_cons.mp hx with hxs | hx'
      · exact ⟨s, off, by rw [hwork1]; exact hmem, (hI1 s).2 (Or.inr rfl), by rw [hxs]⟩
      · obtain ⟨p, off2, hp, hpI, hdp⟩ := h.SE x hx'
        have hps : p ≠ s := fun e => hsI (e ▸ hpI)
        have hxs' : x ≠ s := fun e => hsnot (e ▸ hx')
        exact ⟨p, off2, by rw [hwork1]; exact hp, (hI1 p).2 (Or.inl hpI), by
          rw [hdisc_ne p hps, hdisc_ne x hxs']; exact hdp⟩
    · -- R
      intro v hv
      have hv' : v.val < c.ri := by rw [hc1'] at hv; exact hv
      rw [hwork1]
      rcases h.R v hv' with hh | hh
      · exact Or.inl ((hI1 v).2 (Or.inl hh))
      · exact Or.inr hh
    · -- ri_le
      rw [hc1']; exact h.ri_le
  · -- nothing to do
    have : initNode g s c = c := by simp [initNode, hs]
    rw [this]; exact h

end Sigref.Tarjan
