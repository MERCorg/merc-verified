import Sigref.Proofs.TarjanScanInv_Proofs

/-!
# Proofs: finishing the state at the top of the work stack

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

When the top state `s` has examined all its transitions (`off' = length`), it is finished: if it is
the root of an SCC (`disc s = low s`), the states above it on the SCC stack form exactly its SCC; its
`low` is propagated to its parent.
-/

namespace Sigref.Tarjan

open Relation

variable {n : ℕ}

section Finish

variable {g : Graph n} {V : Ctx n} {s : Fin n} {off' : ℕ} {W : List (Fin n × ℕ)}

/-- The entries below the top of the work stack are initialised. -/
theorem finish_initW (hV : Inv g V) (hw : V.work = (s, off') :: W) :
    ∀ p off2, (p, off2) ∈ W → Init g V p := by
  intro p off2 hp
  rcases hV.work_fresh p off2 (by rw [hw]; exact List.mem_cons_of_mem _ hp) with hh | hh
  · exact hh
  · rw [hw] at hh
    simp at hh
    obtain ⟨⟨e1, _⟩, _⟩ := hh
    rw [← e1] at hp
    exact absurd hp (hV.head_unique hw off2)

/-- Every state below the top of the work stack was discovered before the top state. -/
theorem finish_discW (hV : Inv g V) (hw : V.work = (s, off') :: W) (hsI : Init g V s) :
    ∀ p off2, (p, off2) ∈ W → V.disc p < V.disc s := by
  intro p off2 hp
  have hpw := hV.work_disc
  rw [hw] at hpw
  exact (List.pairwise_cons.1 hpw).1 (p, off2) hp hsI

/-- All hidden edges of the top state are examined. -/
theorem finish_exam_s (hw : V.work = (s, off') :: W) (hV : Inv g V) (hoff : off' = (g.adj s).length)
    (w : Fin n) (hedge : Edge g s w) : Examined g V.work s w := by
  refine ⟨hedge, fun off2 ho => ?_⟩
  rw [hw] at ho
  rcases List.mem_cons.mp ho with e | e
  · have : off2 = off' := (Prod.mk.inj e).2.symm ▸ rfl
    rw [this, hoff]
    obtain ⟨i, hi⟩ := List.getElem_of_mem hedge
    obtain ⟨hi1, hi2⟩ := hi
    exact ⟨i, hi1, by rw [List.getElem?_eq_getElem hi1, hi2]⟩
  · exact absurd e (hV.head_unique hw off2)

/-- States of the SCC stack that were discovered after the top state `s` are not on the work stack. -/
theorem finish_notW (hV : Inv g V) (hw : V.work = (s, off') :: W) (hsI : Init g V s) {x : Fin n}
    (hxI : Init g V x) (hx : x ≠ s) (hd : V.disc s ≤ V.disc x) : x ∉ V.work.map Prod.fst := by
  intro hh
  rw [hw] at hh
  simp only [List.map_cons, List.mem_cons] at hh
  rcases hh with hh | hh
  · exact hx hh
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hh
    have := finish_discW hV hw hsI e.1 e.2 he
    omega


/-- A done state only reaches done states. -/
theorem done_reach (hV : Inv g V) {a b : Fin n} (ha : Done g V a) (h : Reach g a b) : Done g V b := by
  induction h with
  | refl => exact ha
  | tail _ hedge ih => exact hV.E2 _ _ ih hedge

/-- When `s` is the root of an SCC, the states above it on the SCC stack are exactly its SCC. -/
theorem pop_sem (hV : Inv g V) (hw : V.work = (s, off') :: W) (hsI : Init g V s)
    (hoff : off' = (g.adj s).length) (hpop : V.disc s = V.low s) :
    (∀ x, x ∈ V.stk → V.disc s ≤ V.disc x → Reach g s x) ∧
    (∀ x, x ∈ V.stk → V.disc s ≤ V.disc x → Reach g x s) ∧
    (∀ x y, x ∈ V.stk → V.disc s ≤ V.disc x → Reach g x y →
        (y ∈ V.stk ∧ V.disc s ≤ V.disc y) ∨ Done g V y) ∧
    (∀ y, Reach g s y → Reach g y s → y ∈ V.stk ∧ V.disc s ≤ V.disc y) := by
  have hmem : (s, off') ∈ V.work := by rw [hw]; simp
  have hsstk : s ∈ V.stk := hV.work_stk s off' hmem hsI
  have hstepT : ∀ x, x ∈ V.stk → V.disc s ≤ V.disc x → ∀ w, Edge g x w →
      (w ∈ V.stk ∧ V.disc s ≤ V.disc w) ∨ Done g V w := by
    intro x hx hdx w hedge
    have hxI := hV.stk_init x hx
    have hex : Examined g V.work x w := by
      by_cases hxs : x = s
      · subst hxs; exact finish_exam_s hw hV hoff w hedge
      · refine ⟨hedge, fun off2 ho => ?_⟩
        exact absurd (List.mem_map.mpr ⟨(x, off2), ho, rfl⟩) (finish_notW hV hw hsI hxI hxs hdx)
    have hdw := hV.exam_vis x w hxI hex
    have hwI : Init g V w := by
      by_contra hwn
      rcases hV.unv_disc w hwn with hh | ⟨_, rest, hrest⟩
      · exact hdw hh
      · rw [hw] at hrest
        have hsw : s = w := congrArg Prod.fst (List.cons.inj hrest).1
        exact hwn (hsw ▸ hsI)
    by_cases hwst : w ∈ V.stk
    · left
      refine ⟨hwst, ?_⟩
      obtain ⟨q, hq, hql⟩ := hV.K [] s off' W hw hsI x hx hdx w hwst hex
      have : q = s := by simpa using hq
      rw [this] at hql
      omega
    · right; exact ⟨hwI, hwst⟩
  have hclosure : ∀ x y, x ∈ V.stk → V.disc s ≤ V.disc x → Reach g x y →
      (y ∈ V.stk ∧ V.disc s ≤ V.disc y) ∨ Done g V y := by
    intro x y hx hdx h
    induction h with
    | refl => exact Or.inl ⟨hx, hdx⟩
    | tail _ hedge ih =>
      rcases ih with ⟨hz, hdz⟩ | hz
      · exact hstepT _ hz hdz _ hedge
      · exact Or.inr (hV.E2 _ _ hz hedge)
  have hreach_to : ∀ d x, x ∈ V.stk → V.disc s ≤ V.disc x → V.disc x = d → Reach g x s := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hx hdx hxd
      by_cases hxs : x = s
      · rw [hxs]
      · have hxI := hV.stk_init x hx
        have hlt := hV.L x hx (finish_notW hV hw hsI hxI hxs hdx)
        obtain ⟨w, hwst, hdw, hr⟩ := hV.F x hx
        rcases hclosure x w hx hdx hr with ⟨hw1, hw2⟩ | hdone
        · have : V.disc w < d := by rw [← hxd, hdw]; exact hlt
          exact hr.trans (ih _ this w hw1 hw2 rfl)
        · exact absurd hwst hdone.2
  refine ⟨?_, ?_, hclosure, ?_⟩
  · intro x hx hdx
    exact hV.G s off' hmem hsI x hx hdx
  · intro x hx hdx
    exact hreach_to _ x hx hdx rfl
  · intro y h1 h2
    rcases hclosure s y hsstk le_rfl h1 with h | hdone
    · exact h
    · exact absurd hsstk (done_reach hV hdone h2).2


/-- Finishing a state that is not the root of an SCC: the state stays on the SCC stack, and its
`low` is propagated to the parent `p0` (`lowf`). -/
theorem inv_finish_nopop (hV : Inv g V) (hw : V.work = (s, off') :: W) (hsI : Init g V s)
    (hoff : off' = (g.adj s).length) (hnp : V.disc s ≠ V.low s) {p0 : Fin n} {o0 : ℕ}
    {W' : List (Fin n × ℕ)} (hW : W = (p0, o0) :: W') (lowf : Fin n → ℕ)
    (hl1 : ∀ v, v ≠ p0 → lowf v = V.low v) (hl2 : lowf p0 ≤ V.low p0)
    (hl3 : lowf p0 ≤ V.low s) (hl4 : lowf p0 = V.low p0 ∨ (lowf p0 = V.low s ∧ V.low s < V.low p0)) :
    Inv g { V with work := W, low := lowf } := by
  have hmem : (s, off') ∈ V.work := by rw [hw]; simp
  have hsstk : s ∈ V.stk := hV.work_stk s off' hmem hsI
  have hInitW := finish_initW hV hw
  have hdiscW := finish_discW hV hw hsI
  have hWne : ∀ p off2, (p, off2) ∈ W → p ≠ s := fun p off2 hp e =>
    hV.head_unique hw off2 (e ▸ hp)
  have hp0W : (p0, o0) ∈ W := by rw [hW]; simp
  have hp0I : Init g V p0 := hInitW p0 o0 hp0W
  have hp0d : V.disc p0 < V.disc s := hdiscW p0 o0 hp0W
  have hp0s : p0 ≠ s := hWne p0 o0 hp0W
  set c3 : Ctx n := { V with work := W, low := lowf } with hc3
  have hlow_p0 : lowf p0 ≠ g.unv := by
    have h1 := hV.low_le p0 hp0I
    have h2 := hV.disc_lt p0 hp0I
    have h3 := hV.time_le
    have h4 := g.unv_gt
    omega
  have hInit3 : ∀ v, Init g c3 v ↔ Init g V v := by
    intro v
    by_cases hv : v = p0
    · subst hv
      exact ⟨fun _ => hp0I, fun _ => hlow_p0⟩
    · show lowf v ≠ g.unv ↔ V.low v ≠ g.unv
      rw [hl1 v hv]
  have hlow3 : ∀ v, v ≠ p0 → c3.low v = V.low v := hl1
  have hexamV : ∀ x w, Examined g W x w → Examined g V.work x w := by
    intro x w ⟨hed, hh⟩
    by_cases hxs : x = s
    · subst hxs; exact finish_exam_s hw hV hoff w hed
    · refine ⟨hed, fun off2 ho => hh off2 ?_⟩
      rw [hw] at ho
      rcases List.mem_cons.mp ho with e | e
      · exact absurd (congrArg Prod.fst e) hxs
      · exact e
  have hlowmap : ∀ q, V.low q ≤ V.low q → True := fun _ _ => trivial
  have hlowle : ∀ q, c3.low q ≤ V.low q := by
    intro q
    by_cases hq : q = p0
    · subst hq; exact hl2
    · rw [hlow3 q hq]
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
    have hset : Finset.univ.filter (fun v => c3.low v ≠ g.unv) =
        Finset.univ.filter (fun v => V.low v ≠ g.unv) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hInit3 v
    rw [hset]; exact hV.time_card
  · intro v hv; exact hV.disc_lt v ((hInit3 v).1 hv)
  · intro v hv; exact (hlowle v).trans (hV.low_le v ((hInit3 v).1 hv))
  · intro u v hu hv h; exact hV.disc_inj u v ((hInit3 u).1 hu) ((hInit3 v).1 hv) h
  · -- unv_disc
    intro v hv
    have hvI : ¬ Init g V v := fun hh => hv ((hInit3 v).2 hh)
    rcases hV.unv_disc v hvI with hh | ⟨_, rest, hrest⟩
    · exact Or.inl hh
    · exfalso
      rw [hw] at hrest
      have hsv : s = v := congrArg Prod.fst (List.cons.inj hrest).1
      exact hvI (hsv ▸ hsI)
  · exact hV.onSt_iff
  · exact hV.stk_nodup
  · intro v hv; exact (hInit3 v).2 (hV.stk_init v hv)
  · exact hV.stk_sorted
  · -- work_nodup
    have := hV.work_nodup
    rw [hw] at this
    simp only [List.map_cons, List.nodup_cons] at this
    exact this.2
  · intro p off2 hp; exact hV.work_off p off2 (by rw [hw]; exact List.mem_cons_of_mem _ hp)
  · intro p off2 hp; exact Or.inl ((hInit3 p).2 (hInitW p off2 hp))
  · -- work_disc
    have hpw := hV.work_disc
    rw [hw] at hpw
    exact (List.pairwise_cons.1 hpw).2.imp (fun hab hI => hab ((hInit3 _).1 hI))
  · have hpw := hV.work_reach
    rw [hw] at hpw
    exact (List.pairwise_cons.1 hpw).2
  · intro p off2 hp hI
    exact hV.work_stk p off2 (by rw [hw]; exact List.mem_cons_of_mem _ hp) ((hInit3 p).1 hI)
  · intro x w hx hex
    exact hV.exam_vis x w ((hInit3 x).1 hx) (hexamV x w hex)
  · -- K
    intro W1 p off2 W2 hwk hpI x hx hdx w hw' hex
    have hcw : V.work = ((s, off') :: W1) ++ (p, off2) :: W2 := by
      have hwk' : W = W1 ++ (p, off2) :: W2 := hwk
      rw [hw, hwk']; rfl
    obtain ⟨q, hq, hql⟩ := hV.K _ p off2 W2 hcw ((hInit3 p).1 hpI) x hx hdx w hw' (hexamV x w hex)
    by_cases hqs : q = s
    · rw [hqs] at hql
      have hp0mem : p0 ∈ W1.map Prod.fst ++ [p] := by
        have hwk' : W = W1 ++ (p, off2) :: W2 := hwk
        rw [hW] at hwk'
        cases W1 with
        | nil => simp at hwk'; simp [hwk'.1]
        | cons e W1'' =>
          simp only [List.cons_append, List.cons.injEq] at hwk'
          simp [← hwk'.1]
      exact ⟨p0, hp0mem, hl3.trans hql⟩
    · refine ⟨q, ?_, (hlowle q).trans hql⟩
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hq ⊢
      tauto
  · intro p off2 hp hpI x hx hdx
    exact hV.G p off2 (by rw [hw]; exact List.mem_cons_of_mem _ hp) ((hInit3 p).1 hpI) x hx hdx
  · intro v hv; exact hV.E1 v ⟨(hInit3 v).1 hv.1, hv.2⟩
  · intro v w hv he
    have := hV.E2 v w ⟨(hInit3 v).1 hv.1, hv.2⟩ he
    exact ⟨(hInit3 w).2 this.1, this.2⟩
  · intro v w hv hw'
    exact hV.E3 v w ⟨(hInit3 v).1 hv.1, hv.2⟩ ⟨(hInit3 w).1 hw'.1, hw'.2⟩
  · intro b hb
    obtain ⟨v, hv, hbv⟩ := hV.E4 b hb
    exact ⟨v, ⟨(hInit3 v).2 hv.1, hv.2⟩, hbv⟩
  · -- F
    intro v hv
    by_cases hvp : v = p0
    · subst hvp
      rcases hl4 with h4 | ⟨h4, h5⟩
      · obtain ⟨w, hw', hdw, hr⟩ := hV.F v hv
        exact ⟨w, hw', by show V.disc w = lowf v; rw [h4]; exact hdw, hr⟩
      · obtain ⟨w, hw', hdw, hr⟩ := hV.F s hsstk
        have hpw := hV.work_reach
        rw [hw] at hpw
        have hr0 : Reach g v s := (List.pairwise_cons.1 hpw).1 (v, o0) hp0W
        exact ⟨w, hw', by show V.disc w = lowf v; rw [h4]; exact hdw, hr0.trans hr⟩
    · obtain ⟨w, hw', hdw, hr⟩ := hV.F v hv
      exact ⟨w, hw', by show V.disc w = lowf v; rw [hl1 v hvp]; exact hdw, hr⟩
  · -- L
    intro v hv hvn
    by_cases hvs : v = s
    · subst hvs
      have h1 := hV.low_le v hsI
      show lowf v < V.disc v
      rw [hl1 v hp0s.symm]
      omega
    · have hvp : v ≠ p0 := fun e => hvn (by rw [e]; exact List.mem_map.mpr ⟨(p0, o0), hp0W, rfl⟩)
      have hvn' : v ∉ V.work.map Prod.fst := by
        intro hh
        rw [hw] at hh
        simp only [List.map_cons, List.mem_cons] at hh
        rcases hh with hh | hh
        · exact hvs hh
        · exact hvn hh
      show lowf v < V.disc v
      rw [hl1 v hvp]
      exact hV.L v hv hvn'
  · -- SE
    intro x hx
    obtain ⟨p, off2, hp, hpI, hdp⟩ := hV.SE x hx
    rw [hw] at hp
    rcases List.mem_cons.mp hp with e | e
    · have hps : p = s := (Prod.mk.inj e).1
      rw [hps] at hdp
      exact ⟨p0, o0, hp0W, (hInit3 p0).2 hp0I, by
        show V.disc p0 ≤ V.disc x
        omega⟩
    · exact ⟨p, off2, e, (hInit3 p).2 hpI, hdp⟩
  · -- R
    intro v hv
    rcases hV.R v hv with hh | hh
    · exact Or.inl ((hInit3 v).2 hh)
    · rw [hw] at hh
      rcases List.mem_cons.mp hh with e | e
      · have hvs : v = s := (Prod.mk.inj e).1
        left; rw [hvs]; exact (hInit3 s).2 hsI
      · exact Or.inr e
  · exact hV.ri_le


/-- Finishing the root of an SCC: the states above it on the SCC stack (`top`, and `s`) form the
SCC; they are popped and get the next block number. -/
theorem inv_finish_pop (hV : Inv g V) (hw : V.work = (s, off') :: W) (hsI : Init g V s)
    (hoff : off' = (g.adj s).length) (hpop : V.disc s = V.low s) {top rest : List (Fin n)}
    (hstk : V.stk = top ++ s :: rest) {onSt' : Fin n → Bool} {blk' : Fin n → ℕ}
    (hon' : ∀ u, onSt' u = if u ∈ top ++ [s] then false else V.onSt u)
    (hbl' : ∀ u, blk' u = if u ∈ top ++ [s] then V.eq else V.blk u) :
    Inv g { V with work := W, stk := rest, onSt := onSt', blk := blk', eq := V.eq + 1 } := by
  obtain ⟨hA, hB, hC, hD⟩ := pop_sem hV hw hsI hoff hpop
  have hmem : (s, off') ∈ V.work := by rw [hw]; simp
  have hsstk : s ∈ V.stk := hV.work_stk s off' hmem hsI
  have hInitW := finish_initW hV hw
  have hdiscW := finish_discW hV hw hsI
  have hWne : ∀ p off2, (p, off2) ∈ W → p ≠ s := fun p off2 hp e =>
    hV.head_unique hw off2 (e ▸ hp)
  have hsorted := hV.stk_sorted
  rw [hstk] at hsorted
  have hnd := hV.stk_nodup
  rw [hstk] at hnd
  obtain ⟨hsp1, hsp2, hsp3⟩ := List.pairwise_append.1 hsorted
  obtain ⟨hsp2a, hsp2b⟩ := List.pairwise_cons.1 hsp2
  obtain ⟨hnd1, hnd2, hnd3⟩ := List.nodup_append.1 hnd
  have hrestlt : ∀ x ∈ rest, V.disc x < V.disc s := hsp2a
  have hnotT : ∀ x ∈ rest, x ∉ top ++ [s] := by
    intro x hx hxT
    rcases List.mem_append.mp hxT with h1 | h1
    · exact hnd3 x h1 x (List.mem_cons_of_mem _ hx) rfl
    · have : x = s := by simpa using h1
      exact (List.nodup_cons.1 hnd2).1 (this ▸ hx)
  have hTmem : ∀ x, x ∈ V.stk → (V.disc s ≤ V.disc x ↔ x ∈ top ++ [s]) := by
    intro x hx
    rw [hstk] at hx
    constructor
    · intro hd
      rcases List.mem_append.mp hx with h1 | h1
      · exact List.mem_append_left _ h1
      · rcases List.mem_cons.mp h1 with h2 | h2
        · rw [h2]; simp
        · have := hrestlt x h2; omega
    · intro hxT
      rcases List.mem_append.mp hxT with h1 | h1
      · exact (hsp3 x h1 s (List.mem_cons_self ..)).le
      · have : x = s := by simpa using h1
        rw [this]
  have hTstk : ∀ v, v ∈ top ++ [s] → v ∈ V.stk := by
    intro v hv
    rw [hstk]
    rcases List.mem_append.mp hv with h1 | h1
    · exact List.mem_append_left _ h1
    · have : v = s := by simpa using h1
      rw [this]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hrestst : ∀ v, v ∈ rest → v ∈ V.stk := by
    intro v hv; rw [hstk]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hv)
  have hTreach : ∀ v, v ∈ top ++ [s] → Reach g s v ∧ Reach g v s := fun v hv =>
    ⟨hA v (hTstk v hv) ((hTmem v (hTstk v hv)).2 hv), hB v (hTstk v hv) ((hTmem v (hTstk v hv)).2 hv)⟩
  have hTclosed : ∀ v, v ∈ top ++ [s] → ∀ w, Edge g v w → w ∈ top ++ [s] ∨ Done g V w := by
    intro v hv w he
    rcases hC v w (hTstk v hv) ((hTmem v (hTstk v hv)).2 hv) (ReflTransGen.single he) with ⟨hw1, hw2⟩ | hd
    · exact Or.inl ((hTmem w hw1).1 hw2)
    · exact Or.inr hd
  set c3 : Ctx n := { V with work := W, stk := rest, onSt := onSt', blk := blk', eq := V.eq + 1 }
    with hc3
  have hInit3 : ∀ v, Init g c3 v ↔ Init g V v := fun v => Iff.rfl
  have hDone3 : ∀ v, Done g c3 v ↔ (Done g V v ∨ v ∈ top ++ [s]) := by
    intro v
    constructor
    · rintro ⟨hI, hn⟩
      by_cases hvs : v ∈ V.stk
      · right
        rw [hstk] at hvs
        rcases List.mem_append.mp hvs with h1 | h1
        · exact List.mem_append_left _ h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · rw [h2]; simp
          · exact absurd h2 hn
      · exact Or.inl ⟨hI, hvs⟩
    · rintro (⟨hI, hn⟩ | hT)
      · exact ⟨hI, fun hh => hn (hrestst v hh)⟩
      · exact ⟨hV.stk_init v (hTstk v hT), fun hh => hnotT v hh hT⟩
  have hblkT : ∀ v, v ∈ top ++ [s] → c3.blk v = V.eq := by
    intro v hv; show blk' v = V.eq; rw [hbl' v]; simp [hv]
  have hblkD : ∀ v, v ∉ top ++ [s] → c3.blk v = V.blk v := by
    intro v hv; show blk' v = V.blk v; rw [hbl' v]; simp [hv]
  have hexamV : ∀ x w, Examined g W x w → Examined g V.work x w := by
    intro x w ⟨hed, hh⟩
    by_cases hxs : x = s
    · subst hxs; exact finish_exam_s hw hV hoff w hed
    · refine ⟨hed, fun off2 ho => hh off2 ?_⟩
      rw [hw] at ho
      rcases List.mem_cons.mp ho with e | e
      · exact absurd (congrArg Prod.fst e) hxs
      · exact e
  have hstk_rest : ∀ x, x ∈ V.stk → x ∉ top ++ [s] → x ∈ rest := by
    intro x hx hxT
    rw [hstk] at hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact absurd (List.mem_append_left _ h1) hxT
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd (by rw [h2]; simp) hxT
      · exact h2
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
    exact hV.time_card
  · intro v hv; exact hV.disc_lt v hv
  · intro v hv; exact hV.low_le v hv
  · intro u v hu hv h; exact hV.disc_inj u v hu hv h
  · -- unv_disc
    intro v hv
    rcases hV.unv_disc v hv with hh | ⟨_, rest', hrest⟩
    · exact Or.inl hh
    · exfalso
      rw [hw] at hrest
      have hsv : s = v := congrArg Prod.fst (List.cons.inj hrest).1
      exact hv (hsv ▸ hsI)
  · -- onSt_iff
    intro v
    show onSt' v = true ↔ v ∈ rest
    rw [hon' v]
    by_cases hvT : v ∈ top ++ [s]
    · rw [if_pos hvT]
      exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => absurd hvT (hnotT v h)⟩
    · rw [if_neg hvT, hV.onSt_iff v]
      constructor
      · intro hh; exact hstk_rest v hh hvT
      · intro hh; exact hrestst v hh
  · exact (List.nodup_cons.1 hnd2).2
  · intro v hv; exact hV.stk_init v (hrestst v hv)
  · exact hsp2b
  · -- work_nodup
    have := hV.work_nodup
    rw [hw] at this
    simp only [List.map_cons, List.nodup_cons] at this
    exact this.2
  · intro p off2 hp; exact hV.work_off p off2 (by rw [hw]; exact List.mem_cons_of_mem _ hp)
  · intro p off2 hp; exact Or.inl (hInitW p off2 hp)
  · have hpw := hV.work_disc
    rw [hw] at hpw
    exact (List.pairwise_cons.1 hpw).2
  · have hpw := hV.work_reach
    rw [hw] at hpw
    exact (List.pairwise_cons.1 hpw).2
  · -- work_stk
    intro p off2 hp hI
    have hps := hV.work_stk p off2 (by rw [hw]; exact List.mem_cons_of_mem _ hp) hI
    refine hstk_rest p hps fun hT => ?_
    have := (hTmem p hps).2 hT
    have := hdiscW p off2 hp
    omega
  · intro x w hx hex
    exact hV.exam_vis x w hx (hexamV x w hex)
  · -- K
    intro W1 p off2 W2 hwk hpI x hx hdx w hw' hex
    have hcw : V.work = ((s, off') :: W1) ++ (p, off2) :: W2 := by
      have hwk' : W = W1 ++ (p, off2) :: W2 := hwk
      rw [hw, hwk']; rfl
    obtain ⟨q, hq, hql⟩ := hV.K _ p off2 W2 hcw hpI x (hrestst x hx) hdx w (hrestst w hw')
      (hexamV x w hex)
    have hqs : q ≠ s := by
      intro e
      rw [e, ← hpop] at hql
      have := hrestlt w hw'
      omega
    refine ⟨q, ?_, hql⟩
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hq ⊢
    tauto
  · -- G
    intro p off2 hp hpI x hx hdx
    exact hV.G p off2 (by rw [hw]; exact List.mem_cons_of_mem _ hp) hpI x (hrestst x hx) hdx
  · -- E1
    intro v hv
    show c3.blk v < V.eq + 1
    rcases (hDone3 v).1 hv with hd | hT
    · have hvT : v ∉ top ++ [s] := fun hT => hd.2 (hTstk v hT)
      rw [hblkD v hvT]
      have := hV.E1 v hd
      omega
    · rw [hblkT v hT]; omega
  · -- E2
    intro v w hv he
    rcases (hDone3 v).1 hv with hd | hT
    · exact (hDone3 w).2 (Or.inl (hV.E2 v w hd he))
    · exact (hDone3 w).2 (by
        rcases hTclosed v hT w he with h1 | h1
        · exact Or.inr h1
        · exact Or.inl h1)
  · -- E3
    intro v w hv hw'
    rcases (hDone3 v).1 hv with hdv | hTv <;> rcases (hDone3 w).1 hw' with hdw | hTw
    · have hvT : v ∉ top ++ [s] := fun hT => hdv.2 (hTstk v hT)
      have hwT : w ∉ top ++ [s] := fun hT => hdw.2 (hTstk w hT)
      show c3.blk v = c3.blk w ↔ _
      rw [hblkD v hvT, hblkD w hwT]
      exact hV.E3 v w hdv hdw
    · have hvT : v ∉ top ++ [s] := fun hT => hdv.2 (hTstk v hT)
      show c3.blk v = c3.blk w ↔ _
      rw [hblkD v hvT, hblkT w hTw]
      have := hV.E1 v hdv
      constructor
      · intro h; omega
      · rintro ⟨h1, _⟩
        exact absurd (hTstk w hTw) (done_reach hV hdv h1).2
    · have hwT : w ∉ top ++ [s] := fun hT => hdw.2 (hTstk w hT)
      show c3.blk v = c3.blk w ↔ _
      rw [hblkT v hTv, hblkD w hwT]
      have := hV.E1 w hdw
      constructor
      · intro h; omega
      · rintro ⟨_, h2⟩
        exact absurd (hTstk v hTv) (done_reach hV hdw h2).2
    · show c3.blk v = c3.blk w ↔ _
      rw [hblkT v hTv, hblkT w hTw]
      exact ⟨fun _ => ⟨(hTreach v hTv).2.trans (hTreach w hTw).1,
        (hTreach w hTw).2.trans (hTreach v hTv).1⟩, fun _ => rfl⟩
  · -- E4
    intro b hb
    have hb' : b < V.eq + 1 := hb
    by_cases hbe : b = V.eq
    · refine ⟨s, (hDone3 s).2 (Or.inr (by simp)), ?_⟩
      rw [hbe]; exact hblkT s (by simp)
    · obtain ⟨v, hv, hbv⟩ := hV.E4 b (by omega)
      have hvT : v ∉ top ++ [s] := fun hT => hv.2 (hTstk v hT)
      exact ⟨v, (hDone3 v).2 (Or.inl hv), by rw [hblkD v hvT]; exact hbv⟩
  · -- F
    intro v hv
    obtain ⟨w, hw', hdw, hr⟩ := hV.F v (hrestst v hv)
    refine ⟨w, hstk_rest w hw' fun hT => ?_, hdw, hr⟩
    have h1 := (hTmem w hw').2 hT
    have h2 := hV.low_le v (hV.stk_init v (hrestst v hv))
    have h3 := hrestlt v hv
    omega
  · -- L
    intro v hv hvn
    have hvs : v ≠ s := fun e => (List.nodup_cons.1 hnd2).1 (e ▸ hv)
    have hvn' : v ∉ V.work.map Prod.fst := by
      intro hh
      rw [hw] at hh
      simp only [List.map_cons, List.mem_cons] at hh
      rcases hh with hh | hh
      · exact hvs hh
      · exact hvn hh
    exact hV.L v (hrestst v hv) hvn'
  · -- SE
    intro x hx
    obtain ⟨p, off2, hp, hpI, hdp⟩ := hV.SE x (hrestst x hx)
    rw [hw] at hp
    rcases List.mem_cons.mp hp with e | e
    · exfalso
      have hps : p = s := (Prod.mk.inj e).1
      rw [hps] at hdp
      have := hrestlt x hx
      omega
    · exact ⟨p, off2, e, hpI, hdp⟩
  · -- R
    intro v hv
    rcases hV.R v hv with hh | hh
    · exact Or.inl hh
    · rw [hw] at hh
      rcases List.mem_cons.mp hh with e | e
      · have hvs : v = s := (Prod.mk.inj e).1
        left; rw [hvs]; exact hsI
      · exact Or.inr e
  · exact hV.ri_le


/-- **Finishing the top state succeeds and preserves the invariant.** -/
theorem inv_finish (hV : Inv g V) (hw : V.work = (s, off') :: W) (hsI : Init g V s)
    (hoff : off' = (g.adj s).length) :
    ∃ c3, finish s { V with work := W } = some c3 ∧ Inv g c3 := by
  have hmem : (s, off') ∈ V.work := by rw [hw]; simp
  have hsstk : s ∈ V.stk := hV.work_stk s off' hmem hsI
  have hInitW := finish_initW hV hw
  have hdiscW := finish_discW hV hw hsI
  by_cases hpop : V.disc s = V.low s
  · obtain ⟨top, rest, hstk, hstop, onSt', blk', hpc, hon', hbl'⟩ :=
      popComp_spec s V.eq V.stk V.onSt V.blk hsstk
    refine ⟨{ V with work := W, stk := rest, onSt := onSt', blk := blk', eq := V.eq + 1 }, ?_,
      inv_finish_pop hV hw hsI hoff hpop hstk hon' hbl'⟩
    have hlowW : ∀ p0 o0, (p0, o0) ∈ W → ¬ (V.low s < V.low p0) := by
      intro p0 o0 hp
      have h1 := hV.low_le p0 (hInitW p0 o0 hp)
      have h2 := hdiscW p0 o0 hp
      omega
    unfold finish
    simp only [hpop, if_true, hpc, Option.map_some]
    rcases hW : W with _ | ⟨⟨p0, o0⟩, W'⟩
    · rfl
    · simp only
      rw [if_neg (hlowW p0 o0 (by rw [hW]; simp))]
  · -- not the root of an SCC
    have hlt : V.low s < V.disc s := lt_of_le_of_ne (hV.low_le s hsI) (Ne.symm hpop)
    rcases hW : W with _ | ⟨⟨p0, o0⟩, W'⟩
    · exfalso
      obtain ⟨w, hw', hdw, _⟩ := hV.F s hsstk
      obtain ⟨p, off2, hp, hpI, hdp⟩ := hV.SE w hw'
      rw [hw, hW] at hp
      have : p = s := by simpa using congrArg Prod.fst (List.mem_singleton.mp hp)
      rw [this] at hdp
      omega
    · by_cases hlow : V.low s < V.low p0
      · refine ⟨{ V with work := W, low := Function.update V.low p0 (V.low s) }, ?_, ?_⟩
        · unfold finish
          simp only [hpop, if_false, Option.map_some]
          simp only [hW]
          rw [if_pos hlow]
        · refine inv_finish_nopop hV hw hsI hoff hpop hW _ ?_ ?_ ?_ ?_
          · intro v hv; simp [Function.update_of_ne hv]
          · simp; exact hlow.le
          · simp
          · right; simp; exact hlow
      · refine ⟨{ V with work := W }, ?_, ?_⟩
        · unfold finish
          simp only [hpop, if_false, Option.map_some]
          simp only [hW]
          rw [if_neg hlow]
        · exact inv_finish_nopop hV hw hsI hoff hpop hW V.low (fun v _ => rfl) le_rfl
            (by omega) (Or.inl rfl)

end Finish

end Sigref.Tarjan
