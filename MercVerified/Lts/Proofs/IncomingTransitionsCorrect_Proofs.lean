import MercVerified.Lts.Proofs.IncomingTransitions_Proofs

/-!
# `IncomingTransitions::new` is correct

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

Assembles the stage lemmas of `IncomingTransitions_Proofs` (stages 1-7 and the reader
`incoming_transitions`) into `incoming_transitions_correct`, under `WellFormed`.
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open MercVerified.Lts (toLTS tr)

namespace MercVerified.Lts.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-! ## Stage 9: the reader `incoming_transitions` -/

theorem vec_index_sz (v : alloc.vec.Vec Sz) (i : Sz) (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Sz) v i = ok (v.val[i.val]'h) := by
  have hidx' := Aeneas.Std.alloc.vec.Vec.index_usize_spec v i h
  rcases Std.WP.spec_imp_exists hidx' with ⟨x, hx, hxv⟩
  have hidx_u : v.index_usize i = ok (v.val[i.val]) := by rw [hx, hxv]
  simpa [alloc.vec.Vec.index_slice_index] using hidx_u

/-- `incoming_transitions` reads the flat arrays over the state's CSR range. -/
theorem incoming_transitions_spec (self : IncomingTransitions) (s : TagIndex Sz StateTag)
    (hs : s.index.val + 1 < self.state2incoming.val.length)
    (hle : (self.state2incoming.val.getD s.index.val 0#usize).val
      ≤ (self.state2incoming.val.getD (s.index.val + 1) 0#usize).val)
    (hend : (self.state2incoming.val.getD (s.index.val + 1) 0#usize).val
      ≤ self.transition_labels.val.length)
    (hlen : self.transition_labels.val.length = self.transition_from.val.length)
    (hmax : self.transition_labels.val.length ≤ Usize.max) :
    ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions self s = ok res ∧
      res.val = (slotEntries self.transition_labels.val self.transition_from.val
          (self.state2incoming.val.getD s.index.val 0#usize).val
          (self.state2incoming.val.getD (s.index.val + 1) 0#usize).val).map
        (fun p => (⟨p.1, p.2⟩ : FromTransition)) := by
  have hs0 : s.index.val < self.state2incoming.val.length := by omega
  have hmaxS : s.index.val + 1 ≤ Usize.max := by
    have : self.state2incoming.val.length ≤ Usize.max := by
      have := self.state2incoming.property
      simpa [Usize.max] using this
    omega
  obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists
    (Usize.add_spec (x := s.index) (y := 1#usize) (by simp [hmaxS]))
  have hi1v' : i1.val = s.index.val + 1 := by simpa using hi1v
  have hget0 : self.state2incoming.val.getD s.index.val 0#usize
      = self.state2incoming.val[s.index.val]'hs0 :=
    List.getD_eq_getElem _ _ hs0
  have hi1lt : i1.val < self.state2incoming.val.length := by omega
  have hget1 : self.state2incoming.val.getD (s.index.val + 1) 0#usize
      = self.state2incoming.val[i1.val]'hi1lt := by
    rw [← hi1v']; exact List.getD_eq_getElem _ _ hi1lt
  set start := self.state2incoming.val[s.index.val]'hs0 with hstart
  set e := self.state2incoming.val[i1.val]'hi1lt with he
  rw [hget0] at hle ⊢
  rw [hget1] at hle hend ⊢
  obtain ⟨i2, hi2, hi2v, -⟩ := Std.WP.spec_imp_exists (Usize.sub_spec (x := e) (y := start) hle)
  have hcall : IncomingTransitions.incoming_transitions self s
      = verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop
          { start := start, «end» := e } self.transition_labels self.transition_from
          (alloc.vec.Vec.with_capacity FromTransition i2) := by
    unfold IncomingTransitions.incoming_transitions
    have hv : verified.merc_utilities.tagged_index.TagIndex.value core.marker.CopyUsize s
        = ok s.index := rfl
    have hvi0 := vec_index_sz self.state2incoming s.index hs0
    have hvi1 := vec_index_sz self.state2incoming i1 hi1lt
    simp only [hv, hi1, bind_ok]
    rw [hvi0, hvi1]
    simp only [bind_ok]
    rw [hi2]
    simp only [bind_ok]
    rfl
  have hwc : (alloc.vec.Vec.with_capacity FromTransition i2) = alloc.vec.Vec.new FromTransition := rfl
  rw [hcall, hwc]
  have hgather := gather_from_loop_spec (α := FromTransition) e start
    (fun p => ftAt self.transition_labels.val self.transition_from.val p) zeroFT hle
    (by omega)
    (fun it v => verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop.body
      self.transition_labels self.transition_from it v)
    (fun it v hend' hvl hlt hvs => by
      rw [hend'] at hlt
      have hbound : it.start.val < self.transition_labels.val.length := by omega
      exact incoming_transitions_loop_step self.transition_labels self.transition_from it v hlen
        (by rw [hend']; exact hlt) hbound (by omega))
    (fun it v hge => by
      obtain ⟨o, it1, hnext, hopt, hident⟩ := next_range_none it hge
      unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop.body
      rw [hnext, hopt]
      simp)
  obtain ⟨r, hr, ⟨hrlen, hrget⟩⟩ := Std.WP.spec_imp_exists hgather
  refine ⟨r, ?_, ?_⟩
  · unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop
    exact hr
  · apply List.ext_getElem
    · rw [hrlen]; simp [slotEntries]
    · intro k h1 h2
      have hk : k < e.val - start.val := by omega
      have := hrget k hk
      rw [List.getD_eq_getElem _ _ h1] at this
      rw [this]
      simp [slotEntries, ftAt, Nat.add_comm]


/-! ## Counting facts -/

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a List.mem_cons_self
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sum_tick_range_le (t : Transition) (k : Nat) :
    ((List.range k).map (fun j => tick t j)).sum ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : t.to.index.val = k
    · have h0 : ((List.range k).map (fun j => tick t j)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have := List.mem_range.mp hj
        simp only [tick]; rw [if_neg (by omega)]
      have h1 : tick t k = 1 := by simp [tick, h]
      omega
    · have h1 : tick t k = 0 := by simp [tick, h]
      omega

theorem sum_toCount_range_le (ts : List Transition) (k : Nat) :
    ((List.range k).map (fun j => toCount ts j)).sum ≤ ts.length := by
  induction ts with
  | nil => simp [toCount_nil]
  | cons t ts ih =>
    have : ∀ j, toCount (t :: ts) j = tick t j + toCount ts j := toCount_cons t ts
    simp only [this, List.sum_map_add, List.length_cons]
    have e1 : (List.map (tick t) (List.range k)).sum ≤ 1 := sum_tick_range_le t k
    have e2 : (List.map (toCount ts) (List.range k)).sum ≤ ts.length := ih
    omega

/-- Summing the per-state counts over the slots `< k` never exceeds the total number of
    transitions of the states. -/
theorem sum_seen_range_le {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (l : List (TagIndex Sz StateTag)) (k : Nat) :
    ((List.range k).map (fun j =>
        (l.map (fun s => toCount (outVec LTSInst sys s).val j)).sum)).sum
      ≤ (l.map (fun s => (outVec LTSInst sys s).val.length)).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.sum_cons, List.sum_map_add]
    have e1 : (List.map (toCount (outVec LTSInst sys s).val) (List.range k)).sum
        ≤ (outVec LTSInst sys s).val.length := sum_toCount_range_le _ k
    omega

theorem natSum_eq_range_sum (c : List Sz) (k : Nat) (hk : k ≤ c.length) :
    natSum c k = ((List.range k).map (fun j => (c.getD j 0#usize).val)).sum := by
  induction k with
  | zero => simp [natSum]
  | succ k ih =>
    rw [natSum_succ c k (by omega), ih (by omega), List.range_succ, List.map_append,
      List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [List.getD_eq_getElem c 0#usize (show k < c.length by omega)]

theorem natSum_mono (c : List Sz) {a b : Nat} (hab : a ≤ b) (hb : b ≤ c.length) :
    natSum c a ≤ natSum c b := by
  induction b, hab using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ b hab ih =>
    rw [natSum_succ c b (by omega)]
    have := ih (by omega)
    omega

theorem seenCount_full {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : List (TagIndex Sz StateTag)) (j : Nat) :
    seenCount LTSInst sys sv sv.length j
      = (sv.map (fun s => toCount (outVec LTSInst sys s).val j)).sum := by
  simp [seenCount]


/-! ## Assembly of `IncomingTransitions::new` -/

theorem states_length (sv : List (TagIndex Sz StateTag)) (N : Nat)
    (hN : N < 2 ^ UScalarTy.Usize.numBits) (hnd : sv.Nodup)
    (hmem : ∀ s, s ∈ sv ↔ s.index.val < N) : sv.length = N := by
  have h1 : (sv.map (fun s => s.index.val)).Nodup := by
    refine hnd.map ?_
    intro a b h
    exact merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq h)
  have h2 : ∀ x, x ∈ sv.map (fun s => s.index.val) ↔ x ∈ List.range N := by
    intro x
    rw [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact (hmem s).1 hs
    · intro hx
      refine ⟨uTag x, (hmem _).2 ?_, ?_⟩
      · simp only [uTag]; rw [uTotal_val_of_lt (by omega)]; exact hx
      · simp only [uTag]; rw [uTotal_val_of_lt (by omega)]
  have hp := (List.perm_ext_iff_of_nodup h1 List.nodup_range).2 h2
  have := hp.length_eq
  simpa using this

theorem copy_prefix_ok (source : alloc.vec.Vec Sz) (n : Sz) (hn : n.val < Usize.max)
    (hsrc : n.val ≤ source.val.length) :
    ∃ r : alloc.vec.Vec Sz,
      verified.merc_lts.incoming_transitions.copy_prefix source n = ok r ∧
      r.val.length = n.val ∧
      ∀ k, k < n.val → r.val.getD k 0#usize = source.val.getD k 0#usize := by
  obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists (copy_prefix_spec n source hn hsrc)
  exact ⟨r, hr, hp⟩

/-- `IncomingTransitions::new` succeeds on a well-formed LTS, and the structure it leaves behind. -/
theorem incoming_new_structure {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : WellFormed LTSInst sys) (hfit : ∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
      n.val * (n.val + 2) ≤ Std.Usize.max)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n) :
    ∃ incoming : IncomingTransitions, IncomingTransitions.new LTSInst sys = ok incoming ∧
    ∃ sv : alloc.vec.Vec (TagIndex Sz StateTag),
      sv.val.Nodup ∧ (∀ s, s ∈ sv.val ↔ s.index.val < n.val) ∧
      incoming.state2incoming.val.length = n.val + 1 ∧
      (∀ i, i + 1 < incoming.state2incoming.val.length →
        (incoming.state2incoming.val.getD i 0#usize).val
          ≤ (incoming.state2incoming.val.getD (i + 1) 0#usize).val) ∧
      (∀ j, j < incoming.state2incoming.val.length →
        (incoming.state2incoming.val.getD j 0#usize).val ≤ incoming.transition_labels.val.length) ∧
      incoming.transition_labels.val.length = incoming.transition_from.val.length ∧
      incoming.transition_labels.val.length ≤ Usize.max ∧
      (∀ j, j < n.val → ∀ x,
        x ∈ slotEntries incoming.transition_labels.val incoming.transition_from.val
          (incoming.state2incoming.val.getD j 0#usize).val
          (incoming.state2incoming.val.getD (j + 1) 0#usize).val
        ↔ x ∈ towards LTSInst sys sv.val sv.val.length j) ∧
      (∀ j, j < n.val → Zp incoming.transition_labels.val
        (incoming.state2incoming.val.getD j 0#usize).val
        (incoming.state2incoming.val.getD (j + 1) 0#usize).val) := by
  obtain ⟨n0, hn0, hnpos⟩ := hwf.1
  have hnn : n0 = n := by have := hn0.symm.trans hns; simpa using this
  subst hnn
  obtain ⟨sv, m, hiter, hnd, hmem, hnt, hmlt, hsum⟩ := hwf.2.2 n0 hns
  have hn2 := hfit n0 hns
  have hnmax : n0.val ≤ Usize.max := by scalar_tac
  have hN2 : n0.val + 2 ≤ Usize.max := by
    have : n0.val + 2 ≤ n0.val * (n0.val + 2) := Nat.le_mul_of_pos_left _ hnpos
    omega
  have hNbits : n0.val < 2 ^ UScalarTy.Usize.numBits := lt_two_pow_of_le_max hnmax
  have hsvlen : sv.val.length = n0.val := states_length sv.val n0.val hNbits hnd hmem
  -- outgoing transitions of the enumerated states
  have hout : ∀ s ∈ sv.val, LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s) := by
    intro s hs
    obtain ⟨ts, hts, -⟩ := hwf.2.1 n0 hns s ((hmem s).1 hs)
    exact outVec_eq_ok LTSInst sys s ts hts
  have htgt : ∀ s ∈ sv.val, ∀ t ∈ (outVec LTSInst sys s).val, t.to.index.val < n0.val := by
    intro s hs t ht
    obtain ⟨ts, hts, htg⟩ := hwf.2.1 n0 hns s ((hmem s).1 hs)
    rw [outVec_of_ok LTSInst sys s ts hts] at ht
    exact htg t ht
  have htot : (sv.val.map (fun s => (outVec LTSInst sys s).val.length)).sum ≤ m.val :=
    hsum (fun s => outVec LTSInst sys s) hout
  have hseen_le : ∀ j, seenCount LTSInst sys sv.val sv.val.length j ≤ m.val := by
    intro j
    rw [seenCount_full]
    refine le_trans (sum_map_le_sum_map _ _ _ (fun s _ => ?_)) htot
    exact List.length_filter_le _ _
  obtain ⟨labels0, hl0, hl0v⟩ := new_labels_spec m
  obtain ⟨src0, hs0, hs0v⟩ := new_states_spec m
  have hlen0 : labels0.val.length = m.val := by rw [hl0v]; simp
  have hslen0 : src0.val.length = m.val := by rw [hs0v]; simp
  obtain ⟨i, hi, hiv⟩ := Std.WP.spec_imp_exists
    (Usize.add_spec (x := n0) (y := 1#usize) (by simp; omega))
  have hiv' : i.val = n0.val + 1 := by simpa using hiv
  obtain ⟨c0, hc0, hc0v⟩ := new_counts_spec i
  have hc0len : c0.val.length = n0.val + 1 := by rw [hc0v]; simp [hiv']
  have hc0get : ∀ j, (c0.val.getD j 0#usize).val = 0 := by
    intro j
    rw [hc0v]
    by_cases hj : j < i.val
    · simp [List.getD_eq_getElem?_getD, hj]
    · simp [List.getD_eq_getElem?_getD, hj]
  obtain ⟨counts1, hcount, hcl, hcv⟩ := count_all_incoming_state_spec LTSInst sys sv c0 hiter hout
    (fun s hs t ht => by rw [hc0len]; have := htgt s hs t ht; omega)
    (fun j hj => by rw [hc0get j]; have := hseen_le j; omega)
  have hc1len : counts1.val.length = n0.val + 1 := by rw [hcl, hc0len]
  have hc1get : ∀ j, j < n0.val + 1 →
      (counts1.val.getD j 0#usize).val = seenCount LTSInst sys sv.val sv.val.length j := by
    intro j hj
    rw [hcv j (by omega), hc0get j]; omega
  -- prefix sums stay below `m`
  have hnat : ∀ k, k ≤ n0.val + 1 → natSum counts1.val k ≤ m.val := by
    intro k hk
    rw [natSum_eq_range_sum _ _ (by omega)]
    have h1 : (List.map (fun j => (counts1.val.getD j 0#usize).val) (List.range k))
        = List.map (fun j => (sv.val.map (fun s => toCount (outVec LTSInst sys s).val j)).sum)
            (List.range k) := by
      apply List.map_congr_left
      intro j hj
      rw [hc1get j (by have := List.mem_range.mp hj; omega), seenCount_full]
    rw [h1]
    exact le_trans (sum_seen_range_le LTSInst sys sv.val k) htot
  have hmbits : m.val < 2 ^ UScalarTy.Usize.numBits := lt_two_pow_of_le_max (by omega)
  obtain ⟨r, hps, hrlen, hrget⟩ := prefix_sum_spec counts1 n0 (by omega)
    (fun k hk => le_trans (hnat k (by omega)) (by omega))
  have hrlen' : r.val.length = n0.val + 1 := by rw [hrlen, hc1len]
  have hrv : ∀ k, k ≤ n0.val → (r.val.getD k 0#usize).val = natSum counts1.val k := by
    intro k hk
    rw [hrget k (by omega), uTotal_val_of_lt]
    exact lt_of_le_of_lt (hnat k (by omega)) hmbits
  have hrmono : ∀ i, i + 1 < r.val.length →
      (r.val.getD i 0#usize).val ≤ (r.val.getD (i + 1) 0#usize).val := by
    intro i hi
    rw [hrv i (by omega), hrv (i + 1) (by omega)]
    exact natSum_mono _ (by omega) (by omega)
  have hrfill : ∀ j, j < r.val.length → (r.val.getD j 0#usize).val ≤ labels0.val.length := by
    intro j hj
    rw [hrv j (by omega), hlen0]
    exact hnat j (by omega)
  have hrcsr : ∀ j, j + 1 < r.val.length →
      (r.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j
        = (r.val.getD (j + 1) 0#usize).val := by
    intro j hj
    rw [hrv j (by omega), hrv (j + 1) (by omega), natSum_succ _ _ (by omega),
      ← List.getD_eq_getElem _ 0#usize (by omega), hc1get j (by omega)]
  obtain ⟨cursor, hcp, hcurlen, hcurget⟩ := copy_prefix_ok r n0 (by omega) (by omega)
  obtain ⟨cursor1, labels1, src1, hpl, hpost⟩ := place_all_incoming_spec LTSInst sys sv r cursor
    labels0 src0 hiter (by rw [hcurlen, hsvlen]) (fun k hk => hcurget k (by omega))
    hout (fun s hs t ht => by rw [hrlen']; have := htgt s hs t ht; omega)
    (by rw [hlen0, hslen0]) (by rw [hsvlen, hrlen']) hrmono hrcsr hrfill (by omega)
  obtain ⟨hL1, hS1, hcl1, hcv1, hslot⟩ := hpost
  have hL1' : labels1.val.length = m.val := by rw [hL1, hlen0]
  have hS1' : src1.val.length = m.val := by rw [hS1, hslen0]
  obtain ⟨labels2, src2, hsort, hsl, hss, hswin⟩ := sort_all_incoming_spec r n0 labels1 src1
    (by omega) (by omega) hrmono (fun j hj => by rw [hL1']; exact hrfill j hj |>.trans (by omega))
    (by rw [hL1', hS1']) (by omega)
  have hnew : IncomingTransitions.new LTSInst sys =
      ok ({ transition_labels := labels2, transition_from := src2, state2incoming := r } :
        IncomingTransitions) := by
    unfold IncomingTransitions.new
    simp only [hns, hnt, hl0, hs0, hi, hc0, hcount, hps, hcp, hpl, bind_ok]
    change (do
        let (tl2, tf2) ← verified.merc_lts.incoming_transitions.sort_all_incoming r labels1 src1 n0
        ok ({ transition_labels := tl2, transition_from := tf2, state2incoming := r } :
          IncomingTransitions)) = _
    simp only [hsort, bind_tc_ok]
  refine ⟨_, hnew, sv, hnd, hmem, hrlen', hrmono, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    show (r.val.getD j 0#usize).val ≤ labels2.val.length
    rw [hsl, hL1']; exact hrfill j hj |>.trans (by omega)
  · show labels2.val.length = src2.val.length
    rw [hsl, hss, hL1', hS1']
  · show labels2.val.length ≤ Usize.max
    rw [hsl, hL1']; omega
  · intro j hj x
    show x ∈ slotEntries labels2.val src2.val _ _ ↔ _
    rw [(hswin j hj).1 x]
    have h1 := hslot j (by omega)
    have h2 := hcv1 j (by omega)
    have h3 := hrcsr j (by omega)
    rw [← h3, ← h2, h1]
  · intro j hj
    exact (hswin j hj).2



/-- `IncomingTransitions::new` builds a correct index of the incoming transitions. -/
theorem incoming_transitions_correct {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : WellFormed LTSInst sys) (hfit : ∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
      n.val * (n.val + 2) ≤ Std.Usize.max) (incoming : IncomingTransitions)
    (hinc : IncomingTransitions.new LTSInst sys = ok incoming) :
    IncomingTransitionsCorrect LTSInst sys incoming := by
  intro n hns s hs
  obtain ⟨incoming', hinc', sv, hnd, hmem, hrlen, hrmono, hrfill, hlens, hlmax, hwin, -⟩ :=
    incoming_new_structure LTSInst sys hwf hfit n hns
  have hii : incoming' = incoming := by
    have := hinc'.symm.trans hinc; simpa using this
  subst hii
  obtain ⟨n0, hn0, hnpos⟩ := hwf.1
  have hnn : n0 = n := by have := hn0.symm.trans hns; simpa using this
  subst hnn
  have hn2 := hfit n0 hns
  have hnmax : n0.val ≤ Usize.max := by scalar_tac
  have hN2 : n0.val + 2 ≤ Usize.max := by
    have : n0.val + 2 ≤ n0.val * (n0.val + 2) := Nat.le_mul_of_pos_left _ hnpos
    omega
  have hsvlen : sv.val.length = n0.val := by
    have hNbits : n0.val < 2 ^ UScalarTy.Usize.numBits := lt_two_pow_of_le_max hnmax
    exact states_length sv.val n0.val hNbits hnd hmem
  obtain ⟨res, hres, hresv⟩ := incoming_transitions_spec incoming' s (by omega)
    (hrmono _ (by omega)) (hrfill _ (by omega)) hlens hlmax
  refine ⟨res, hres, ?_⟩
  have hiff : ∀ i : FromTransition, i ∈ res.val ↔
      ∃ μ s', s'.index.val < n0.val ∧ tr LTSInst sys s' μ s ∧ (i.label, i.«from») = (μ, s') := by
    intro i
    rw [hresv, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hwin s.index.val hs p] at hp
      rw [towards, List.mem_flatMap] at hp
      obtain ⟨s', hs', hp⟩ := hp
      rw [List.mem_map] at hp
      obtain ⟨t, ht, hpt⟩ := hp
      rw [List.mem_filter] at ht
      rw [List.take_length] at hs'
      have hs'n : s'.index.val < n0.val := (hmem s').1 hs'
      obtain ⟨ts, hts, -⟩ := hwf.2.1 n0 hns s' hs'n
      refine ⟨t.label, s', hs'n, ⟨ts, hts, ?_⟩, ?_⟩
      · have ht1 := ht.1
        rw [outVec_of_ok LTSInst sys s' ts hts] at ht1
        have hto : t.to = s := merc_utilities.tagged_index.TagIndex.ext
          (UScalar.eq_of_val_eq (of_decide_eq_true ht.2))
        have : t = ({ label := t.label, «to» := s } : Transition) := by
          cases t; simp_all
        rw [← this]; exact ht1
      · rw [← hpt]
    · rintro ⟨μ, s', hs'n, ⟨ts, hts, hmt⟩, heq⟩
      refine ⟨(μ, s'), ?_, ?_⟩
      · rw [hwin s.index.val hs, towards, List.take_length, List.mem_flatMap]
        refine ⟨s', (hmem s').2 hs'n, ?_⟩
        rw [List.mem_map]
        refine ⟨{ label := μ, «to» := s }, ?_, rfl⟩
        rw [List.mem_filter, outVec_of_ok LTSInst sys s' ts hts]
        exact ⟨hmt, by simp⟩
      · cases i; simpa using heq.symm
  refine ⟨fun i hi => ?_, hiff⟩
  obtain ⟨μ, s', hs', -, heq⟩ := (hiff i).1 hi
  have := congrArg Prod.snd heq
  simp only at this
  rw [this]; exact hs'

/-- `IncomingTransitions::new` never fails on a well-formed LTS. -/
theorem incoming_new_ok {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : WellFormed LTSInst sys) (hfit : ∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
      n.val * (n.val + 2) ≤ Std.Usize.max) :
    ∃ incoming, IncomingTransitions.new LTSInst sys = ok incoming := by
  obtain ⟨n, hns, -⟩ := hwf.1
  obtain ⟨incoming, hinc, -⟩ := incoming_new_structure LTSInst sys hwf hfit n hns
  exact ⟨incoming, hinc⟩

end MercVerified.Lts.Proofs
