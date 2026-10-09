import MercVerified.Refinement.Proofs.SccRust_Proofs
import MercVerified.Lts.Proofs.LtsData_Proofs
import MercVerified.Refinement.Proofs.QuotientSort_Proofs

/-!
# `quotient_lts_naive` computes the τ-SCC quotient

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_collections.indexed_partition (IndexedPartition BlockTag)
open MercVerified.Lts.Proofs MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

abbrev QElem := TagIndex Std.Usize LabelTag × TagIndex Std.Usize StateTag

theorem ip_block_number (ip : IndexedPartition) (st : TagIndex Std.Usize StateTag)
    (h : st.index.val < ip.partition.val.length) :
    verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition.block_number
      ip st = ok (ip.partition.val[st.index.val]'h) := by
  unfold verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition.block_number
  simp only [tag_value_id, bind_ok]
  unfold verified.merc_collections.indexed_partition.IndexedPartition.block
  exact vec_index_ok' _ _ h

theorem ip_num_of_blocks (ip : IndexedPartition) :
    verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition.num_of_blocks
      ip = ok ip.num_of_blocks := rfl

section Collect

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

/-- The pair pushed for a kept transition. -/
def qelem (ip : IndexedPartition) (t : Transition) (h : t.to.index.val < ip.partition.val.length) : QElem :=
  (t.label, ({ index := (ip.partition.val[t.to.index.val]'h).index, marker := () } : TagIndex Std.Usize StateTag))

/-- Whether the quotient keeps the transition `t` of the state `s` (both elimination flags set). -/
def qkeep (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag) (t : Transition)
    (hs : s.index.val < ip.partition.val.length) (h : t.to.index.val < ip.partition.val.length) : Prop :=
  ¬ (t.label.index.val = 0 ∧
    (ip.partition.val[s.index.val]'hs).index.val = (ip.partition.val[t.to.index.val]'h).index.val)

open verified.merc_reduction.quotient in
theorem coll_body_spec
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag)
    (hs : s.index.val < ip.partition.val.length) (t : Transition) (rest : List Transition)
    (ht : t.to.index.val < ip.partition.val.length)
    (it : alloc.vec.into_iter.IntoIter Transition) (hit : it.val = t :: rest)
    (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem))
    (hb : (ip.partition.val[s.index.val]'hs).index.val < outgoing.val.length)
    (hpl : (outgoing.val[(ip.partition.val[s.index.val]'hs).index.val]'hb).val.length < Std.Usize.max) :
    ∃ it1 out1, quotient_collect_transitions_loop0_loop0_loop0.body LTSInst
        verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
        sys ip true true s it outgoing = ok (cont (it1, out1)) ∧ it1.val = rest ∧
      ((qkeep ip s t hs ht ∧ ∃ v1 : alloc.vec.Vec QElem,
          v1.val = (outgoing.val[(ip.partition.val[s.index.val]'hs).index.val]'hb).val ++ [qelem ip t ht] ∧
          out1.val = outgoing.val.set (ip.partition.val[s.index.val]'hs).index.val v1) ∨
        (¬ qkeep ip s t hs ht ∧ out1.val = outgoing.val)) := by
  obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' it t rest hit
  have hbn1 := ip_block_number ip s hs
  have hbn2 := ip_block_number ip t.to ht
  have hmut := vec_index_mut_usize_ok outgoing (ip.partition.val[s.index.val]'hs).index hb
  obtain ⟨v1, hpush, hv1⟩ := vec_push_val (outgoing.val[(ip.partition.val[s.index.val]'hs).index.val]'hb)
    (qelem ip t ht) hpl
  unfold qelem at hpush hv1
  have hset : ∀ (v : alloc.vec.Vec QElem), (vset outgoing (ip.partition.val[s.index.val]'hs).index v).val =
      outgoing.val.set (ip.partition.val[s.index.val]'hs).index.val v := fun v => vset_val _ _ _
  by_cases hk : qkeep ip s t hs ht
  · have hk' : t.label.index.val = 0 →
        (ip.partition.val[s.index.val]'hs).index.val ≠ (ip.partition.val[t.to.index.val]'ht).index.val := by
      intro h1 h2; exact hk ⟨h1, h2⟩
    refine ⟨it1, vset outgoing (ip.partition.val[s.index.val]'hs).index v1, ?_, hit1, Or.inl ⟨hk, v1, ?_, hset v1⟩⟩
    · unfold quotient_collect_transitions_loop0_loop0_loop0.body
      by_cases hh : t.label.index.val = 0
      · have hbb : ¬ ((ip.partition.val[s.index.val]'hs).index = (ip.partition.val[t.to.index.val]'ht).index) :=
          fun e => hk' hh (congrArg UScalar.val e)
        have hne : ¬ (s.index = t.to.index) := by
          intro e
          apply hbb
          have : s.index.val = t.to.index.val := congrArg UScalar.val e
          simp only [this]
        simp [hnext, hbn1, hbn2, hid, tag_ne_ok, hmut, hpush, hh, hbb, hne]
        rfl
      · simp [hnext, hbn1, hbn2, hid, tag_ne_ok, hmut, hpush, hh]
        rfl
    · rw [hv1]; rfl
  · have hk' : t.label.index.val = 0 ∧
        (ip.partition.val[s.index.val]'hs).index.val = (ip.partition.val[t.to.index.val]'ht).index.val := by
      by_contra hc; exact hk hc
    obtain ⟨hh, hbb⟩ := hk'
    have hbb' : (ip.partition.val[s.index.val]'hs).index = (ip.partition.val[t.to.index.val]'ht).index :=
      UScalar.eq_of_val_eq hbb
    refine ⟨it1, outgoing, ?_, hit1, Or.inr ⟨hk, rfl⟩⟩
    unfold quotient_collect_transitions_loop0_loop0_loop0.body
    by_cases hst : s.index = t.to.index
    · simp [hnext, hbn1, hbn2, hid, tag_ne_ok, hh, hst]
    · have hst' : ¬ (s.index.val = t.to.index.val) := fun e => hst (UScalar.eq_of_val_eq e)
      simp [hnext, hbn1, hbn2, hid, tag_ne_ok, hh, hbb', hst, hst']

/-- The block of an element (the stored entry, default when out of range). -/
def bk (ip : IndexedPartition) (i : Nat) : TagIndex Std.Usize BlockTag := ip.partition.val.getD i default

def keepB (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag) (t : Transition) : Bool :=
  !(decide (t.label.index.val = 0) && decide ((bk ip s.index.val).index.val = (bk ip t.to.index.val).index.val))

def elemD (ip : IndexedPartition) (t : Transition) : QElem :=
  (t.label, ({ index := (bk ip t.to.index.val).index, marker := () } : TagIndex Std.Usize StateTag))

/-- The pairs the quotient keeps from the transitions `l` of the state `s`. -/
def keptList (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag) (l : List Transition) : List QElem :=
  l.filterMap fun t => if keepB ip s t then some (elemD ip t) else none

theorem keptList_cons (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag) (t : Transition)
    (l : List Transition) :
    keptList ip s (t :: l) = (if keepB ip s t then [elemD ip t] else []) ++ keptList ip s l := by
  unfold keptList
  simp only [List.filterMap_cons]
  split_ifs <;> simp

theorem keepB_iff (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag) (t : Transition)
    (hs : s.index.val < ip.partition.val.length) (ht : t.to.index.val < ip.partition.val.length) :
    keepB ip s t = true ↔ qkeep ip s t hs ht := by
  unfold keepB qkeep bk
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, List.getElem?_eq_getElem ht]
  tauto

theorem elemD_eq (ip : IndexedPartition) (t : Transition) (ht : t.to.index.val < ip.partition.val.length) :
    elemD ip t = qelem ip t ht := by
  unfold elemD qelem bk
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

/-- The list stored in row `b` of the outgoing table. -/
def rowOf (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem)) (b : Nat) : List QElem :=
  (outgoing.val[b]?.map (fun v => v.val)).getD []

theorem rowOf_set (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem)) (b : Nat) (hb : b < outgoing.val.length)
    (v : alloc.vec.Vec QElem) (out1 : alloc.vec.Vec (alloc.vec.Vec QElem))
    (h : out1.val = outgoing.val.set b v) : rowOf out1 b = v.val := by
  unfold rowOf
  rw [h]; simp [hb]

open verified.merc_reduction.quotient in
theorem coll_inner_spec
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag)
    (hs : s.index.val < ip.partition.val.length) (K : Nat) (hbK : (bk ip s.index.val).index.val < K) :
    ∀ (l : List Transition), (∀ t ∈ l, t.to.index.val < ip.partition.val.length) →
      ∀ (it : alloc.vec.into_iter.IntoIter Transition) (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem)),
        it.val = l → outgoing.val.length = K →
        (rowOf outgoing (bk ip s.index.val).index.val).length + l.length < Std.Usize.max →
        ∃ (out1 : alloc.vec.Vec (alloc.vec.Vec QElem)) (vb : alloc.vec.Vec QElem),
          quotient_collect_transitions_loop0_loop0_loop0 LTSInst
            verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
            it sys ip true true outgoing s = ok out1 ∧
          out1.val = outgoing.val.set (bk ip s.index.val).index.val vb ∧
          vb.val = rowOf outgoing (bk ip s.index.val).index.val ++ keptList ip s l := by
  intro l
  induction l with
  | nil =>
    intro _ it outgoing hit hlen _
    have hbl : (bk ip s.index.val).index.val < outgoing.val.length := by rw [hlen]; exact hbK
    refine ⟨outgoing, outgoing.val[(bk ip s.index.val).index.val]'hbl, ?_, ?_, ?_⟩
    · unfold quotient_collect_transitions_loop0_loop0_loop0
      apply loop_done'
      show quotient_collect_transitions_loop0_loop0_loop0.body LTSInst _ sys ip true true s it outgoing = _
      unfold quotient_collect_transitions_loop0_loop0_loop0.body
      rw [into_iter_next_none' it hit]
      simp
    · simp
    · unfold rowOf
      simp [hbl, keptList]
  | cons t rest ih =>
    intro hl it outgoing hit hlen hcap
    have ht : t.to.index.val < ip.partition.val.length := hl t (by simp)
    have hlrest : ∀ t' ∈ rest, t'.to.index.val < ip.partition.val.length := fun t' h => hl t' (by simp [h])
    have hbl : (bk ip s.index.val).index.val < outgoing.val.length := by rw [hlen]; exact hbK
    have hrow : (rowOf outgoing (bk ip s.index.val).index.val).length =
        (outgoing.val[(bk ip s.index.val).index.val]'hbl).val.length := by
      unfold rowOf; simp [hbl]
    have hcap' : (outgoing.val[(bk ip s.index.val).index.val]'hbl).val.length < Std.Usize.max := by
      simp at hcap; omega
    have hbs : bk ip s.index.val = ip.partition.val[s.index.val]'hs := List.getD_eq_getElem _ _ hs
    have hbl' : (ip.partition.val[s.index.val]'hs).index.val < outgoing.val.length := by
      rw [← hbs]; exact hbl
    have hcap'' : (outgoing.val[(ip.partition.val[s.index.val]'hs).index.val]'hbl').val.length <
        Std.Usize.max := by
      have : (outgoing.val[(bk ip s.index.val).index.val]'hbl) =
          (outgoing.val[(ip.partition.val[s.index.val]'hs).index.val]'hbl') := by simp [hbs]
      rw [← this]; exact hcap'
    obtain ⟨it1, out1, hbody, hit1, hres⟩ := coll_body_spec LTSInst sys hid ip s hs t rest ht it hit
      outgoing hbl' hcap''
    have hkeep := keepB_iff ip s t hs ht
    have hel := elemD_eq ip t ht
    have hrowb : rowOf outgoing (bk ip s.index.val).index.val =
        (outgoing.val[(ip.partition.val[s.index.val]'hs).index.val]'hbl').val := by
      unfold rowOf; simp [hbs, hbl']
    rcases hres with ⟨hq, v1, hv1, hout⟩ | ⟨hq, hout⟩
    · have hkb : keepB ip s t = true := hkeep.2 hq
      have hlen1 : out1.val.length = K := by rw [hout]; simpa using hlen
      have hr1 : rowOf out1 (bk ip s.index.val).index.val = v1.val := by
        rw [hbs]; exact rowOf_set outgoing _ hbl' v1 out1 hout
      obtain ⟨out2, vb2, hl2, ho2, hv2⟩ := ih hlrest it1 out1 hit1 hlen1
        (by rw [hr1, hv1, ← hrowb]; simp at hcap; simp; omega)
      refine ⟨out2, vb2, ?_, ?_, ?_⟩
      · unfold quotient_collect_transitions_loop0_loop0_loop0 at hl2 ⊢
        rw [loop_cont' _ _ _ hbody]
        exact hl2
      · rw [ho2, hout, ← hbs]; simp
      · rw [hv2, hr1, hv1, ← hrowb, keptList_cons, hkb, ← hel]; simp
    · have hkb : ¬ keepB ip s t = true := fun h => hq (hkeep.1 h)
      have hlen1 : out1.val.length = K := by rw [hout]; exact hlen
      have hr1 : rowOf out1 (bk ip s.index.val).index.val = rowOf outgoing (bk ip s.index.val).index.val := by
        unfold rowOf; rw [hout]
      obtain ⟨out2, vb2, hl2, ho2, hv2⟩ := ih hlrest it1 out1 hit1 hlen1
        (by rw [hr1]; simp at hcap; omega)
      refine ⟨out2, vb2, ?_, ?_, ?_⟩
      · unfold quotient_collect_transitions_loop0_loop0_loop0 at hl2 ⊢
        rw [loop_cont' _ _ _ hbody]
        exact hl2
      · rw [ho2, hout]
      · rw [hv2, hr1, keptList_cons]
        simp [hkb]

/-- What rows the first states of the iteration have contributed. -/
def rowAcc (ip : IndexedPartition) (tsOf : TagIndex Std.Usize StateTag → List Transition)
    (ps : List (TagIndex Std.Usize StateTag)) (c : Nat) : List QElem :=
  ps.flatMap fun s => if (bk ip s.index.val).index.val = c then keptList ip s (tsOf s) else []

theorem rowAcc_len_le (ip : IndexedPartition) (tsOf : TagIndex Std.Usize StateTag → List Transition)
    (ps : List (TagIndex Std.Usize StateTag)) (c : Nat) :
    (rowAcc ip tsOf ps c).length ≤ (ps.map (fun s => (tsOf s).length)).sum := by
  induction ps with
  | nil => simp [rowAcc]
  | cons s ps ih =>
    unfold rowAcc at ih ⊢
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    have : (if (bk ip s.index.val).index.val = c then keptList ip s (tsOf s) else []).length ≤
        (tsOf s).length := by
      split_ifs
      · unfold keptList
        exact (List.length_filterMap_le _ _)
      · simp
    omega

theorem rowAcc_append (ip : IndexedPartition) (tsOf : TagIndex Std.Usize StateTag → List Transition)
    (a b : List (TagIndex Std.Usize StateTag)) (c : Nat) :
    rowAcc ip tsOf (a ++ b) c = rowAcc ip tsOf a c ++ rowAcc ip tsOf b c := by
  unfold rowAcc; simp

open verified.merc_reduction.quotient in
theorem coll_states_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (ip : IndexedPartition) (hip : ip.partition.val.length = n0.val) (K : Nat)
    (hbK : ∀ s : TagIndex Std.Usize StateTag, s.index.val < n0.val → (bk ip s.index.val).index.val < K) :
    ∀ (l pre : List (TagIndex Std.Usize StateTag)), (∀ s ∈ l, s.index.val < n0.val) →
      ∀ (it : alloc.vec.into_iter.IntoIter (TagIndex Std.Usize StateTag))
        (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem)),
        it.val = l → outgoing.val.length = K →
        (∀ c, rowOf outgoing c = rowAcc ip (fun s => (outVec LTSInst sys s).val) pre c) →
        (((pre ++ l).map (fun s => (outVec LTSInst sys s).val.length)).sum < Std.Usize.max) →
        ∃ out1 : alloc.vec.Vec (alloc.vec.Vec QElem),
          quotient_collect_transitions_loop0_loop0 LTSInst
            verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
            it sys ip true true outgoing = ok out1 ∧ out1.val.length = K ∧
          ∀ c, rowOf out1 c = rowAcc ip (fun s => (outVec LTSInst sys s).val) (pre ++ l) c := by
  intro l
  induction l with
  | nil =>
    intro pre _ it outgoing hit hlen hrows _
    refine ⟨outgoing, ?_, hlen, by simpa using hrows⟩
    unfold quotient_collect_transitions_loop0_loop0
    apply loop_done'
    show quotient_collect_transitions_loop0_loop0.body LTSInst _ sys ip true true it outgoing = _
    unfold quotient_collect_transitions_loop0_loop0.body
    rw [into_iter_next_none' it hit]
    simp
  | cons s rest ih =>
    intro pre hl it outgoing hit hlen hrows hcap
    have hs : s.index.val < n0.val := hl s (by simp)
    have hlrest : ∀ s' ∈ rest, s'.index.val < n0.val := fun s' h => hl s' (by simp [h])
    obtain ⟨ts, hts, htlt⟩ := hwf.2.1 n0 hns s hs
    have hov := outVec_of_ok LTSInst sys s ts hts
    have hsip : s.index.val < ip.partition.val.length := by rw [hip]; exact hs
    obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' it s rest hit
    have hts' : ∀ t ∈ (outVec LTSInst sys s).val, t.to.index.val < ip.partition.val.length := by
      intro t ht; rw [hip, hov] at *; exact htlt t ht
    have hbs := hbK s hs
    have hrowle : (rowOf outgoing (bk ip s.index.val).index.val).length ≤
        (pre.map (fun s => (outVec LTSInst sys s).val.length)).sum := by
      rw [hrows]; exact rowAcc_len_le ip _ pre _
    have hcapin : (rowOf outgoing (bk ip s.index.val).index.val).length +
        (outVec LTSInst sys s).val.length < Std.Usize.max := by
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hcap
      omega
    obtain ⟨iter, hiter, hiterv⟩ : ∃ iter : alloc.vec.into_iter.IntoIter Transition,
        alloc.vec.IntoIteratorVec.into_iter (outVec LTSInst sys s) = ok iter ∧
        iter.val = (outVec LTSInst sys s).val := ⟨_, rfl, rfl⟩
    obtain ⟨outI, vb, hI, hIv, hvb⟩ := coll_inner_spec LTSInst sys hid ip s hsip K hbs
      (outVec LTSInst sys s).val hts' iter outgoing hiterv hlen hcapin
    have hout := outVec_eq_ok LTSInst sys s ts hts
    have hlenI : outI.val.length = K := by rw [hIv]; simpa using hlen
    have hbody : quotient_collect_transitions_loop0_loop0.body LTSInst
        verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
        sys ip true true it outgoing = ok (cont (it1, outI)) := by
      unfold quotient_collect_transitions_loop0_loop0.body
      simp [hnext, hout, hiter, hI]
    have hbl : (bk ip s.index.val).index.val < outgoing.val.length := by rw [hlen]; exact hbs
    have hrowsI : ∀ c, rowOf outI c = rowAcc ip (fun s => (outVec LTSInst sys s).val) (pre ++ [s]) c := by
      intro c
      rw [rowAcc_append]
      by_cases hc : (bk ip s.index.val).index.val = c
      · subst hc
        rw [show rowOf outI _ = vb.val from rowOf_set outgoing _ hbl vb outI hIv, hvb, hrows]
        simp [rowAcc]
      · have : rowOf outI c = rowOf outgoing c := by
          unfold rowOf
          rw [hIv]
          simp [Ne.symm hc]
        rw [this, hrows]
        simp [rowAcc, hc]
    have hcap2 : (((pre ++ [s]) ++ rest).map (fun s => (outVec LTSInst sys s).val.length)).sum <
        Std.Usize.max := by simpa using hcap
    obtain ⟨out2, hl2, hlen2, hr2⟩ := ih (pre ++ [s]) hlrest it1 outI hit1 hlenI hrowsI hcap2
    refine ⟨out2, ?_, hlen2, ?_⟩
    · unfold quotient_collect_transitions_loop0_loop0 at hl2 ⊢
      rw [loop_cont' _ _ _ hbody]
      exact hl2
    · intro c
      rw [hr2 c]
      simp

open verified.merc_reduction.quotient in
theorem collect_loop0_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (ip : IndexedPartition) (hip : ip.partition.val.length = n0.val)
    (hbK : ∀ s : TagIndex Std.Usize StateTag, s.index.val < n0.val →
      (bk ip s.index.val).index.val < ip.num_of_blocks.val)
    (sv : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (hsv : LTSInst.iter_states sys = ok sv)
    (hmem : ∀ s, s ∈ sv.val ↔ s.index.val < n0.val)
    (hsum' : (sv.val.map (fun s => (outVec LTSInst sys s).val.length)).sum < Std.Usize.max) :
    ∃ out : alloc.vec.Vec (alloc.vec.Vec QElem),
      quotient_collect_transitions_loop0 LTSInst
        verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
        { start := 0#usize, «end» := ip.num_of_blocks } sys ip true true
        (alloc.vec.Vec.new (alloc.vec.Vec QElem)) = ok out ∧ out.val.length = ip.num_of_blocks.val ∧
      ∀ c, rowOf out c = rowAcc ip (fun s => (outVec LTSInst sys s).val) sv.val c := by
  unfold quotient_collect_transitions_loop0
  have hspec := range_loop_spec (σ := alloc.vec.Vec (alloc.vec.Vec QElem))
    (ρ := alloc.vec.Vec (alloc.vec.Vec QElem))
    (fun x => quotient_collect_transitions_loop0.body LTSInst
      verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
      sys ip true true x.1 x.2)
    (fun i out => out.val.length = i ∧ ∀ c, rowOf out c = [])
    (fun r => r.val.length = ip.num_of_blocks.val ∧
      ∀ c, rowOf r c = rowAcc ip (fun s => (outVec LTSInst sys s).val) sv.val c)
    ip.num_of_blocks ?hsome ?hnone 0#usize
    (alloc.vec.Vec.new (alloc.vec.Vec QElem)) (by simp) ?h0
  case h0 => exact ⟨by simp [alloc.vec.Vec.new], fun c => by simp [rowOf, alloc.vec.Vec.new]⟩
  case hsome =>
    intro i out hi hinv
    obtain ⟨hl, hr⟩ := hinv
    obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some
      ({ start := i, «end» := ip.num_of_blocks } : core.ops.range.Range Std.Usize) (by simpa using hi)
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := ip.num_of_blocks } := by rw [he1]
    rw [hit1] at hnext
    obtain ⟨out1, hp, hv⟩ := vec_push_val out (alloc.vec.Vec.new QElem) (by
      have h1 : ip.num_of_blocks.val ≤ Std.Usize.max := by scalar_tac
      have h2 : i.val < ip.num_of_blocks.val := hi
      rw [hl]; omega)
    refine ⟨st1, out1, hs1, ?_, ?_, ?_⟩
    · unfold quotient_collect_transitions_loop0.body
      simp [hnext, hsome, hp]
    · simp [hv, hl]
    · intro c
      unfold rowOf
      rw [hv]
      by_cases hc : c < out.val.length
      · rw [List.getElem?_append_left hc]; have := hr c; unfold rowOf at this; exact this
      · simp only [List.getElem?_append_right (by omega : out.val.length ≤ c)]
        by_cases hc2 : c - out.val.length = 0 <;> simp [hc2, alloc.vec.Vec.new]
  case hnone =>
    intro i out hi hinv
    obtain ⟨hl, hr⟩ := hinv
    obtain ⟨o, it1, hnext, hone, hident⟩ := MercVerified.Lts.Proofs.next_range_none
      ({ start := i, «end» := ip.num_of_blocks } : core.ops.range.Range Std.Usize) (by simp [hi])
    obtain ⟨iter, hiter, hiterv⟩ : ∃ iter : alloc.vec.into_iter.IntoIter (TagIndex Std.Usize StateTag),
        alloc.vec.IntoIteratorVec.into_iter sv = ok iter ∧ iter.val = sv.val := ⟨_, rfl, rfl⟩
    obtain ⟨out2, hl2, hlen2, hr2⟩ := coll_states_spec LTSInst sys hwf n0 hns hid ip hip ip.num_of_blocks.val hbK
      sv.val [] (fun s hs => (hmem s).1 hs) iter out hiterv (by rw [hl, hi])
      (fun c => by rw [hr c]; simp [rowAcc]) (by simpa using hsum')
    refine ⟨out2, ?_, hlen2, fun c => by simpa using hr2 c⟩
    unfold quotient_collect_transitions_loop0.body
    simp [hnext, hone, hsv, hiter, hl2]
  obtain ⟨r, hr, hp⟩ := hspec
  exact ⟨r, hr, hp.1, hp.2⟩

open verified.merc_reduction.quotient in
theorem collect_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (ip : IndexedPartition) (hip : ip.partition.val.length = n0.val)
    (hbK : ∀ s : TagIndex Std.Usize StateTag, s.index.val < n0.val →
      (bk ip s.index.val).index.val < ip.num_of_blocks.val) :
    ∃ (sv : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem)),
      LTSInst.iter_states sys = ok sv ∧ sv.val.Nodup ∧ (∀ s, s ∈ sv.val ↔ s.index.val < n0.val) ∧
      quotient_collect_transitions LTSInst
        verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
        sys ip true true = ok outgoing ∧ outgoing.val.length = ip.num_of_blocks.val ∧
      ∀ c, rowOf outgoing c = rowAcc ip (fun s => (outVec LTSInst sys s).val) sv.val c := by
  obtain ⟨sv, m, hsv, hnd, hmem, hm, hmlt, hsum⟩ := hwf.2.2 n0 hns
  have hsum' : (sv.val.map (fun s => (outVec LTSInst sys s).val.length)).sum < Std.Usize.max := by
    have := hsum (fun s => outVec LTSInst sys s) (fun s hs => by
      obtain ⟨ts, hts, _⟩ := hwf.2.1 n0 hns s ((hmem s).1 hs)
      exact outVec_eq_ok LTSInst sys s ts hts)
    exact lt_of_le_of_lt this hmlt
  obtain ⟨r, hr, hl, hp⟩ := collect_loop0_spec LTSInst sys hwf n0 hns hid ip hip hbK sv hsv hmem hsum'
  refine ⟨sv, r, hsv, hnd, hmem, ?_, hl, hp⟩
  unfold quotient_collect_transitions
  simp only [ip_num_of_blocks, bind_ok]
  exact hr

end Collect

section Build

open merc_collections.compressed_vec (ByteCompressedVec)
open verified.merc_reduction.quotient

open verified.merc_lts.lts (StateTag LabelTag)

theorem push_transitions_loop_spec (transitions : Slice QElem) :
    ∀ (m : Nat) (iter : core.ops.range.Range Std.Usize)
      (lb : ByteCompressedVec (TagIndex Std.Usize LabelTag))
      (tb : ByteCompressedVec (TagIndex Std.Usize StateTag)),
      iter.«end».val - iter.start.val = m → iter.«end».val ≤ transitions.val.length →
      (ByteCompressedVec.toList lb).length + m < Std.Usize.max →
      (ByteCompressedVec.toList tb).length + m < Std.Usize.max →
      ∃ lb' tb', push_transitions_loop iter transitions lb tb = ok (lb', tb') ∧
        ByteCompressedVec.toList lb' = ByteCompressedVec.toList lb ++
          ((transitions.val.drop iter.start.val).take m).map Prod.fst ∧
        ByteCompressedVec.toList tb' = ByteCompressedVec.toList tb ++
          ((transitions.val.drop iter.start.val).take m).map Prod.snd := by
  intro m
  induction m with
  | zero =>
    intro iter lb tb hm hend _ _
    refine ⟨lb, tb, ?_, by simp, by simp⟩
    unfold push_transitions_loop
    apply loop_done'
    show push_transitions_loop.body transitions iter lb tb = _
    have hge : iter.start.val ≥ iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hident⟩ := next_range_none iter hge
    unfold push_transitions_loop.body
    rw [hnext, ho]
    simp
  | succ m ih =>
    intro iter lb tb hm hend hl ht
    have hlt : iter.start.val < iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hstart', hend'⟩ := next_range_some iter hlt
    have hi : iter.start.val < transitions.val.length := by omega
    obtain ⟨x1, x2, hel⟩ : ∃ x1 x2, transitions.val[iter.start.val]'hi = (x1, x2) := ⟨_, _, rfl⟩
    obtain ⟨lb1, hp1, hv1⟩ := merc_collections.compressed_vec.ByteCompressedVec.push_spec LIdx lb
      x1 (by omega)
    obtain ⟨tb1, hp2, hv2⟩ := merc_collections.compressed_vec.ByteCompressedVec.push_spec SIdx tb
      x2 (by omega)
    have hn1 : iter1.«end».val - iter1.start.val = m := by
      have : iter1.«end».val = iter.«end».val := by rw [hend']
      omega
    obtain ⟨lb', tb', hloop, hlb, htb⟩ := ih iter1 lb1 tb1 hn1 (by rw [hend']; exact hend)
      (by rw [hv1]; simp; omega) (by rw [hv2]; simp; omega)
    refine ⟨lb', tb', ?_, ?_, ?_⟩
    · unfold push_transitions_loop at hloop ⊢
      have hb : push_transitions_loop.body transitions iter lb tb = ok (cont (iter1, lb1, tb1)) := by
        unfold push_transitions_loop.body
        have hidx : Slice.index_usize transitions iter.start = ok (transitions.val[iter.start.val]'hi) :=
          slice_index_ok transitions iter.start hi
        simp [hnext, ho, hidx, hel, hp1, hp2]
      rw [loop_cont' _ _ _ hb]
      exact hloop
    · rw [hlb, hv1, hstart']
      have : (transitions.val.drop iter.start.val).take (m + 1) =
          (x1, x2) :: (transitions.val.drop (iter.start.val + 1)).take m := by
        rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, hel]
      rw [this]; simp
    · rw [htb, hv2, hstart']
      have : (transitions.val.drop iter.start.val).take (m + 1) =
          (x1, x2) :: (transitions.val.drop (iter.start.val + 1)).take m := by
        rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, hel]
      rw [this]; simp

theorem push_transitions_spec (transitions : Slice QElem)
    (lb : ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (tb : ByteCompressedVec (TagIndex Std.Usize StateTag))
    (hl : (ByteCompressedVec.toList lb).length + transitions.val.length < Std.Usize.max)
    (ht : (ByteCompressedVec.toList tb).length + transitions.val.length < Std.Usize.max) :
    ∃ lb' tb', push_transitions transitions lb tb = ok (lb', tb') ∧
      ByteCompressedVec.toList lb' = ByteCompressedVec.toList lb ++ transitions.val.map Prod.fst ∧
      ByteCompressedVec.toList tb' = ByteCompressedVec.toList tb ++ transitions.val.map Prod.snd := by
  have hlen : (Slice.len transitions).val = transitions.val.length := by simp [Slice.len]
  obtain ⟨lb', tb', h, h1, h2⟩ := push_transitions_loop_spec transitions transitions.val.length
    { start := 0#usize, «end» := Slice.len transitions } lb tb (by simp [hlen]) (by simp [hlen])
    hl ht
  refine ⟨lb', tb', ?_, by simpa using h1, by simpa using h2⟩
  unfold push_transitions
  exact h

/-- The sum of the first `i` row lengths. -/
def tot (out0 : alloc.vec.Vec (alloc.vec.Vec QElem)) (i : Nat) : Nat :=
  ((List.range i).map (fun b => (rowOf out0 b).length)).sum

/-- The offsets of the first `i` blocks given the sorted rows `Ls`. -/
def offs (Ls : List (List QElem)) (i : Nat) : List Nat :=
  (List.range i).map (fun j => ((Ls.take j).flatten).length)

structure BuildInv (out0 : alloc.vec.Vec (alloc.vec.Vec QElem)) (K i : Nat) (Ls : List (List QElem))
    (out : alloc.vec.Vec (alloc.vec.Vec QElem))
    (st : ByteCompressedVec Std.Usize) (lb : ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (tb : ByteCompressedVec (TagIndex Std.Usize StateTag)) : Prop where
  hLs : Ls.length = i
  sorted : ∀ b (hb : b < i), List.Pairwise qLt (Ls[b]'(by omega))
  mem : ∀ b (hb : b < i), ∀ x, x ∈ Ls[b]'(by omega) ↔ x ∈ rowOf out0 b
  olen : out.val.length = K
  rowlt : ∀ b (hb : b < i), rowOf out b = Ls[b]'(by omega)
  rowge : ∀ b, i ≤ b → rowOf out b = rowOf out0 b
  stl : (ByteCompressedVec.toList st).map (fun u : Std.Usize => u.val) = offs Ls i
  lbl : ByteCompressedVec.toList lb = Ls.flatten.map Prod.fst
  tbl : ByteCompressedVec.toList tb = Ls.flatten.map Prod.snd
  tlen : Ls.flatten.length ≤ tot out0 i

theorem tot_succ (out0 : alloc.vec.Vec (alloc.vec.Vec QElem)) (i : Nat) :
    tot out0 (i + 1) = tot out0 i + (rowOf out0 i).length := by
  unfold tot; rw [List.range_succ]; simp

theorem tot_mono (out0 : alloc.vec.Vec (alloc.vec.Vec QElem)) {i K : Nat} (h : i ≤ K) :
    tot out0 i ≤ tot out0 K := by
  induction K, h using Nat.le_induction with
  | base => exact le_refl _
  | succ K _ ih => rw [tot_succ]; omega

theorem qelem_ord_total' : core.cmp.Ord.IsTotalOrder
    (verified.Pair.Insts.CoreCmpOrd
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd StateTag core.cmp.OrdUsize)) :=
  q_ord_total

open verified.merc_reduction.quotient in
theorem build_body_step (out0 : alloc.vec.Vec (alloc.vec.Vec QElem)) (K : Nat) (e i : Std.Usize)
    (he : e.val = K) (hi : i.val < K)
    (hBig : tot out0 K < Std.Usize.max)
    (out : alloc.vec.Vec (alloc.vec.Vec QElem))
    (st : ByteCompressedVec Std.Usize) (lb : ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (tb : ByteCompressedVec (TagIndex Std.Usize StateTag)) (Ls : List (List QElem))
    (hinv : BuildInv out0 K i.val Ls out st lb tb) :
    ∃ (i1 : Std.Usize) (out' : alloc.vec.Vec (alloc.vec.Vec QElem)) (st' : ByteCompressedVec Std.Usize)
      (lb' : ByteCompressedVec (TagIndex Std.Usize LabelTag))
      (tb' : ByteCompressedVec (TagIndex Std.Usize StateTag)) (Ls' : List (List QElem)),
      i1.val = i.val + 1 ∧
      quotient_build_loop.body { start := i, «end» := e } out st lb tb =
        ok (cont ({ start := i1, «end» := e }, out', st', lb', tb')) ∧
      BuildInv out0 K (i.val + 1) Ls' out' st' lb' tb' := by
  obtain ⟨hLs, hsorted, hmem, holen, hrowlt, hrowge, hstl, hlbl, htbl, htlen⟩ := hinv
  have hiK : i.val < out.val.length := by rw [holen]; exact hi
  have hie : i.val < e.val := by omega
  obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some
    ({ start := i, «end» := e } : core.ops.range.Range Std.Usize) hie
  obtain ⟨st1, en1⟩ := it1
  simp only at hs1 he1
  have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
      { start := st1, «end» := e } := by rw [he1]
  rw [hit1] at hnext
  set v := out.val[i.val]'hiK with hvdef
  have hrowi : rowOf out i.val = v.val := by unfold rowOf; simp [hiK, hvdef]
  have hrow0 : rowOf out i.val = rowOf out0 i.val := hrowge i.val (le_refl _)
  have hmut := vec_index_mut_usize_ok out i hiK
  obtain ⟨s1, hs1', hperm, hsort⟩ := core.slice.Slice.sort_unstable_spec
    (verified.Pair.Insts.CoreCmpOrd
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd StateTag core.cmp.OrdUsize))
    qelem_ord_total' v.slice
  set b3 : alloc.vec.Vec QElem := { slice := s1 } with hb3
  obtain ⟨v3, hdedup, hdmem, hdsub, hdchain⟩ := alloc.vec.Vec.dedup_spec (T := QElem) Global
    (verified.Pair.Insts.CoreCmpPartialEqPair
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag core.cmp.PartialEqUsize)
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex StateTag core.cmp.PartialEqUsize))
    q_partialEq_lawful b3
  have hb3v : b3.val = s1.val := rfl
  have hsortv : List.Pairwise (fun a b => qOrd.cmp a b ≠ ok Ordering.gt) v3.val :=
    List.Pairwise.sublist hdsub (by rw [hb3v]; exact hsort)
  have hstrict : List.Pairwise qLt v3.val := q_sorted_chain_strict hsortv hdchain
  have hmemv3 : ∀ x, x ∈ v3.val ↔ x ∈ rowOf out0 i.val := by
    intro x
    rw [hdmem x, hb3v, ← hrow0, hrowi]
    exact (List.Perm.mem_iff hperm)
  have hlen3 : v3.val.length ≤ (rowOf out0 i.val).length := by
    have h1 : v3.val.length ≤ s1.val.length := by
      have := hdsub.length_le
      rwa [hb3v] at this
    have h2 : s1.val.length = v.val.length := by
      have := hperm.length_eq
      simpa [alloc.vec.Vec.val] using this
    rw [← hrow0, hrowi]
    omega
  have hKle : K ≤ Std.Usize.max := by rw [← he]; scalar_tac
  have htotK : tot out0 (i.val + 1) ≤ tot out0 K := tot_mono out0 (by omega)
  have htotS := tot_succ out0 i.val
  have hfl : (ByteCompressedVec.toList lb).length ≤ tot out0 i.val := by
    rw [hlbl, List.length_map]; exact htlen
  have hlbmax : (ByteCompressedVec.toList lb).length ≤ Std.Usize.max := by omega
  obtain ⟨l, hlenl, hlv⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec LIdx lb hlbmax
  have hstlen : (ByteCompressedVec.toList st).length = i.val := by
    have := congrArg List.length hstl
    simpa [offs] using this
  obtain ⟨st2, hpst, hst2⟩ := merc_collections.compressed_vec.ByteCompressedVec.push_spec UIdx st l
    (by omega)
  have hv3sl : (alloc.vec.Vec.deref v3).val = v3.val := vec_deref_val v3
  obtain ⟨lb2, tb2, hpt, hlb2, htb2⟩ := push_transitions_spec (alloc.vec.Vec.deref v3) lb tb
    (by rw [hv3sl]; omega) (by rw [hv3sl, htbl, List.length_map]; omega)
  have hlen1 : i.val < (vset out i b3).val.length := by rw [vset_val]; simpa using hiK
  have hmut2 := vec_index_mut_usize_ok (vset out i b3) i hlen1
  have hget1 : (vset out i b3).val[i.val]'hlen1 = b3 := by simp [vset_val]
  rw [hget1] at hmut2
  have hlen2 : i.val < (vset (vset out i b3) i v3).val.length := by rw [vset_val, vset_val]; simpa using hiK
  have hget2 : (vset (vset out i b3) i v3).val[i.val]'hlen2 = v3 := by simp [vset_val]
  have hidx2 := vec_index_usize_ok (vset (vset out i b3) i v3) i hlen2
  rw [hget2] at hidx2
  refine ⟨st1, vset (vset out i b3) i v3, st2, lb2, tb2, Ls ++ [v3.val], hs1, ?_, ?_⟩
  · unfold quotient_build_loop.body
    simp [hnext, hsome, hlenl, hpst, hmut, Aeneas.Std.lift, alloc.vec.Vec.deref_mut]
    trace_state
    sorry
  · sorry

end Build

end MercVerified.Refinement.Proofs
