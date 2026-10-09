import MercVerified.Refinement.Proofs.BranchingDirty_Proofs
import MercVerified.Refinement.Proofs.BranchingProcess_Proofs
import Aeneas.Std.WP

/-!
# `BlockPartition::mark_backward_closure`

The backwards inert closure of the marked states of a block: the marked states of the block after
the call are exactly the states that reach a marked state of the block along inert τ-steps.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder Block)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- `q` arises from `q0` by marking states of block `b` (the only change is that the marked suffix
of `b` grew; the elements at the previously marked positions did not move). -/
structure Mono (n : Nat) (q0 q : BlockPartition) (b : Nat) : Prop where
  inv : PartInv n q
  e2b : q.element_to_block = q0.element_to_block
  nblocks : q.blocks.val.length = q0.blocks.val.length
  other : ∀ j, j ≠ b → blkAt q j = blkAt q0 j
  begin_eq : (blkAt q b).begin = (blkAt q0 b).begin
  end_eq : (blkAt q b).«end» = (blkAt q0 b).«end»
  ms_le : (blkAt q b).marked_split.val ≤ (blkAt q0 b).marked_split.val
  pos : ∀ i, (blkAt q0 b).marked_split.val ≤ i → eAt q i = eAt q0 i

theorem Mono.refl {n : Nat} {p : BlockPartition} (hp : PartInv n p) (b : Nat) : Mono n p p b :=
  ⟨hp, rfl, rfl, fun _ _ => rfl, rfl, rfl, le_rfl, fun _ _ => rfl⟩

theorem Mono.trans {n : Nat} {q0 q1 q2 : BlockPartition} {b : Nat} (h1 : Mono n q0 q1 b)
    (h2 : Mono n q1 q2 b) : Mono n q0 q2 b :=
  ⟨h2.inv, h2.e2b.trans h1.e2b, h2.nblocks.trans h1.nblocks,
    fun j hj => (h2.other j hj).trans (h1.other j hj),
    h2.begin_eq.trans h1.begin_eq, h2.end_eq.trans h1.end_eq, le_trans h2.ms_le h1.ms_le,
    fun i hi => (h2.pos i (le_trans h1.ms_le hi)).trans (h1.pos i hi)⟩

theorem Mono.e2bAt_eq {n : Nat} {q0 q : BlockPartition} {b : Nat} (h : Mono n q0 q b) (s : Nat) :
    e2bAt q s = e2bAt q0 s := by simp [e2bAt, h.e2b]

/-- Marking one state of block `b` extends `Mono` and marks exactly that state. -/
theorem mono_mark {n : Nat} {q0 q : BlockPartition} {b : Nat} (_hb : b < q0.blocks.val.length)
    (h : Mono n q0 q b) (s : ST) (hs : s.index.val < n) (hsb : e2bAt q0 s.index.val = b) :
    ∃ q', verified.merc_reduction.block_partition.BlockPartition.mark_element q s = ok q' ∧
      Mono n q0 q' b ∧ (∀ t, t < n → (IsMarked q' t ↔ IsMarked q t ∨ t = s.index.val)) := by
  obtain ⟨q', hmk, hp', he2b', hlen', hother, hbeg, hend, hle, hlt, hmark, hpos⟩ :=
    mark_element_spec h.inv s hs
  have hKq : e2bAt q s.index.val = b := by rw [h.e2bAt_eq]; exact hsb
  rw [hKq] at hother hbeg hend hle hlt hpos
  refine ⟨q', hmk, ⟨hp', he2b'.trans h.e2b, hlen'.trans h.nblocks, fun j hj => ?_, ?_, ?_, ?_, ?_⟩,
    hmark⟩
  · rw [hother j hj, h.other j hj]
  · rw [hbeg, h.begin_eq]
  · rw [hend, h.end_eq]
  · exact le_trans hle h.ms_le
  · intro i hi
    rw [hpos i (le_trans h.ms_le hi), h.pos i hi]

open verified.merc_reduction.block_partition in
/-- The marking loop of `mark_backward_closure`: marks every listed state of block `b`. -/
theorem bc_mark_loop {n : Nat} {q0 q : BlockPartition} (bT : BT) (hb : bT.index.val < q0.blocks.val.length)
    (hq : Mono n q0 q bT.index.val)
    (iter : alloc.vec.into_iter.IntoIter FromTransition) (l : List FromTransition)
    (hl : iter.val = l) (hf : ∀ i ∈ l, i.«from».index.val < n) :
    ∃ q', BlockPartition.mark_backward_closure_loop0_loop1 iter q bT = ok q' ∧
      Mono n q0 q' bT.index.val ∧
      (∀ t, t < n → (IsMarked q' t ↔ IsMarked q t ∨
        (e2bAt q0 t = bT.index.val ∧ ∃ i ∈ l, i.«from».index.val = t))) := by
  unfold BlockPartition.mark_backward_closure_loop0_loop1
  obtain ⟨y, hy, hmono, hmk⟩ := loop_nat_spec
    (fun (x : alloc.vec.into_iter.IntoIter FromTransition × BlockPartition) =>
      BlockPartition.mark_backward_closure_loop0_loop1.body bT x.1 x.2)
    (fun x => l.length - x.1.val.length)
    (fun m x => m ≤ l.length ∧ x.1.val = l.drop m ∧ Mono n q0 x.2 bT.index.val ∧
      (∀ t, t < n → (IsMarked x.2 t ↔ IsMarked q t ∨
        (e2bAt q0 t = bT.index.val ∧ ∃ i ∈ l.take m, i.«from».index.val = t))))
    (fun y => Mono n q0 y bT.index.val ∧
      (∀ t, t < n → (IsMarked y t ↔ IsMarked q t ∨
        (e2bAt q0 t = bT.index.val ∧ ∃ i ∈ l, i.«from».index.val = t))))
    l.length
    (by intro m x hx; obtain ⟨h1, h2, -⟩ := hx; rw [h2]; simp; omega)
    (by intro m x hx; exact hx.1)
    (by
      intro m x hm hx
      obtain ⟨-, h2, h3, h4⟩ := hx
      have hdrop : l.drop m = l[m] :: l.drop (m + 1) := List.drop_eq_getElem_cons hm
      obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' x.1 l[m] (l.drop (m + 1)) (by rw [h2, hdrop])
      have hfm : l[m].«from».index.val < n := hf _ (List.getElem_mem hm)
      have hbn := block_number_ok h3.inv l[m].«from» hfm
      have hoB : ((x.2.element_to_block.val.getD l[m].«from».index.val zBT)).index.val =
          e2bAt q0 l[m].«from».index.val := by
        rw [e2bAt_eq h3.inv _ hfm, h3.e2bAt_eq]
      by_cases hin : e2bAt q0 l[m].«from».index.val = bT.index.val
      · obtain ⟨q', hmk', hmono', hmarks⟩ := mono_mark hb h3 l[m].«from» hfm hin
        have heq : (x.2.element_to_block.val.getD l[m].«from».index.val zBT) = bT :=
          (bt_eq_iff _ _).2 (by rw [hoB]; exact hin)
        have heq' : ((x.2.element_to_block.val)[l[m].«from».index.val]?.getD zBT).index = bT.index := by
          rw [← List.getD_eq_getElem?_getD]; exact congrArg _ heq
        refine ⟨(it1, q'), ?_, hm, by rw [hit1], hmono', fun t ht => ?_⟩
        · show BlockPartition.mark_backward_closure_loop0_loop1.body bT x.1 x.2 = _
          unfold BlockPartition.mark_backward_closure_loop0_loop1.body
          rw [hnext]
          simp [hbn, heq', hmk']
        · rw [hmarks t ht, h4 t ht, List.take_succ_eq_append_getElem hm]
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro ((h | ⟨e, i, hi, e'⟩) | e)
            · exact Or.inl h
            · exact Or.inr ⟨e, i, Or.inl hi, e'⟩
            · exact Or.inr ⟨by rw [e]; exact hin, l[m], Or.inr rfl, e.symm⟩
          · rintro (h | ⟨e, i, hi | hi, e'⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨e, i, hi, e'⟩)
            · subst hi; exact Or.inr e'.symm
      · have hne : (x.2.element_to_block.val.getD l[m].«from».index.val zBT) ≠ bT :=
          fun h => hin (by rw [← hoB, h])
        have hne' : ¬ ((x.2.element_to_block.val)[l[m].«from».index.val]?.getD zBT).index = bT.index := by
          intro h
          rw [← List.getD_eq_getElem?_getD] at h
          exact hne ((bt_eq_iff _ _).2 (by rw [h]))
        refine ⟨(it1, x.2), ?_, hm, by rw [hit1], h3, fun t ht => ?_⟩
        · show BlockPartition.mark_backward_closure_loop0_loop1.body bT x.1 x.2 = _
          unfold BlockPartition.mark_backward_closure_loop0_loop1.body
          rw [hnext]
          simp [hbn, hne']
        · rw [h4 t ht, List.take_succ_eq_append_getElem hm]
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro (h | ⟨e, i, hi, e'⟩)
            · exact Or.inl h
            · exact Or.inr ⟨e, i, Or.inl hi, e'⟩
          · rintro (h | ⟨e, i, hi | hi, e'⟩)
            · exact Or.inl h
            · exact Or.inr ⟨e, i, hi, e'⟩
            · subst hi
              exfalso; apply hin; rw [e']; exact e)
    (by
      intro x hx
      obtain ⟨hm, h2, h3, h4⟩ := hx
      have : x.1.val = [] := by rw [h2]; simp
      refine ⟨x.2, ?_, h3, fun t ht => ?_⟩
      · show BlockPartition.mark_backward_closure_loop0_loop1.body bT x.1 x.2 = _
        unfold BlockPartition.mark_backward_closure_loop0_loop1.body
        rw [into_iter_next_none' _ this]
        simp
      · rw [h4 t ht]; simp)
    (iter, q) ⟨by omega, by rw [hl]; simp, hq, by intro t ht; simp⟩
  exact ⟨y, hy, hmono, hmk⟩

open verified.merc_reduction.block_partition in
theorem chk_body_eq2 : @BlockPartition.mark_backward_closure_loop0_loop2_loop0.body =
    @BlockPartition.mark_backward_closure_loop0_loop0_loop0.body := rfl

open verified.merc_reduction.block_partition in
theorem chk_body_eq3 : @BlockPartition.mark_backward_closure_loop0_loop3_loop0.body =
    @BlockPartition.mark_backward_closure_loop0_loop0_loop0.body := rfl

theorem partition_eta (q : BlockPartition) :
    ({ elements := q.elements, blocks := q.blocks, element_to_block := q.element_to_block,
       element_offset := q.element_offset } : BlockPartition) = q := rfl

open verified.merc_reduction.block_partition in
/-- The debug-assertion loop of `mark_backward_closure` succeeds when every in-block source is
marked. -/
theorem bc_chk_loop {n : Nat} {q : BlockPartition} (hq : PartInv n q) (bT : BT)
    (iter : alloc.vec.into_iter.IntoIter FromTransition) (l : List FromTransition)
    (hl : iter.val = l)
    (hok : ∀ i ∈ l, i.«from».index.val < n ∧
      (e2bAt q i.«from».index.val = bT.index.val → IsMarked q i.«from».index.val)) :
    BlockPartition.mark_backward_closure_loop0_loop0_loop0 iter q.elements q.blocks
      q.element_to_block q.element_offset bT = ok () := by
  unfold BlockPartition.mark_backward_closure_loop0_loop0_loop0
  obtain ⟨y, hy, -⟩ := loop_nat_spec
    (fun (x : alloc.vec.into_iter.IntoIter FromTransition) =>
      BlockPartition.mark_backward_closure_loop0_loop0_loop0.body q.elements q.blocks
        q.element_to_block q.element_offset bT x)
    (fun x => l.length - x.val.length)
    (fun m x => m ≤ l.length ∧ x.val = l.drop m)
    (fun _ => True)
    l.length
    (by intro m x hx; rw [hx.2]; simp; omega)
    (by intro m x hx; exact hx.1)
    (by
      intro m x hm hx
      obtain ⟨-, h2⟩ := hx
      have hdrop : l.drop m = l[m] :: l.drop (m + 1) := List.drop_eq_getElem_cons hm
      obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' x l[m] (l.drop (m + 1)) (by rw [h2, hdrop])
      obtain ⟨hfm, hmk⟩ := hok l[m] (List.getElem_mem hm)
      refine ⟨it1, ?_, hm, by rw [hit1]⟩
      unfold BlockPartition.mark_backward_closure_loop0_loop0_loop0.body
      rw [hnext]
      have hqq : PartInv n (⟨q.elements, q.blocks, q.element_to_block, q.element_offset⟩ : BlockPartition) := hq
      have hbn := block_number_ok hqq _ hfm
      by_cases hin : e2bAt q l[m].«from».index.val = bT.index.val
      · have hmk' := hmk hin
        have heq : q.element_to_block.val.getD l[m].«from».index.val zBT = bT :=
          (bt_eq_iff _ _).2 (by rw [← e2bAt_eq hq _ hfm] at hin; exact hin)
        have heq' : ((q.element_to_block.val)[l[m].«from».index.val]?.getD zBT) = bT := by
          rw [← List.getD_eq_getElem?_getD]; exact heq
        have hmk'' : IsMarked (⟨q.elements, q.blocks, q.element_to_block, q.element_offset⟩ : BlockPartition)
            l[m].«from».index.val := hmk'
        simp [neq_tag, hbn, heq', is_element_marked_ok hqq _ hfm, hmk'',
          massert]
      · have hne : ¬ ((q.element_to_block.val)[l[m].«from».index.val]?.getD zBT) = bT := by
          intro h
          rw [← List.getD_eq_getElem?_getD] at h
          apply hin
          rw [← e2bAt_eq hq _ hfm, h]
        simp [neq_tag, hbn, hne])
    (by
      intro x hx
      obtain ⟨hm, h2⟩ := hx
      have : x.val = [] := by rw [h2]; simp
      refine ⟨(), ?_, trivial⟩
      unfold BlockPartition.mark_backward_closure_loop0_loop0_loop0.body
      rw [into_iter_next_none' _ this]
      simp)
    iter ⟨by omega, by rw [hl]; simp⟩
  rw [hy]

/-- `incoming_silent_transitions` returns exactly the silent incoming transitions of every in-range
state (this needs `IncomingTransitions::new` to sort the silent transitions first). -/
def IncSilent {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Nat)
    (incoming : IncomingTransitions) : Prop :=
  ∀ x : ST, x.index.val < n → ∃ sil : alloc.vec.Vec FromTransition,
    IncomingTransitions.incoming_silent_transitions incoming x = ok sil ∧
    ∀ i : FromTransition, i ∈ sil.val ↔
      (i.label.index.val = 0 ∧ i.«from».index.val < n ∧ MercVerified.Lts.tr LTSInst sys i.«from» i.label x)

/-- The silent predecessors `y` of `x`. -/
def SilPred {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Nat) (y x : ST) : Prop :=
  y.index.val < n ∧ ∃ μ : TagIndex Std.Usize LabelTag, μ.index.val = 0 ∧
    MercVerified.Lts.tr LTSInst sys y μ x

/-- Every in-block silent predecessor of `x` is marked. -/
def PredsMarked {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Nat) (q : BlockPartition)
    (b : Nat) (x : ST) : Prop :=
  ∀ y, SilPred LTSInst sys n y x → e2bAt q y.index.val = b → IsMarked q y.index.val

open verified.merc_reduction.block_partition in
/-- The assertion pass of `mark_backward_closure` for one element. -/
theorem bc_chk_elem {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {incoming : IncomingTransitions} (hs : IncSilent LTSInst sys n incoming)
    {q : BlockPartition} (hq : PartInv n q) (bT : BT) (x : ST) (hx : x.index.val < n)
    (hP : PredsMarked LTSInst sys n q bT.index.val x) :
    ∃ sil, IncomingTransitions.incoming_silent_transitions incoming x = ok sil ∧
      BlockPartition.mark_backward_closure_loop0_loop0_loop0
        (sil : alloc.vec.into_iter.IntoIter FromTransition) q.elements
        q.blocks q.element_to_block q.element_offset bT = ok () := by
  obtain ⟨sil, hsil, hmem⟩ := hs x hx
  refine ⟨sil, hsil, bc_chk_loop hq bT (sil : alloc.vec.into_iter.IntoIter FromTransition) sil.val rfl ?_⟩
  intro i hi
  obtain ⟨h0, hf, htr⟩ := (hmem i).1 hi
  exact ⟨hf, fun hb => hP i.«from» ⟨hf, i.label, h0, htr⟩ hb⟩

open verified.merc_reduction.block_partition in
theorem chk2_body_eq : @BlockPartition.mark_backward_closure_loop0_loop3.body =
    @BlockPartition.mark_backward_closure_loop0_loop2.body := rfl

open verified.merc_reduction.block_partition in
/-- The assertion pass over a range of positions (variant returning the partition). -/
theorem bc_chk_range_a {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {incoming : IncomingTransitions} (hs : IncSilent LTSInst sys n incoming)
    {q : BlockPartition} (hq : PartInv n q) (bT : BT) (iter : core.ops.range.Range Std.Usize)
    (hrange : ∀ pos, iter.start.val ≤ pos → pos < iter.«end».val →
      pos < n ∧ PredsMarked LTSInst sys n q bT.index.val (eAt q pos)) :
    BlockPartition.mark_backward_closure_loop0_loop0 iter q bT incoming = ok q := by
  unfold BlockPartition.mark_backward_closure_loop0_loop0
  obtain ⟨y, hy, hyq⟩ := loop_nat_spec
    (fun (x : core.ops.range.Range Std.Usize) =>
      BlockPartition.mark_backward_closure_loop0_loop0.body q bT incoming x)
    (fun x => x.start.val - iter.start.val)
    (fun m x => x.start.val = iter.start.val + m ∧ x.«end» = iter.«end» ∧
      m ≤ iter.«end».val - iter.start.val)
    (fun y => y = q)
    (iter.«end».val - iter.start.val)
    (by intro m x hx; omega)
    (by intro m x hx; omega)
    (by
      intro m x hm hx
      obtain ⟨h1, h2, -⟩ := hx
      have hlt : x.start.val < x.«end».val := by rw [h1, h2]; omega
      obtain ⟨o, it1, hnext, hsome, hstart1, hend1⟩ := next_range_some x hlt
      obtain ⟨hposn, hP⟩ := hrange x.start.val (by omega) (by rw [← h2]; exact hlt)
      have hel : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ST) q.elements x.start
          = ok (eAt q x.start.val) := by
        have hlen : x.start.val < q.elements.val.length := by rw [hq.len_e]; exact hposn
        rw [vec_index_ok _ _ hlen, eAt_eq_getElem hlen]
      have hel' : q.elements.index_usize x.start = ok (eAt q x.start.val) := by
        rw [← alloc.vec.Vec.index_slice_index]; exact hel
      obtain ⟨sil, hsil, hchk⟩ := bc_chk_elem hs hq bT (eAt q x.start.val)
        (hq.perm _ hposn).1 hP
      refine ⟨it1, ?_, ?_⟩
      · unfold BlockPartition.mark_backward_closure_loop0_loop0.body
        rw [hnext, hsome]
        simp [hel', hsil, alloc.vec.IntoIteratorVec.into_iter, hchk]
      · refine ⟨by omega, by rw [hend1, h2], by omega⟩)
    (by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hx
      have hge : x.start.val ≥ x.«end».val := by rw [h1, h2]; omega
      obtain ⟨o, it1, hnext, hnone, hid⟩ := next_range_none x hge
      refine ⟨q, ?_, rfl⟩
      unfold BlockPartition.mark_backward_closure_loop0_loop0.body
      rw [hnext, hnone]
      simp)
    iter ⟨by omega, rfl, by omega⟩
  rw [hy, hyq]

open verified.merc_reduction.block_partition in
/-- The assertion pass over a range of positions (variant returning `()`). -/
theorem bc_chk_range_b {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {incoming : IncomingTransitions} (hs : IncSilent LTSInst sys n incoming)
    {q : BlockPartition} (hq : PartInv n q) (bT : BT) (iter : core.ops.range.Range Std.Usize)
    (hrange : ∀ pos, iter.start.val ≤ pos → pos < iter.«end».val →
      pos < n ∧ PredsMarked LTSInst sys n q bT.index.val (eAt q pos)) :
    BlockPartition.mark_backward_closure_loop0_loop2 iter q.elements q.blocks q.element_to_block
      q.element_offset bT incoming = ok () := by
  unfold BlockPartition.mark_backward_closure_loop0_loop2
  obtain ⟨y, hy, hyq⟩ := loop_nat_spec
    (fun (x : core.ops.range.Range Std.Usize) =>
      BlockPartition.mark_backward_closure_loop0_loop2.body q.elements q.blocks q.element_to_block
        q.element_offset bT incoming x)
    (fun x => x.start.val - iter.start.val)
    (fun m x => x.start.val = iter.start.val + m ∧ x.«end» = iter.«end» ∧
      m ≤ iter.«end».val - iter.start.val)
    (fun _ => True)
    (iter.«end».val - iter.start.val)
    (by intro m x hx; omega)
    (by intro m x hx; omega)
    (by
      intro m x hm hx
      obtain ⟨h1, h2, -⟩ := hx
      have hlt : x.start.val < x.«end».val := by rw [h1, h2]; omega
      obtain ⟨o, it1, hnext, hsome, hstart1, hend1⟩ := next_range_some x hlt
      obtain ⟨hposn, hP⟩ := hrange x.start.val (by omega) (by rw [← h2]; exact hlt)
      have hel : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ST) q.elements x.start
          = ok (eAt q x.start.val) := by
        have hlen : x.start.val < q.elements.val.length := by rw [hq.len_e]; exact hposn
        rw [vec_index_ok _ _ hlen, eAt_eq_getElem hlen]
      have hel' : q.elements.index_usize x.start = ok (eAt q x.start.val) := by
        rw [← alloc.vec.Vec.index_slice_index]; exact hel
      obtain ⟨sil, hsil, hchk⟩ := bc_chk_elem hs hq bT (eAt q x.start.val)
        (hq.perm _ hposn).1 hP
      have hchk2 : BlockPartition.mark_backward_closure_loop0_loop2_loop0
          (sil : alloc.vec.into_iter.IntoIter FromTransition) q.elements q.blocks q.element_to_block
          q.element_offset bT = ok () := hchk
      refine ⟨it1, ?_, ?_⟩
      · unfold BlockPartition.mark_backward_closure_loop0_loop2.body
        rw [hnext, hsome]
        simp [hel', hsil, alloc.vec.IntoIteratorVec.into_iter, hchk2]
      · refine ⟨by omega, by rw [hend1, h2], by omega⟩)
    (by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hx
      have hge : x.start.val ≥ x.«end».val := by rw [h1, h2]; omega
      obtain ⟨o, it1, hnext, hnone, hid⟩ := next_range_none x hge
      refine ⟨(), ?_, trivial⟩
      unfold BlockPartition.mark_backward_closure_loop0_loop2.body
      rw [hnext, hnone]
      simp)
    iter ⟨by omega, rfl, by omega⟩
  rw [hy]

section Outer

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Nat) (p : BlockPartition) (b : Nat)

/-- A silent step inside block `b` of `p`. -/
def BStep (u v : ST) : Prop :=
  SilPred LTSInst sys n u v ∧ v.index.val < n ∧ e2bAt p u.index.val = b ∧ e2bAt p v.index.val = b

/-- States of block `b` that reach `d` by silent steps inside the block. -/
abbrev BReach : ST → ST → Prop := Relation.ReflTransGen (BStep LTSInst sys n p b)

/-- Soundness of the marks of `q`: every marked state of block `b` reaches a state that was marked
in `p`. -/
def CSound (q : BlockPartition) : Prop :=
  ∀ t : ST, t.index.val < n → e2bAt p t.index.val = b → IsMarked q t.index.val →
    ∃ d : ST, d.index.val < n ∧ e2bAt p d.index.val = b ∧ IsMarked p d.index.val ∧
      BReach LTSInst sys n p b t d

/-- The marks of `q` only extend those of `p`, and only inside block `b`. -/
def CMarks (q : BlockPartition) : Prop :=
  (∀ t : ST, t.index.val < n → IsMarked p t.index.val → IsMarked q t.index.val) ∧
  (∀ t : ST, t.index.val < n → e2bAt p t.index.val ≠ b → (IsMarked q t.index.val ↔ IsMarked p t.index.val))

/-- The marked states of block `b` are closed under silent predecessors in the block. -/
def CClosed (q : BlockPartition) : Prop :=
  ∀ x : ST, x.index.val < n → e2bAt p x.index.val = b → IsMarked q x.index.val →
    PredsMarked LTSInst sys n q b x

/-- The positions `[E - m, E)` hold marked elements whose silent predecessors in the block are
all marked. -/
def CScan (q : BlockPartition) (E m : Nat) : Prop :=
  ∀ pos, E - m ≤ pos → pos < E →
    (blkAt q b).marked_split.val ≤ pos ∧ PredsMarked LTSInst sys n q b (eAt q pos)

end Outer

/-- The element at a position of block `b` belongs to block `b` and sits at that position. -/
theorem pos_in_block {n : Nat} {q : BlockPartition} (hq : PartInv n q) {b : Nat}
    (hb : b < q.blocks.val.length) {pos : Nat}
    (h1 : (blkAt q b).begin.val ≤ pos) (h2 : pos < (blkAt q b).«end».val) :
    (eAt q pos).index.val < n ∧ e2bAt q (eAt q pos).index.val = b ∧
      offAt q (eAt q pos).index.val = pos := by
  have hbk := hq.blk b hb
  have hpn : pos < n := by omega
  obtain ⟨hx1, hx2⟩ := hq.perm pos hpn
  obtain ⟨o1, o2, o3⟩ := hq.own _ hx1
  rw [hx2] at o2 o3
  exact ⟨hx1, hq.pos_block_unique o1 hb ⟨o2, o3⟩ ⟨h1, h2⟩, hx2⟩

/-- A state of block `b` lies in the position window of the block. -/
theorem state_pos {n : Nat} {q : BlockPartition} (hq : PartInv n q) {b : Nat} {x : ST}
    (hx : x.index.val < n) (hxb : e2bAt q x.index.val = b) :
    (blkAt q b).begin.val ≤ offAt q x.index.val ∧ offAt q x.index.val < (blkAt q b).«end».val := by
  obtain ⟨h1, h2, h3⟩ := hq.own x.index.val hx
  rw [hxb] at h2 h3
  exact ⟨h2, h3⟩

theorem isMarked_iff_ms {q : BlockPartition} {b : Nat} {x : ST} (hxb : e2bAt q x.index.val = b) :
    IsMarked q x.index.val ↔ (blkAt q b).marked_split.val ≤ offAt q x.index.val := by
  unfold IsMarked; rw [hxb]

open verified.merc_reduction.block_partition in
/-- One scan step of the closure: the silent predecessors of the element at position `it` that lie
in block `b` get marked, and the invariants of the scan are maintained. -/
theorem bc_scan_step {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {incoming : IncomingTransitions} (hs : IncSilent LTSInst sys n incoming)
    {p : BlockPartition} (_hp : PartInv n p) (bT : BT) (hb : bT.index.val < p.blocks.val.length)
    {q : BlockPartition} (hmono : Mono n p q bT.index.val)
    (hsound : CSound LTSInst sys n p bT.index.val q) (hmarks : CMarks n p bT.index.val q)
    {E m : Nat} (hE : E = (blkAt p bT.index.val).«end».val)
    (hscan : CScan LTSInst sys n bT.index.val q E m)
    (hm : m < E) (hit : (blkAt q bT.index.val).marked_split.val ≤ E - 1 - m) :
    ∃ q', ∃ sil : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_silent_transitions incoming (eAt q (E - 1 - m)) = ok sil ∧
      BlockPartition.mark_backward_closure_loop0_loop1 (sil : alloc.vec.into_iter.IntoIter FromTransition)
        q bT = ok q' ∧
      Mono n p q' bT.index.val ∧ CSound LTSInst sys n p bT.index.val q' ∧
      CMarks n p bT.index.val q' ∧ CScan LTSInst sys n bT.index.val q' E (m + 1) := by
  set b := bT.index.val with hbdef
  have hbq : b < q.blocks.val.length := by rw [hmono.nblocks]; exact hb
  have hq := hmono.inv
  have hbk := hq.blk b hbq
  have hEq : (blkAt q b).«end».val = E := by rw [hmono.end_eq, hE]
  have hBeg : (blkAt q b).begin.val ≤ E - 1 - m := by omega
  obtain ⟨hxn, hxb, hxoff⟩ := pos_in_block hq hbq hBeg (by omega)
  set x := eAt q (E - 1 - m) with hxdef
  obtain ⟨sil, hsil, hmem⟩ := hs x hxn
  have hxmk : IsMarked q x.index.val := by
    rw [isMarked_iff_ms hxb, hxoff]; exact hit
  obtain ⟨q', hloop, hmono', hmk'⟩ := bc_mark_loop (q0 := q) (q := q) bT hbq (Mono.refl hq b)
    (sil : alloc.vec.into_iter.IntoIter FromTransition) sil.val rfl
    (fun i hi => ((hmem i).1 hi).2.1)
  have hmono2 : Mono n p q' b := hmono.trans hmono'
  have he2b : ∀ t, e2bAt q' t = e2bAt p t := fun t => by rw [hmono2.e2bAt_eq]
  have he2bq : ∀ t, e2bAt q t = e2bAt p t := fun t => by rw [hmono.e2bAt_eq]
  refine ⟨q', sil, hsil, hloop, hmono2, ?_, ?_, ?_⟩
  · intro t ht htb hmk
    rcases (hmk' t.index.val ht).1 hmk with h | ⟨_, i, hi, he⟩
    · exact hsound t ht htb h
    · obtain ⟨h0, hfn, htr⟩ := (hmem i).1 hi
      have hti : i.«from» = t := merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq he)
      obtain ⟨d, hdn, hdb, hdm, hreach⟩ := hsound x hxn (by rw [← he2bq]; exact hxb) hxmk
      refine ⟨d, hdn, hdb, hdm, Relation.ReflTransGen.head ?_ hreach⟩
      refine ⟨⟨ht, i.label, h0, by rw [← hti]; exact htr⟩, hxn, htb, by rw [← he2bq]; exact hxb⟩
  · refine ⟨fun t ht hpm => (hmk' t.index.val ht).2 (Or.inl (hmarks.1 t ht hpm)), fun t ht htb => ?_⟩
    rw [hmk' t.index.val ht]
    constructor
    · rintro (h | ⟨he, -⟩)
      · exact (hmarks.2 t ht htb).1 h
      · exact absurd (by rw [← he2bq]; exact he) htb
    · intro h; exact Or.inl ((hmarks.2 t ht htb).2 h)
  · intro pos hpos1 hpos2
    have hpos0 : E - 1 - m ≤ pos := by omega
    have hmsq : (blkAt q b).marked_split.val ≤ pos := by omega
    refine ⟨le_trans hmono'.ms_le hmsq, ?_⟩
    rw [hmono'.pos pos hmsq]
    by_cases hpe : pos = E - 1 - m
    · subst hpe
      intro y hy hyb
      have hyq : e2bAt q y.index.val = b := by rw [he2bq, ← he2b]; exact hyb
      obtain ⟨hyn, μ, hμ, htr⟩ := hy
      refine (hmk' y.index.val hyn).2 (Or.inr ⟨hyq, ⟨μ, y⟩, ?_, rfl⟩)
      exact (hmem ⟨μ, y⟩).2 ⟨hμ, hyn, htr⟩
    · have hpos3 : E - m ≤ pos := by omega
      obtain ⟨-, hpm⟩ := hscan pos hpos3 hpos2
      intro y hy hyb
      have hyq : e2bAt q y.index.val = b := by rw [he2bq, ← he2b]; exact hyb
      exact (hmk' y.index.val hy.1).2 (Or.inl (hpm y hy hyq))

theorem eAt_off {n : Nat} {q : BlockPartition} (hq : PartInv n q) {x : ST} (hx : x.index.val < n) :
    eAt q (offAt q x.index.val) = x :=
  merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (hq.inv _ hx))

theorem cclosed_of_all {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {p q : BlockPartition} (hq : PartInv n q) {b : Nat} (_hb : b < q.blocks.val.length)
    (_hpq : ∀ s, e2bAt q s = e2bAt p s)
    (hall : (blkAt q b).marked_split.val = (blkAt q b).begin.val) :
    CClosed LTSInst sys n p b q := by
  intro x hx hxb hxm y hy hyb
  have hxq : e2bAt q y.index.val = b := hyb
  obtain ⟨h1, h2⟩ := state_pos hq hy.1 hxq
  rw [isMarked_iff_ms hxq]
  omega

theorem cclosed_of_scan {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {p q : BlockPartition} (hq : PartInv n q) {b E m : Nat}
    (hpq : ∀ s, e2bAt q s = e2bAt p s) (hE : E = (blkAt q b).«end».val)
    (hscan : CScan LTSInst sys n b q E m) (hm : m < E)
    (hit : E - 1 - m < (blkAt q b).marked_split.val) :
    CClosed LTSInst sys n p b q := by
  intro x hx hxb hxm
  have hxq : e2bAt q x.index.val = b := by rw [hpq]; exact hxb
  obtain ⟨h1, h2⟩ := state_pos hq hx hxq
  have hmk := (isMarked_iff_ms hxq).1 hxm
  have := hscan (offAt q x.index.val) (by omega) (by omega)
  have hex := eAt_off hq hx
  rw [hex] at this
  exact this.2

open verified.merc_reduction.block_partition in
/-- **`mark_backward_closure`**: the marked states of block `b` afterwards are exactly those that
reach a previously marked state of the block along silent steps inside the block. -/
theorem bc_outer {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {incoming : IncomingTransitions} (hs : IncSilent LTSInst sys n incoming)
    {p : BlockPartition} (hp : PartInv n p) (bT : BT) (hb : bT.index.val < p.blocks.val.length) :
    ∃ q, BlockPartition.mark_backward_closure p bT incoming = ok q ∧
      Mono n p q bT.index.val ∧ CSound LTSInst sys n p bT.index.val q ∧
      CMarks n p bT.index.val q ∧ CClosed LTSInst sys n p bT.index.val q := by
  set b := bT.index.val with hbdef
  have hbk := hp.blk b hb
  have hwfb := partInv_blockWF hp hb
  have hblkv : verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice Block) p.blocks bT
      = ok (blkAt p b) := by
    rw [vec_tagged_index_val p.blocks bT hb]
    congr 1; exact (blkAt_eq_getElem hb).symm
  unfold BlockPartition.mark_backward_closure
  rw [hblkv]
  simp only [bind_ok]
  obtain ⟨span, hspan, hspanv⟩ : ∃ span : Std.Usize,
      (blkAt p b).«end» - (blkAt p b).begin = ok span ∧
      span.val = (blkAt p b).«end».val - (blkAt p b).begin.val := by
    obtain ⟨y, hy, hv, -⟩ := spec_imp_exists
      (Usize.sub_spec (x := (blkAt p b).«end») (y := (blkAt p b).begin) (by omega))
    exact ⟨y, hy, hv⟩
  rw [hspan]
  simp only [bind_ok]
  unfold BlockPartition.mark_backward_closure_loop0
  set E := (blkAt p b).«end».val with hEdef
  have hspan_le : span.val ≤ E := by omega
  -- the check loops of the three exits
  have hrange : ∀ (q : BlockPartition), Mono n p q b → CClosed LTSInst sys n p b q →
      ∀ pos, (blkAt p b).marked_split.val ≤ pos → pos < (blkAt p b).«end».val →
        pos < n ∧ PredsMarked LTSInst sys n q b (eAt q pos) := by
    intro q hmono hcl pos h1 h2
    have hbq : b < q.blocks.val.length := by rw [hmono.nblocks]; exact hb
    have hbkq := hmono.inv.blk b hbq
    obtain ⟨hxn, hxb, hxoff⟩ := pos_in_block hmono.inv hbq (pos := pos)
      (by rw [hmono.begin_eq]; omega) (by rw [hmono.end_eq]; exact h2)
    have hmk : IsMarked q (eAt q pos).index.val := by
      rw [isMarked_iff_ms hxb, hxoff]; have := hmono.ms_le; omega
    exact ⟨by omega, hcl _ hxn (by rw [← hmono.e2bAt_eq]; exact hxb) hmk⟩
  have hspec :
      loop (fun (x : core.ops.range.Range Std.Usize × BlockPartition) =>
          BlockPartition.mark_backward_closure_loop0.body bT incoming (blkAt p b).marked_split
            (blkAt p b).«end» x.1 x.2) ({ start := 0#usize, «end» := span }, p)
        ⦃ q => Mono n p q b ∧ CSound LTSInst sys n p b q ∧ CMarks n p b q ∧
          CClosed LTSInst sys n p b q ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : core.ops.range.Range Std.Usize × BlockPartition =>
        span.val - x.1.start.val)
      (inv := fun x : core.ops.range.Range Std.Usize × BlockPartition =>
        x.1.«end» = span ∧ x.1.start.val ≤ span.val ∧ Mono n p x.2 b ∧
        CSound LTSInst sys n p b x.2 ∧ CMarks n p b x.2 ∧ CScan LTSInst sys n b x.2 E x.1.start.val)
      (post := fun q : BlockPartition => Mono n p q b ∧ CSound LTSInst sys n p b q ∧
        CMarks n p b q ∧ CClosed LTSInst sys n p b q)
      (body := fun x : core.ops.range.Range Std.Usize × BlockPartition =>
        BlockPartition.mark_backward_closure_loop0.body bT incoming (blkAt p b).marked_split
          (blkAt p b).«end» x.1 x.2)
      (x := ({ start := 0#usize, «end» := span }, p))
    · intro x hx
      obtain ⟨iter, q⟩ := x
      obtain ⟨hend, hle, hmono, hsound, hmarks, hscan⟩ := hx
      simp only at hend hle hmono hsound hmarks hscan
      have hendv : iter.«end».val = span.val := congrArg UScalar.val hend
      have hbq : b < q.blocks.val.length := by rw [hmono.nblocks]; exact hb
      have hqinv := hmono.inv
      have hbkq := hqinv.blk b hbq
      have hEq : (blkAt q b).«end».val = E := by rw [hmono.end_eq]
      have hBq : (blkAt q b).begin = (blkAt p b).begin := hmono.begin_eq
      have hblkq : verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
          (core.slice.index.SliceIndexUsizeSlice Block) q.blocks bT = ok (blkAt q b) := by
        have hbq' : bT.index.val < q.blocks.val.length := hbq
        rw [vec_tagged_index_val q.blocks bT hbq']
        congr 1; exact (blkAt_eq_getElem hbq').symm
      by_cases hlt : iter.start.val < iter.«end».val
      · obtain ⟨o, it1, hnext, hsome, hstart1, hend1⟩ := next_range_some iter hlt
        have hm : iter.start.val < E := by omega
        obtain ⟨i2, hi2, hi2v⟩ : ∃ i2 : Std.Usize, (blkAt p b).«end» - 1#usize = ok i2 ∧
            i2.val = E - 1 := by
          obtain ⟨y, hy, hv, -⟩ := spec_imp_exists
            (Usize.sub_spec (x := (blkAt p b).«end») (y := 1#usize) (by simp; omega))
          exact ⟨y, hy, by simpa using hv⟩
        obtain ⟨it, hit, hitv⟩ : ∃ it : Std.Usize, i2 - iter.start = ok it ∧
            it.val = E - 1 - iter.start.val := by
          obtain ⟨y, hy, hv, -⟩ := spec_imp_exists
            (Usize.sub_spec (x := i2) (y := iter.start) (by omega))
          exact ⟨y, hy, by rw [hv, hi2v]⟩
        by_cases hge : (blkAt q b).marked_split.val ≤ E - 1 - iter.start.val
        · by_cases hun : (blkAt q b).begin.val < (blkAt q b).marked_split.val
          · -- the scan step
            obtain ⟨q', sil, hsil, hloop, hmono', hsound', hmarks', hscan'⟩ :=
              bc_scan_step hs hp bT hb hmono hsound hmarks (E := E) (m := iter.start.val) hEdef hscan hm hge
            have hel : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ST) q.elements it
                = ok (eAt q (E - 1 - iter.start.val)) := by
              have hlen : it.val < q.elements.val.length := by
                rw [hqinv.len_e]; have := hqinv.blk b hbq; omega
              rw [vec_index_ok _ _ hlen, ← hitv, eAt_eq_getElem hlen]
            have hhas := block_has_unmarked_contract (blkAt q b) (partInv_blockWF hqinv hbq)
            have hhas' : (blkAt q b).has_unmarked = ok true := by rw [hhas]; simp [hun]
            have hitgeN : (blkAt q b).marked_split.val ≤ it.val := by omega
            have hel' : q.elements.index_usize it = ok (eAt q (E - 1 - iter.start.val)) := by
              rw [← alloc.vec.Vec.index_slice_index]; exact hel
            refine Std.WP.exists_imp_spec ⟨cont (it1, q'), ?_, ?_⟩
            · unfold BlockPartition.mark_backward_closure_loop0.body
              rw [hnext, hsome]
              simp [hi2, hit, hblkq, hitgeN, hhas', hel', hsil, alloc.vec.IntoIteratorVec.into_iter, hloop]
            · show _ ∧ _
              have h1 : it1.start.val ≤ span.val := by omega
              have h2 : span.val - it1.start.val < span.val - iter.start.val := by omega
              refine ⟨⟨by rw [hend1, hend], h1, hmono', hsound', hmarks', ?_⟩, h2⟩
              rw [hstart1]; exact hscan'
          · -- everything in the block is marked
            have hall : (blkAt q b).marked_split.val = (blkAt q b).begin.val := by omega
            have hcl := cclosed_of_all (LTSInst := LTSInst) (sys := sys) (p := p) hqinv hbq
              (fun s => by rw [hmono.e2bAt_eq]) hall
            have hchk := bc_chk_range_b hs hqinv bT ⟨(blkAt p b).marked_split, (blkAt p b).«end»⟩
              (fun pos h1 h2 => hrange q hmono hcl pos h1 h2)
            have hhas := block_has_unmarked_contract (blkAt q b) (partInv_blockWF hqinv hbq)
            have hhas' : (blkAt q b).has_unmarked = ok false := by rw [hhas]; simp [hun]
            have hitgeN : (blkAt q b).marked_split.val ≤ it.val := by omega
            refine Std.WP.exists_imp_spec ⟨done q, ?_, ⟨hmono, hsound, hmarks, hcl⟩⟩
            unfold BlockPartition.mark_backward_closure_loop0.body
            rw [hnext, hsome]
            simp [hi2, hit, hblkq, hitgeN, hhas', hchk]
        · -- every marked element has been scanned
          have hcl := cclosed_of_scan (LTSInst := LTSInst) (sys := sys) (p := p) hqinv
            (fun s => by rw [hmono.e2bAt_eq]) (by rw [hEq]) hscan hm (by omega)
          have hchk := bc_chk_range_b hs hqinv bT ⟨(blkAt p b).marked_split, (blkAt p b).«end»⟩
            (fun pos h1 h2 => hrange q hmono hcl pos h1 h2)
          have hchk3 : BlockPartition.mark_backward_closure_loop0_loop3
              (⟨(blkAt p b).marked_split, (blkAt p b).«end»⟩ : core.ops.range.Range Std.Usize)
              q.elements q.blocks q.element_to_block q.element_offset bT incoming = ok () := hchk
          have hitltN : ¬ (blkAt q b).marked_split.val ≤ it.val := by omega
          refine Std.WP.exists_imp_spec ⟨done q, ?_, ⟨hmono, hsound, hmarks, hcl⟩⟩
          unfold BlockPartition.mark_backward_closure_loop0.body
          rw [hnext, hsome]
          simp [hi2, hit, hblkq, hitltN, hchk3]
      · -- the range is exhausted
        have hge : iter.start.val ≥ iter.«end».val := by omega
        obtain ⟨o, it1, hnext, hnone, hid⟩ := next_range_none iter hge
        have hstart : iter.start.val = span.val := by omega
        have hcl : CClosed LTSInst sys n p b q := by
          have hmsq : (blkAt q b).marked_split.val ≤ (blkAt q b).begin.val := by
            have := hscan (E - span.val) (by omega) (by omega)
            have hbv := congrArg UScalar.val hBq
            omega
          exact cclosed_of_all hqinv hbq (fun s => by rw [hmono.e2bAt_eq]) (by omega)
        have hchk := bc_chk_range_a hs hqinv bT ⟨(blkAt p b).marked_split, (blkAt p b).«end»⟩
          (fun pos h1 h2 => hrange q hmono hcl pos h1 h2)
        refine Std.WP.exists_imp_spec ⟨done q, ?_, ⟨hmono, hsound, hmarks, hcl⟩⟩
        unfold BlockPartition.mark_backward_closure_loop0.body
        rw [hnext, hnone]
        simp [hchk]
    · refine ⟨rfl, by simp, Mono.refl hp b, ?_, ⟨fun t _ h => h, fun t _ _ => Iff.rfl⟩, ?_⟩
      · intro t ht htb hm
        exact ⟨t, ht, htb, hm, Relation.ReflTransGen.refl⟩
      · intro pos h1 h2
        change E - (0#usize).val ≤ pos at h1
        rw [show (0#usize).val = 0 from rfl] at h1
        omega
  obtain ⟨y, hy, hpost⟩ := spec_imp_exists hspec
  exact ⟨y, hy, hpost⟩

theorem tr_tau_iff {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Nat) (_hn : n ≤ Usize.max)
    (u v : Fin n) :
    (aLTS LTSInst sys n).Tr u Cslib.HasTau.τ v ↔
      MercVerified.Lts.tr LTSInst sys (stOf u) MercVerified.Lts.tauLabelIndex (stOf v) := Iff.rfl

theorem stOf_lt {n : Nat} (x : Fin n) (hn : n ≤ Usize.max) : (stOf x).index.val < n := by
  rw [stOf_index _ hn]; exact x.2

/-- Reachability inside block `b` is the abstract inert reachability. -/
theorem breach_iff_inert {L Label : Type} (LTSInst : LTS L Label) (sys : L) {n : Nat}
    (hn : n ≤ Usize.max) (p : BlockPartition) (b : Nat) (x d : Fin n)
    (hxb : e2bAt p x.val = b) :
    BReach LTSInst sys n p b (stOf x) (stOf d) ↔
      Sigref.InertReach (aLTS LTSInst sys n) (bdOf p n).setoid x d := by
  have hfin : ∀ y : ST, ∀ hy : y.index.val < n, stOf (⟨y.index.val, hy⟩ : Fin n) = y := by
    intro y hy
    apply merc_utilities.tagged_index.TagIndex.ext
    apply UScalar.eq_of_val_eq
    rw [stOf_index _ hn]
  have hstv : ∀ y : Fin n, (stOf y).index.val = y.val := fun y => stOf_index y hn
  have htauiff : ∀ μ : TagIndex Std.Usize LabelTag, μ.index.val = 0 ↔
      μ = (Cslib.HasTau.τ : TagIndex Std.Usize LabelTag) := fun μ => (label_eq_tau_iff μ).symm
  constructor
  · intro h
    generalize hu : stOf x = u at h
    generalize hw : stOf d = w at h
    induction h using Relation.ReflTransGen.head_induction_on generalizing x with
    | refl =>
      have : x = d := Fin.ext (by
        have := congrArg (fun z : ST => z.index.val) (hu.trans hw.symm)
        simpa [hstv] using this)
      subst this; exact Relation.ReflTransGen.refl
    | @head u' v hstep hrest ih =>
      obtain ⟨⟨hun, μ, hμ, htr⟩, hvn, hub, hvb⟩ := hstep
      let y : Fin n := ⟨v.index.val, hvn⟩
      have hy : stOf y = v := hfin v hvn
      have hμτ : μ = (Cslib.HasTau.τ : TagIndex Std.Usize LabelTag) := (htauiff μ).1 hμ
      have hxy : (aLTS LTSInst sys n).Tr x Cslib.HasTau.τ y := by
        show MercVerified.Lts.tr LTSInst sys (stOf x) _ (stOf y)
        rw [hu, hy, ← hμτ]; exact htr
      have hxv : x.val = u'.index.val := by rw [← hu, hstv]
      have hπ : (bdOf p n).setoid.r x y := by
        show e2bAt p x.val = e2bAt p y.val
        rw [hxv, hub]; exact hvb.symm
      exact Relation.ReflTransGen.head ⟨hxy, hπ⟩ (ih y (by show e2bAt p y.val = b; exact hvb) hy)
  · intro h
    revert hxb
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @head x' y' hstep hrest ih =>
      intro hxb'
      obtain ⟨htr, hπ⟩ := hstep
      have hπ' : e2bAt p x'.val = e2bAt p y'.val := hπ
      have hyb : e2bAt p y'.val = b := by rw [← hπ']; exact hxb'
      refine Relation.ReflTransGen.head ⟨⟨?_, Cslib.HasTau.τ, ?_, htr⟩, ?_, ?_, ?_⟩ (ih hyb)
      · exact stOf_lt x' hn
      · rfl
      · exact stOf_lt y' hn
      · rw [hstv]; exact hxb'
      · rw [hstv]; exact hyb

theorem breach_marked {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    {p q : BlockPartition} {b : Nat} (hpq : ∀ s, e2bAt q s = e2bAt p s)
    (hcl : CClosed LTSInst sys n p b q) {u w : ST}
    (h : BReach LTSInst sys n p b u w) (hw : IsMarked q w.index.val) (_hwn : w.index.val < n)
    (_hwb : e2bAt p w.index.val = b) : IsMarked q u.index.val := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hw
  | @head u' v hstep hrest ih =>
    obtain ⟨hsp, hvn, hub, hvb⟩ := hstep
    have hvm := ih
    exact hcl v hvn hvb hvm u' hsp (by rw [hpq]; exact hub)

open verified.merc_reduction.block_partition in
/-- **`mark_backward_closure`** (abstract statement). -/
theorem mark_backward_closure_spec {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    (hn : n ≤ Usize.max) {incoming : IncomingTransitions} (hs : IncSilent LTSInst sys n incoming)
    {p : BlockPartition} (hp : PartInv n p) (bT : BT) (hb : bT.index.val < p.blocks.val.length) :
    ∃ q, BlockPartition.mark_backward_closure p bT incoming = ok q ∧
      Mono n p q bT.index.val ∧
      (∀ x : Fin n, e2bAt p x.val ≠ bT.index.val → (IsMarked q x.val ↔ IsMarked p x.val)) ∧
      (∀ x : Fin n, e2bAt p x.val = bT.index.val →
        (IsMarked q x.val ↔ x ∈ Sigref.inertClosure (aLTS LTSInst sys n) (bdOf p n).setoid
          {d : Fin n | e2bAt p d.val = bT.index.val ∧ IsMarked p d.val})) := by
  obtain ⟨q, hq, hmono, hsound, hmarks, hcl⟩ := bc_outer hs hp bT hb
  have hstv : ∀ y : Fin n, (stOf y).index.val = y.val := fun y => stOf_index y hn
  have hfin : ∀ y : ST, ∀ hy : y.index.val < n, stOf (⟨y.index.val, hy⟩ : Fin n) = y := by
    intro y hy
    apply merc_utilities.tagged_index.TagIndex.ext
    apply UScalar.eq_of_val_eq
    rw [stOf_index _ hn]
  refine ⟨q, hq, hmono, fun x hx => ?_, fun x hx => ?_⟩
  · have := hmarks.2 (stOf x) (stOf_lt x hn) (by rw [hstv]; exact hx)
    rwa [hstv] at this
  constructor
  · intro hm
    have hm' : IsMarked q (stOf x).index.val := by rw [hstv]; exact hm
    obtain ⟨d, hdn, hdb, hdm, hreach⟩ := hsound (stOf x) (stOf_lt x hn) (by rw [hstv]; exact hx) hm'
    refine ⟨⟨d.index.val, hdn⟩, ⟨hdb, hdm⟩, ?_⟩
    have := (breach_iff_inert LTSInst sys hn p _ x ⟨d.index.val, hdn⟩ hx).1
      (by rw [hfin d hdn]; exact hreach)
    exact this
  · rintro ⟨d, ⟨hdb, hdm⟩, hreach⟩
    have hbr := (breach_iff_inert LTSInst sys hn p _ x d hx).2 hreach
    have hdq : IsMarked q (stOf d).index.val :=
      hmarks.1 (stOf d) (stOf_lt d hn) (by rw [hstv]; exact hdm)
    have := breach_marked (fun s => by rw [hmono.e2bAt_eq]) hcl hbr hdq (stOf_lt d hn)
      (by rw [hstv]; exact hdb)
    rwa [hstv] at this

end MercVerified.Refinement.Proofs
