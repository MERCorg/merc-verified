import MercVerified.Refinement.Proofs.Split_Proofs
import Aeneas.Std.WP

/-!
# `mark_dirty_states` / `mark_dirty_new_blocks` (non-branching): the worklist invariant

The worklist stays duplicate-free, every queued block is valid and has a marked suffix, and the
partition stays a consistent one with the same number of blocks.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The invariant of the worklist `w` w.r.t. the partition `p`. -/
def DirtyInv (n : Nat) (p : BlockPartition) (w : VecTy BT) : Prop :=
  PartInv n p ∧ w.val.Nodup ∧
  ∀ x ∈ w.val, x.index.val < p.blocks.val.length ∧
    (blkAt p x.index.val).marked_split.val < (blkAt p x.index.val).«end».val

theorem e2bAt_eq {n : Nat} {p : BlockPartition} (hp : PartInv n p) (s : Nat) (hs : s < n) :
    (p.element_to_block.val.getD s zBT).index.val = e2bAt p s := by
  have h : s < p.element_to_block.val.length := by rw [hp.len_e2b]; exact hs
  simp [e2bAt]

/-- Marks and worklist of a partition `p` derived from `p1` by marking states: the block map is
    unchanged, the marked states are those marked in `p1` together with the set `D`, and the block of
    every marked state is queued. -/
def DirtySem (n : Nat) (p1 p : BlockPartition) (w : VecTy BT) (D : ST → Prop) : Prop :=
  p.element_to_block = p1.element_to_block ∧
  (∀ t : ST, t.index.val < n → (IsMarked p t.index.val ↔ IsMarked p1 t.index.val ∨ D t)) ∧
  (∀ t : ST, t.index.val < n → IsMarked p t.index.val → ∃ x ∈ w.val, x.index.val = e2bAt p t.index.val)

theorem DirtySem.congr {n : Nat} {p1 p : BlockPartition} {w : VecTy BT} {D D' : ST → Prop}
    (h : DirtySem n p1 p w D) (hD : ∀ t : ST, t.index.val < n → (D t ↔ D' t)) :
    DirtySem n p1 p w D' :=
  ⟨h.1, fun t ht => by rw [h.2.1 t ht, hD t ht], h.2.2⟩

/-- A block that has a marked suffix is queued. -/
theorem queued_of_has_marked {n : Nat} {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop}
    (hp : PartInv n p) (hs : DirtySem n p1 p w D) {o : Nat} (ho : o < p.blocks.val.length)
    (hm : (blkAt p o).marked_split.val < (blkAt p o).«end».val) : ∃ x ∈ w.val, x.index.val = o := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hp.blk o ho
  have hz := hp.perm (blkAt p o).marked_split.val (by omega)
  have hzo : e2bAt p (eAt p (blkAt p o).marked_split.val).index.val = o := by
    obtain ⟨h1, h2, h3⟩ := hp.own (eAt p (blkAt p o).marked_split.val).index.val hz.1
    rw [hz.2] at h2 h3
    exact hp.pos_block_unique h1 ho ⟨h2, h3⟩ ⟨hb3, hm⟩
  have hmk : IsMarked p (eAt p (blkAt p o).marked_split.val).index.val := by
    unfold IsMarked; rw [hzo, hz.2]
  obtain ⟨x, hx, hxe⟩ := hs.2.2 (eAt p (blkAt p o).marked_split.val) hz.1 hmk
  exact ⟨x, hx, by rw [hxe, hzo]⟩

/-- Marking one more state `f`: the semantics extends by `f`, provided the queue contains its block. -/
theorem DirtySem.mark {n : Nat} {p1 p p' : BlockPartition} {w w1 : VecTy BT} {D : ST → Prop}
    (hsem : DirtySem n p1 p w D) (f : ST)
    (he2b' : p'.element_to_block = p.element_to_block)
    (hmk : ∀ t, t < n → (IsMarked p' t ↔ IsMarked p t ∨ t = f.index.val))
    (hw : ∀ x ∈ w.val, x ∈ w1.val) (hq : ∃ x ∈ w1.val, x.index.val = e2bAt p f.index.val) :
    DirtySem n p1 p' w1 (fun t => D t ∨ t.index.val = f.index.val) := by
  have he : ∀ t, e2bAt p' t = e2bAt p t := fun t => by simp [e2bAt, he2b']
  refine ⟨by rw [he2b']; exact hsem.1, fun t ht => ?_, fun t ht hm => ?_⟩
  · rw [hmk _ ht, hsem.2.1 t ht]; tauto
  · rcases (hmk _ ht).mp hm with h | h
    · obtain ⟨x, hx, hxe⟩ := hsem.2.2 t ht h
      exact ⟨x, hw x hx, by rw [he, hxe]⟩
    · obtain ⟨x, hx, hxe⟩ := hq
      exact ⟨x, hx, by rw [he, h]; exact hxe⟩

/-- One incoming transition processed by `mark_dirty_states` (non-branching): the source state's
    block is queued unless it is already marked, and the source state is marked. The conclusion
    lists the results of the successive calls of the loop body. -/
theorem dirty_transition_step {n : Nat} {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop}
    (h : DirtyInv n p w) (hsem : DirtySem n p1 p w D) (hn : n ≤ Usize.max) (f : ST)
    (hf : f.index.val < n) :
    ∃ (oB : BT) (bm : Bool) (p' : BlockPartition) (w1 : VecTy BT),
      verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number p f = ok oB ∧
      (∃ blk, verified.merc_reduction.block_partition.BlockPartition.block p oB = ok blk ∧
        verified.merc_reduction.block_partition.Block.has_marked blk = ok bm) ∧
      ((bm = true ∧ w1 = w) ∨ (bm = false ∧ alloc.vec.Vec.push w oB = ok w1)) ∧
      verified.merc_reduction.block_partition.BlockPartition.mark_element p f = ok p' ∧
      DirtyInv n p' w1 ∧ p'.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 p' w1 (fun t => D t ∨ t.index.val = f.index.val) := by
  obtain ⟨hp, hnd, hw⟩ := h
  obtain ⟨hK, ho1, ho2⟩ := hp.own _ hf
  set o := e2bAt p f.index.val with ho
  obtain ⟨p', hmark, hp', he2b', hlen', hother, hbeg, hend, hle, hlt, hmk⟩ := mark_element_spec hp f hf
  generalize hoB : p.element_to_block.val.getD f.index.val zBT = oB
  have hoBv : oB.index.val = o := by rw [← hoB]; exact e2bAt_eq hp _ hf
  have hoBlt : oB.index.val < p.blocks.val.length := by rw [hoBv]; exact hK
  have hblk : p.blocks.slice.val[oB.index.val] = blkAt p o := by
    rw [blkAt_eq_getElem hK]; simp only [hoBv]; rfl
  have hbn : verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number p f = ok oB := by
    rw [block_number_ok hp f hf, hoB]
  have hblock : verified.merc_reduction.block_partition.BlockPartition.block p oB = ok (blkAt p o) := by
    rw [block_partition_block_val p oB hoBlt, hblk]
  have hhm := block_has_marked_contract (blkAt p o)
  have hNle := hp.blocks_le_n
  have hbeg' : (blkAt p' o).begin = (blkAt p o).begin := hbeg
  have hend' : (blkAt p' o).«end» = (blkAt p o).«end» := hend
  by_cases hm : (blkAt p o).marked_split.val < (blkAt p o).«end».val
  · have hq := queued_of_has_marked hp hsem hK hm
    refine ⟨oB, true, p', w, hbn, ⟨_, hblock, by rw [hhm]; simp [hm]⟩, Or.inl ⟨rfl, rfl⟩, hmark,
      ⟨hp', hnd, ?_⟩, hlen', ?_⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := hw x hx
      refine ⟨by rw [hlen']; exact hx1, ?_⟩
      by_cases hxo : x.index.val = o
      · rw [hxo]; rw [hend']; have := hle; omega
      · rw [hother _ hxo]; exact hx2
    · exact DirtySem.mark hsem f he2b' hmk (fun x hx => hx) hq
  · have hnm : ¬ (blkAt p o).marked_split.val < (blkAt p o).«end».val := hm
    have hnotin : oB ∉ w.val := by
      intro hin
      have := (hw oB hin).2
      rw [hoBv] at this
      exact hnm this
    have hnd' : (w.val ++ [oB]).Nodup := by
      refine List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      intro hab; subst hab; exact hnotin ha
    have hlenle : (w.val ++ [oB]).length ≤ p.blocks.val.length :=
      nodup_bounded_length_le _ _ hnd' (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (hw x hx).1
        · simp at hx; subst hx; exact hoBlt)
    have hwlen : w.val.length < Usize.max := by
      simp at hlenle; omega
    obtain ⟨w1, hpush, hw1⟩ := spec_imp_exists (alloc.vec.Vec.push_spec w oB hwlen)
    refine ⟨oB, false, p', w1, hbn, ⟨_, hblock, by rw [hhm]; simp [hnm]⟩, Or.inr ⟨rfl, hpush⟩, hmark,
      ⟨hp', by rw [hw1]; exact hnd', ?_⟩, hlen', ?_⟩
    · intro x hx
      rw [hw1] at hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hx1, hx2⟩ := hw x hx
        refine ⟨by rw [hlen']; exact hx1, ?_⟩
        by_cases hxo : x.index.val = o
        · rw [hxo]; rw [hend']; have := hle; omega
        · rw [hother _ hxo]; exact hx2
      · simp at hx; subst hx
        refine ⟨by rw [hlen']; exact hoBlt, ?_⟩
        rw [hoBv, hend']; exact hlt
    · refine DirtySem.mark hsem f he2b' hmk (fun x hx => by rw [hw1]; exact List.mem_append_left _ hx) ?_
      exact ⟨oB, by rw [hw1]; simp, hoBv⟩

theorem into_iter_next_some' {T : Type} (it : alloc.vec.into_iter.IntoIter T) (v : T) (tl : List T)
    (h : it.val = v :: tl) :
    ∃ it1 : alloc.vec.into_iter.IntoIter T,
      alloc.vec.into_iter.IteratorIntoIter.next it = ok (some v, it1) ∧ it1.val = tl := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rename_i heq'
    have : v :: tl = [] := h.symm.trans heq'
    cases this
  · rename_i hd' tl' heq'
    have hvc : v :: tl = hd' :: tl' := h.symm.trans heq'
    cases hvc
    refine ⟨alloc.vec.Vec.from tl (by grind), ?_⟩
    constructor
    · congr
    · simp [alloc.vec.Vec.from, alloc.vec.Vec.val]

theorem into_iter_next_none' {T : Type} (it : alloc.vec.into_iter.IntoIter T) (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rfl
  · rename_i hd' tl' heq'
    have : hd' :: tl' = [] := heq'.symm.trans h
    cases this

/-- The states that have an incoming transition recorded in `incoming` from a state of `S`'s
    successors: `t` is a source of a transition into some state of `S`. -/
def PredOf (incoming : IncomingTransitions) (S : List ST) (t : ST) : Prop :=
  ∃ s ∈ S, ∃ res : alloc.vec.Vec FromTransition,
    IncomingTransitions.incoming_transitions incoming s = ok res ∧
      ∃ i ∈ res.val, i.«from».index.val = t.index.val

/-- The states with a transition into block `bl` of `p`. -/
def PredBlk (incoming : IncomingTransitions) (n : Nat) (p : BlockPartition) (bl : Nat) (t : ST) : Prop :=
  ∃ s : ST, s.index.val < n ∧ e2bAt p s.index.val = bl ∧
    ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∃ i ∈ res.val, i.«from».index.val = t.index.val

/-- The inner loop of `mark_dirty_states` (non-branching): all incoming transitions of one state. -/
theorem dirty_inner_loop {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (num_blocks : Sz) {n : Nat} (hn : n ≤ Usize.max)
    (iter : alloc.vec.into_iter.IntoIter FromTransition) (l : List FromTransition)
    (hl : iter.val = l) (hf : ∀ i ∈ l, i.«from».index.val < n)
    {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (h : DirtyInv n p w)
    (hsem : DirtySem n p1 p w D) :
    ∃ p' w', verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0 false LTSInst
        iter lts p w num_blocks = ok (p', w') ∧ DirtyInv n p' w' ∧
      p'.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 p' w' (fun t => D t ∨ ∃ i ∈ l, i.«from».index.val = t.index.val) := by
  unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0
  have hDm : ∀ m (hm : m < l.length) (t : ST),
      ((D t ∨ ∃ i ∈ l.take m, i.«from».index.val = t.index.val) ∨ t.index.val = l[m].«from».index.val) ↔
      (D t ∨ ∃ i ∈ l.take (m + 1), i.«from».index.val = t.index.val) := by
    intro m hm t
    rw [List.take_succ_eq_append_getElem hm]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ((h | ⟨i, hi, e⟩) | e)
      · exact Or.inl h
      · exact Or.inr ⟨i, Or.inl hi, e⟩
      · exact Or.inr ⟨l[m], Or.inr rfl, e.symm⟩
    · rintro (h | ⟨i, hi | hi, e⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨i, hi, e⟩)
      · subst hi; exact Or.inr e.symm
  obtain ⟨y, hy, hp', hw', hyl, hysem⟩ := loop_nat_spec
    (fun (x : alloc.vec.into_iter.IntoIter FromTransition × BlockPartition × VecTy BT) =>
      verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body false LTSInst lts
        num_blocks x.1 x.2.1 x.2.2)
    (fun x => l.length - x.1.val.length)
    (fun m x => m ≤ l.length ∧ x.1.val = l.drop m ∧ DirtyInv n x.2.1 x.2.2 ∧
      x.2.1.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 x.2.1 x.2.2 (fun t => D t ∨ ∃ i ∈ l.take m, i.«from».index.val = t.index.val))
    (fun y => DirtyInv n y.1 y.2 ∧ y.1.blocks.val.length = p.blocks.val.length ∧ True ∧
      DirtySem n p1 y.1 y.2 (fun t => D t ∨ ∃ i ∈ l, i.«from».index.val = t.index.val))
    l.length
    (by intro m x hx; obtain ⟨h1, h2, -⟩ := hx; rw [h2]; simp; omega)
    (by intro m x hx; exact hx.1)
    (by
      intro m x hm hx
      obtain ⟨-, h2, h3, h4, h5⟩ := hx
      have hdrop : l.drop m = l[m] :: l.drop (m + 1) := List.drop_eq_getElem_cons hm
      obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' x.1 l[m] (l.drop (m + 1)) (by rw [h2, hdrop])
      obtain ⟨oB, bm, p1', w1, hbn, ⟨blk, hblk, hhm⟩, hcase, hmk, hI, hlen, hsem'⟩ :=
        dirty_transition_step h3 h5 hn l[m].«from» (hf _ (List.getElem_mem hm))
      refine ⟨(it1, p1', w1), ?_, hm, by rw [hit1], hI, by rw [hlen, h4],
        hsem'.congr (fun t _ => hDm m hm t)⟩
      show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body false LTSInst lts
        num_blocks x.1 x.2.1 x.2.2 = _
      unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body
      rw [hnext]
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, hpush⟩
      · simp [hbn, hblk, hhm, hmk]
      · simp [hbn, hblk, hhm, hpush, hmk])
    (by
      intro x hx
      obtain ⟨hm, h2, h3, h4, h5⟩ := hx
      have : x.1.val = [] := by rw [h2]; simp
      refine ⟨(x.2.1, x.2.2), ?_, h3, h4, trivial, by simpa using h5⟩
      show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body false LTSInst lts
        num_blocks x.1 x.2.1 x.2.2 = _
      unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body
      rw [into_iter_next_none' _ this]
      simp)
    (iter, p, w) ⟨by omega, by rw [hl]; simp, h, rfl, by simpa using hsem⟩
  exact ⟨y.1, y.2, hy, hp', hw', hysem⟩


/-- The outer loop of `mark_dirty_states` (non-branching): all states of the new block, each with
    all its incoming transitions. -/
theorem dirty_outer_loop {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : IncomingTransitions) (num_blocks : Sz) {n : Nat} (hn : n ≤ Usize.max)
    (hinc : ∀ s : ST, s.index.val < n → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n)
    (sl : Slice ST) (hsl : ∀ s ∈ sl.val, s.index.val < n)
    {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (h : DirtyInv n p w)
    (hsem : DirtySem n p1 p w D) :
    ∃ p' w', verified.merc_reduction.signature_refinement.mark_dirty_states_loop0 false LTSInst
        ({ slice := sl, i := 0 } : core.slice.iter.Iter ST) lts p incoming w num_blocks = ok (p', w') ∧
      DirtyInv n p' w' ∧ p'.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 p' w' (fun t => D t ∨ PredOf incoming sl.val t) := by
  unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0
  have hPm : ∀ m (hm : m < sl.val.length) (res : alloc.vec.Vec FromTransition)
      (hres : IncomingTransitions.incoming_transitions incoming sl.val[m] = ok res) (t : ST),
      ((D t ∨ PredOf incoming (sl.val.take m) t) ∨ ∃ i ∈ res.val, i.«from».index.val = t.index.val) ↔
      (D t ∨ PredOf incoming (sl.val.take (m + 1)) t) := by
    intro m hm res hres t
    unfold PredOf
    rw [List.take_succ_eq_append_getElem hm]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ((h | ⟨s, hs, r, hr, i, hi, e⟩) | ⟨i, hi, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, Or.inl hs, r, hr, i, hi, e⟩
      · exact Or.inr ⟨sl.val[m], Or.inr rfl, res, hres, i, hi, e⟩
    · rintro (h | ⟨s, hs | hs, r, hr, i, hi, e⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨s, hs, r, hr, i, hi, e⟩)
      · subst hs
        have : r = res := by simpa using hr.symm.trans hres
        subst this
        exact Or.inr ⟨i, hi, e⟩
  obtain ⟨y, hy, hp', hw', hysem⟩ := loop_nat_spec
    (fun (x : core.slice.iter.Iter ST × BlockPartition × VecTy BT) =>
      verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body false LTSInst lts
        incoming num_blocks x.1 x.2.1 x.2.2)
    (fun x => x.1.i)
    (fun m x => x.1.slice = sl ∧ x.1.i = m ∧ m ≤ sl.val.length ∧ DirtyInv n x.2.1 x.2.2 ∧
      x.2.1.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 x.2.1 x.2.2 (fun t => D t ∨ PredOf incoming (sl.val.take m) t))
    (fun y => DirtyInv n y.1 y.2 ∧ y.1.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 y.1 y.2 (fun t => D t ∨ PredOf incoming sl.val t))
    sl.val.length
    (by intro m x hx; exact hx.2.1) (by intro m x hx; exact hx.2.2.1)
    (by
      intro m x hm hx
      obtain ⟨h1, h2, -, h3, h4, h5⟩ := hx
      obtain ⟨x1, x2, x3⟩ := x
      obtain ⟨xs, xi⟩ := x1
      simp only at h1 h2 h3 h4 h5
      subst h1; subst h2
      have hml : xi < xs.length := by simpa [Slice.length] using hm
      have hnext : core.slice.iter.IteratorSliceIter.next
          ({ slice := xs, i := xi } : core.slice.iter.Iter ST)
          = ok (some (xs.val[xi]'hml), ({ slice := xs, i := xi + 1 } : core.slice.iter.Iter ST)) := by
        unfold core.slice.iter.IteratorSliceIter.next
        simp [hml, Slice.len]
        rfl
      obtain ⟨res, hres, hresn⟩ := hinc _ (hsl _ (List.getElem_mem hml))
      obtain ⟨p1', w1, hloop, hI, hlen, hsem'⟩ := dirty_inner_loop LTSInst lts num_blocks hn
        (res : alloc.vec.into_iter.IntoIter FromTransition) res.val rfl hresn h3 h5
      refine ⟨(⟨xs, xi + 1⟩, p1', w1), ?_, rfl, rfl, by omega, hI, by rw [hlen, h4],
        hsem'.congr (fun t _ => hPm xi hml res hres t)⟩
      · show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body false LTSInst lts
          incoming num_blocks ⟨xs, xi⟩ x2 x3 = _
        unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body
        rw [hnext]
        simp [hres, alloc.vec.IntoIteratorVec.into_iter, hloop])
    (by
      intro x hx
      obtain ⟨h1, h2, -, h3, h4, h5⟩ := hx
      obtain ⟨x1, x2, x3⟩ := x
      obtain ⟨xs, xi⟩ := x1
      simp only at h1 h2 h3 h4 h5
      subst h1
      have hml : ¬ xi < xs.length := by
        intro hh; have := hh; simp [Slice.length] at this; omega
      have hnext : core.slice.iter.IteratorSliceIter.next ({ slice := xs, i := xi } : core.slice.iter.Iter ST)
          = ok (none, ({ slice := xs, i := xi } : core.slice.iter.Iter ST)) := by
        unfold core.slice.iter.IteratorSliceIter.next
        simp [hml, Slice.len]
      refine ⟨(x2, x3), ?_, h3, h4, by simpa using h5⟩
      show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body false LTSInst lts
          incoming num_blocks ⟨xs, xi⟩ x2 x3 = _
      unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body
      rw [hnext]
      simp)
    (⟨sl, 0⟩, p, w) ⟨rfl, rfl, by omega, h, rfl, by simpa [PredOf] using hsem⟩
  exact ⟨y.1, y.2, hy, hp', hw', hysem⟩


/-- The states of block `nb`: exactly the members of the window `regionElems` of its range. -/
theorem regionElems_mem_iff {n : Nat} {p : BlockPartition} (hp : PartInv n p) {nb : Nat}
    (hnb : nb < p.blocks.val.length) (x : ST) :
    x ∈ regionElems p (blkAt p nb).begin.val ((blkAt p nb).«end».val - (blkAt p nb).begin.val) ↔
      (x.index.val < n ∧ e2bAt p x.index.val = nb) := by
  have hbk := hp.blk nb hnb
  rw [mem_old_iff _ _ _ (List.Perm.refl _) x]
  constructor
  · rintro ⟨q, h1, h2, rfl⟩
    have hq : q < n := by omega
    obtain ⟨hx1, hx2⟩ := hp.perm q hq
    refine ⟨hx1, ?_⟩
    obtain ⟨o1, o2, o3⟩ := hp.own _ hx1
    rw [hx2] at o2 o3
    exact hp.pos_block_unique o1 hnb ⟨o2, o3⟩ ⟨h1, by omega⟩
  · rintro ⟨hx, he⟩
    obtain ⟨o1, o2, o3⟩ := hp.own _ hx
    rw [he] at o2 o3
    refine ⟨offAt p x.index.val, o2, by omega, ?_⟩
    exact tag_eq_of_val (hp.inv _ hx)


/-- `mark_dirty_states` (non-branching) on a valid block keeps the worklist invariant and marks
    exactly the sources of transitions into the block. -/
theorem dirty_states_spec {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : IncomingTransitions) (num_blocks : Sz) {n : Nat} (hn : n ≤ Usize.max)
    (hinc : ∀ s : ST, s.index.val < n → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n)
    {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (h : DirtyInv n p w)
    (hsem : DirtySem n p1 p w D)
    (states : VecTy ST) (nb : BT) (hnb : nb.index.val < p.blocks.val.length) :
    ∃ p' w' states',
      verified.merc_reduction.signature_refinement.mark_dirty_states false LTSInst lts p incoming w
        states nb num_blocks = ok (p', w', states') ∧
      DirtyInv n p' w' ∧ p'.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 p' w' (fun t => D t ∨ PredBlk incoming n p nb.index.val t) := by
  have hp := h.1
  have hbk := hp.blk nb.index.val hnb
  obtain ⟨v1, hv1, hv10⟩ := alloc.vec.Vec.clear_spec Global states
  have hnle : n ≤ Usize.max := hn
  have hlenE : (alloc.vec.Vec.deref p.elements).val.length = n := by
    simp [alloc.vec.Vec.deref, hp.len_e]
  have hbi : verified.merc_reduction.block_partition.BlockPartition.iter_block p nb
      = ok { elements := alloc.vec.Vec.deref p.elements, index := (blkAt p nb.index.val).begin,
             «end» := (blkAt p nb.index.val).«end» } := by
    unfold verified.merc_reduction.block_partition.BlockPartition.iter_block
    rw [vec_tagged_index_val p.blocks nb hnb]
    have hrd : p.blocks.slice.val[nb.index.val]'hnb = blkAt p nb.index.val := (blkAt_eq_getElem hnb).symm
    simp [hrd]
  obtain ⟨v2, hv2, hv2v⟩ := alloc.vec.Vec.extend_blockIter_spec v1
    { elements := alloc.vec.Vec.deref p.elements, index := (blkAt p nb.index.val).begin,
      «end» := (blkAt p nb.index.val).«end» }
    (by simp only []; omega) (by simp only []; rw [hv10]; simp; omega)
  have hwin : ((alloc.vec.Vec.deref p.elements).val.drop (blkAt p nb.index.val).begin.val).take
      ((blkAt p nb.index.val).«end».val - (blkAt p nb.index.val).begin.val)
      = regionElems p (blkAt p nb.index.val).begin.val
        ((blkAt p nb.index.val).«end».val - (blkAt p nb.index.val).begin.val) := by
    rw [region_eq_window hp _ _ (by omega)]
    simp [alloc.vec.Vec.deref, Slice.from_val]
  have hv2mem : ∀ s, s ∈ v2.val ↔ (s.index.val < n ∧ e2bAt p s.index.val = nb.index.val) := by
    intro s
    rw [hv2v, hv10]
    simp only [List.nil_append]
    rw [hwin]
    exact regionElems_mem_iff hp hnb s
  have hsl : ∀ s ∈ (alloc.vec.Vec.deref v2).val, s.index.val < n := by
    intro s hs
    have hs' : s ∈ v2.val := by simpa [alloc.vec.Vec.deref, Slice.from_val] using hs
    exact ((hv2mem s).mp hs').1
  obtain ⟨p', w', hloop, hI, hlen, hsem'⟩ := dirty_outer_loop LTSInst lts incoming num_blocks hn hinc
    (alloc.vec.Vec.deref v2) hsl h hsem
  refine ⟨p', w', v2, ?_, hI, hlen, hsem'.congr (fun t _ => ?_)⟩
  · unfold verified.merc_reduction.signature_refinement.mark_dirty_states
    simp [hv1, hbi, hv2, core.slice.Slice.iter, hloop]
  · have hval : (alloc.vec.Vec.deref v2).val = v2.val := by simp [alloc.vec.Vec.deref, Slice.from_val]
    rw [hval]
    constructor
    · rintro (h | ⟨s, hs, r⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, ((hv2mem s).mp hs).1, ((hv2mem s).mp hs).2, r⟩
    · rintro (h | ⟨s, hs1, hs2, r⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, (hv2mem s).mpr ⟨hs1, hs2⟩, r⟩


/-- `mark_dirty_new_blocks` (the `markDirtyAcc` fold, non-branching) keeps the worklist invariant and
    marks exactly the sources of transitions into the scanned blocks. -/
theorem markDirtyAcc_spec {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : IncomingTransitions) (block_index : BT) (num_blocks : Sz) {n : Nat}
    (hn : n ≤ Usize.max)
    (hinc : ∀ s : ST, s.index.val < n → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n) :
    ∀ (l : List BT) {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (s : VecTy ST),
      (∀ nb ∈ l, nb.index.val < p.blocks.val.length) → DirtyInv n p w → DirtySem n p1 p w D →
      ∃ p' w' s', markDirtyAcc false LTSInst lts incoming block_index num_blocks p w s l
          = ok (p', w', s') ∧ DirtyInv n p' w' ∧ p'.blocks.val.length = p.blocks.val.length ∧
        DirtySem n p1 p' w' (fun t => D t ∨ ∃ nb ∈ l, nb ≠ block_index ∧
          PredBlk incoming n p1 nb.index.val t) := by
  intro l
  induction l with
  | nil =>
    intro p1 p w D s _ h hsem
    exact ⟨p, w, s, by simp [markDirtyAcc], h, rfl, hsem.congr (fun t _ => by simp)⟩
  | cons nb tl ih =>
    intro p1 p w D s hl h hsem
    rw [markDirtyAcc_cons]
    by_cases hb : block_index = nb
    · rw [markDirtyStep_pos false LTSInst lts incoming block_index num_blocks nb p w s hb]
      simp only [bind_tc_ok]
      obtain ⟨p2, w2, s2, hrest, hI2, hlen2, hsem2⟩ :=
        ih s (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h hsem
      refine ⟨p2, w2, s2, hrest, hI2, hlen2, hsem2.congr (fun t _ => ?_)⟩
      constructor
      · rintro (h | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl h
        · exact Or.inr ⟨nb', List.mem_cons_of_mem _ hnb', hne, r⟩
      · rintro (h | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hnb' with rfl | hnb'
          · exact absurd hb.symm hne
          · exact Or.inr ⟨nb', hnb', hne, r⟩
    · rw [markDirtyStep_neg false LTSInst lts incoming block_index num_blocks nb p w s hb]
      obtain ⟨p1', w1, s1, hst, hI, hlen, hsem1⟩ := dirty_states_spec LTSInst lts incoming num_blocks hn hinc h hsem s nb
        (hl nb (List.mem_cons_self ..))
      rw [hst]
      simp only [bind_tc_ok]
      obtain ⟨p2, w2, s2, hrest, hI2, hlen2, hsem2⟩ := ih s1
        (fun x hx => by rw [hlen]; exact hl x (List.mem_cons_of_mem _ hx)) hI hsem1
      refine ⟨p2, w2, s2, hrest, hI2, by rw [hlen2, hlen], hsem2.congr (fun t _ => ?_)⟩
      have he : e2bAt p nb.index.val = e2bAt p nb.index.val := rfl
      have hpp1 : ∀ x, e2bAt p x = e2bAt p1 x := fun x => by simp [e2bAt, hsem.1]
      have hPB : ∀ bl, PredBlk incoming n p bl t ↔ PredBlk incoming n p1 bl t := by
        intro bl
        unfold PredBlk
        simp only [hpp1]
      constructor
      · rintro ((h | hP) | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl h
        · exact Or.inr ⟨nb, List.mem_cons_self .., hb ∘ Eq.symm, (hPB _).mp hP⟩
        · exact Or.inr ⟨nb', List.mem_cons_of_mem _ hnb', hne, r⟩
      · rintro (h | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hnb' with rfl | hnb'
          · exact Or.inl (Or.inr ((hPB _).mpr r))
          · exact Or.inr ⟨nb', hnb', hne, r⟩

end MercVerified.Refinement.Proofs
