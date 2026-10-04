import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Partition_Proofs
import MercVerified.Refinement.Proofs.PartitionInv_Proofs
import MercVerified.Refinement.Proofs.LoopTools_Proofs
import MercVerified.Refinement.Proofs.SwapBlocks_Proofs
import Sigref.Proofs.CountingSort_Proofs
import MercVerified.Refinement.Proofs.FinishPartition_Proofs
import MercVerified.Refinement.Proofs.ScatterLoop_Proofs
import MercVerified.Refinement.Proofs.SplitPartInv_Proofs
import Aeneas.Std.WP

/-!
# The block-creation loop of `finish_partition_marked`

`finish_partition_marked_loop0` walks the class sizes, creating one new block per class (the
first class reuses the old block when the block has no unmarked part), and overwrites each size
with the class's start offset (through the `IterMut`'s write-back closure).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition Block)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

open Sigref

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- `Block::new_unmarked begin end` on a non-empty range. -/
theorem new_unmarked_ok (bg e : Std.Usize) (h : bg.val < e.val) :
    verified.merc_reduction.block_partition.Block.new_unmarked bg e = ok (unmRec bg e) := by
  unfold verified.merc_reduction.block_partition.Block.new_unmarked
  simp [h, unmRec]

/-- One iteration of `finish_partition_marked_loop0` when the current class is the first one and
    the block has an unmarked part: the old block keeps the unmarked part, class `0` becomes a new
    block. -/
theorem finish0_step_first_unmarked
    (deref_mut_back : Slice Std.Usize → alloc.vec.Vec Std.Usize)
    (iter_mut_back : core.slice.iter.IterMut Std.Usize → Slice Std.Usize)
    (E : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (B : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (O : alloc.vec.Vec Std.Usize)
    (block_index : TagIndex Std.Usize BlockTag)
    (idxv : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (end_of_blocks new_block_index : Std.Usize)
    (S : Slice Std.Usize) (m : Nat)
    (back : core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize)
    (v5 : alloc.vec.Vec Block) (block : Block)
    (hblock : merc_reduction.block_partition.Block.WellFormed block)
    (hm : m < S.val.length) (hpos : 0 < (S.val[m]'hm).val)
    (hb : block_index.index.val < v5.val.length)
    (hun : block.begin.val < block.marked_split.val)
    (hadd : block.marked_split.val + (S.val[m]'hm).val ≤ Usize.max)
    (hpush : v5.val.length < Usize.max) :
    ∃ (i1 : Std.Usize) (v6 : alloc.vec.Vec Block),
      i1.val = block.marked_split.val + (S.val[m]'hm).val ∧
      v6.val = v5.val.set block_index.index.val (unmRec block.begin block.marked_split) ++
        [unmRec block.marked_split i1] ∧
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
        deref_mut_back iter_mut_back E B O block_index idxv old end_of_blocks new_block_index
        ({ slice := S, i := m } : core.slice.iter.IterMut Std.Usize) back v5 block 0#usize
      = ok (cont ({ slice := S, i := m + 1 },
          fun im => back { im with slice := im.slice.setAtNat m block.marked_split },
          v6, block, i1)) := by
  have hmS : m < S.length := hm
  obtain ⟨i1, hi1, hi1v⟩ := spec_imp_exists
    (Usize.add_spec (x := block.marked_split) (y := S.val[m]'hm) (by omega))
  have hv8 : ({ slice := v5.slice.set block_index.index (unmRec block.begin block.marked_split) } :
      alloc.vec.Vec Block).val = v5.val.set block_index.index.val
      (unmRec block.begin block.marked_split) := by
    show (v5.slice.set _ _).val = _
    rw [Slice.set_val_eq]; rfl
  have hv8len : ({ slice := v5.slice.set block_index.index (unmRec block.begin block.marked_split) } :
      alloc.vec.Vec Block).val.length = v5.val.length := by rw [hv8]; simp
  obtain ⟨v9, hpush9, hv9⟩ := vec_push_val
    ({ slice := v5.slice.set block_index.index (unmRec block.begin block.marked_split) } :
      alloc.vec.Vec Block) (unmRec block.marked_split i1) (by omega)
  refine ⟨i1, v9, hi1v, by rw [hv9, hv8], ?_⟩
  unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
  have hnext : core.slice.iter.IteratorIterMut.next
      ({ slice := S, i := m } : core.slice.iter.IterMut Std.Usize) = ok (some (S.val[m]'hm),
        ({ slice := S, i := m + 1 } : core.slice.iter.IterMut Std.Usize),
        fun it' x => match x with
          | none => it'
          | some x => { it' with slice := it'.slice.setAtNat m x }) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dif_pos (by simpa [Slice.len] using hmS)]
    simp only []
    congr
    funext it' x
    cases x <;> rfl
  have hhas : block.has_unmarked = ok true := by
    rw [block_has_unmarked_contract block hblock]; simp [hun]
  have hnu1 := new_unmarked_ok block.begin block.marked_split hun
  have hnu2 := new_unmarked_ok block.marked_split i1 (by omega)
  simp [hnext, massert, hpos, hhas, hnu1, hnu2, vec_tagged_index_mut_ok v5 block_index hb,
    hi1, hpush9]

/-- First class, block without an unmarked part: the old block itself becomes class `0`'s block. -/
theorem finish0_step_first_plain
    (deref_mut_back : Slice Std.Usize → alloc.vec.Vec Std.Usize)
    (iter_mut_back : core.slice.iter.IterMut Std.Usize → Slice Std.Usize)
    (E : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (B : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (O : alloc.vec.Vec Std.Usize)
    (block_index : TagIndex Std.Usize BlockTag)
    (idxv : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (end_of_blocks new_block_index : Std.Usize)
    (S : Slice Std.Usize) (m : Nat)
    (back : core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize)
    (v5 : alloc.vec.Vec Block) (block : Block)
    (hblock : merc_reduction.block_partition.Block.WellFormed block)
    (hm : m < S.val.length) (hpos : 0 < (S.val[m]'hm).val)
    (hb : block_index.index.val < v5.val.length)
    (hun : ¬ block.begin.val < block.marked_split.val)
    (hadd : block.begin.val + (S.val[m]'hm).val ≤ Usize.max) :
    ∃ (i1 : Std.Usize) (v6 : alloc.vec.Vec Block),
      i1.val = block.begin.val + (S.val[m]'hm).val ∧
      v6.val = v5.val.set block_index.index.val (unmRec block.begin i1) ∧
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
        deref_mut_back iter_mut_back E B O block_index idxv old end_of_blocks new_block_index
        ({ slice := S, i := m } : core.slice.iter.IterMut Std.Usize) back v5 block 0#usize
      = ok (cont ({ slice := S, i := m + 1 },
          fun im => back { im with slice := im.slice.setAtNat m block.begin },
          v6, block, i1)) := by
  have hmS : m < S.length := hm
  have hnext : core.slice.iter.IteratorIterMut.next
      ({ slice := S, i := m } : core.slice.iter.IterMut Std.Usize) = ok (some (S.val[m]'hm),
        ({ slice := S, i := m + 1 } : core.slice.iter.IterMut Std.Usize),
        fun it' x => match x with
          | none => it'
          | some x => { it' with slice := it'.slice.setAtNat m x }) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dif_pos (by simpa [Slice.len] using hmS)]
    simp only []
    congr
    funext it' x
    cases x <;> rfl
  obtain ⟨i1, hi1, hi1v⟩ := spec_imp_exists
    (Usize.add_spec (x := block.begin) (y := S.val[m]'hm) (by omega))
  have hv8 : ({ slice := v5.slice.set block_index.index (unmRec block.begin i1) } :
      alloc.vec.Vec Block).val = v5.val.set block_index.index.val (unmRec block.begin i1) := by
    show (v5.slice.set _ _).val = _
    rw [Slice.set_val_eq]; rfl
  refine ⟨i1, { slice := v5.slice.set block_index.index (unmRec block.begin i1) }, hi1v, hv8, ?_⟩
  unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
  have hhas : block.has_unmarked = ok false := by
    rw [block_has_unmarked_contract block hblock]; simp [hun]
  have hnu1 := new_unmarked_ok block.begin i1 (by omega)
  simp [hnext, massert, hpos, hhas, hnu1, vec_tagged_index_mut_ok v5 block_index hb, hi1]

/-- Later classes: a fresh block `[current, current + size)` is appended. -/
theorem finish0_step_later
    (deref_mut_back : Slice Std.Usize → alloc.vec.Vec Std.Usize)
    (iter_mut_back : core.slice.iter.IterMut Std.Usize → Slice Std.Usize)
    (E : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (B : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (O : alloc.vec.Vec Std.Usize)
    (block_index : TagIndex Std.Usize BlockTag)
    (idxv : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (end_of_blocks new_block_index : Std.Usize)
    (S : Slice Std.Usize) (m : Nat)
    (back : core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize)
    (v5 : alloc.vec.Vec Block) (block : Block)
    (hm : m < S.val.length) (hpos : 0 < (S.val[m]'hm).val)
    (current : Std.Usize) (hcur : current.val ≠ 0)
    (hadd : current.val + (S.val[m]'hm).val ≤ Usize.max)
    (hpush : v5.val.length < Usize.max) :
    ∃ (i1 : Std.Usize) (v6 : alloc.vec.Vec Block),
      i1.val = current.val + (S.val[m]'hm).val ∧
      v6.val = v5.val ++ [unmRec current i1] ∧
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
        deref_mut_back iter_mut_back E B O block_index idxv old end_of_blocks new_block_index
        ({ slice := S, i := m } : core.slice.iter.IterMut Std.Usize) back v5 block current
      = ok (cont ({ slice := S, i := m + 1 },
          fun im => back { im with slice := im.slice.setAtNat m current },
          v6, block, i1)) := by
  have hmS : m < S.length := hm
  have hnext : core.slice.iter.IteratorIterMut.next
      ({ slice := S, i := m } : core.slice.iter.IterMut Std.Usize) = ok (some (S.val[m]'hm),
        ({ slice := S, i := m + 1 } : core.slice.iter.IterMut Std.Usize),
        fun it' x => match x with
          | none => it'
          | some x => { it' with slice := it'.slice.setAtNat m x }) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dif_pos (by simpa [Slice.len] using hmS)]
    simp only []
    congr
    funext it' x
    cases x <;> rfl
  obtain ⟨i1, hi1, hi1v⟩ := spec_imp_exists
    (Usize.add_spec (x := current) (y := S.val[m]'hm) (by omega))
  obtain ⟨v9, hpush9, hv9⟩ := vec_push_val v5 (unmRec current i1) hpush
  refine ⟨i1, v9, hi1v, hv9, ?_⟩
  unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
  have hnu1 := new_unmarked_ok current i1 (by omega)
  have hne : ¬ current = 0#usize := fun h => hcur (by rw [h]; rfl)
  simp [hnext, massert, hpos, hne, hnu1, hi1, hpush9]

/-- The first record: the unmarked part keeps the old block when there is one, otherwise class `0`
    takes it. -/
def firstRec (u : Bool) (block : Block) (ms : Nat) (szs : List Nat) : Block :=
  if u then unmRec block.begin block.marked_split else pieceRec ms szs 0

/-- The block list after the first `m` classes have been processed. -/
def blkSeq (blocks : List Block) (b : Nat) (u : Bool) (block : Block) (ms : Nat) (szs : List Nat)
    (m : Nat) : List Block :=
  if m = 0 then blocks
  else blocks.set b (firstRec u block ms szs) ++
    (List.range' (firstNew u) (m - firstNew u)).map (pieceRec ms szs)

theorem blkSeq_length (blocks : List Block) (b : Nat) (u : Bool) (block : Block) (ms : Nat)
    (szs : List Nat) (m : Nat) :
    (blkSeq blocks b u block ms szs m).length =
      if m = 0 then blocks.length else blocks.length + (m - firstNew u) := by
  unfold blkSeq; split_ifs <;> simp

/-- `blkSeq K` has exactly the shape `split_partInv` asks of the new block list. -/
theorem blkSeq_getD_new (blocks : List Block) (b : Nat) (u : Bool) (block : Block) (ms : Nat)
    (szs : List Nat) (K : Nat) (hK : 0 < K) (_hb : b < blocks.length) (c : Nat)
    (hc1 : firstNew u ≤ c) (hc2 : c < K) :
    (blkSeq blocks b u block ms szs K).getD (blocks.length + (c - firstNew u)) blk0 =
      pieceRec ms szs c := by
  unfold blkSeq
  rw [if_neg (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp only [List.length_set, Nat.add_sub_cancel_left]
  rw [List.getElem?_map, List.getElem?_range' (by omega)]
  simp only [Option.map_some, Option.getD_some, one_mul]
  congr 1
  omega

theorem blkSeq_getD_first (blocks : List Block) (b : Nat) (u : Bool) (block : Block) (ms : Nat)
    (szs : List Nat) (K : Nat) (hK : 0 < K) (hb : b < blocks.length) :
    (blkSeq blocks b u block ms szs K).getD b blk0 = firstRec u block ms szs := by
  unfold blkSeq
  rw [if_neg (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [hb]

theorem blkSeq_getD_old (blocks : List Block) (b : Nat) (u : Bool) (block : Block) (ms : Nat)
    (szs : List Nat) (K : Nat) (hK : 0 < K) (j : Nat) (hj : j < blocks.length) (hjb : j ≠ b) :
    (blkSeq blocks b u block ms szs K).getD j blk0 = blocks.getD j blk0 := by
  unfold blkSeq
  rw [if_neg (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [hjb.symm, List.getD_eq_getElem?_getD]

theorem drop_set_self {α : Type} (l : List α) (m : Nat) (x : α) (h : m < l.length) :
    (l.set m x).drop m = x :: l.drop (m + 1) := by
  rw [List.set_eq_take_append_cons_drop, if_pos h]
  simp [List.length_take, Nat.min_eq_left h.le]

theorem unmRec_eq_pieceRec (ms : Nat) (szs : List Nat) (K : Nat) (a e : Std.Usize) (c : Nat)
    (hc : c < K) (hbnd : ∀ c', c' ≤ K → cumS ms szs c' < 2 ^ UScalarTy.Usize.numBits)
    (ha : a.val = cumS ms szs c) (he : e.val = cumS ms szs (c + 1)) :
    unmRec a e = pieceRec ms szs c := by
  unfold unmRec pieceRec
  have h1 : a = uTotal (cumS ms szs c) := by
    apply UScalar.eq_of_val_eq; rw [uTotal_val_of_lt (hbnd c (by omega)), ha]
  have h2 : e = uTotal (cumS ms szs (c + 1)) := by
    apply UScalar.eq_of_val_eq; rw [uTotal_val_of_lt (hbnd (c + 1) (by omega)), he]
  rw [← h1, ← h2]

/-- The iterator-mut loop state of `finish_partition_marked_loop0`. -/
abbrev Lp0State := core.slice.iter.IterMut Std.Usize ×
  (core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize) ×
  alloc.vec.Vec Block × Block × Std.Usize

/-- Invariant of the block-creation loop after `m` classes. -/
def Loop0Inv (S : Slice Std.Usize) (block : Block) (ms : Nat) (szs : List Nat)
    (blocks : List Block) (b : Nat) (u : Bool) (K : Nat) (m : Nat) (x : Lp0State) : Prop :=
  ∃ vals : List Std.Usize,
    x.1 = ({ slice := S, i := m } : core.slice.iter.IterMut Std.Usize) ∧ m ≤ K ∧
    x.2.2.1.val = blkSeq blocks b u block ms szs m ∧ x.2.2.2.1 = block ∧
    x.2.2.2.2.val = (if m = 0 then 0 else cumS ms szs m) ∧
    vals.length = m ∧ (∀ j, j < m → (vals.getD j 0#usize).val = cumS ms szs j) ∧
    ∀ im : core.slice.iter.IterMut Std.Usize, m ≤ im.slice.val.length →
      (x.2.1 im).slice.val = vals ++ im.slice.val.drop m ∧ (x.2.1 im).i = im.i

theorem back_step (back : core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize)
    (vals : List Std.Usize) (m : Nat) (nc : Std.Usize) (_hlen : vals.length = m)
    (h8 : ∀ im : core.slice.iter.IterMut Std.Usize, m ≤ im.slice.val.length →
      (back im).slice.val = vals ++ im.slice.val.drop m ∧ (back im).i = im.i) :
    ∀ im : core.slice.iter.IterMut Std.Usize, m + 1 ≤ im.slice.val.length →
      ((fun im : core.slice.iter.IterMut Std.Usize =>
        back { im with slice := im.slice.setAtNat m nc }) im).slice.val =
        (vals ++ [nc]) ++ im.slice.val.drop (m + 1) ∧
      ((fun im : core.slice.iter.IterMut Std.Usize =>
        back { im with slice := im.slice.setAtNat m nc }) im).i = im.i := by
  intro im him
  have hsl : ({ im with slice := im.slice.setAtNat m nc } :
      core.slice.iter.IterMut Std.Usize).slice.val = im.slice.val.set m nc := by
    simp [Slice.setAtNat]
  have hlen' : m ≤ ({ im with slice := im.slice.setAtNat m nc } :
      core.slice.iter.IterMut Std.Usize).slice.val.length := by
    rw [hsl]; simp; omega
  obtain ⟨h1, h2⟩ := h8 _ hlen'
  refine ⟨?_, h2⟩
  show (back { im with slice := im.slice.setAtNat m nc }).slice.val = _
  rw [h1, hsl, drop_set_self _ _ _ (by omega)]
  simp

theorem blkSeq_one (blocks : List Block) (b : Nat) (u : Bool) (block : Block) (ms : Nat)
    (szs : List Nat) :
    blkSeq blocks b u block ms szs 1 =
      blocks.set b (firstRec u block ms szs) ++ (if u then [pieceRec ms szs 0] else []) := by
  unfold blkSeq firstNew
  cases u <;> simp

theorem blkSeq_succ (blocks : List Block) (b : Nat) (u : Bool) (block : Block) (ms : Nat)
    (szs : List Nat) (m : Nat) (hm : 1 ≤ m) :
    blkSeq blocks b u block ms szs (m + 1) =
      blkSeq blocks b u block ms szs m ++ [pieceRec ms szs m] := by
  unfold blkSeq
  rw [if_neg (by omega), if_neg (by omega)]
  have hfn : firstNew u ≤ 1 := by unfold firstNew; split_ifs <;> omega
  have hr : m + 1 - firstNew u = (m - firstNew u) + 1 := by omega
  rw [hr, List.range'_concat, List.map_append, ← List.append_assoc]
  congr 2
  have : firstNew u + 1 * (m - firstNew u) = m := by omega
  rw [this]; simp

theorem loop0_inv_step
    (deref_mut_back : Slice Std.Usize → alloc.vec.Vec Std.Usize)
    (iter_mut_back : core.slice.iter.IterMut Std.Usize → Slice Std.Usize)
    (E : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (B : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (O : alloc.vec.Vec Std.Usize)
    (block_index : TagIndex Std.Usize BlockTag)
    (idxv : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (eob nbiU : Std.Usize)
    (S : Slice Std.Usize) (block : Block)
    (hblock : merc_reduction.block_partition.Block.WellFormed block)
    (ms : Nat) (szs : List Nat) (blocks : List Block)
    (b : Nat) (u : Bool) (K : Nat)
    (hb : block_index.index.val = b) (hbN : b < blocks.length)
    (hS : S.val.map (fun z => z.val) = szs) (hK : szs.length = K)
    (hszpos : ∀ j, j < K → 0 < szs.getD j 0)
    (hms : block.marked_split.val = ms)
    (hu : u = decide (block.begin.val < block.marked_split.val))
    (hbgle : block.begin.val ≤ ms)
    (hcumle : ∀ c, c ≤ K → cumS ms szs c ≤ Usize.max)
    (hNK : blocks.length + K ≤ Usize.max)
    (hbnd : ∀ c, c ≤ K → cumS ms szs c < 2 ^ UScalarTy.Usize.numBits)
    (m : Nat) (hm : m < K) (x : Lp0State)
    (hI : Loop0Inv S block ms szs blocks b u K m x) :
    ∃ x', verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
        deref_mut_back iter_mut_back E B O block_index idxv old eob nbiU x.1 x.2.1 x.2.2.1
        x.2.2.2.1 x.2.2.2.2 = ok (cont x') ∧
      Loop0Inv S block ms szs blocks b u K (m + 1) x' := by
  rcases x with ⟨iter, back, v5, bl, cur⟩
  obtain ⟨vals, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI
  simp only at h1 h3 h4 h5 h8
  subst h1
  have h4' : block = bl := h4.symm
  subst h4'
  have hSlen : S.val.length = K := by
    have := congrArg List.length hS; simpa [hK] using this
  have hSm : m < S.val.length := by omega
  have hsz : (S.val[m]'hSm).val = szs.getD m 0 := by
    have := congrArg (fun l => l[m]?) hS
    simp [List.getElem?_map, List.getElem?_eq_getElem hSm] at this
    rw [List.getD_eq_getElem?_getD]
    rw [← this]; rfl
  have hpos : 0 < (S.val[m]'hSm).val := by rw [hsz]; exact hszpos m hm
  have hc1 := cumS_succ ms szs m (by omega)
  have hgetD : szs.getD m 0 = szs[m]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < szs.length by omega)]
  have hcm : cumS ms szs (m + 1) = cumS ms szs m + (S.val[m]'hSm).val := by
    rw [hc1, hsz, hgetD]
  have hcum0 : cumS ms szs 0 = ms := by simp [cumS]
  have hlenv5 : v5.val.length = blocks.length + (if m = 0 then 0 else m - firstNew u) := by
    rw [h3, blkSeq_length]; split_ifs <;> omega
  have hfn : firstNew u ≤ 1 := by unfold firstNew; split_ifs <;> omega
  by_cases hm0 : m = 0
  · subst hm0
    have hcur : cur = 0#usize := UScalar.eq_of_val_eq (by rw [h5]; simp)
    subst hcur
    have hv5 : v5.val = blocks := by rw [h3]; simp [blkSeq]
    have hb' : block_index.index.val < v5.val.length := by rw [hb, hlenv5]; simp; omega
    have hadd : block.marked_split.val + (S.val[0]'hSm).val ≤ Usize.max := by
      have := hcumle 1 (by omega); rw [hcm, hcum0] at this; rw [hms]; simpa using this
    have hv0 : vals = [] := List.eq_nil_of_length_eq_zero h6
    subst hv0
    by_cases hun : block.begin.val < block.marked_split.val
    · have hu1 : u = true := by rw [hu]; simp [hun]
      obtain ⟨i1, v6, hi1, hv6, hbody⟩ := finish0_step_first_unmarked deref_mut_back iter_mut_back E B
        O block_index idxv old eob nbiU S 0 back v5 block hblock hSm hpos hb' hun hadd
        (by rw [hlenv5]; simp; omega)
      refine ⟨_, hbody, [block.marked_split], rfl, by omega, ?_, rfl, ?_, by simp, ?_, ?_⟩
      · show v6.val = _
        rw [hv6, hv5, blkSeq_one, firstRec, if_pos hu1, if_pos hu1, hb]
        congr 2
        exact unmRec_eq_pieceRec ms szs K block.marked_split i1 0 hm hbnd
          (by rw [hms, hcum0]) (by omega)
      · show i1.val = if 0 + 1 = 0 then 0 else cumS ms szs (0 + 1)
        rw [if_neg (by omega)]; omega
      · intro j hj
        obtain rfl : j = 0 := by omega
        simp [hms, hcum0]
      · exact back_step back [] 0 block.marked_split rfl h8
    · have hu0 : u = false := by rw [hu]; simp [hun]
      have hbg : block.begin.val = ms := by omega
      obtain ⟨i1, v6, hi1, hv6, hbody⟩ := finish0_step_first_plain deref_mut_back iter_mut_back E B O
        block_index idxv old eob nbiU S 0 back v5 block hblock hSm hpos hb' hun (by
          rw [hbg]; rw [hms] at hadd; exact hadd)
      refine ⟨_, hbody, [block.begin], rfl, by omega, ?_, rfl, ?_, by simp, ?_, ?_⟩
      · show v6.val = _
        rw [hv6, hv5, blkSeq_one, firstRec, if_neg (by simp [hu0]), if_neg (by simp [hu0]), hb]
        simp only [List.append_nil]
        congr 1
        exact unmRec_eq_pieceRec ms szs K block.begin i1 0 hm hbnd
          (by rw [hbg, hcum0]) (by omega)
      · show i1.val = if 0 + 1 = 0 then 0 else cumS ms szs (0 + 1)
        rw [if_neg (by omega)]; omega
      · intro j hj
        obtain rfl : j = 0 := by omega
        simp [hbg, hcum0]
      · exact back_step back [] 0 block.begin rfl h8
  · have hcur : cur.val ≠ 0 := by
      rw [h5, if_neg hm0]
      have := hszpos 0 (by omega)
      have h0 : cumS ms szs m ≥ cumS ms szs 1 := cumS_mono ms szs (by omega)
      have h1' : cumS ms szs 1 = cumS ms szs 0 + szs[0]'(by omega) := cumS_succ ms szs 0 (by omega)
      have hg0 : szs.getD 0 0 = szs[0]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < szs.length by omega)]
      omega
    have hadd : cur.val + (S.val[m]'hSm).val ≤ Usize.max := by
      have := hcumle (m + 1) (by omega); rw [hcm] at this
      rw [h5, if_neg hm0]; exact this
    obtain ⟨i1, v6, hi1, hv6, hbody⟩ := finish0_step_later deref_mut_back iter_mut_back E B O
      block_index idxv old eob nbiU S m back v5 block hSm hpos cur hcur hadd
      (by rw [hlenv5, if_neg hm0]; omega)
    refine ⟨_, hbody, vals ++ [cur], rfl, by omega, ?_, rfl, ?_, by simp [h6], ?_, ?_⟩
    · show v6.val = _
      rw [hv6, h3, blkSeq_succ _ _ _ _ _ _ m (by omega)]
      congr 2
      exact unmRec_eq_pieceRec ms szs K cur i1 m hm hbnd (by rw [h5, if_neg hm0])
        (by rw [hi1, hcm, h5, if_neg hm0])
    · show i1.val = _
      rw [if_neg (Nat.succ_ne_zero m), hi1, hcm, h5, if_neg hm0]
    · intro j hj
      by_cases hjm : j < m
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact h7 j hjm
      · have : j = m := by omega
        subst this
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp [h6, h5, if_neg hm0]
    · exact back_step back vals m cur h6 h8

/-- The number of the block that class `c` gets: the old block for class `0` when the block has no
    unmarked part, and the fresh block `N + (c - firstNew u)` otherwise. -/
def labelIdx (bi : Nat) (u : Bool) (N c : Nat) : Nat :=
  if c = 0 ∧ u = false then bi else N + (c - firstNew u)

theorem labelNat_index (b : TagIndex Std.Usize BlockTag) (u : Bool) (nbi : Std.Usize) (N K c : Nat)
    (hN : 1 ≤ N) (hnbi : nbi.val = if u then N else N - 1) (hc : c < K)
    (hNK : N + K < 2 ^ UScalarTy.Usize.numBits) :
    (labelNat b u nbi c).index.val = labelIdx b.index.val u N c := by
  unfold labelNat labelIdx
  by_cases h : c = 0 ∧ u = false
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    show (uTag (Tag := BlockTag) (nbi.val + c)).index.val = _
    have hlt : nbi.val + c < 2 ^ UScalarTy.Usize.numBits := by
      rw [hnbi]; split_ifs <;> omega
    simp only [uTag]
    rw [uTotal_val_of_lt hlt, hnbi]
    unfold firstNew
    by_cases hu : u = true
    · simp [hu]
    · have hu' : u = false := by simpa using hu
      have hc0 : c ≠ 0 := fun e => h ⟨e, hu'⟩
      simp [hu']
      omega

/-- The block of every state after `finish_partition_marked`: a marked state (one of `old`, in class
    `cls[t]`) lands in the piece of its class, all other states keep their block and offset; the
    pieces' indices are exchanged by `swap_blocks b mx` for some `mx` among the new indices. -/
def FinishSem (n : Nat) (p : BlockPartition) (b : TagIndex Std.Usize BlockTag) (K : Nat) (u : Bool)
    (cls : List Nat) (old : List (TagIndex Std.Usize StateTag)) (p3 : BlockPartition) : Prop :=
  ∃ mx : Nat, (mx = b.index.val ∨ (p.blocks.val.length ≤ mx ∧ mx < p.blocks.val.length + (K - firstNew u))) ∧
    (∀ t, t < cls.length → e2bAt p3 (old.getD t zST).index.val =
      swapIdx b.index.val mx (labelIdx b.index.val u p.blocks.val.length (cls.getD t 0))) ∧
    (∀ s, s < n → (∀ t, t < cls.length → (old.getD t zST).index.val ≠ s) →
      e2bAt p3 s = swapIdx b.index.val mx (e2bAt p s) ∧ offAt p3 s = offAt p s)

/-- The exhausted-iterator branch of `finish_partition_marked_loop0.body`: scatter the marked
    elements, pick and swap the largest piece, and return the new block indices. -/
theorem finish0_tail
    {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (b : TagIndex Std.Usize BlockTag) (hb : b.index.val < p.blocks.val.length)
    (hmark : (blkAt p b.index.val).marked_split.val < (blkAt p b.index.val).«end».val)
    (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    (hszpos : ∀ j, j < K → 0 < szs.getD j 0)
    (hlen : cls.length = (blkAt p b.index.val).«end».val - (blkAt p b.index.val).marked_split.val)
    (idxv : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (hidx : idxv.val.map (fun x => x.index.val) = cls)
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (hold : old.val.length = cls.length)
    (hperm : old.val.Perm (regionElems p (blkAt p b.index.val).marked_split.val cls.length))
    (u : Bool)
    (hu : u = decide ((blkAt p b.index.val).begin.val < (blkAt p b.index.val).marked_split.val))
    (hn : n < 2 ^ UScalarTy.Usize.numBits) (hn' : n ≤ Usize.max)
    (hNK : p.blocks.val.length + K ≤ Usize.max)
    (eob nbiU : Std.Usize) (heob : eob.val = p.blocks.val.length)
    (hnbi : nbiU.val = if u then p.blocks.val.length else p.blocks.val.length - 1)
    (deref_mut_back : Slice Std.Usize → alloc.vec.Vec Std.Usize)
    (iter_mut_back : core.slice.iter.IterMut Std.Usize → Slice Std.Usize)
    (hdm : ∀ s, deref_mut_back s = ({ slice := s } : alloc.vec.Vec Std.Usize))
    (him : ∀ it, iter_mut_back it = it.slice)
    (S : Slice Std.Usize) (hS : S.val.map (fun z => z.val) = szs)
    (back : core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize)
    (v5 : alloc.vec.Vec Block) (cur : Std.Usize)
    (hI : Loop0Inv S (blkAt p b.index.val) (blkAt p b.index.val).marked_split.val szs
      p.blocks.val b.index.val u K K
      (({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize), back, v5,
        blkAt p b.index.val, cur)) :
    ∃ (nbi : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (p3 : BlockPartition)
      (bo1 : alloc.vec.Vec Std.Usize),
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
        deref_mut_back iter_mut_back p.elements p.element_to_block p.element_offset b idxv old eob nbiU
        ({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize) back v5 (blkAt p b.index.val) cur
      = ok (done (nbi, p3, bo1)) ∧
      PartInv n p3 ∧ p3.blocks.val.length = p.blocks.val.length + (K - firstNew u) ∧
      nbi.val = b :: (List.range' p.blocks.val.length (K - firstNew u)).map uTag ∧
      (∀ j, j < p.blocks.val.length → j ≠ b.index.val → blkAt p3 j = blkAt p j) ∧
      (∀ j, (j = b.index.val ∨ (p.blocks.val.length ≤ j ∧ j < p.blocks.val.length + (K - firstNew u))) →
        (blkAt p3 j).marked_split.val = (blkAt p3 j).«end».val) ∧
      FinishSem n p b K u cls old.val p3 := by
  obtain ⟨vals, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI
  simp only at h3 h5 h8
  have hSlen : S.val.length = K := by
    have := congrArg List.length hS; simpa [hK] using this
  have hnextnone : core.slice.iter.IteratorIterMut.next
      ({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize)
      = ok (none, ({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize),
        fun it _ => it) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dif_neg (by simp [Slice.len]; omega)]
  have hback : (back ({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize)).slice.val = vals := by
    have := (h8 ({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize) (by simp; omega)).1
    rw [this]; simp [hSlen]
  unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
  simp [hnextnone, him, hdm, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, core.slice.Slice.iter,
    alloc.vec.Vec.deref]
  -- facts about the block being split
  set N := p.blocks.val.length with hN
  set bk := blkAt p b.index.val with hbk
  set ms := bk.marked_split.val with hms
  set en := bk.«end».val with hen
  have hbkr : bk.begin.val < en ∧ en ≤ n ∧ bk.begin.val ≤ ms ∧ ms ≤ en := hp.blk b.index.val hb
  have hmark' : ms < en := hmark
  have hlen' : cls.length = en - ms := hlen
  have hle : ms + cls.length ≤ n := by omega
  have hnd : old.val.Nodup := (hperm.nodup_iff).mpr (regionElems_nodup hp ms cls.length hle)
  have hoidx : ∀ x ∈ old.val, x.index.val < n := by
    intro x hx
    obtain ⟨q, h1, h2, rfl⟩ := (mem_old_iff old.val ms cls.length hperm x).mp hx
    exact (hp.perm q (by omega)).1
  have hKpos : 0 < K := by
    have : 0 < cls.length := by omega
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos this
    have := hlt x hx; omega
  have hbnd : ∀ c, c ≤ K → cumS ms szs c < 2 ^ UScalarTy.Usize.numBits := by
    intro c hc
    have := cumS_le_end ms szs cls K hK hcnt hlt c
    omega
  have hmaxlt := usize_max_succ
  -- the scatter
  have hbo0 : ({ slice := (back ({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize)).slice } :
      alloc.vec.Vec Std.Usize).val = vals := hback
  obtain ⟨E', B', O', bo1, hscat, hsc⟩ := scatter_loop_spec (ms := ms) hK hcnt hlt b old bk
    (partInv_blockWF hp hb) nbiU idxv hidx
    hold hnd p.elements p.element_to_block p.element_offset
    { slice := (back ({ slice := S, i := K } : core.slice.iter.IterMut Std.Usize)).slice } n
    hp.len_e hp.len_e2b hp.len_off (by rw [hbo0]; exact h6)
    (by intro j hj; rw [hbo0]; exact h7 j hj) hle hn hn' hoidx (by rw [hnbi]; split_ifs <;> omega)
  rw [← hu] at hsc
  set p2 : BlockPartition := { elements := E', blocks := v5, element_to_block := B', element_offset := O' } with hp2def
  have hVlen : p2.blocks.val.length = N + (K - firstNew u) := by
    show v5.val.length = _
    rw [h3, blkSeq_length, if_neg (by omega)]
  have hVb : p2.blocks.val.getD b.index.val blk0 =
      (if u then unmRec bk.begin bk.marked_split else pieceRec ms szs 0) := by
    show v5.val.getD b.index.val blk0 = _
    rw [h3, blkSeq_getD_first _ _ _ _ _ _ K hKpos hb]; rfl
  have hVnew : ∀ c, firstNew u ≤ c → c < K →
      p2.blocks.val.getD (N + (c - firstNew u)) blk0 = pieceRec ms szs c := by
    intro c hc1 hc2
    show v5.val.getD _ blk0 = _
    rw [h3]; exact blkSeq_getD_new _ _ _ _ _ _ K hKpos hb c hc1 hc2
  have hVold : ∀ j, j < N → j ≠ b.index.val → p2.blocks.val.getD j blk0 = blkAt p j := by
    intro j hj hjb
    show v5.val.getD j blk0 = _
    rw [h3, blkSeq_getD_old _ _ _ _ _ _ K hKpos j hj hjb]; rfl
  have hNK2 : N + K < 2 ^ UScalarTy.Usize.numBits := by omega
  have hp2 : PartInv n p2 := split_partInv hp b hb hmark szs cls K hK hcnt hlt hszpos hlen old.val hold
    hperm u hu hn hNK2 nbiU bo1.val p2 hsc (by rw [hnbi]) hVlen hVb hVnew hVold
  have hb2 : b.index.val < p2.blocks.val.length := by rw [hVlen]; omega
  obtain ⟨mx, nbi', hnbts, hnbival, hmxmem⟩ := new_block_to_swap_spec hp2 b hb2 eob (by omega)
    (by rw [heob, hVlen]; omega)
  have hnbival' : nbi'.val = b :: (List.range' N (K - firstNew u)).map uTag := by
    rw [hnbival, heob, hVlen]; simp
  have hmxcls : mx.index.val = b.index.val ∨ (N ≤ mx.index.val ∧ mx.index.val < N + (K - firstNew u)) := by
    rw [hnbival'] at hmxmem
    simp only [List.mem_cons, List.mem_map, List.mem_range'_1] at hmxmem
    rcases hmxmem with rfl | ⟨j, hj, rfl⟩
    · left; rfl
    · right
      have : (uTag (Tag := BlockTag) j).index.val = j :=
        uTotal_val_of_lt (by omega)
      rw [this]; omega
  have hmxlt : mx.index.val < p2.blocks.val.length := by rw [hVlen]; omega
  obtain ⟨p3, hswap, hp3, hp3e, hp3o, hp3len, hp3blk, hp3e2b⟩ := swap_blocks_spec hp2 b mx hb2 hmxlt
  have hassert := merc_reduction.block_partition.BlockPartition.assert_consistent_ok p3 hp3
  have hT2 : ∀ i, (i = b.index.val ∨ (N ≤ i ∧ i < N + (K - firstNew u))) →
      (blkAt p2 i).marked_split.val = (blkAt p2 i).«end».val := by
    intro i hi
    rcases hi with hib | ⟨h1, h2⟩
    · subst hib
      show (p2.blocks.val.getD b.index.val blk0).marked_split.val =
        (p2.blocks.val.getD b.index.val blk0).«end».val
      rw [hVb]
      by_cases hu' : u = true
      · simp [hu', unmRec]
      · simp [hu', pieceRec]
    · have hc1 : firstNew u ≤ i - N + firstNew u := by omega
      have hfn : firstNew u ≤ 1 := by unfold firstNew; split_ifs <;> omega
      have := hVnew (i - N + firstNew u) hc1 (by omega)
      have e : N + (i - N + firstNew u - firstNew u) = i := by omega
      rw [e] at this
      show (p2.blocks.val.getD i blk0).marked_split.val = (p2.blocks.val.getD i blk0).«end».val
      rw [this]; simp [pieceRec]
  have hswapT : ∀ j, (j = b.index.val ∨ (N ≤ j ∧ j < N + (K - firstNew u))) →
      (swapIdx b.index.val mx.index.val j = b.index.val ∨
        (N ≤ swapIdx b.index.val mx.index.val j ∧
          swapIdx b.index.val mx.index.val j < N + (K - firstNew u))) := by
    intro j hj
    unfold swapIdx
    split_ifs with h1 h2
    · left; rfl
    · rcases hmxcls with h | h
      · left; exact h
      · right; exact h
    · exact hj
  refine ⟨nbi', p3, ⟨bo1, ?_⟩, hp3, by rw [hp3len, hVlen], hnbival', ?_, ?_, ?_, ?_⟩
  · simp only [alloc.vec.Vec.deref] at hscat
    rw [hscat]
    have hp2eq : ({ elements := E', blocks := v5, element_to_block := B', element_offset := O' } :
      BlockPartition) = p2 := rfl
    simp [hp2eq, hnbts, hswap, hassert]
  · intro j hj hjb
    rw [hp3blk]
    have : swapIdx b.index.val mx.index.val j = j := by
      unfold swapIdx
      rw [if_neg (by rcases hmxcls with h | h <;> omega), if_neg hjb]
    rw [this]
    show p2.blocks.val.getD j blk0 = _
    exact hVold j hj hjb
  · rw [hp3blk]; exact hT2 _ (hswapT _ (Or.inl rfl))
  · intro a h1 h2
    rw [hp3blk]; exact hT2 _ (hswapT _ (Or.inr ⟨h1, h2⟩))
  · have hNpos : 1 ≤ N := by omega
    refine ⟨mx.index.val, hmxcls, ?_, ?_⟩
    · intro t ht
      have hs_lt : (old.val.getD t zST).index.val < n := hoidx _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _)
      rw [hp3e2b _ hs_lt]
      congr 1
      have hB1 := hsc.hB1 t ht
      have hcK : cls.getD t 0 < K := hlt _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; exact List.getElem_mem _)
      have := labelNat_index b u nbiU N K (cls.getD t 0) hNpos hnbi hcK hNK2
      rw [← this, ← hB1]
      rfl
    · intro s hs hnot
      have hB2 := hsc.hB2 s hnot
      have hO2 := hsc.hO2 s hnot
      refine ⟨?_, ?_⟩
      · rw [hp3e2b s hs]
        congr 1
        show (B'.val.getD s zBT).index.val = (p.element_to_block.val.getD s zBT).index.val
        rw [hB2]
      · have : p3.element_offset = p2.element_offset := hp3o
        show (p3.element_offset.val.getD s 0#usize).val = (p.element_offset.val.getD s 0#usize).val
        rw [this]
        show (O'.val.getD s 0#usize).val = _
        rw [hO2]

/-- Facts the step lemma consumes about the result of `finish_partition_marked`'s main loop. -/
def FinishPost (n : Nat) (p : BlockPartition) (b : TagIndex Std.Usize BlockTag) (K : Nat) (u : Bool)
    (cls : List Nat) (old : List (TagIndex Std.Usize StateTag))
    (y : alloc.vec.Vec (TagIndex Std.Usize BlockTag) × BlockPartition × alloc.vec.Vec Std.Usize) : Prop :=
  PartInv n y.2.1 ∧ y.2.1.blocks.val.length = p.blocks.val.length + (K - firstNew u) ∧
  y.1.val = b :: (List.range' p.blocks.val.length (K - firstNew u)).map uTag ∧
  (∀ j, j < p.blocks.val.length → j ≠ b.index.val → blkAt y.2.1 j = blkAt p j) ∧
  (∀ j, (j = b.index.val ∨ (p.blocks.val.length ≤ j ∧ j < p.blocks.val.length + (K - firstNew u))) →
    (blkAt y.2.1 j).marked_split.val = (blkAt y.2.1 j).«end».val) ∧
  FinishSem n p b K u cls old y.2.1

/-- The block-creation loop of `finish_partition_marked` as a whole. -/
theorem finish0_loop_spec
    {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (b : TagIndex Std.Usize BlockTag) (hb : b.index.val < p.blocks.val.length)
    (hmark : (blkAt p b.index.val).marked_split.val < (blkAt p b.index.val).«end».val)
    (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    (hszpos : ∀ j, j < K → 0 < szs.getD j 0)
    (hlen : cls.length = (blkAt p b.index.val).«end».val - (blkAt p b.index.val).marked_split.val)
    (idxv : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (hidx : idxv.val.map (fun x => x.index.val) = cls)
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (hold : old.val.length = cls.length)
    (hperm : old.val.Perm (regionElems p (blkAt p b.index.val).marked_split.val cls.length))
    (u : Bool)
    (hu : u = decide ((blkAt p b.index.val).begin.val < (blkAt p b.index.val).marked_split.val))
    (hn : n < 2 ^ UScalarTy.Usize.numBits) (hn' : n ≤ Usize.max)
    (hNK : p.blocks.val.length + K ≤ Usize.max)
    (eob nbiU : Std.Usize) (heob : eob.val = p.blocks.val.length)
    (hnbi : nbiU.val = if u then p.blocks.val.length else p.blocks.val.length - 1)
    (deref_mut_back : Slice Std.Usize → alloc.vec.Vec Std.Usize)
    (iter_mut_back : core.slice.iter.IterMut Std.Usize → Slice Std.Usize)
    (hdm : ∀ s, deref_mut_back s = ({ slice := s } : alloc.vec.Vec Std.Usize))
    (him : ∀ it, iter_mut_back it = it.slice)
    (S : Slice Std.Usize) (hS : S.val.map (fun z => z.val) = szs) :
    ∃ y, verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0
        deref_mut_back iter_mut_back ({ slice := S } : core.slice.iter.IterMut Std.Usize)
        (fun im => im) p.elements p.blocks p.element_to_block p.element_offset b idxv old
        (blkAt p b.index.val) eob nbiU 0#usize = ok y ∧ FinishPost n p b K u cls old.val y := by
  set bk := blkAt p b.index.val with hbk
  set ms := bk.marked_split.val with hms
  set en := bk.«end».val with hen
  have hbkr : bk.begin.val < en ∧ en ≤ n ∧ bk.begin.val ≤ ms ∧ ms ≤ en := hp.blk b.index.val hb
  have hlen' : cls.length = en - ms := hlen
  have hSlen : S.val.length = K := by
    have := congrArg List.length hS; simpa [hK] using this
  have hcumle : ∀ c, c ≤ K → cumS ms szs c ≤ Usize.max := by
    intro c hc
    have := cumS_le_end ms szs cls K hK hcnt hlt c
    omega
  have hbnd : ∀ c, c ≤ K → cumS ms szs c < 2 ^ UScalarTy.Usize.numBits := by
    intro c hc
    have := cumS_le_end ms szs cls K hK hcnt hlt c
    omega
  obtain ⟨y, hy, hQ⟩ := loop_nat_spec
    (fun x : Lp0State =>
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body
        deref_mut_back iter_mut_back p.elements p.element_to_block p.element_offset b idxv old eob nbiU
        x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun x => x.1.i) (Loop0Inv S bk ms szs p.blocks.val b.index.val u K) (FinishPost n p b K u cls old.val) K
    (by
      rintro m x ⟨vals, h1, -⟩
      rw [h1])
    (by rintro m x ⟨vals, h1, h2, -⟩; exact h2)
    (by
      intro m x hm hI
      exact loop0_inv_step deref_mut_back iter_mut_back p.elements p.element_to_block p.element_offset
        b idxv old eob nbiU S bk ⟨hbkr.1, hbkr.2.2.1, hbkr.2.2.2⟩ ms szs p.blocks.val b.index.val u K rfl hb hS hK hszpos rfl hu
        hbkr.2.2.1 hcumle hNK hbnd m hm x hI)
    (by
      rintro ⟨iter, back, v5, bl, cur⟩ hI
      have hI' := hI
      obtain ⟨vals, h1, -, -, h4, -⟩ := hI'
      simp only at h1 h4
      subst h1
      subst h4
      obtain ⟨nbi, p3, bo1, hbody, hp3, hlen3, hnbi3, hold3, hmk3, hsem3⟩ := finish0_tail hp b hb hmark szs cls K hK
        hcnt hlt hszpos hlen idxv hidx old hold hperm u hu hn hn' hNK eob nbiU heob hnbi
        deref_mut_back iter_mut_back hdm him S hS back v5 cur hI
      exact ⟨(nbi, p3, bo1), hbody, hp3, hlen3, hnbi3, hold3, hmk3, hsem3⟩)
    (({ slice := S, i := 0 } : core.slice.iter.IterMut Std.Usize), (fun im => im), p.blocks, bk, 0#usize)
    ⟨[], rfl, by omega, by simp [blkSeq], rfl, by simp, rfl, fun j hj => by omega,
      fun im _ => by simp⟩
  exact ⟨y, hy, hQ⟩

/-- Unfolding of `finish_partition_marked` down to its main loop. -/
theorem finish_unfold (p : BlockPartition) (b : TagIndex Std.Usize BlockTag)
    (sb : verified.merc_reduction.block_partition.BlockPartitionBuilder)
    (hb : b.index.val < p.blocks.val.length)
    (hblkWF : merc_reduction.block_partition.Block.WellFormed (blkAt p b.index.val)) :
    ∃ nbiU : Std.Usize,
      nbiU.val = (if decide ((blkAt p b.index.val).begin.val < (blkAt p b.index.val).marked_split.val)
        then p.blocks.val.length else p.blocks.val.length - 1) ∧
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked p b sb =
        (do
          let y ← verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0
            (fun s => ({ slice := s } : alloc.vec.Vec Std.Usize)) (fun it => it.slice)
            ({ slice := sb.block_sizes.slice } : core.slice.iter.IterMut Std.Usize)
            (fun im => im) p.elements p.blocks p.element_to_block p.element_offset b
            sb.index_to_block sb.old_elements (blkAt p b.index.val) (alloc.vec.Vec.len p.blocks)
            nbiU 0#usize
          ok (y.1, y.2.1, { sb with block_sizes := y.2.2 })) := by
  have hlen : (alloc.vec.Vec.len p.blocks).val = p.blocks.val.length := by simp [alloc.vec.Vec.len]
  have hhas := block_has_unmarked_contract (blkAt p b.index.val) hblkWF
  have hbk : p.blocks.slice.val[b.index.val]'hb = blkAt p b.index.val := (blkAt_eq_getElem hb).symm
  unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked
  by_cases hun : (blkAt p b.index.val).begin.val < (blkAt p b.index.val).marked_split.val
  · refine ⟨alloc.vec.Vec.len p.blocks, by simp [hun, hlen], ?_⟩
    simp [hun, hbk, hhas, vec_tagged_index_val p.blocks b hb, alloc.vec.Vec.deref_mut,
      core.slice.Slice.iter_mut, lift]
    rfl
  · have hsub : 1 ≤ p.blocks.val.length := by omega
    obtain ⟨z, hz, hzv, -⟩ := spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len p.blocks) (y := 1#usize) (by simp [hlen]; omega))
    refine ⟨z, by simp [hun, hzv, hlen], ?_⟩
    simp [hun, hbk, hhas, vec_tagged_index_val p.blocks b hb, alloc.vec.Vec.deref_mut,
      core.slice.Slice.iter_mut, lift, hz]
    rfl

/-- What `strong_process_marked_elements` leaves in the builder before `finish_partition_marked`
    runs: `block_sizes` are the (positive) class sizes, `index_to_block` the class of each marked
    element, and `old_elements` is a permutation of the block's marked elements. -/
def BuilderDense (p : BlockPartition) (b : TagIndex Std.Usize BlockTag)
    (sb : verified.merc_reduction.block_partition.BlockPartitionBuilder) (szs cls : List Nat) : Prop :=
  sb.block_sizes.val.map (fun z => z.val) = szs ∧
  sb.index_to_block.val.map (fun x => x.index.val) = cls ∧
  sb.old_elements.val.length = cls.length ∧
  sb.old_elements.val.Perm (regionElems p (blkAt p b.index.val).marked_split.val cls.length) ∧
  cls.length = (blkAt p b.index.val).«end».val - (blkAt p b.index.val).marked_split.val ∧
  (∀ x ∈ cls, x < szs.length) ∧ (∀ j, j < szs.length → szs.getD j 0 = cls.count j) ∧
  (∀ j, j < szs.length → 0 < szs.getD j 0)

/-- Contract of `BlockPartition::finish_partition_marked`. -/
theorem finish_partition_marked_spec
    {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (b : TagIndex Std.Usize BlockTag) (hb : b.index.val < p.blocks.val.length)
    (hmark : (blkAt p b.index.val).marked_split.val < (blkAt p b.index.val).«end».val)
    (sb : verified.merc_reduction.block_partition.BlockPartitionBuilder) (szs cls : List Nat)
    (hd : BuilderDense p b sb szs cls)
    (hn : n < 2 ^ UScalarTy.Usize.numBits) (hn' : n ≤ Usize.max) (h2n : 2 * n ≤ Usize.max) :
    ∃ (nbi : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (p3 : BlockPartition)
      (bo1 : alloc.vec.Vec Std.Usize),
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked p b sb =
        ok (nbi, p3, { sb with block_sizes := bo1 }) ∧
      FinishPost n p b szs.length
        (decide ((blkAt p b.index.val).begin.val < (blkAt p b.index.val).marked_split.val))
        cls sb.old_elements.val (nbi, p3, bo1) := by
  obtain ⟨hS, hidx, hold, hperm, hlen, hlt, hcnt, hszpos⟩ := hd
  obtain ⟨nbiU, hnbiUv, hunf⟩ := finish_unfold p b sb hb (partInv_blockWF hp hb)
  have hbn : p.blocks.val.length ≤ n := hp.blocks_le_n
  have hbkr := hp.blk b.index.val hb
  have hsum := szs_sum_eq szs cls szs.length rfl hcnt hlt
  have hKle : szs.length ≤ cls.length := by
    have := List.length_le_sum_of_one_le szs (fun i hi => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
      have := hszpos j hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at this
      simp only [Option.getD_some] at this
      exact this)
    omega
  have hlenU : (alloc.vec.Vec.len p.blocks).val = p.blocks.val.length := by
    simp [alloc.vec.Vec.len]
  obtain ⟨y, hy, hpost⟩ := finish0_loop_spec hp b hb hmark szs cls szs.length rfl hcnt hlt hszpos hlen
    sb.index_to_block hidx sb.old_elements hold hperm _ rfl hn hn' (by omega)
    (alloc.vec.Vec.len p.blocks) nbiU hlenU (by rw [hnbiUv])
    (fun s => { slice := s }) (fun it => it.slice) (fun s => rfl) (fun it => rfl)
    sb.block_sizes.slice hS
  refine ⟨y.1, y.2.1, y.2.2, ?_, hpost⟩
  rw [hunf, hy]
  simp only [bind_ok]

end MercVerified.Refinement.Proofs
