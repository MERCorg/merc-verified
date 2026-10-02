import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Partition_Proofs
import MercVerified.Refinement.Proofs.PartitionInv_Proofs
import MercVerified.Refinement.Proofs.LoopTools_Proofs
import MercVerified.Refinement.Proofs.SplitPartInv_Proofs
import MercVerified.Refinement.Proofs.SigKey_Proofs
import Aeneas.Std.WP

/-!
# `BlockPartition::marked_elements_sorted`

Resets the builder for a block: `block_sizes` is emptied, `index_to_block` becomes `len_marked`
zeros and `old_elements` the sorted marked elements of the block.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition Block)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem region_eq_window {n : Nat} {p : BlockPartition} (hp : PartInv n p) (ms len : Nat)
    (hle : ms + len ≤ n) :
    regionElems p ms len = (p.elements.val.drop ms).take len := by
  apply List.ext_getElem
  · simp [regionElems, hp.len_e]; omega
  · intro i h1 h2
    simp only [regionElems, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    rw [eAt]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show ms + i < p.elements.val.length by
      have := hp.len_e; simp [regionElems] at h1; omega)]

/-- Contract of `BlockPartition::marked_elements_sorted`. -/
theorem marked_elements_sorted_spec {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (b : TagIndex Std.Usize BlockTag) (hb : b.index.val < p.blocks.val.length)
    (sb : verified.merc_reduction.block_partition.BlockPartitionBuilder) :
    ∃ sb' : verified.merc_reduction.block_partition.BlockPartitionBuilder,
      verified.merc_reduction.block_partition.BlockPartition.marked_elements_sorted p b sb = ok sb' ∧
      sb'.block_sizes.val = [] ∧
      sb'.index_to_block.val = List.replicate
        ((blkAt p b.index.val).«end».val - (blkAt p b.index.val).marked_split.val)
        ({ index := 0#usize, marker := () } : TagIndex Std.Usize BlockTag) ∧
      sb'.old_elements.val.Perm (regionElems p (blkAt p b.index.val).marked_split.val
        ((blkAt p b.index.val).«end».val - (blkAt p b.index.val).marked_split.val)) := by
  set bk := blkAt p b.index.val with hbk
  have hbkr : bk.begin.val < bk.«end».val ∧ bk.«end».val ≤ n ∧ bk.begin.val ≤ bk.marked_split.val ∧
      bk.marked_split.val ≤ bk.«end».val := hp.blk b.index.val hb
  have hbkread : p.blocks.slice.val[b.index.val]'hb = bk := (blkAt_eq_getElem hb).symm
  obtain ⟨v, hv, hv0⟩ := alloc.vec.Vec.clear_spec Global sb.index_to_block
  obtain ⟨v1, hv1, hv10⟩ := alloc.vec.Vec.clear_spec Global sb.block_sizes
  obtain ⟨v2, hv2, hv20⟩ := alloc.vec.Vec.clear_spec Global sb.old_elements
  -- `len_marked`
  obtain ⟨u, hu⟩ := merc_reduction.block_partition.Block.assert_consistent_ok bk
    ⟨hbkr.1, hbkr.2.2.1, hbkr.2.2.2⟩
  obtain ⟨i, hi, hiv, -⟩ := spec_imp_exists
    (Usize.sub_spec (x := bk.«end») (y := bk.marked_split) (by omega))
  have hlm : verified.merc_reduction.block_partition.Block.len_marked bk = ok i := by
    unfold verified.merc_reduction.block_partition.Block.len_marked
    rw [hu]; simpa using hi
  have hcl : ∀ x : TagIndex Std.Usize BlockTag,
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone BlockTag
        core.clone.CloneUsize).clone x = ok x := by
    intro x
    simp [verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone.clone]
  obtain ⟨v3, hv3, hv3v⟩ := spec_imp_exists (alloc.vec.Vec.resize_spec
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone BlockTag core.clone.CloneUsize)
    v i ({ index := 0#usize, marker := () } : TagIndex Std.Usize BlockTag) (hcl _))
  have hnle : n ≤ Usize.max := by
    have := p.elements.property
    rw [hp.len_e] at this; exact this
  have hlenE : (alloc.vec.Vec.deref p.elements).val.length = n := by
    simp [alloc.vec.Vec.deref, hp.len_e]
  obtain ⟨v4, hv4, hv4v⟩ := alloc.vec.Vec.extend_blockIter_spec v2
    { elements := alloc.vec.Vec.deref p.elements, index := bk.marked_split, «end» := bk.«end» }
    (by simp only []; omega) (by simp only []; rw [hv20]; simp; omega)
  obtain ⟨s2, hs2, hs2p, -⟩ := core.slice.Slice.sort_unstable_spec
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd StateTag core.cmp.OrdUsize)
    (tagIndex_ord_total StateTag) (alloc.vec.Vec.deref_mut v4).1
  refine ⟨{ index_to_block := v3, block_sizes := v1, old_elements := (alloc.vec.Vec.deref_mut v4).2 s2 }, ?_, hv10, ?_, ?_⟩
  · unfold verified.merc_reduction.block_partition.BlockPartition.marked_elements_sorted
    simp [vec_tagged_index_val p.blocks b hb, hbkread, hv, hv1, hv2, hlm,
      verified.merc_utilities.tagged_index.TagIndex.new, hv3,
      verified.merc_reduction.block_partition.Block.iter_marked, hv4, lift]
    simp only [alloc.vec.Vec.deref_mut] at hs2 ⊢
    show (do
      let s2 ← core.slice.Slice.sort_unstable
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd StateTag core.cmp.OrdUsize) v4.slice
      ok ({ index_to_block := v3, block_sizes := v1, old_elements := { slice := s2 } } :
        verified.merc_reduction.block_partition.BlockPartitionBuilder)) = _
    rw [hs2]
    simp only [bind_tc_ok]
  · show v3.val = _
    rw [hv3v, hv0, hiv]
    simp [List.resize]
  · show s2.val.Perm _
    refine hs2p.trans ?_
    have hwin : v4.deref_mut.1.val = regionElems p bk.marked_split.val (bk.«end».val - bk.marked_split.val) := by
      show v4.val = _
      rw [hv4v, hv20, region_eq_window hp _ _ (by omega)]
      simp [alloc.vec.Vec.deref, Slice.from_val]
    rw [hwin]

end MercVerified.Refinement.Proofs
