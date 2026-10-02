import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Partition_Proofs
import MercVerified.Refinement.Proofs.PartitionInv_Proofs
import MercVerified.Refinement.Proofs.LoopTools_Proofs
import MercVerified.Refinement.Proofs.SwapBlocks_Proofs
import Aeneas.Std.WP

/-!
# `BlockPartition::finish_partition_marked` and its helpers

`new_block_to_swap` collects the block indices of the freshly created pieces and picks the
largest one, `swap_blocks` (see `SwapBlocks_Proofs.lean`) moves that piece to the original block
index, and `finish_partition_marked` (two loops that create the pieces and scatter the marked
elements) glues them together.

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

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- The inner (max-search) loop of `new_block_to_swap` succeeds and returns one of the candidate
    block indices. -/
theorem nbts_inner_spec {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (nbi : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (hall : ∀ x ∈ nbi.val, x.index.val < p.blocks.val.length)
    (hne : 1 ≤ nbi.val.length) (mx : TagIndex Std.Usize BlockTag) (ml : Std.Usize)
    (hmx : mx ∈ nbi.val) :
    ∃ r, verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0_loop0
        { start := 1#usize, «end» := alloc.vec.Vec.len nbi } p.elements p.blocks
        p.element_to_block p.element_offset nbi mx ml = ok r ∧ r ∈ nbi.val := by
  unfold verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0_loop0
  refine range_loop_spec
    (fun x => verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0_loop0.body
      p.elements p.blocks p.element_to_block p.element_offset nbi x.1 x.2.1 x.2.2)
    (fun _ st => st.1 ∈ nbi.val) (fun r => r ∈ nbi.val) (alloc.vec.Vec.len nbi) ?_ ?_ 1#usize
    (mx, ml) ?_ hmx
  · rintro i ⟨mx', ml'⟩ hi hst
    simp only at hst
    obtain ⟨o, it1, hnext, ho, hstart, hend⟩ := next_range_some
      ({ start := i, «end» := alloc.vec.Vec.len nbi } : core.ops.range.Range Std.Usize) hi
    have hiv : i.val < nbi.val.length := by simpa [alloc.vec.Vec.len] using hi
    have hcmem : nbi.val[i.val]'hiv ∈ nbi.val := List.getElem_mem hiv
    have hcb := hall _ hcmem
    have hblk : verified.merc_reduction.block_partition.BlockPartition.block
        { elements := p.elements, blocks := p.blocks, element_to_block := p.element_to_block,
          element_offset := p.element_offset } (nbi.val[i.val]'hiv)
        = ok (blkAt p (nbi.val[i.val]'hiv).index.val) := by
      show verified.merc_reduction.block_partition.BlockPartition.block p _ = _
      rw [block_partition_block_val p _ hcb]
      congr 1
      exact (blkAt_eq_getElem hcb).symm
    have hbk := hp.blk _ hcb
    have hbkWF : merc_reduction.block_partition.Block.WellFormed (blkAt p (nbi.val[i.val]'hiv).index.val) :=
      partInv_blockWF hp hcb
    obtain ⟨cl, hcl, hclv, -⟩ := spec_imp_exists
      (Usize.sub_spec (x := (blkAt p (nbi.val[i.val]'hiv).index.val).«end»)
        (y := (blkAt p (nbi.val[i.val]'hiv).index.val).begin) (by omega))
    have hidx : nbi.index_usize i = ok (nbi.val[i.val]'hiv) := by
      obtain ⟨x, hx, hxe⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec nbi i hiv)
      rw [hx, hxe]
    generalize alloc.vec.Vec.len nbi = E at hi hnext hend ⊢
    have hit1 : it1 = ({ start := it1.start, «end» := E } : core.ops.range.Range Std.Usize) := by
      cases it1; simp only at hend ⊢; simp [hend]
    unfold verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0_loop0.body
    subst ho
    by_cases hge : cl ≥ ml'
    · have hge' : ml'.val ≤ cl.val := hge
      refine ⟨it1.start, (nbi.val[i.val]'hiv, cl), hstart, ?_, hcmem⟩
      simp [hnext, hidx, hblk, block_len_contract _ hbkWF, hcl, hge']
      exact hit1
    · have hge' : ¬ ml'.val ≤ cl.val := hge
      refine ⟨it1.start, (mx', ml'), hstart, ?_, hst⟩
      simp [hnext, hidx, hblk, block_len_contract _ hbkWF, hcl, hge']
      exact hit1
  · intro i st hi hst
    obtain ⟨o, it1, hnext, ho, hid⟩ := next_range_none
      ({ start := i, «end» := alloc.vec.Vec.len nbi } : core.ops.range.Range Std.Usize)
      (by simp [hi])
    refine ⟨st.1, ?_, hst⟩
    unfold verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0_loop0.body
    subst ho
    simp [hnext]
  · simp [alloc.vec.Vec.len]; omega

/-- The tagged index of a `usize` in range, in `uTag` form. -/
theorem tag_new_eq_uTag {Tag : Type} (i : Std.Usize) :
    (({ index := i, marker := () } : TagIndex Std.Usize Tag)) = uTag i.val := by
  unfold uTag
  congr 1
  apply sz_eq_from_val
  rw [uTotal_val_of_lt (sz_val_lt_two_pow i)]

/-- Reading `blocks[c]` through a partition literal. -/
theorem block_lit_ok (p : BlockPartition) (c : TagIndex Std.Usize BlockTag)
    (hc : c.index.val < p.blocks.val.length) :
    verified.merc_reduction.block_partition.BlockPartition.block
      { elements := p.elements, blocks := p.blocks, element_to_block := p.element_to_block,
        element_offset := p.element_offset } c = ok (blkAt p c.index.val) := by
  show verified.merc_reduction.block_partition.BlockPartition.block p c = _
  rw [block_partition_block_val p c hc]
  congr 1
  exact (blkAt_eq_getElem hc).symm

/-- The outer loop of `new_block_to_swap`: pushes the new block indices `[es, ee)` after the
    ones in `nbi0` and then picks the largest block. -/
theorem nbts_outer_spec {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (es ee : Std.Usize) (nbi0 : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (hle : es.val ≤ ee.val) (hee : ee.val ≤ p.blocks.val.length)
    (hne : nbi0.val ≠ []) (hall : ∀ x ∈ nbi0.val, x.index.val < p.blocks.val.length)
    (hlen : nbi0.val.length + (ee.val - es.val) ≤ Usize.max) :
    ∃ mx nbi', verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0
        { start := es, «end» := ee } p.elements p.blocks p.element_to_block p.element_offset nbi0
        = ok (mx, nbi') ∧
      nbi'.val = nbi0.val ++ (List.range' es.val (ee.val - es.val)).map uTag ∧
      mx ∈ nbi'.val := by
  unfold verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0
  obtain ⟨r, hr, hrpost⟩ : ∃ r, loop
      (fun x : core.ops.range.Range Std.Usize × alloc.vec.Vec (TagIndex Std.Usize BlockTag) =>
        verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0.body
          p.elements p.blocks p.element_to_block p.element_offset x.1 x.2)
      ({ start := es, «end» := ee }, nbi0) = ok r ∧
      (r.2.val = nbi0.val ++ (List.range' es.val (ee.val - es.val)).map uTag ∧
        r.1 ∈ r.2.val) := by
    refine range_loop_spec
      (fun x => verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0.body
        p.elements p.blocks p.element_to_block p.element_offset x.1 x.2)
      (fun i cur => es.val ≤ i ∧
        cur.val = nbi0.val ++ (List.range' es.val (i - es.val)).map uTag)
      (fun r => r.2.val = nbi0.val ++ (List.range' es.val (ee.val - es.val)).map uTag ∧
        r.1 ∈ r.2.val) ee ?_ ?_ es nbi0 hle ⟨le_refl _, by simp⟩
    · rintro i cur hi ⟨hrs, hcur⟩
      obtain ⟨o, it1, hnext, ho, hstart, hend⟩ := next_range_some
        ({ start := i, «end» := ee } : core.ops.range.Range Std.Usize) hi
      have hclen : cur.val.length = nbi0.val.length + (i.val - es.val) := by
        rw [hcur]; simp
      have hpushlen : cur.val.length < Usize.max := by
        have : i.val < ee.val := hi
        omega
      obtain ⟨v', hpush, hv'⟩ := vec_push_val cur ({ index := i, marker := () } : TagIndex Std.Usize BlockTag) hpushlen
      have hit1 : it1 = ({ start := it1.start, «end» := ee } : core.ops.range.Range Std.Usize) := by
        cases it1; simp only at hend ⊢; simp [hend]
      refine ⟨it1.start, v', hstart, ?_, ?_, ?_⟩
      · unfold verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0.body
        subst ho
        simp [hnext, verified.merc_utilities.tagged_index.TagIndex.new, hpush]
        exact hit1
      · omega
      · rw [hv', hcur, tag_new_eq_uTag]
        have h1 : i.val + 1 - es.val = (i.val - es.val) + 1 := by omega
        rw [h1, List.range'_concat]
        have h2 : es.val + 1 * (i.val - es.val) = i.val := by omega
        rw [h2]
        simp
    · rintro i cur hi ⟨hrs, hcur⟩
      obtain ⟨o, it1, hnext, ho, hid⟩ := next_range_none
        ({ start := i, «end» := ee } : core.ops.range.Range Std.Usize) (by simp [hi])
      have hallcur : ∀ x ∈ cur.val, x.index.val < p.blocks.val.length := by
        intro x hx
        rw [hcur] at hx
        simp only [List.mem_append, List.mem_map, List.mem_range'_1] at hx
        rcases hx with hx | ⟨j, hj, rfl⟩
        · exact hall x hx
        · have hjlt : j < ee.val := by omega
          have : (uTag (Tag := BlockTag) j).index.val = j :=
            uTotal_val_of_lt (lt_trans hjlt (sz_val_lt_two_pow ee))
          rw [this]; omega
      have hne' : 0 < cur.val.length := by
        rw [hcur]
        have : 0 < nbi0.val.length := List.length_pos_of_ne_nil hne
        simp; omega
      have hidx0 : cur.index_usize 0#usize = ok (cur.val[0]'hne') := by
        obtain ⟨x, hx, hxe⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec cur 0#usize (by simpa using hne'))
        rw [hx, hxe]; rfl
      have hc0mem : cur.val[0]'hne' ∈ cur.val := List.getElem_mem hne'
      have hc0 := hallcur _ hc0mem
      have hbk := hp.blk _ hc0
      have hbkWF : merc_reduction.block_partition.Block.WellFormed (blkAt p (cur.val[0]'hne').index.val) :=
        partInv_blockWF hp hc0
      obtain ⟨ml, hml, -, -⟩ := spec_imp_exists
        (Usize.sub_spec (x := (blkAt p (cur.val[0]'hne').index.val).«end»)
          (y := (blkAt p (cur.val[0]'hne').index.val).begin) (by omega))
      obtain ⟨mx, hmx, hmxmem⟩ := nbts_inner_spec hp cur hallcur (by omega) _ ml hc0mem
      refine ⟨(mx, cur), ?_, ?_, hmxmem⟩
      · unfold verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0.body
        subst ho
        simp [hnext, hidx0, block_lit_ok p _ hc0, block_len_contract _ hbkWF, hml, hmx]
      · rw [hcur, hi]
  exact ⟨r.1, r.2, hr, hrpost⟩

/-- Contract of `BlockPartition::new_block_to_swap`: it collects `block_index` followed by the
    freshly created block indices `[end_of_blocks, blocks.len)` and returns one of them. -/
theorem new_block_to_swap_spec {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (b : TagIndex Std.Usize BlockTag) (hb : b.index.val < p.blocks.val.length)
    (eb : Std.Usize) (heb1 : 1 ≤ eb.val) (hebN : eb.val ≤ p.blocks.val.length) :
    ∃ mx nbi, verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap p b eb
        = ok (mx, nbi) ∧
      nbi.val = b :: (List.range' eb.val (p.blocks.val.length - eb.val)).map uTag ∧
      mx ∈ nbi.val := by
  have hNmax : p.blocks.val.length ≤ Usize.max := p.blocks.property
  unfold verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap
  have hlen : (alloc.vec.Vec.len p.blocks).val = p.blocks.val.length := by
    simp [alloc.vec.Vec.len]
  obtain ⟨i1, hi1, hi1v, -⟩ := spec_imp_exists
    (Usize.sub_spec (x := alloc.vec.Vec.len p.blocks) (y := eb) (by omega))
  have h1 : (1#usize).val = 1 := rfl
  obtain ⟨i2, hi2, hi2v⟩ := spec_imp_exists
    (Usize.add_spec (x := 1#usize) (y := i1) (by
      simp only [h1]; omega))
  have hwc : (alloc.vec.Vec.with_capacity (TagIndex Std.Usize BlockTag) i2).val = [] := rfl
  have hmaxpos : 0 < Usize.max := by
    simp [Usize.max, Usize.numBits]
    cases System.Platform.numBits_eq with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num
  obtain ⟨nbi1, hpush, hnbi1⟩ := vec_push_val
    (alloc.vec.Vec.with_capacity (TagIndex Std.Usize BlockTag) i2) b (by
      rw [hwc]; simpa using hmaxpos)
  have hnbi1' : nbi1.val = [b] := by rw [hnbi1, hwc]; rfl
  obtain ⟨mx, nbi', hloop, hval, hmem⟩ := nbts_outer_spec hp eb (alloc.vec.Vec.len p.blocks) nbi1
    (by omega) (by omega) (by rw [hnbi1']; simp) (by
      intro x hx; rw [hnbi1'] at hx; simp at hx; rw [hx]; exact hb)
    (by rw [hnbi1']; simp only [List.length_singleton]; omega)
  refine ⟨mx, nbi', ?_, ?_, hmem⟩
  · simp [hi1, hi2, hpush, hloop]
  · rw [hval, hnbi1', hlen]; simp


end MercVerified.Refinement.Proofs
