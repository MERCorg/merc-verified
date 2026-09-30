import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Partition_Proofs
import MercVerified.Refinement.Proofs.PartitionInv_Proofs
import MercVerified.Refinement.Proofs.LoopTools_Proofs
import Aeneas.Std.WP

/-!
# `BlockPartition::swap_blocks`

`swap_blocks left right` exchanges the records of two blocks and then re-labels
`element_to_block` for the elements in the two ranges, so that the partition stays consistent
(`PartInv`).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition Block)

open MercVerified.Lts.Proofs
open Classical

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- Pointwise effect of one `Slice.set` write on the `getD` view of a `Vec`. -/
theorem vec_set_getD {α : Type} (cur : alloc.vec.Vec α) (t : Std.Usize) (x d : α) (s : Nat)
    (ht : t.val < cur.val.length) :
    (({ slice := cur.slice.set t x } : alloc.vec.Vec α).val.getD s d)
      = if t.val = s then x else cur.val.getD s d := by
  show (cur.slice.set t x).val.getD s d = _
  rw [Slice.set_val_eq]
  have hcs : cur.slice.val = cur.val := rfl
  rw [hcs]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hs : t.val = s
  · rw [if_pos hs, if_pos hs, if_pos ht]; simp
  · rw [if_neg hs, if_neg hs]

/-- One step of the "written so far" pointwise description used by the re-labelling loops. -/
theorem pw_step {α : Type} (idx : Nat → Nat) (rs i s : Nat) (hrs : rs ≤ i) (lab : α)
    (base cur : Nat → α)
    (hpt : ∀ s, cur s = if (∃ q, rs ≤ q ∧ q < i ∧ idx q = s) then lab else base s) :
    (if idx i = s then lab else cur s)
      = if (∃ q, rs ≤ q ∧ q < i + 1 ∧ idx q = s) then lab else base s := by
  by_cases hs : idx i = s
  · rw [if_pos hs, if_pos]
    exact ⟨i, hrs, by omega, hs⟩
  · rw [if_neg hs, hpt s]
    by_cases hex : ∃ q, rs ≤ q ∧ q < i ∧ idx q = s
    · rw [if_pos hex, if_pos]
      obtain ⟨q, h1, h2, h3⟩ := hex
      exact ⟨q, h1, by omega, h3⟩
    · rw [if_neg hex, if_neg]
      rintro ⟨q, h1, h2, h3⟩
      by_cases hq : q = i
      · subst hq; exact hs h3
      · exact hex ⟨q, h1, by omega, h3⟩

/-- The re-labelling loop (`swap_blocks_loop0_loop0`, and the same-shaped first loop of
    `swap_blocks_loop0`): for each position `q ∈ [rs, re)` the element `v[q]` gets the label
    `lab` in `element_to_block`. -/
theorem relabel_loop_spec (v : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (lab : TagIndex Std.Usize BlockTag) (rs re : Std.Usize)
    (e2b0 : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (hle : rs.val ≤ re.val) (hre : re.val ≤ v.val.length)
    (hb : ∀ q, rs.val ≤ q → q < re.val →
      (v.val.getD q zST).index.val < e2b0.val.length) :
    ∃ r, verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0_loop0
        { start := rs, «end» := re } v e2b0 lab = ok r ∧
      r.val.length = e2b0.val.length ∧
      ∀ s, r.val.getD s zBT =
        if (∃ q, rs.val ≤ q ∧ q < re.val ∧ (v.val.getD q zST).index.val = s)
        then lab else e2b0.val.getD s zBT := by
  unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0_loop0
  refine range_loop_spec
    (fun x => verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0_loop0.body
      v lab x.1 x.2)
    (fun i cur => rs.val ≤ i ∧ cur.val.length = e2b0.val.length ∧
      ∀ s, cur.val.getD s zBT =
        if (∃ q, rs.val ≤ q ∧ q < i ∧ (v.val.getD q zST).index.val = s)
        then lab else e2b0.val.getD s zBT)
    (fun r => r.val.length = e2b0.val.length ∧
      ∀ s, r.val.getD s zBT =
        if (∃ q, rs.val ≤ q ∧ q < re.val ∧ (v.val.getD q zST).index.val = s)
        then lab else e2b0.val.getD s zBT) re ?_ ?_ rs e2b0 hle ⟨le_refl _, rfl, ?_⟩
  · intro i cur hi ⟨hrs, hlen, hpt⟩
    obtain ⟨o, it1, hnext, ho, hstart, hend⟩ := next_range_some
      ({ start := i, «end» := re } : core.ops.range.Range Std.Usize) hi
    have hiv : i.val < v.val.length := lt_of_lt_of_le hi hre
    have hbi := hb i.val hrs hi
    have hget : v.val.getD i.val zST = v.val[i.val] := by
      simp [List.getD_eq_getElem?_getD, hiv]
    rw [hget] at hbi
    have hbnd : (v.val[i.val]'hiv).index.val < cur.val.length := by rw [hlen]; exact hbi
    refine ⟨it1.start, { slice := cur.slice.set (v.val[i.val]'hiv).index lab }, hstart, ?_, ?_⟩
    · have hit1 : it1 = ({ start := it1.start, «end» := re } : core.ops.range.Range Std.Usize) := by
        cases it1; simp only at hend ⊢; simp [hend]
      unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0_loop0.body
      subst ho
      have hidx : v.index_usize i = ok (v.val[i.val]'hiv) := by
        obtain ⟨x, hx, hxe⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hiv)
        rw [hx, hxe]
      simp [hnext, hidx, vec_tagged_index_mut_ok cur _ hbnd]
      exact hit1
    · refine ⟨by omega, ?_, ?_⟩
      · show (cur.slice.set _ lab).val.length = _
        rw [Slice.set_val_eq, List.length_set]; exact hlen
      · intro s
        show (cur.slice.set _ lab).val.getD s zBT = _
        rw [Slice.set_val_eq]
        have hcs : cur.slice.val = cur.val := rfl
        rw [hcs]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
        have hpts := hpt s
        simp only [List.getD_eq_getElem?_getD] at hpts hget
        by_cases hs : (v.val[i.val]'hiv).index.val = s
        · rw [if_pos hs, if_pos hbnd]
          have hex : ∃ q, rs.val ≤ q ∧ q < i.val + 1 ∧
              ((v.val)[q]?.getD zST).index.val = s :=
            ⟨i.val, hrs, by omega, by rw [hget]; exact hs⟩
          rw [if_pos hex]; simp
        · rw [if_neg hs, hpts]
          by_cases hex : ∃ q, rs.val ≤ q ∧ q < i.val ∧ ((v.val)[q]?.getD zST).index.val = s
          · rw [if_pos hex, if_pos]
            obtain ⟨q, h1, h2, h3⟩ := hex
            exact ⟨q, h1, by omega, h3⟩
          · rw [if_neg hex, if_neg]
            rintro ⟨q, h1, h2, h3⟩
            by_cases hq : q = i.val
            · subst hq; rw [hget] at h3; exact hs h3
            · exact hex ⟨q, h1, by omega, h3⟩
  · intro i cur hi ⟨hrs, hlen, hpt⟩
    obtain ⟨o, it1, hnext, ho, hid⟩ := next_range_none
      ({ start := i, «end» := re } : core.ops.range.Range Std.Usize) (by simp [hi])
    refine ⟨cur, ?_, hlen, ?_⟩
    · unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0_loop0.body
      subst ho
      simp [hnext]
    · intro s
      rw [hpt s, hi]
  · intro s
    rw [if_neg]
    rintro ⟨q, h1, h2, _⟩
    omega

/-- The `element_to_block` produced by `swap_blocks`: the elements in `rb`'s range get `r`, then
    those in `[rs1, re1)` get `l` (only where not already overwritten), everything else keeps its
    label. -/
noncomputable def swapF (v : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (e2b0 : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (l r : TagIndex Std.Usize BlockTag)
    (rs1 re1 : Std.Usize) (rb : Block) (s : Nat) : TagIndex Std.Usize BlockTag :=
  if (∃ q, rb.begin.val ≤ q ∧ q < rb.«end».val ∧ (v.val.getD q zST).index.val = s) then r
  else if (∃ q, rs1.val ≤ q ∧ q < re1.val ∧ (v.val.getD q zST).index.val = s) then l
  else e2b0.val.getD s zBT

/-- The two `element_to_block` re-labelling loops of `swap_blocks`
    (`swap_blocks_loop0`, then `swap_blocks_loop0_loop0`), followed by the closing
    `assert_consistent`. The assertion is an external; its success on the result is a
    hypothesis, discharged (via `PartInv`) by the caller. -/
theorem swap_blocks_loop0_spec (v : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (v1 : alloc.vec.Vec Block) (v2 : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (v3 : alloc.vec.Vec Std.Usize) (l r : TagIndex Std.Usize BlockTag)
    (rs1 re1 : Std.Usize) (rb : Block)
    (hle1 : rs1.val ≤ re1.val) (hre1 : re1.val ≤ v.val.length)
    (hrbN : r.index.val < v1.val.length) (hrb : v1.val.getD r.index.val blk0 = rb)
    (hrbe : rb.begin.val ≤ rb.«end».val) (hrbl : rb.«end».val ≤ v.val.length)
    (hb1 : ∀ q, rs1.val ≤ q → q < re1.val → (v.val.getD q zST).index.val < v2.val.length)
    (hb2 : ∀ q, rb.begin.val ≤ q → q < rb.«end».val →
      (v.val.getD q zST).index.val < v2.val.length)
    (hA : ∀ e : alloc.vec.Vec (TagIndex Std.Usize BlockTag), e.val.length = v2.val.length →
      (∀ s, e.val.getD s zBT = swapF v v2 l r rs1 re1 rb s) →
      merc_reduction.block_partition.BlockPartition.assert_consistent
        { elements := v, blocks := v1, element_to_block := e, element_offset := v3 } = ok true) :
    ∃ res, verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0
        { start := rs1, «end» := re1 } v v1 v2 v3 l r = ok res ∧
      res.val.length = v2.val.length ∧ ∀ s, res.val.getD s zBT = swapF v v2 l r rs1 re1 rb s := by
  unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0
  refine range_loop_spec
    (fun x => verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0.body
      v v1 v3 l r x.1 x.2)
    (fun i cur => rs1.val ≤ i ∧ cur.val.length = v2.val.length ∧
      ∀ s, cur.val.getD s zBT =
        if (∃ q, rs1.val ≤ q ∧ q < i ∧ (v.val.getD q zST).index.val = s)
        then l else v2.val.getD s zBT)
    (fun res => res.val.length = v2.val.length ∧
      ∀ s, res.val.getD s zBT = swapF v v2 l r rs1 re1 rb s) re1 ?_ ?_ rs1 v2 hle1
    ⟨le_refl _, rfl, ?_⟩
  · intro i cur hi ⟨hrs, hlen, hpt⟩
    obtain ⟨o, it1, hnext, ho, hstart, hend⟩ := next_range_some
      ({ start := i, «end» := re1 } : core.ops.range.Range Std.Usize) hi
    have hiv : i.val < v.val.length := lt_of_lt_of_le hi hre1
    have hbi := hb1 i.val hrs hi
    have hget : v.val.getD i.val zST = v.val[i.val] := by
      simp [List.getD_eq_getElem?_getD, hiv]
    rw [hget] at hbi
    have hbnd : (v.val[i.val]'hiv).index.val < cur.val.length := by rw [hlen]; exact hbi
    refine ⟨it1.start, { slice := cur.slice.set (v.val[i.val]'hiv).index l }, hstart, ?_, ?_⟩
    · have hit1 : it1 = ({ start := it1.start, «end» := re1 } : core.ops.range.Range Std.Usize) := by
        cases it1; simp only at hend ⊢; simp [hend]
      unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0.body
      subst ho
      have hidx : v.index_usize i = ok (v.val[i.val]'hiv) := by
        obtain ⟨x, hx, hxe⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hiv)
        rw [hx, hxe]
      simp [hnext, hidx, vec_tagged_index_mut_ok cur _ hbnd]
      exact hit1
    · refine ⟨by omega, ?_, ?_⟩
      · show (cur.slice.set _ l).val.length = _
        rw [Slice.set_val_eq, List.length_set]; exact hlen
      · intro s
        rw [vec_set_getD cur _ l zBT s hbnd]
        have := pw_step (fun q => (v.val.getD q zST).index.val) rs1.val i.val s hrs l
          (fun s => v2.val.getD s zBT) (fun s => cur.val.getD s zBT) hpt
        simpa only [hget] using this
  · intro i cur hi ⟨hrs, hlen, hpt⟩
    obtain ⟨o, it1, hnext, ho, hid⟩ := next_range_none
      ({ start := i, «end» := re1 } : core.ops.range.Range Std.Usize) (by simp [hi])
    have hrb' : v1.slice.val[r.index.val]'hrbN = rb := by
      rw [← hrb]; simp [List.getD_eq_getElem?_getD, hrbN]; rfl
    obtain ⟨v4, hv4, hv4len, hv4pt⟩ := relabel_loop_spec v r rb.begin rb.«end» cur hrbe hrbl
      (fun q h1 h2 => by rw [hlen]; exact hb2 q h1 h2)
    have hpost : v4.val.length = v2.val.length ∧
        ∀ s, v4.val.getD s zBT = swapF v v2 l r rs1 re1 rb s := by
      refine ⟨by rw [hv4len, hlen], fun s => ?_⟩
      rw [hv4pt s, hpt s, hi]
      rfl
    refine ⟨v4, ?_, hpost⟩
    unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0.body
    subst ho
    simp [hnext, vec_tagged_index_val v1 r hrbN, hrb', hv4,
      hA v4 hpost.1 hpost.2]
  · intro s
    rw [if_neg]
    rintro ⟨q, h1, h2, _⟩
    omega

/-- The block index permutation induced by exchanging the records at `l` and `r`. -/
def swapIdx (l r j : Nat) : Nat := if j = r then l else if j = l then r else j

/-- The block vector of `swap_blocks`: the records at `l` and `r` exchanged. -/
def swapBlocksVec (bs : alloc.vec.Vec Block) (l r : TagIndex Std.Usize BlockTag)
    (bl br : Block) : alloc.vec.Vec Block :=
  { slice := (bs.slice.set l.index br).set r.index bl }

theorem swapBlocksVec_val (bs : alloc.vec.Vec Block) (l r : TagIndex Std.Usize BlockTag)
    (bl br : Block) :
    (swapBlocksVec bs l r bl br).val = (bs.val.set l.index.val br).set r.index.val bl := by
  show ((bs.slice.set l.index br).set r.index bl).val = _
  rw [Slice.set_val_eq, Slice.set_val_eq]
  rfl

theorem swapBlocksVec_length (bs : alloc.vec.Vec Block) (l r : TagIndex Std.Usize BlockTag)
    (bl br : Block) :
    (swapBlocksVec bs l r bl br).val.length = bs.val.length := by
  rw [swapBlocksVec_val]; simp

/-- Reading the exchanged block vector. -/
theorem swapBlocksVec_getD (bs : alloc.vec.Vec Block) (l r : TagIndex Std.Usize BlockTag)
    (hl : l.index.val < bs.val.length) (hr : r.index.val < bs.val.length) (hne : l.index.val ≠ r.index.val)
    (j : Nat) :
    (swapBlocksVec bs l r (bs.val.getD l.index.val blk0) (bs.val.getD r.index.val blk0)).val.getD j blk0
      = bs.val.getD (swapIdx l.index.val r.index.val j) blk0 := by
  rw [swapBlocksVec_val]
  simp only [swapIdx, List.getD_eq_getElem?_getD, List.getElem?_set, List.length_set]
  by_cases hjr : j = r.index.val
  · subst hjr; simp [hr]
  · by_cases hjl : j = l.index.val
    · subst hjl; simp [hl, hr, hne, Ne.symm hne]
    · simp [hjr, hjl, Ne.symm hjr, Ne.symm hjl]

/-- Elements in `[b, e)` (as positions) are exactly the states whose offset lies in it. -/
theorem PartInv_exists_pos_iff {n : Nat} {p : BlockPartition} (hp : PartInv n p) {b e : Nat}
    (he : e ≤ n) {s : Nat} (hs : s < n) :
    (∃ q, b ≤ q ∧ q < e ∧ (p.elements.val.getD q zST).index.val = s) ↔
      (b ≤ offAt p s ∧ offAt p s < e) := by
  constructor
  · rintro ⟨q, h1, h2, h3⟩
    have hq : q < n := by omega
    have := (hp.perm q hq).2
    change (eAt p q).index.val = s at h3
    rw [h3] at this
    rw [this]; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨offAt p s, h1, h2, hp.inv s hs⟩

/-- Exchanging two blocks (records and `element_to_block` labels) preserves `PartInv`. -/
theorem swap_blocks_partInv {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (l r : TagIndex Std.Usize BlockTag) (hl : l.index.val < p.blocks.val.length)
    (hr : r.index.val < p.blocks.val.length) (hne : l.index.val ≠ r.index.val)
    (e : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (hlen : e.val.length = n)
    (he : ∀ s, e.val.getD s zBT =
      swapF p.elements p.element_to_block l r (blkAt p r.index.val).begin
        (blkAt p r.index.val).«end» (blkAt p l.index.val) s) :
    PartInv n { p with
      blocks := swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val),
      element_to_block := e } := by
  set N := p.blocks.val.length with hNdef
  set bl := blkAt p l.index.val with hbl
  set br := blkAt p r.index.val with hbr
  set p' : BlockPartition := { p with
      blocks := swapBlocksVec p.blocks l r bl br, element_to_block := e } with hp'
  have hbp : ∀ j, blkAt p' j = blkAt p (swapIdx l.index.val r.index.val j) := by
    intro j
    exact swapBlocksVec_getD p.blocks l r hl hr hne j
  have hN' : p'.blocks.val.length = N := swapBlocksVec_length _ _ _ _ _
  have hσlt : ∀ j, j < N → swapIdx l.index.val r.index.val j < N := by
    intro j hj; unfold swapIdx; split_ifs <;> omega
  have hσinj : ∀ j k, j < N → k < N → j ≠ k →
      swapIdx l.index.val r.index.val j ≠ swapIdx l.index.val r.index.val k := by
    intro j k hj hk hjk; unfold swapIdx; split_ifs <;> omega
  have hbl_range := hp.blk l.index.val hl
  have hbr_range := hp.blk r.index.val hr
  refine ⟨hp.len_e, hlen, hp.len_off, hp.perm, hp.inv, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : k < N := hN' ▸ hk
    rw [hbp k]
    exact hp.blk _ (hσlt k hk')
  · intro s hs
    obtain ⟨hk, hb1, hb2⟩ := hp.own s hs
    have hoff_lt : offAt p s < n := by
      have := (hp.blk _ hk).2.1; omega
    have hLiff := PartInv_exists_pos_iff hp hbl_range.2.1 hs (b := bl.begin.val)
    have hRiff := PartInv_exists_pos_iff hp hbr_range.2.1 hs (b := br.begin.val)
    have hes : e2bAt p' s = (swapF p.elements p.element_to_block l r br.begin br.«end» bl s).index.val := by
      show (e.val.getD s zBT).index.val = _
      rw [he s]
    have hoffeq : offAt p' s = offAt p s := rfl
    rw [hes, hoffeq]
    unfold swapF
    by_cases cL : bl.begin.val ≤ offAt p s ∧ offAt p s < bl.«end».val
    · rw [if_pos (hLiff.mpr cL)]
      have : blkAt p' r.index.val = bl := by
        rw [hbp, swapIdx]; simp; exact hbl.symm
      refine ⟨by rw [hN']; exact hr, ?_⟩
      rw [this]; exact cL
    · rw [if_neg (fun h => cL (hLiff.mp h))]
      by_cases cR : br.begin.val ≤ offAt p s ∧ offAt p s < br.«end».val
      · rw [if_pos (hRiff.mpr cR)]
        have : blkAt p' l.index.val = br := by
          rw [hbp, swapIdx]; simp [hne]; exact hbr.symm
        refine ⟨by rw [hN']; exact hl, ?_⟩
        rw [this]; exact cR
      · rw [if_neg (fun h => cR (hRiff.mp h))]
        have hk_ne_l : e2bAt p s ≠ l.index.val := by
          intro h; apply cL; rw [h] at hb1 hb2; exact ⟨hb1, hb2⟩
        have hk_ne_r : e2bAt p s ≠ r.index.val := by
          intro h; apply cR; rw [h] at hb1 hb2; exact ⟨hb1, hb2⟩
        have hσk : swapIdx l.index.val r.index.val (e2bAt p s) = e2bAt p s := by
          unfold swapIdx; simp [hk_ne_l, hk_ne_r]
        have hcur : (p.element_to_block.val.getD s zBT).index.val = e2bAt p s := rfl
        rw [hcur, hbp, hσk]
        exact ⟨by rw [hN']; exact hk, hb1, hb2⟩
  · intro j k hj hk hjk
    have hj' : j < N := hN' ▸ hj
    have hk' : k < N := hN' ▸ hk
    rw [hbp j, hbp k]
    exact hp.disj _ _ (hσlt j hj') (hσlt k hk') (hσinj j k hj' hk' hjk)

theorem tag_eq_decide {Tag : Type} (a b : TagIndex Std.Usize Tag) :
    verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq
      core.cmp.PartialEqUsize a b = ok (decide (a.index = b.index)) := by
  rw [tag_partial_eq_inst]

theorem swapIdx_lt {l r N j : Nat} (hl : l < N) (hr : r < N) (hj : j < N) : swapIdx l r j < N := by
  unfold swapIdx; split_ifs <;> omega

theorem swapIdx_invol (l r j : Nat) : swapIdx l r (swapIdx l r j) = j := by
  unfold swapIdx
  by_cases h1 : j = r
  · by_cases h2 : l = r
    · subst h2; simp [h1]
    · simp [h1, h2]
  · by_cases h2 : j = l
    · by_cases h3 : r = l
      · subst h3; simp [h2]
      · simp [h2]
    · simp [h1, h2]

/-- Once the block records are exchanged (`blkAt p' j = blkAt p (swapIdx j)`) and `element_offset`
    is unchanged, the block of a state is the exchanged block index: `PartInv` determines
    `element_to_block` from the offsets and the block ranges. -/
theorem swap_blocks_e2b {n : Nat} {p p' : BlockPartition} (hp : PartInv n p) (hp' : PartInv n p')
    (l r : Nat) (hl : l < p.blocks.val.length) (hr : r < p.blocks.val.length)
    (hoff : p'.element_offset = p.element_offset) (hlen : p'.blocks.val.length = p.blocks.val.length)
    (hblk : ∀ j, blkAt p' j = blkAt p (swapIdx l r j)) {s : Nat} (hs : s < n) :
    e2bAt p' s = swapIdx l r (e2bAt p s) := by
  obtain ⟨hi1, hi2, hi3⟩ := hp.own s hs
  obtain ⟨hj1, hj2, hj3⟩ := hp'.own s hs
  have hoffeq : offAt p' s = offAt p s := by simp [offAt, hoff]
  rw [hoffeq, hblk] at hj2 hj3
  have hsw : swapIdx l r (e2bAt p' s) < p.blocks.val.length :=
    swapIdx_lt hl hr (by rw [← hlen]; exact hj1)
  have := hp.pos_block_unique hi1 hsw ⟨hi2, hi3⟩ ⟨hj2, hj3⟩
  rw [this, swapIdx_invol]

/-- Contract of `BlockPartition::swap_blocks`: exchanges the two block records (`swapIdx`) and
    re-labels `element_to_block`; `elements` and `element_offset` are untouched; `PartInv` is
    preserved. -/
theorem swap_blocks_spec {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (l r : TagIndex Std.Usize BlockTag) (hl : l.index.val < p.blocks.val.length)
    (hr : r.index.val < p.blocks.val.length) :
    ∃ p', verified.merc_reduction.block_partition.BlockPartition.swap_blocks p l r = ok p' ∧
      PartInv n p' ∧ p'.elements = p.elements ∧ p'.element_offset = p.element_offset ∧
      p'.blocks.val.length = p.blocks.val.length ∧
      (∀ j, blkAt p' j = blkAt p (swapIdx l.index.val r.index.val j)) ∧
      ∀ s, s < n → e2bAt p' s = swapIdx l.index.val r.index.val (e2bAt p s) := by
  by_cases hlr : l.index.val = r.index.val
  · have hid : ∀ j, swapIdx l.index.val r.index.val j = j := by
      intro j; unfold swapIdx; by_cases h : j = r.index.val <;> simp [h, hlr]
    refine ⟨p, ?_, hp, rfl, rfl, rfl, ?_, ?_⟩
    · unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks
      have : l.index = r.index := UScalar.eq_of_val_eq hlr
      simp [this]
    · intro j; rw [hid]
    · intro s _; rw [hid]
  · have hne : l.index.val ≠ r.index.val := hlr
    have hlr' : l.index ≠ r.index := fun h => hlr (by rw [h])
    have hdec : decide (l.index = r.index) = false := by simp [hlr']
    have hbl_read : p.blocks.slice.val[l.index.val]'hl = blkAt p l.index.val :=
      (blkAt_eq_getElem hl).symm
    have hbr_read : p.blocks.slice.val[r.index.val]'hr = blkAt p r.index.val :=
      (blkAt_eq_getElem hr).symm
    have hlb := hp.blk l.index.val hl
    have hrb := hp.blk r.index.val hr
    have hv0len : r.index.val < ({ slice := p.blocks.slice.set l.index (blkAt p r.index.val) } :
        alloc.vec.Vec Block).val.length := by
      show r.index.val < (p.blocks.slice.set _ _).val.length
      rw [Slice.set_val_eq, List.length_set]; exact hr
    have hv1len : l.index.val < (swapBlocksVec p.blocks l r (blkAt p l.index.val)
        (blkAt p r.index.val)).val.length := by
      rw [swapBlocksVec_length]; exact hl
    have hv1l : (swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val)).slice.val[
        l.index.val]'hv1len = blkAt p r.index.val := by
      have h2 : (swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val)).val.getD
          l.index.val blk0 = p.blocks.val.getD (swapIdx l.index.val r.index.val l.index.val) blk0 :=
        swapBlocksVec_getD p.blocks l r hl hr hne _
      have h3 : (swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val)).val.getD
          l.index.val blk0 = (swapBlocksVec p.blocks l r (blkAt p l.index.val)
            (blkAt p r.index.val)).val[l.index.val]'hv1len := by
        simp [List.getD_eq_getElem?_getD, hv1len]
      show (swapBlocksVec p.blocks l r (blkAt p l.index.val)
            (blkAt p r.index.val)).val[l.index.val]'hv1len = _
      rw [← h3, h2]
      simp [swapIdx, hne]
      rfl
    unfold verified.merc_reduction.block_partition.BlockPartition.swap_blocks
    simp [hdec, vec_tagged_index_val p.blocks l hl,
      vec_tagged_index_val p.blocks r hr, hbl_read, hbr_read,
      vec_tagged_index_mut_ok p.blocks l hl, vec_tagged_index_mut_ok _ r hv0len]
    have hv1eq : (alloc.vec.Vec.mk ((p.blocks.slice.set l.index (blkAt p r.index.val)).set r.index (blkAt p l.index.val)) : alloc.vec.Vec Block) = swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val) := rfl
    rw [hv1eq, vec_tagged_index_val _ l hv1len, hv1l]
    simp only [bind_tc_ok]
    have hN1 : (swapBlocksVec p.blocks l r (blkAt p l.index.val)
        (blkAt p r.index.val)).val.length = p.blocks.val.length := swapBlocksVec_length _ _ _ _ _
    have hrb' : (swapBlocksVec p.blocks l r (blkAt p l.index.val)
        (blkAt p r.index.val)).val.getD r.index.val blk0 = blkAt p l.index.val := by
      have h2 : (swapBlocksVec p.blocks l r (blkAt p l.index.val)
          (blkAt p r.index.val)).val.getD r.index.val blk0 =
          p.blocks.val.getD (swapIdx l.index.val r.index.val r.index.val) blk0 :=
        swapBlocksVec_getD p.blocks l r hl hr hne _
      rw [h2]; simp [swapIdx]; rfl
    have hlenE : p.elements.val.length = n := hp.len_e
    have hlenB : p.element_to_block.val.length = n := hp.len_e2b
    obtain ⟨res, hres, hreslen, hrespt⟩ := swap_blocks_loop0_spec p.elements
      (swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val))
      p.element_to_block p.element_offset l r (blkAt p r.index.val).begin
      (blkAt p r.index.val).«end» (blkAt p l.index.val)
      (by omega) (by omega) (by rw [hN1]; exact hr) hrb' (by omega) (by omega)
      (fun q h1 h2 => by
        have hq : q < n := by omega
        have := (hp.perm q hq).1
        change (eAt p q).index.val < _ at this ⊢
        omega)
      (fun q h1 h2 => by
        have hq : q < n := by omega
        have := (hp.perm q hq).1
        change (eAt p q).index.val < _ at this ⊢
        omega)
      (fun e hlen hpt =>
        merc_reduction.block_partition.BlockPartition.assert_consistent_ok _
          (swap_blocks_partInv hp l r hl hr hne e (by rw [hlen]; exact hlenB) hpt))
    rw [hres]
    simp only [bind_tc_ok]
    have hPI := swap_blocks_partInv hp l r hl hr hne res (by rw [hreslen]; exact hlenB) hrespt
    have hblkeq : ∀ j, blkAt { p with blocks := swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val), element_to_block := res } j = blkAt p (swapIdx l.index.val r.index.val j) := fun j =>
      swapBlocksVec_getD p.blocks l r hl hr hne j
    refine ⟨{ p with blocks := swapBlocksVec p.blocks l r (blkAt p l.index.val) (blkAt p r.index.val), element_to_block := res }, rfl, hPI, rfl, rfl, hN1, hblkeq, ?_⟩
    intro s hs
    exact swap_blocks_e2b hp hPI l.index.val r.index.val hl hr rfl hN1 hblkeq hs


end MercVerified.Refinement.Proofs
