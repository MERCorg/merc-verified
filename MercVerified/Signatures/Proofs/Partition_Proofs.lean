import MercVerified.Signatures.Refinement
import MercVerified.Code.FunsExternalSpecs
import Aeneas.Std.WP

/-!
# Partition data-model foundation

With `TagIndex` given its concrete model (`TagIndex T Tag := T`, see
`MercVerified/Code/TypesExternal_Template.lean`), every tagged operation is
definitional arithmetic on the payload, and index-by-tag is plain list
indexing. This file records the lemmas the worklist-loop proof derives from
that: reads like `BlockPartition.block` and `BlockPartition.element_to_block`
collapse to `List.get` on the underlying vectors.

Machine-generated proofs; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_collections.indexed_partition (BlockTag)

namespace MercVerified.Signatures.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private abbrev BlockIndex := TagIndex Std.Usize BlockTag

/-- `BlockPartition::block` accesses `blocks` by the tag's payload. -/
theorem block_partition_block_val
    (p : verified.merc_reduction.block_partition.BlockPartition)
    (b : BlockIndex) (h : b.index.val < p.blocks.val.length) :
    verified.merc_reduction.block_partition.BlockPartition.block p b =
      ok (p.blocks.slice.val[b.index.val]) := by
  simp only [verified.merc_reduction.block_partition.BlockPartition.block]
  rw [vec_tagged_index_val p.blocks b h]

/-- `Block::len` is the derived length `end - begin`: the `assert_consistent`
    integrity check always completes (vetted boundary axiom), so the result is
    the scalar subtraction (which may itself fail on underflow). -/
theorem block_len_contract
    (b : verified.merc_reduction.block_partition.Block) :
    verified.merc_reduction.block_partition.Block.len b = b.end - b.begin := by
  unfold verified.merc_reduction.block_partition.Block.len
  rcases merc_reduction.block_partition.Block.assert_consistent_ok b with ⟨u, hu⟩
  rw [hu]
  simp

/-- `Block::has_marked` probes whether the marked suffix is non-empty: the
    `assert_consistent` integrity check always completes and the predicate is
    `marked_split < end` (decided into `Bool`). -/
theorem block_has_marked_contract
    (b : verified.merc_reduction.block_partition.Block) :
    verified.merc_reduction.block_partition.Block.has_marked b =
      ok (decide ((b.marked_split : Nat) < (b.«end» : Nat))) := by
  unfold verified.merc_reduction.block_partition.Block.has_marked
  rcases merc_reduction.block_partition.Block.assert_consistent_ok b with ⟨u, hu⟩
  rw [hu]
  simp

/-- `BlockPartition::num_of_blocks` is just the length of `blocks`. -/
theorem num_of_blocks_contract
    (p : verified.merc_reduction.block_partition.BlockPartition) :
    verified.merc_reduction.block_partition.BlockPartition.num_of_blocks p =
      ok (alloc.vec.Vec.len p.blocks) := by
  unfold verified.merc_reduction.block_partition.BlockPartition.num_of_blocks
  rfl

/-- `BlockPartition::is_trivially_partitioned` reads `blocks[block_index]` and
    reports whether its derived length is exactly `1`: the do-mirror equation. -/
theorem is_trivially_partitioned_contract
    (self : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : BlockIndex) :
    verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned self block_index =
      (do
        let b ←
          verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
            (core.slice.index.SliceIndexUsizeSlice
              verified.merc_reduction.block_partition.Block) self.blocks block_index
        let i ← verified.merc_reduction.block_partition.Block.len b
        ok (i = 1#usize)) := by
  rfl

/-- Value form of `is_trivially_partitioned` once the read of `blocks[block_index]`
    is resolved: the pending `Block::len` call on the indexed block. -/
theorem is_trivially_partitioned_after_ok
    (self : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : BlockIndex) (h : block_index.index.val < self.blocks.val.length) :
    verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned self block_index =
      (do
        let b ← ok (self.blocks.val[block_index.index.val]'h)
        let i ← verified.merc_reduction.block_partition.Block.len b
        ok (i = 1#usize)) := by
  unfold verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned
  rw [vec_tagged_index_val self.blocks block_index h]
  rfl

private abbrev PartitionSigKey := alloc.vec.Vec ((TagIndex Std.Usize verified.merc_lts.lts.LabelTag) × BlockIndex)
private abbrev PartitionInternMap :=
  std.collections.hash.map.HashMap PartitionSigKey BlockIndex verified.rustc_hash.FxBuildHasher Global

private abbrev PPBuilder := verified.merc_reduction.block_partition.BlockPartitionBuilder

/-- `block_index`'s block with its whole suffix marked (applied by
    `trivial_partition_marked`). -/
private def mark_all (self : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : BlockIndex) (h : block_index.index.val < self.blocks.val.length) :
    verified.merc_reduction.block_partition.Block :=
  { self.blocks.val[block_index.index.val]'h with
      marked_split := (self.blocks.val[block_index.index.val]'h).«end» }

/-- `BlockPartition::new_loop` semantics

`new_loop` fills `elements`/`element_to_block`/`element_offset` for a fresh
partition over `[0, num)`: `elements` and `element_offset` enumerate the range,
`element_to_block` is constantly the initial block (`0`). This is the
worklist-loop proof's base case, and it doubles as the template for every
`Range`-driven inner-frame proof (`strong_process_marked_elements`,
`mark_dirty_new_blocks`).
-/

private abbrev Sz := Std.Usize
private abbrev StateTag := verified.merc_lts.lts.StateTag
private abbrev BlockTagIdx := verified.merc_collections.indexed_partition.BlockTag

private abbrev NewLoopState : Type :=
  core.ops.range.Range Sz × alloc.vec.Vec (TagIndex Sz StateTag) ×
    alloc.vec.Vec (TagIndex Sz BlockTagIdx) × alloc.vec.Vec Sz

/-- `usize` with payload `k % 2^bits` (total construction). -/
def uTotal (k : Nat) : Sz := { bv := BitVec.ofNat UScalarTy.Usize.numBits k }

lemma uTotal_val_of_lt {k : Nat} (h : k < 2 ^ UScalarTy.Usize.numBits) :
    (uTotal k).val = k := by
  unfold uTotal UScalar.val
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The tagged index with payload `k % 2^bits`. -/
def uTag {Tag : Type} (k : Nat) : TagIndex Sz Tag := { index := uTotal k, marker := () }

lemma uTotal_zero : uTotal 0 = 0#usize := by
  apply UScalar.eq_of_val_eq
  rw [uTotal_val_of_lt (by exact pow_pos (by decide) UScalarTy.Usize.numBits)]
  simp

lemma sz_eq_from_val {a b : Sz} (h : a.val = b.val) : a = b :=
  UScalar.eq_of_val_eq h

/-- Every `usize` payload fits in `[0, 2^numBits)`. -/
lemma sz_val_lt_two_pow (x : Sz) : x.val < 2 ^ UScalarTy.Usize.numBits := by
  change x.bv.toNat < 2 ^ UScalarTy.Usize.numBits
  exact x.bv.isLt

/-- Every `usize` payload is at most `Usize.max`. -/
lemma sz_val_le_max (x : Sz) : x.val ≤ Usize.max := by
  have h := sz_val_lt_two_pow x
  simp [Usize.max, Usize.numBits] at h ⊢
  omega

/-- `1`, the length of a singleton list, fits in `usize`. -/
private lemma one_le_max : (1 : Nat) ≤ Usize.max := by
  simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq with
  | inl h => rw [h]; norm_num
  | inr h => rw [h]; norm_num

/-- `BlockPartition::trivial_partition_marked` returns the singleton marked list
    `[block_index]` and updates `blocks[block_index]` to be unconditionally
    marked (`unmark_all`: its `marked_split` suffix is pulled up to `end`). -/
theorem trivial_partition_marked_contract
    (self : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : BlockIndex) (h : block_index.index.val < self.blocks.val.length) :
    ∃ (v : alloc.vec.Vec BlockIndex)
      (p : verified.merc_reduction.block_partition.BlockPartition),
      verified.merc_reduction.block_partition.BlockPartition.trivial_partition_marked self block_index = ok (v, p) ∧
      v.val = [block_index] ∧
      p.blocks.val =
        self.blocks.val.set block_index.index.val
          ({ self.blocks.val[block_index.index.val]'h with
              marked_split := (self.blocks.val[block_index.index.val]'h).«end» }) := by
  have hb : block_index.index.val < self.blocks.slice.val.length := by exact h
  refine ⟨alloc.vec.Vec.from [block_index] one_le_max,
    ({ self with
       blocks := alloc.vec.Vec.mk (self.blocks.slice.set block_index.index
         ({ (self.blocks.slice.val[block_index.index.val]'hb) with
             marked_split := (self.blocks.slice.val[block_index.index.val]'hb).«end» })) }),
    ?_, ?_, ?_⟩
  · rw [verified.merc_reduction.block_partition.BlockPartition.trivial_partition_marked]
    rw [blocks_index_mut_contract self block_index hb]
    simp [verified.merc_reduction.block_partition.Block.unmark_all,
      alloc.vec.FromVecArray.from, Aeneas.Std.Array.make]
  · simp [alloc.vec.Vec.from_val]
  · change (self.blocks.slice.set block_index.index
        ({ (self.blocks.slice.val[block_index.index.val]'hb) with
            marked_split := (self.blocks.slice.val[block_index.index.val]'hb).«end» })).val =
      self.blocks.val.set block_index.index.val
        ({ (self.blocks.val[block_index.index.val]'h) with
            marked_split := (self.blocks.val[block_index.index.val]'h).«end» })
    rw [Slice.set_val_eq]
    rfl

/-!
## `signature_refinement::strong_partition_marked`

`strong_partition_marked` probes `is_trivially_partitioned`: a partition whose
indexed block has derived length `1` takes the cheap singleton path
(`trivial_partition_marked`), everything else flows through
`marked_elements_sorted`/`strong_process_marked_elements`/
`finish_partition_marked`. The two branch contracts below mirror that
decision point; the `true` branch is closed to a concrete value, the `false`
branch stays a do-mirror (its three calls are contracted away by the worklist
loop proof that consumes them).
-/

theorem strong_partition_marked_trivial_contract {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (partition : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : BlockIndex) (id : PartitionInternMap)
    (key_to_signature : alloc.vec.Vec PartitionSigKey)
    (signature_builder : PartitionSigKey) (split_builder : PPBuilder)
    (state_to_key : alloc.vec.Vec BlockIndex)
    (hAll : verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned partition block_index = ok true) :
    verified.merc_reduction.signature_refinement.strong_partition_marked LTSInst sys partition block_index
        id key_to_signature signature_builder split_builder state_to_key =
      (do
        let (v, partition1) ←
          verified.merc_reduction.block_partition.BlockPartition.trivial_partition_marked partition block_index
        ok (v, partition1, id, key_to_signature, signature_builder, split_builder, state_to_key)) := by
  unfold verified.merc_reduction.signature_refinement.strong_partition_marked
  rw [hAll]
  simp

/-- The singleton partition case closes fully: the fresh index list is
    `[block_index]` and `blocks[block_index]` becomes unconditionally marked. -/
theorem strong_partition_marked_trivial {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (partition : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : BlockIndex) (id : PartitionInternMap)
    (key_to_signature : alloc.vec.Vec PartitionSigKey)
    (signature_builder : PartitionSigKey) (split_builder : PPBuilder)
    (state_to_key : alloc.vec.Vec BlockIndex)
    (hAll : verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned partition block_index = ok true)
    (hIdx : block_index.index.val < partition.blocks.val.length) :
    ∃ (v : alloc.vec.Vec BlockIndex)
      (p : verified.merc_reduction.block_partition.BlockPartition),
      verified.merc_reduction.signature_refinement.strong_partition_marked LTSInst sys partition block_index
        id key_to_signature signature_builder split_builder state_to_key =
          ok (v, p, id, key_to_signature, signature_builder, split_builder, state_to_key) ∧
      v.val = [block_index] ∧
      p.blocks.val = partition.blocks.val.set block_index.index.val (mark_all partition block_index hIdx) := by
  rw [strong_partition_marked_trivial_contract LTSInst sys partition block_index id key_to_signature
    signature_builder split_builder state_to_key hAll]
  rcases trivial_partition_marked_contract partition block_index hIdx with ⟨v0, p0, heq, hv, hp⟩
  refine ⟨v0, p0, ?_, ?_, ?_⟩
  · rw [heq]
    simp
  · exact hv
  · rw [hp]
    rfl

/-- The non-singleton path: `strong_partition_marked` chains the three
    refinement helpers; this do-mirror defers their individual contracts. -/
theorem strong_partition_marked_nontrivial_contract {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (partition : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : BlockIndex) (id : PartitionInternMap)
    (key_to_signature : alloc.vec.Vec PartitionSigKey)
    (signature_builder : PartitionSigKey) (split_builder : PPBuilder)
    (state_to_key : alloc.vec.Vec BlockIndex)
    (hAll : verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned partition block_index = ok false) :
    verified.merc_reduction.signature_refinement.strong_partition_marked LTSInst sys partition block_index
        id key_to_signature signature_builder split_builder state_to_key =
      (do
        let split_builder1 ←
          verified.merc_reduction.block_partition.BlockPartition.marked_elements_sorted
            partition block_index split_builder
        let (id1, key_to_signature1, signature_builder1, split_builder2, state_to_key1) ←
          verified.merc_reduction.signature_refinement.strong_process_marked_elements
            LTSInst sys partition id key_to_signature signature_builder split_builder1 state_to_key
        let (v, partition1, split_builder3) ←
          verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked
            partition block_index split_builder2
        ok (v, partition1, id1, key_to_signature1, signature_builder1, split_builder3, state_to_key1)) := by
  unfold verified.merc_reduction.signature_refinement.strong_partition_marked
  rw [hAll]
  simp

lemma map_range_concat (s : Nat) :
    (List.range s).map uTotal ++ [uTotal s] = (List.range (s + 1)).map uTotal := by
  rw [List.range_succ, List.map_append]
  rfl

lemma map_range_concat_tag {Tag : Type} (s : Nat) :
    (List.range s).map (uTag (Tag := Tag)) ++ [uTag s] = (List.range (s + 1)).map uTag := by
  rw [List.range_succ, List.map_append]
  rfl

lemma replicate_append_succ {α : Type} (m : Nat) (x : α) :
    List.replicate m x ++ [x] = List.replicate (Nat.succ m) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.replicate_succ, List.cons_append, ih]

lemma next_range_some (it : core.ops.range.Range Sz)
    (h : it.start.val < it.end.val) :
    ∃ (o : Option Sz) (it1 : core.ops.range.Range Sz),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it = ok (o, it1) ∧
      o = some it.start ∧ it1.start.val = it.start.val + 1 ∧ it1.end = it.end := by
  have hnext := core.iter.range.IteratorRange.next_UScalar_some_spec
    (ty := UScalarTy.Usize) (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intro x; simp) (by intros a b; rfl) it h
  rcases Std.WP.spec_imp_exists hnext with ⟨p, hp, hpost⟩
  rcases p with ⟨opt, it1⟩
  rcases hpost with ⟨hopt, hstart, hend⟩
  exact ⟨opt, it1, hp, hopt, hstart, hend⟩

lemma next_range_none (it : core.ops.range.Range Sz)
    (h : it.start.val ≥ it.end.val) :
    ∃ (o : Option Sz) (it1 : core.ops.range.Range Sz),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it = ok (o, it1) ∧
      o = none ∧ it1 = it := by
  have hnext := core.iter.range.IteratorRange.next_UScalar_none_spec
    (ty := UScalarTy.Usize) (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) (by intros a b; rfl) it h
  rcases Std.WP.spec_imp_exists hnext with ⟨p, hp, hpost⟩
  rcases p with ⟨opt, it1⟩
  rcases hpost with ⟨hopt, hident⟩
  exact ⟨opt, it1, hp, hopt, hident⟩

/-- The invariant carried by the loop: at `[it.start, it.end)`, the three
    accumulated lists contain exactly the processed prefix of the range. -/
private def newLoopInv (num : Sz) : NewLoopState → Prop :=
  fun st =>
    st.1.end = num ∧ st.1.start.val ≤ num.val ∧
    st.2.1.val = (List.range st.1.start.val).map uTag ∧
    st.2.2.1.val = List.replicate st.1.start.val (uTag 0) ∧
    st.2.2.2.val = (List.range st.1.start.val).map uTotal

/-- Postcondition: all three lists fully enumerate `[0, num)`. -/
private def newLoopPost (num : Sz) : (alloc.vec.Vec (TagIndex Sz StateTag)
      × alloc.vec.Vec (TagIndex Sz BlockTagIdx) × alloc.vec.Vec Sz) → Prop :=
  fun r =>
    r.1.val = (List.range num.val).map uTag ∧
    r.2.1.val = List.replicate num.val (uTag 0) ∧
    r.2.2.val = (List.range num.val).map uTotal

private def newLoopMeasure (st : NewLoopState) : Nat := st.1.end.val - st.1.start.val

lemma vec_push_val {U : Type} (v : alloc.vec.Vec U) (x : U)
    (hb : v.val.length < Usize.max) :
    ∃ v', v.push x = ok v' ∧ v'.val = v.val ++ [x] :=
  Std.WP.spec_imp_exists (alloc.vec.Vec.push_spec v x hb)

private lemma newLoopInv_start_lt_max {num : Sz} {st : NewLoopState}
    (hinv : newLoopInv num st) (hlt : st.1.start.val < st.1.end.val) :
    st.1.start.val < Usize.max := by
  rcases hinv with ⟨hend_eq, hstart_le, _⟩
  have hlt_num : st.1.start.val < num.val := by simpa [hend_eq] using hlt
  have hnum : num.val ≤ Usize.max := sz_val_le_max num
  omega

/-- One `new_loop.body` step (`start < end`): pushes the current index, and
    the block list grows by one `0`. -/
private theorem new_loop_body_step (num : Sz) (st : NewLoopState)
    (hinv : newLoopInv num st) (hlt : st.1.start.val < st.1.end.val) :
    ∃ st' : NewLoopState,
      verified.merc_reduction.block_partition.BlockPartition.new_loop.body
        st.1 st.2.1 st.2.2.1 st.2.2.2 = ok (cont st') ∧
      newLoopInv num st' ∧ newLoopMeasure st' < newLoopMeasure st := by
  have hnext := next_range_some st.1 hlt
  rcases hnext with ⟨o, it1, hnext_e, hopt, hstart', hend'⟩
  have hbound : st.1.start.val < Usize.max := newLoopInv_start_lt_max hinv hlt
  have hlen_es : st.2.1.val.length < Usize.max := by
    rcases hinv with ⟨_, _, hlen1, _, _⟩
    calc
      st.2.1.val.length = (List.map uTag (List.range st.1.start.val)).length := by
        exact congrArg List.length hlen1
      _ = st.1.start.val := by rw [List.length_map, List.length_range]
      _ < Usize.max := hbound
  have hlen_bs : st.2.2.1.val.length < Usize.max := by
    rcases hinv with ⟨_, _, _, hlen2, _⟩
    calc
      st.2.2.1.val.length = (List.replicate st.1.start.val (uTag 0)).length := by
        exact congrArg List.length hlen2
      _ = st.1.start.val := by rw [List.length_replicate]
      _ < Usize.max := hbound
  have hlen_os : st.2.2.2.val.length < Usize.max := by
    rcases hinv with ⟨_, _, _, _, hlen3⟩
    calc
      st.2.2.2.val.length = (List.map uTotal (List.range st.1.start.val)).length := by
        exact congrArg List.length hlen3
      _ = st.1.start.val := by rw [List.length_map, List.length_range]
      _ < Usize.max := hbound
  rcases vec_push_val st.2.1 ⟨st.1.start, ()⟩ hlen_es with ⟨es1, hes1, hesv⟩
  rcases vec_push_val st.2.2.1 ⟨0#usize, ()⟩ hlen_bs with ⟨bs1, hbs1, hbsv⟩
  rcases vec_push_val st.2.2.2 st.1.start hlen_os with ⟨os1, hos1, hosv⟩
  refine ⟨(it1, es1, bs1, os1), ?_, ?_, ?_⟩
  · unfold verified.merc_reduction.block_partition.BlockPartition.new_loop.body
    rw [hnext_e]
    simp [hopt, merc_utilities.tagged_index.TagIndex.new_eq, hes1, hbs1, hos1]
  · rcases hinv with ⟨hend_eq, hstart_le, hes, hbs, hos⟩
    constructor
    · rw [hend']; exact hend_eq
    · constructor
      · rw [hstart', ← hend_eq]; omega
      · constructor
        · rw [hesv, hes]
          change (List.range st.1.start.val).map uTag ++ [({ index := st.1.start, marker := () } : TagIndex Sz StateTag)]
            = (List.range it1.start.val).map uTag
          have hlt2 : st.1.start.val < 2 ^ UScalarTy.Usize.numBits := by
            rw [hend_eq] at hlt
            exact lt_trans hlt (sz_val_lt_two_pow num)
          have hstart_eq : ({ index := st.1.start, marker := () } : TagIndex Sz StateTag)
              = uTag st.1.start.val := by
            unfold uTag
            congr 1
            apply sz_eq_from_val
            rw [uTotal_val_of_lt hlt2]
          rw [hstart', ← map_range_concat_tag st.1.start.val, ← hstart_eq]
        · constructor
          · rw [hbsv, hbs]
            have h0 : ({ index := 0#usize, marker := () } : TagIndex Sz BlockTagIdx) = uTag 0 := by
              unfold uTag; rw [uTotal_zero]
            rw [h0]
            change List.replicate st.1.start.val (uTag 0) ++ [uTag 0]
              = List.replicate it1.start.val (uTag 0)
            rw [hstart']
            simp [replicate_append_succ]
          · rw [hosv, hos]
            change (List.range st.1.start.val).map uTotal ++ [st.1.start]
              = (List.range it1.start.val).map uTotal
            have hlt2 : st.1.start.val < 2 ^ UScalarTy.Usize.numBits := by
              rw [hend_eq] at hlt
              exact lt_trans hlt (sz_val_lt_two_pow num)
            have hstart_eq : st.1.start = uTotal st.1.start.val := by
              apply sz_eq_from_val
              rw [uTotal_val_of_lt hlt2]
            rw [hstart', ← map_range_concat st.1.start.val, ← hstart_eq]
  · rcases hinv with ⟨hend_eq, _⟩
    change (it1.end.val - it1.start.val) < (st.1.end.val - st.1.start.val)
    rw [hstart', hend', hend_eq]
    rw [hend_eq] at hlt
    omega

/-- One `new_loop.body` step (`start ≥ end`): exhausted, returns the lists. -/
private theorem new_loop_body_done (num : Sz) (st : NewLoopState)
    (hinv : newLoopInv num st) (hge : st.1.start.val ≥ st.1.end.val) :
    verified.merc_reduction.block_partition.BlockPartition.new_loop.body
      st.1 st.2.1 st.2.2.1 st.2.2.2 = ok (done (st.2.1, st.2.2.1, st.2.2.2)) ∧
    newLoopPost num (st.2.1, st.2.2.1, st.2.2.2) := by
  have hnext := next_range_none st.1 hge
  rcases hnext with ⟨o, it1, hnext_e, hopt, hident⟩
  constructor
  · unfold verified.merc_reduction.block_partition.BlockPartition.new_loop.body
    rw [hnext_e]
    simp [hopt, hident]
  · rcases hinv with ⟨hend_eq, hstart_le, hes, hbs, hos⟩
    have hstart_eq_end : st.1.start.val = num.val := by
      exact le_antisymm hstart_le (by rw [← hend_eq]; exact hge)
    constructor
    · simpa [hstart_eq_end] using hes
    · constructor
      · simpa [hstart_eq_end] using hbs
      · simpa [hstart_eq_end] using hos

/-- `new_loop` over `[0, num)` produces the three enumerating lists. -/
theorem new_loop_spec (num : Sz) :
    ∃ res,
      verified.merc_reduction.block_partition.BlockPartition.new_loop
        { start := 0#usize, «end» := num }
        (alloc.vec.Vec.new (TagIndex Sz StateTag))
        (alloc.vec.Vec.new (TagIndex Sz BlockTagIdx))
        (alloc.vec.Vec.new Sz)
        = ok res ∧ newLoopPost num res := by
  apply Std.WP.spec_imp_exists
  have hInit : newLoopInv num
      ({ start := 0#usize, «end» := num },
        (alloc.vec.Vec.new (TagIndex Sz StateTag)),
        (alloc.vec.Vec.new (TagIndex Sz BlockTagIdx)),
        (alloc.vec.Vec.new Sz)) := by
    dsimp [newLoopInv]
    constructor
    · rfl
    · constructor
      · simp
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl
  apply loop.spec_decr_nat
  · intro x hx
    by_cases h : x.1.start.val < x.1.end.val
    · rcases new_loop_body_step num x hx h with ⟨x', hstep, hinv', hl⟩
      exact Std.WP.exists_imp_spec ⟨cont x', hstep, hinv', hl⟩
    · have hge : x.1.end.val ≤ x.1.start.val := by omega
      rcases new_loop_body_done num x hx hge with ⟨hstep, hpost⟩
      exact Std.WP.exists_imp_spec ⟨done (x.2.1, x.2.2.1, x.2.2.2), hstep, hpost⟩
  · exact hInit

/-- `BlockPartition::new` builds the initial partition over `[0, num)`: one
    block `[0, num)`, `elements`/`element_offset` enumerating the range,
    `element_to_block` constantly the initial block (`0`). -/
theorem block_partition_new_spec (num : Sz) (hpos : 0 < num.val) :
    ∃ p : verified.merc_reduction.block_partition.BlockPartition,
      verified.merc_reduction.block_partition.BlockPartition.new num = ok p ∧
      p.blocks.val = [ { begin := 0#usize, marked_split := 0#usize, «end» := num } ] ∧
      p.elements.val = (List.range num.val).map uTag ∧
      p.element_to_block.val = List.replicate num.val (uTag 0) ∧
      p.element_offset.val = (List.range num.val).map uTotal := by
  rcases new_loop_spec num with ⟨tr, hnew_loop, hpost⟩
  rcases hpost with ⟨hes, hbs, hos⟩
  have hm : 0#usize < num := by simpa using hpos
  let p : verified.merc_reduction.block_partition.BlockPartition :=
    { blocks := alloc.vec.Vec.from
        [ { begin := 0#usize, marked_split := 0#usize, «end» := num } ]
        (by exact le_trans (Nat.succ_le_of_lt hpos) (sz_val_le_max num)),
      elements := tr.1,
      element_to_block := tr.2.1,
      element_offset := tr.2.2 }
  have hnew_eq : verified.merc_reduction.block_partition.BlockPartition.new num = ok p := by
    unfold verified.merc_reduction.block_partition.BlockPartition.new
    rcases tr with ⟨ea, e2b, e2bo⟩
    rcases e2b with ⟨eb, eo⟩
    simp [massert, hm, hnew_loop, p, alloc.vec.Vec.with_capacity,
      verified.merc_reduction.block_partition.Block.new,
      alloc.vec.FromVecArray.from, Aeneas.Std.Array.make]
  refine ⟨p, hnew_eq, ?_, ?_, ?_, ?_⟩
  · simp [p, alloc.vec.Vec.from_val]
  · rw [hes]
  · rw [hbs]
  · rw [hos]

/-!
# `mark_element`: the marking primitive

`BlockPartition::mark_element` (`block_partition.rs:288`) is the only operation
that turns an unmarked state into a marked one, so the worklist loop's
counting argument rests entirely on what it does and does not touch:

- it reads `element_to_block`, `element_offset` and `blocks[block_index]`, and
  the marked region is the *tail* `[marked_split, end)`
  (`is_element_marked` is `offset >= marked_split`, `block_partition.rs:308`);
- if the element is already marked it is a **no-op**;
- otherwise it swaps the element with the last marked one *within the same
  block* and decrements `marked_split` by one. `swap_elements`
  (`block_partition.rs:1168`) only rewrites `elements` and `element_offset`, so
  `element_to_block` and `blocks` are untouched apart from that single
  `marked_split`.

The two consequences used by the termination measure are: `|blocks|` never
changes (only `strong_partition_marked` adds blocks), and `block_number` is
stable under marking.
-/

private abbrev StateIdx := TagIndex Std.Usize verified.merc_lts.lts.StateTag
private abbrev BP := verified.merc_reduction.block_partition.BlockPartition

/-- Auxiliary well-formedness: the three per-state vectors agree in length,
    every state index occurring in `elements` has a slot in `element_offset`,
    and every block satisfies `begin ≤ marked_split ≤ end`,
    the invariant `assert_consistent` checks. -/
private def PartWF (p : BP) : Prop :=
  p.elements.val.length = p.element_to_block.val.length ∧
  p.elements.val.length = p.element_offset.val.length ∧
  (∀ x ∈ p.elements.val, x.index.val < p.element_offset.val.length) ∧
  (∀ (i : Nat) (hi : i < p.blocks.val.length),
    (p.blocks.val[i]'hi).begin.val ≤ (p.blocks.val[i]'hi).marked_split.val ∧
    (p.blocks.val[i]'hi).marked_split.val ≤ (p.blocks.val[i]'hi).«end».val)

/-- `swap_elements` exchanges two entries of `elements`, repairs their
    `element_offset` entries, and leaves `blocks` and `element_to_block`
    completely alone (`block_partition.rs:265`). -/
theorem swap_elements_spec (p : BP) (a b : Std.Usize) (hwf : PartWF p)
    (ha : a.val < p.elements.val.length) (hb : b.val < p.elements.val.length) :
    ∃ p' : BP,
      verified.merc_reduction.block_partition.BlockPartition.swap_elements p a b = ok p' ∧
      PartWF p' ∧
      p'.blocks = p.blocks ∧
      p'.element_to_block = p.element_to_block ∧
      p'.elements.val.length = p.elements.val.length ∧
      p'.element_offset.val.length = p.element_offset.val.length := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  unfold verified.merc_reduction.block_partition.BlockPartition.swap_elements
  have haS : a.val < p.elements.slice.length := ha
  have hbS : b.val < p.elements.slice.length := hb
  obtain ⟨s1, hs1, hl1, hA, hB, hO⟩ :=
    spec_imp_exists (core.slice.Slice.swap_spec p.elements.slice a b haS hbS)
  have hsa : a.val < s1.length := by rw [hl1]; exact haS
  have hsb : b.val < s1.length := by rw [hl1]; exact hbS
  obtain ⟨xa, hxa, hxa'⟩ := spec_imp_exists (Slice.index_usize_spec s1 a hsa)
  obtain ⟨xb, hxb, hxb'⟩ := spec_imp_exists (Slice.index_usize_spec s1 b hsb)
  have hxa_eq : xa = p.elements.val[b.val] := by
    rw [hxa']
    have := hA
    simp only [getElem!_pos, hsa, hbS] at this
    exact this
  have hxb_eq : xb = p.elements.val[a.val] := by
    rw [hxb']
    have := hB
    simp only [getElem!_pos, hsb, haS] at this
    exact this
  have hmem_b : p.elements.val[b.val] ∈ p.elements.val := List.getElem_mem hb
  have hmem_a : p.elements.val[a.val] ∈ p.elements.val := List.getElem_mem ha
  have hbnd_a : (p.elements.val[b.val]).index.val < p.element_offset.slice.length :=
    h3 _ hmem_b
  have hbnd_b : (p.elements.val[a.val]).index.val < p.element_offset.slice.length :=
    h3 _ hmem_a
  obtain ⟨⟨_, back1⟩, hm1, _, hb1⟩ := spec_imp_exists
    (Slice.index_mut_usize_spec p.element_offset.slice (p.elements.val[b.val]).index hbnd_a)
  have hbnd2 : (p.elements.val[a.val]).index.val <
      (p.element_offset.slice.set (p.elements.val[b.val]).index a).length := by
    rw [Slice.set_length]; exact hbnd_b
  obtain ⟨⟨_, back2⟩, hm2, _, hb2⟩ := spec_imp_exists
    (Slice.index_mut_usize_spec (p.element_offset.slice.set (p.elements.val[b.val]).index a)
      (p.elements.val[a.val]).index hbnd2)
  refine ⟨{ elements := ⟨s1⟩, blocks := p.blocks, element_to_block := p.element_to_block,
            element_offset := ⟨back2 b⟩ }, ?_, ?_⟩
  · simp [alloc.vec.Vec.deref_mut, lift, hs1, alloc.vec.Vec.index, core.slice.index.Usize.index,
      hxa, hxb, hxa_eq, hxb_eq, vec_tagged_index_mut_eq, hm1, hm2, hb1]
  · have hlen : (back2 b).length = p.element_offset.slice.length := by
      rw [hb2]; simp
    refine ⟨⟨?_, ?_, ?_, h4⟩, rfl, rfl, ?_, ?_⟩
    · show s1.length = _; rw [hl1]; exact h1
    · show s1.length = (back2 b).length; rw [hl1, hlen]; exact h2
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      change (s1.val[i]).index.val < (back2 b).length
      rw [hlen]
      have hi' : i < p.elements.val.length := by
        have : i < s1.length := hi
        rw [hl1] at this; exact this
      by_cases hia : i = a.val
      · subst hia
        have e : s1.val[a.val] = p.elements.val[b.val] := by
          have := hA; simp only [getElem!_pos, hsa, hbS] at this; exact this
        rw [e]; exact hbnd_a
      · by_cases hib : i = b.val
        · subst hib
          have e : s1.val[b.val] = p.elements.val[a.val] := by
            have := hB; simp only [getElem!_pos, hsb, haS] at this; exact this
          rw [e]; exact hbnd_b
        · have e : s1.val[i] = p.elements.val[i] := by
            have hi2 : i < s1.val.length := hi
            have hi3 : i < p.elements.slice.val.length := hi'
            have := hO i hia hib
            simp only [getElem!_pos, hi2, hi3] at this; exact this
          rw [e]; exact h3 _ (List.getElem_mem hi')
    · show s1.length = _; rw [hl1]; rfl
    · show (back2 b).length = _; rw [hlen]; rfl

end MercVerified.Signatures.Proofs