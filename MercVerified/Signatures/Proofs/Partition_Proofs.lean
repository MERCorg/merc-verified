import MercVerified.Signatures.Refinement
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
open merc_utilities.tagged_index (TagIndex)
open verified.merc_collections.indexed_partition (BlockTag)

namespace MercVerified.Signatures.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private abbrev BlockIndex := TagIndex Std.Usize BlockTag

/-- `TagIndex::value` is a no-op under the model. -/
theorem tag_value_id {T : Type} {Tag : Type} (CopyInst : core.marker.Copy T)
    (t : merc_utilities.tagged_index.TagIndex T Tag) :
    merc_utilities.tagged_index.TagIndex.value CopyInst t = ok t := by
  rfl

/-- Bit vectors indexing by a tagged `usize` is list indexing by the payload. -/
theorem vec_tagged_index_val {U : Type} {Tag : Type}
    (v : alloc.vec.Vec U) (t : merc_utilities.tagged_index.TagIndex Std.Usize Tag)
    (h : t.val < v.length) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t = ok (v.slice.val[t.val]) := by
  simp only [alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index,
    core.slice.index.Usize.index, Slice.index_usize]
  have hget : v.slice.val[t.val]? = some (v.slice.val[t.val]) :=
    List.getElem?_eq_getElem h
  simp [hget]

/-- `BlockPartition::block` accesses `blocks` by the tag's payload. -/
theorem block_partition_block_val
    (p : verified.merc_reduction.block_partition.BlockPartition)
    (b : BlockIndex) (h : b.val < p.blocks.val.length) :
    verified.merc_reduction.block_partition.BlockPartition.block p b =
      ok (p.blocks.slice.val[b.val]) := by
  simp only [
    verified.merc_reduction.block_partition.BlockPartition.block,
    vec_tagged_index_val p.blocks b h,
  ]

/-!
## `BlockPartition::new_loop` semantics

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

lemma map_range_concat (s : Nat) :
    (List.range s).map uTotal ++ [uTotal s] = (List.range (s + 1)).map uTotal := by
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
    st.2.1.val = (List.range st.1.start.val).map uTotal ∧
    st.2.2.1.val = List.replicate st.1.start.val (uTotal 0) ∧
    st.2.2.2.val = (List.range st.1.start.val).map uTotal

/-- Postcondition: all three lists fully enumerate `[0, num)`. -/
private def newLoopPost (num : Sz) : (alloc.vec.Vec (TagIndex Sz StateTag)
      × alloc.vec.Vec (TagIndex Sz BlockTagIdx) × alloc.vec.Vec Sz) → Prop :=
  fun r =>
    r.1.val = (List.range num.val).map uTotal ∧
    r.2.1.val = List.replicate num.val (uTotal 0) ∧
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
      st.2.1.val.length = (List.map uTotal (List.range st.1.start.val)).length := by
        exact congrArg List.length hlen1
      _ = st.1.start.val := by rw [List.length_map, List.length_range]
      _ < Usize.max := hbound
  have hlen_bs : st.2.2.1.val.length < Usize.max := by
    rcases hinv with ⟨_, _, _, hlen2, _⟩
    calc
      st.2.2.1.val.length = (List.replicate st.1.start.val (uTotal 0)).length := by
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
  rcases vec_push_val st.2.1 st.1.start hlen_es with ⟨es1, hes1, hesv⟩
  rcases vec_push_val st.2.2.1 (0#usize) hlen_bs with ⟨bs1, hbs1, hbsv⟩
  rcases vec_push_val st.2.2.2 st.1.start hlen_os with ⟨os1, hos1, hosv⟩
  refine ⟨(it1, es1, bs1, os1), ?_, ?_, ?_⟩
  · unfold verified.merc_reduction.block_partition.BlockPartition.new_loop.body
    rw [hnext_e]
    simp [hopt, merc_utilities.tagged_index.TagIndex.new, hes1, hbs1, hos1]
  · rcases hinv with ⟨hend_eq, hstart_le, hes, hbs, hos⟩
    constructor
    · rw [hend']; exact hend_eq
    · constructor
      · rw [hstart', ← hend_eq]; omega
      · constructor
        · rw [hesv, hes]
          change (List.range st.1.start.val).map uTotal ++ [st.1.start]
            = (List.range it1.start.val).map uTotal
          have hlt2 : st.1.start.val < 2 ^ UScalarTy.Usize.numBits := by
            rw [hend_eq] at hlt
            exact lt_trans hlt (sz_val_lt_two_pow num)
          have hstart_eq : st.1.start = uTotal st.1.start.val := by
            apply sz_eq_from_val
            rw [uTotal_val_of_lt hlt2]
          rw [hstart', ← map_range_concat st.1.start.val, ← hstart_eq]
        · constructor
          · rw [hbsv, hbs, ← uTotal_zero]
            change List.replicate st.1.start.val (uTotal 0) ++ [uTotal 0]
              = List.replicate it1.start.val (uTotal 0)
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
      p.elements.val = (List.range num.val).map uTotal ∧
      p.element_to_block.val = List.replicate num.val (uTotal 0) ∧
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
  · simp [p, alloc.vec.Vec.from_val, Slice.from_val]
  · rw [hes]
  · rw [hbs]
  · rw [hos]

end MercVerified.Signatures.Proofs