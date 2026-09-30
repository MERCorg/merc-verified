import MercVerified.Lts.Lts
import MercVerified.Code.FunsExternalSpecs
import Aeneas.Std.WP

/-!
# Foundation lemmas for the `merc_lts` proofs

`toLTS`/`tr` unfolding, the `TagIndex` and `Vec`-by-`TagIndex` semantics, `usize` construction
helpers and `Range`/`Vec::push` step lemmas. These are used by the `merc_lts` proofs
(`IncomingTransitions_Proofs`, `LabelledTransitionSystem_Proofs`) and by the `merc_refinement`
proofs, which import this file, mirroring the crate dependency direction.

Machine-generated proofs; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag LTS)

namespace MercVerified.Lts

/-- `(toLTS LTSInst sys).Tr` unfolds to `tr LTSInst sys` - a real theorem (`Iff.rfl`), moved here
    (from `MercVerified/Lts/Lts.lean`) since it is a proof, not part of the trust boundary. -/
@[simp] theorem toLTS_Tr {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L)
    (s : TagIndex Std.Usize StateTag)
    (μ : TagIndex Std.Usize LabelTag)
    (s' : TagIndex Std.Usize StateTag) :
    (toLTS LTSInst sys).Tr s μ s' ↔ tr LTSInst sys s μ s' := Iff.rfl

end MercVerified.Lts

namespace MercVerified.Lts.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private abbrev Sz := Std.Usize

/-!
## `TagIndex` semantics

`merc_utilities::tagged_index` is in Charon's `include` list, so `TagIndex T Tag`
is the translated structure `{ index : T, marker : PhantomData Tag }` and all of
its operations are generated definitions. The lemmas below are *theorems*
(no trust boundary) that unfold those definitions, so proofs can rewrite with
them instead of unfolding by hand. Moved here (from
`MercVerified/Code/FunsExternalSpecs.lean`) since they are genuine proofs, not
hand-vetted trust-boundary axioms.
-/

/-- `TagIndex` is determined by its payload (the phantom marker is `Unit`). -/
theorem merc_utilities.tagged_index.TagIndex.ext {T Tag : Type}
    {a b : TagIndex T Tag} (h : a.index = b.index) : a = b := by
  cases a; cases b; simp_all

instance {T Tag : Type} [DecidableEq T] :
    DecidableEq (TagIndex T Tag) := fun a b =>
  if h : a.index = b.index then isTrue (merc_utilities.tagged_index.TagIndex.ext h)
  else isFalse (fun e => h (congrArg (·.index) e))

instance {T Tag : Type} [Inhabited T] :
    Inhabited (TagIndex T Tag) := ⟨⟨default, ()⟩⟩

/-- `TagIndex::new` never fails. -/
theorem merc_utilities.tagged_index.TagIndex.new_spec
    {T : Type} (Tag : Type) (i : T) :
    ∃ t, verified.merc_utilities.tagged_index.TagIndex.new Tag i = ok t :=
  ⟨_, rfl⟩

/-- `TagIndex::new` wraps its argument. -/
@[simp] theorem merc_utilities.tagged_index.TagIndex.new_eq {T : Type} (Tag : Type)
    (i : T) :
    verified.merc_utilities.tagged_index.TagIndex.new Tag i = ok { index := i, marker := () } :=
  rfl

/-- `TagIndex::value` projects the payload. -/
@[simp] theorem tag_value_id {T : Type} {Tag : Type} (CopyInst : core.marker.Copy T)
    (t : TagIndex T Tag) :
    verified.merc_utilities.tagged_index.TagIndex.value CopyInst t = ok t.index :=
  rfl

/-- `TagIndex`'s `PartialEq` is the payload's `PartialEq`. -/
@[simp] theorem tag_partial_eq_inst {T : Type} {Tag : Type}
    (peqInst : core.cmp.PartialEq T T)
    (a b : TagIndex T Tag) :
    verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq
      peqInst a b = peqInst.eq a.index b.index :=
  rfl

/-- Indexing a `Vec` by a tagged `usize` is `Slice` indexing by the payload. -/
theorem vec_tagged_index_eq {U : Type} {Tag : Type}
    (v : alloc.vec.Vec U) (t : TagIndex Std.Usize Tag) :
    verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t
      = v.slice.index_usize t.index := by
  simp [verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index, alloc.vec.Vec.index,
    core.slice.index.Usize.index]

/-- Likewise for `IndexMut`. -/
theorem vec_tagged_index_mut_eq {U : Type} {Tag : Type}
    (v : alloc.vec.Vec U) (t : TagIndex Std.Usize Tag) :
    verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t
      = (do
        let p ← v.slice.index_mut_usize t.index
        ok (p.1, fun u => ({ slice := p.2 u } : alloc.vec.Vec U))) := by
  simp [verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut, alloc.vec.Vec.index_mut,
    core.slice.index.Usize.index_mut]
  rfl

theorem vec_tagged_index_val {U : Type} {Tag : Type}
    (v : alloc.vec.Vec U) (t : TagIndex Std.Usize Tag)
    (h : t.index.val < v.length) :
    verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t = ok (v.slice.val[t.index.val]) := by
  rw [vec_tagged_index_eq]
  have := Slice.index_usize_spec v.slice t.index (by simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h)
  obtain ⟨x, hx, hxe⟩ := Std.WP.spec_imp_exists this
  rw [hx, hxe]
  rfl

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

lemma vec_push_val {U : Type} (v : alloc.vec.Vec U) (x : U)
    (hb : v.val.length < Usize.max) :
    ∃ v', v.push x = ok v' ∧ v'.val = v.val ++ [x] :=
  Std.WP.spec_imp_exists (alloc.vec.Vec.push_spec v x hb)

end MercVerified.Lts.Proofs
