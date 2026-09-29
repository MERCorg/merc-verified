import MercVerified.Code.Funs

/-!
Hand-written boundary specs for the opaque externals of `MercVerified/Code/FunsExternal.lean`
that must mention *generated* definitions.

This file is part of the axiom-policy-approved set (see `scripts/check_axioms.py`),
so every `axiom` here is a deliberate trust boundary.  Each docstring cites the
Rust body it is read off, by file and line number.
-/

open Aeneas Aeneas.Std Result
open verified

/-- `IncomingTransitions::new` never fails (it just indexes the transitions of
    the LTS). -/
axiom merc_lts.incoming_transitions.IncomingTransitions.new_spec
  {L : Type} {Clause0_Label : Type} (ltsLTSInst : verified.merc_lts.lts.LTS L Clause0_Label) :
  (lts : L) → ∃ incoming,
    merc_lts.incoming_transitions.IncomingTransitions.new ltsLTSInst lts = ok incoming

/-- `Block::assert_consistent` is the integrity check that every `Block` field
    access runs first. It is an Aeneas external (an axiom in
    `MercVerified/Code/FunsExternal_Template.lean`), so its *success* is asserted
    here at the boundary: it only validates `begin ≤ marked_split ≤ end` and so
    never fails. `MercVerified/Signatures/Proofs/Partition_Proofs.lean` uses this
    to reduce `Block::len` and `Block::has_marked` to plain arithmetic and
    `decide` on their fields. -/
axiom merc_reduction.block_partition.Block.assert_consistent_ok
  (b : merc_reduction.block_partition.Block) :
  ∃ u : Unit, merc_reduction.block_partition.Block.assert_consistent b = ok u

/-!
# `TagIndex` semantics

`merc_utilities::tagged_index` is in Charon's `include` list, so `TagIndex T Tag`
is the translated structure `{ index : T, marker : PhantomData Tag }` and all of
its operations are generated definitions.  The lemmas below are *theorems*
(no trust boundary) that unfold those definitions, so proofs can rewrite with
them instead of unfolding by hand.
-/

/-- `TagIndex` is determined by its payload (the phantom marker is `Unit`). -/
theorem merc_utilities.tagged_index.TagIndex.ext {T Tag : Type}
    {a b : merc_utilities.tagged_index.TagIndex T Tag} (h : a.index = b.index) : a = b := by
  cases a; cases b; simp_all

instance {T Tag : Type} [DecidableEq T] :
    DecidableEq (merc_utilities.tagged_index.TagIndex T Tag) := fun a b =>
  if h : a.index = b.index then isTrue (merc_utilities.tagged_index.TagIndex.ext h)
  else isFalse (fun e => h (congrArg (·.index) e))

instance {T Tag : Type} [Inhabited T] :
    Inhabited (merc_utilities.tagged_index.TagIndex T Tag) := ⟨⟨default, ()⟩⟩

/-- `TagIndex::new` never fails. -/
theorem merc_utilities.tagged_index.TagIndex.new_spec
    {T : Type} (Tag : Type) (i : T) :
    ∃ t, merc_utilities.tagged_index.TagIndex.new Tag i = ok t :=
  ⟨_, rfl⟩

/-- `TagIndex::new` wraps its argument. -/
@[simp] theorem merc_utilities.tagged_index.TagIndex.new_eq {T : Type} (Tag : Type)
    (i : T) :
    merc_utilities.tagged_index.TagIndex.new Tag i = ok { index := i, marker := () } :=
  rfl

/-- `TagIndex::value` projects the payload. -/
@[simp] theorem tag_value_id {T : Type} {Tag : Type} (CopyInst : core.marker.Copy T)
    (t : merc_utilities.tagged_index.TagIndex T Tag) :
    merc_utilities.tagged_index.TagIndex.value CopyInst t = ok t.index :=
  rfl

/-- `TagIndex`'s `PartialEq` is the payload's `PartialEq`. -/
@[simp] theorem tag_partial_eq_inst {T : Type} {Tag : Type}
    (peqInst : core.cmp.PartialEq T T)
    (a b : merc_utilities.tagged_index.TagIndex T Tag) :
    merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq
      peqInst a b = peqInst.eq a.index b.index :=
  rfl

/-- Indexing a `Vec` by a tagged `usize` is `Slice` indexing by the payload. -/
theorem vec_tagged_index_eq {U : Type} {Tag : Type}
    (v : alloc.vec.Vec U) (t : merc_utilities.tagged_index.TagIndex Std.Usize Tag) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t
      = v.slice.index_usize t.index := by
  simp [alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index, alloc.vec.Vec.index,
    core.slice.index.Usize.index]

/-- Likewise for `IndexMut`. -/
theorem vec_tagged_index_mut_eq {U : Type} {Tag : Type}
    (v : alloc.vec.Vec U) (t : merc_utilities.tagged_index.TagIndex Std.Usize Tag) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t
      = (do
        let p ← v.slice.index_mut_usize t.index
        ok (p.1, fun u => ({ slice := p.2 u } : alloc.vec.Vec U))) := by
  simp [alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut, alloc.vec.Vec.index_mut,
    core.slice.index.Usize.index_mut]
  rfl

theorem vec_tagged_index_val {U : Type} {Tag : Type}
    (v : alloc.vec.Vec U) (t : merc_utilities.tagged_index.TagIndex Std.Usize Tag)
    (h : t.index.val < v.length) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t = ok (v.slice.val[t.index.val]) := by
  rw [vec_tagged_index_eq]
  have := Slice.index_usize_spec v.slice t.index (by simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h)
  obtain ⟨x, hx, hxe⟩ := Std.WP.spec_imp_exists this
  rw [hx, hxe]
  rfl

theorem blocks_index_mut_contract
    (p : verified.merc_reduction.block_partition.BlockPartition)
    (block_index : merc_utilities.tagged_index.TagIndex Std.Usize
      verified.merc_collections.indexed_partition.BlockTag)
    (h : block_index.index.val < p.blocks.slice.val.length) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
        (core.slice.index.SliceIndexUsizeSlice
          verified.merc_reduction.block_partition.Block)
        p.blocks block_index =
      ok (p.blocks.slice.val[block_index.index.val]'h,
          fun u => ({ slice := p.blocks.slice.set block_index.index u } : alloc.vec.Vec
                  verified.merc_reduction.block_partition.Block)) := by
  rw [vec_tagged_index_mut_eq]
  have := Slice.index_mut_usize_spec p.blocks.slice block_index.index
    (by simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h)
  obtain ⟨⟨x, back⟩, hx, hxe, hb⟩ := Std.WP.spec_imp_exists this
  simp only [hx]
  simp only [bind_tc_ok]
  subst hb
  simp [hxe]

/-!
# `HashMap` boundary semantics
-/

/-- `HashMap::insert` never fails, and immediately afterwards a lookup of the
    freshly inserted key (through the same equality/hash instances) returns
    exactly that `(key, value)` pair. -/
axiom std.collections.hash.map.HashMap.insert_spec
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) :
  ∃ old : Option V, ∃ m' : std.collections.hash.map.HashMap K V S A,
    std.collections.hash.map.HashMap.insert corecmpEqInst corehashHashInst
      corehashBuildHasherInst m k v = ok (old, m') ∧
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m' k = ok (some (k, v))

/-- Inserting `k ↦ v` leaves all lookups of keys the map's own equality test
    reports as *different* from `k` untouched. -/
axiom std.collections.hash.map.HashMap.insert_get_key_value_other
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) (q : K)
  (hneq : corecmpEqInst.partialEqInst.eq k q = ok false) :
  ∃ old : Option V, ∃ m' : std.collections.hash.map.HashMap K V S A,
    std.collections.hash.map.HashMap.insert corecmpEqInst corehashHashInst
      corehashBuildHasherInst m k v = ok (old, m') ∧
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m' q =
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m q
