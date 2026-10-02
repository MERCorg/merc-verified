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

/-- A well-formed block: non-empty, with `marked_split` inside it. These are exactly the three
    `debug_assert!`s of `Block::assert_consistent` (`block_partition.rs`). -/
def merc_reduction.block_partition.Block.WellFormed
    (b : merc_reduction.block_partition.Block) : Prop :=
  b.begin.val < b.«end».val ∧ b.begin.val ≤ b.marked_split.val ∧
    b.marked_split.val ≤ b.«end».val

/-- `Block::assert_consistent` is the integrity check that every `Block` field
    access runs first. It is an Aeneas external (an axiom in
    `MercVerified/Code/FunsExternal_Template.lean`) whose body is three `debug_assert!`s: it
    returns `()` on a well-formed block and panics otherwise, so success is asserted
    only under `Block.WellFormed`. `MercVerified/Refinement/Proofs/Partition_Proofs.lean` uses this
    to reduce `Block::len` and `Block::has_marked` to plain arithmetic and
    `decide` on their fields. -/
axiom merc_reduction.block_partition.Block.assert_consistent_ok
  (b : merc_reduction.block_partition.Block)
  (h : merc_reduction.block_partition.Block.WellFormed b) :
  ∃ u : Unit, merc_reduction.block_partition.Block.assert_consistent b = ok u

namespace MercVerified.Refinement

open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition Block)

/-! ### The partition invariant

`PartInv n p` says that `p : BlockPartition` is a consistent partition of the states `[0, n)`:
`elements` is a permutation of `[0, n)` with `element_offset` its inverse, the blocks are
non-empty, pairwise disjoint ranges of `elements`, and `element_to_block` sends every state to the
block whose range contains its offset. This is what `BlockPartition::assert_consistent`
(`block_partition.rs`) checks, and it is stated here (rather than with the proofs) because the
boundary axiom `BlockPartition.assert_consistent_ok` below is conditional on it. The accessors
use default values so that statements need no bound proofs. -/

/-- A dummy block, the default of `blkAt`. -/
def blk0 : Block := { begin := 0#usize, marked_split := 0#usize, «end» := 0#usize }

/-- `p.blocks[k]` (dummy if out of range). -/
def blkAt (p : BlockPartition) (k : Nat) : Block := p.blocks.val.getD k blk0

/-- `p.elements[i]` (state `0` if out of range). -/
def eAt (p : BlockPartition) (i : Nat) : TagIndex Std.Usize StateTag :=
  p.elements.val.getD i { index := 0#usize, marker := () }

/-- `p.element_offset[s]` (`0` if out of range). -/
def offAt (p : BlockPartition) (s : Nat) : Nat := (p.element_offset.val.getD s 0#usize).val

/-- `p.element_to_block[s]`'s block number (`0` if out of range). -/
def e2bAt (p : BlockPartition) (s : Nat) : Nat :=
  (p.element_to_block.val.getD s { index := 0#usize, marker := () }).index.val

structure PartInv (n : Nat) (p : BlockPartition) : Prop where
  len_e : p.elements.val.length = n
  len_e2b : p.element_to_block.val.length = n
  len_off : p.element_offset.val.length = n
  perm : ∀ i, i < n → (eAt p i).index.val < n ∧ offAt p (eAt p i).index.val = i
  inv : ∀ s, s < n → (eAt p (offAt p s)).index.val = s
  blk : ∀ k, k < p.blocks.val.length →
    (blkAt p k).begin.val < (blkAt p k).«end».val ∧ (blkAt p k).«end».val ≤ n ∧
    (blkAt p k).begin.val ≤ (blkAt p k).marked_split.val ∧
    (blkAt p k).marked_split.val ≤ (blkAt p k).«end».val
  own : ∀ s, s < n → e2bAt p s < p.blocks.val.length ∧
    (blkAt p (e2bAt p s)).begin.val ≤ offAt p s ∧ offAt p s < (blkAt p (e2bAt p s)).«end».val
  disj : ∀ j k, j < p.blocks.val.length → k < p.blocks.val.length → j ≠ k →
    (blkAt p j).«end».val ≤ (blkAt p k).begin.val ∨
    (blkAt p k).«end».val ≤ (blkAt p j).begin.val

end MercVerified.Refinement

/-- `BlockPartition::assert_consistent` (`block_partition.rs`, the `debug_assert!`-based integrity
    check) returns `true` on a consistent partition: it panics only when an invariant is
    broken, and `PartInv` (elements a permutation with inverse `element_offset`, disjoint
    non-empty blocks covering every element, `element_to_block` naming the containing block)
    implies every one of its checks. -/
axiom merc_reduction.block_partition.BlockPartition.assert_consistent_ok
  {n : Nat} (p : merc_reduction.block_partition.BlockPartition)
  (h : MercVerified.Refinement.PartInv n p) :
  merc_reduction.block_partition.BlockPartition.assert_consistent p = ok true

/-- `Vec::extend` over a `BlockIter` appends exactly the elements the iterator yields, in order:
    `BlockIter::next` (`block_partition.rs:556`, a generated definition) yields
    `elements[index], elements[index + 1], …` while `index < end`, so the appended list is the
    window `elements[index, end)`. Success is assumed absent allocation failure: the only failure
    mode of `extend` is the vector's length overflowing `usize`, which the hypotheses exclude. -/
axiom alloc.vec.Vec.extend_blockIter_spec
    (v : alloc.vec.Vec (merc_utilities.tagged_index.TagIndex Std.Usize merc_lts.lts.StateTag))
    (bi : merc_reduction.block_partition.BlockIter)
    (hend : bi.«end».val ≤ bi.elements.val.length)
    (hlen : v.val.length + (bi.«end».val - bi.index.val) ≤ Std.Usize.max) :
    ∃ v' : alloc.vec.Vec (merc_utilities.tagged_index.TagIndex Std.Usize merc_lts.lts.StateTag),
      alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend Global
        (core.iter.traits.collect.IntoIterator.Blanket
          merc_reduction.block_partition.BlockIter.Insts.CoreIterTraitsIteratorIteratorTagIndexUsizeStateTag)
        v bi = ok v' ∧
      v'.val = v.val ++
        ((bi.elements.val.drop bi.index.val).take (bi.«end».val - bi.index.val))

/-!
# `TagIndex` semantics

`merc_utilities::tagged_index` is in Charon's `include` list, so `TagIndex T Tag`
is the translated structure `{ index : T, marker : PhantomData Tag }` and all of
its operations are generated definitions. The lemmas that unfold those
definitions are *theorems* (no trust boundary), so they now live with the rest
of the machine-generated proofs, in
`MercVerified/Lts/Proofs/Foundation_Proofs.lean` (see `TagIndex.ext`,
`vec_tagged_index_eq`, `vec_tagged_index_mut_eq`, `vec_tagged_index_val`,
`blocks_index_mut_contract`, ...).
-/

/-!
# Hash totality of the concrete instances

The `HashMap` axioms below need the `Hash`/`BuildHasher` instances to never fail. For the
instances the project uses this is read off the Rust bodies: each only feeds its components to the
hasher (`write`/`finish`), so it is total exactly when its components and the hasher are.
-/

/-- `usize::hash` is `state.write_usize(*self)`: total for a total hasher. -/
axiom Usize.Insts.CoreHashHash.isTotal : core.hash.Hash.IsTotal Usize.Insts.CoreHashHash

/-- `TagIndex::hash` hashes only the `index` field (`tagged_index.rs:83`). -/
axiom merc_utilities.tagged_index.TagIndex.Insts.CoreHashHash.isTotal
  {T : Type} (Tag : Type) (I : core.hash.Hash T) (h : core.hash.Hash.IsTotal I) :
  core.hash.Hash.IsTotal (merc_utilities.tagged_index.TagIndex.Insts.CoreHashHash Tag I)

/-- Tuple hashing (`core::tuple`) hashes both components in turn. -/
axiom Pair.Insts.CoreHashHash.isTotal {T B : Type} (I : core.hash.Hash T) (J : core.hash.Hash B)
  (hI : core.hash.Hash.IsTotal I) (hJ : core.hash.Hash.IsTotal J) :
  core.hash.Hash.IsTotal (Pair.Insts.CoreHashHash I J)

/-- `Vec::hash` hashes the slice: the length, then every element in turn. -/
axiom alloc.vec.Vec.Insts.CoreHashHash.isTotal {T : Type} (A : Type) (I : core.hash.Hash T)
  (h : core.hash.Hash.IsTotal I) :
  core.hash.Hash.IsTotal (alloc.vec.Vec.Insts.CoreHashHash A I)

/-- `FxBuildHasher::build_hasher` and `FxHasher::{write, finish}` are plain integer arithmetic. -/
axiom rustc_hash.FxBuildHasher.Insts.CoreHashBuildHasherFxHasher.isTotal :
  verified.core.hash.BuildHasher.IsTotal
    rustc_hash.FxBuildHasher.Insts.CoreHashBuildHasherFxHasher

/-!
# `HashMap` boundary semantics
-/

/-- `HashMap::insert` never fails (for a lawful `Eq` and total `Hash`/`BuildHasher`: the
    instance methods it calls may otherwise fail), and immediately afterwards a lookup of the
    freshly inserted key (through the same equality/hash instances) returns
    exactly that `(key, value)` pair. (With a lawful `Eq`, equal keys are identical, so the
    stored key that `insert` keeps is `k` itself.) -/
axiom std.collections.hash.map.HashMap.insert_spec
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (hEq : core.cmp.Eq.IsLawful corecmpEqInst) (hHash : core.hash.Hash.IsTotal corehashHashInst)
  (hBH : verified.core.hash.BuildHasher.IsTotal corehashBuildHasherInst)
  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) :
  ∃ old : Option V, ∃ m' : std.collections.hash.map.HashMap K V S A,
    std.collections.hash.map.HashMap.insert corecmpEqInst corehashHashInst
      corehashBuildHasherInst m k v = ok (old, m') ∧
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m' k = ok (some (k, v))

/-- Every value a lookup can return satisfies `P` (lookups through the map's own
    equality/hash instances, the way `strong_intern_signature` queries it). -/
def std.collections.hash.map.HashMap.AllValues
    {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
    (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
    (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
    (m : std.collections.hash.map.HashMap K V S A) (P : V → Prop) : Prop :=
  ∀ (q : K) (k : K) (v : V),
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m q = ok (some (k, v)) → P v

/-- `HashMap::insert` only ever *adds* the inserted value to what lookups can return: every
    property of all stored values that held before still holds after, provided the inserted
    value has it. (A hash map stores exactly the values inserted into it.) -/
axiom std.collections.hash.map.HashMap.insert_allValues
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (hEq : core.cmp.Eq.IsLawful corecmpEqInst) (hHash : core.hash.Hash.IsTotal corehashHashInst)
  (hBH : verified.core.hash.BuildHasher.IsTotal corehashBuildHasherInst)
  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) :
  ∃ old : Option V, ∃ m' : std.collections.hash.map.HashMap K V S A,
    std.collections.hash.map.HashMap.insert corecmpEqInst corehashHashInst
      corehashBuildHasherInst m k v = ok (old, m') ∧
    ∀ P : V → Prop,
      std.collections.hash.map.HashMap.AllValues corecmpEqInst corehashHashInst
        corehashBuildHasherInst m P → P v →
      std.collections.hash.map.HashMap.AllValues corecmpEqInst corehashHashInst
        corehashBuildHasherInst m' P

/-- A lookup on a hash map never fails (`HashMap::get_key_value` only hashes and compares). -/
axiom std.collections.hash.map.HashMap.get_key_value_ok
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (hEq : core.cmp.Eq.IsLawful corecmpEqInst) (hHash : core.hash.Hash.IsTotal corehashHashInst)
  (hBH : verified.core.hash.BuildHasher.IsTotal corehashBuildHasherInst)
  (m : std.collections.hash.map.HashMap K V S A) (q : K) :
  ∃ o : Option (K × V),
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m q = ok o

/-- A lookup that finds an entry returns a stored key that the map's own equality test reports
    equal to the query (`HashMap::get_key_value` only returns entries whose key equals `q`). -/
axiom std.collections.hash.map.HashMap.get_key_value_eq
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (m : std.collections.hash.map.HashMap K V S A) (q k : K) (v : V)
  (h : std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m q = ok (some (k, v))) :
  corecmpEqInst.partialEqInst.eq q k = ok true

/-- `HashMap::default` succeeds and yields an empty map: every lookup finds nothing. -/
axiom std.collections.hash.map.HashMapKVSGlobal.default_spec
  (K : Type) (V : Type) {S : Type} (coredefaultDefaultInst : core.default.Default S) :
  ∃ m : std.collections.hash.map.HashMap K V S Global,
    std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault.default K V
      coredefaultDefaultInst = ok m ∧
    ∀ {Clause2_Hasher : Type} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
      (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
      (_hHash : core.hash.Hash.IsTotal corehashHashInst)
      (_hBH : verified.core.hash.BuildHasher.IsTotal corehashBuildHasherInst) (q : K),
      std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
        corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
        corehashHashInst corecmpEqInst m q = ok none

/-- Inserting `k ↦ v` leaves all lookups of keys the map's own equality test
    reports as *different* from `k` untouched. -/
axiom std.collections.hash.map.HashMap.insert_get_key_value_other
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (hEq : core.cmp.Eq.IsLawful corecmpEqInst) (hHash : core.hash.Hash.IsTotal corehashHashInst)
  (hBH : verified.core.hash.BuildHasher.IsTotal corehashBuildHasherInst)
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
