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
its operations are generated definitions. The lemmas that unfold those
definitions are *theorems* (no trust boundary), so they now live with the rest
of the machine-generated proofs, in
`MercVerified/Signatures/Proofs/Partition_Proofs.lean` (see `TagIndex.ext`,
`vec_tagged_index_eq`, `vec_tagged_index_mut_eq`, `vec_tagged_index_val`,
`blocks_index_mut_contract`, ...).
-/

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
