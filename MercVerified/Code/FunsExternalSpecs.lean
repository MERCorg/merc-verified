import MercVerified.Code.Funs

/-!
Hand-written boundary specs for the opaque externals of `MercVerified/Code/FunsExternal.lean`
that must mention *generated* definitions (e.g. `core.borrow.Borrow.Blanket` from `Funs.lean`),
and so cannot live in `FunsExternal.lean` itself, which `Funs.lean` imports. Being named
`*External*.lean`, this file is covered by the boundary-axiom approval in
`scripts/check_axioms.py`.
-/

open Aeneas Aeneas.Std Result
open verified

/-!
# Externals that moved out of `FunsExternal_Template.lean`

`IncomingTransitions::new` and `TagIndex::new` are no longer Aeneas externals:
the new `lang_items` resolution of commit `7cee08f` translates them into real
`def`s in `MercVerified/Code/Funs.lean`. Their specs therefore have to be stated
here rather than in `FunsExternal.lean`, which `Funs.lean` imports.
-/

/-- `IncomingTransitions::new` never fails (it just indexes the transitions of
    the LTS). -/
axiom merc_lts.incoming_transitions.IncomingTransitions.new_spec
  {L : Type} {Clause0_Label : Type} (ltsLTSInst : verified.merc_lts.lts.LTS L Clause0_Label) :
  (lts : L) → ∃ incoming,
    merc_lts.incoming_transitions.IncomingTransitions.new ltsLTSInst lts = ok incoming

/-- `TagIndex::new` never fails (it is a total constructor in the translated
    code, and returns exactly its argument under the `TagIndex` structure
    model). -/
theorem merc_utilities.tagged_index.TagIndex.new_spec
  {T : Type} (Tag : Type) :
  (i : T) → ∃ t, merc_utilities.tagged_index.TagIndex.new Tag i = ok t := by
  intro i
  exact ⟨{ index := i, marker := () }, rfl⟩

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
# `HashMap` boundary semantics

The `std::collections::hash::map::HashMap` type and its operations are opaque
externals (axioms in `MercVerified/Code/FunsExternal_Template.lean`). To prove
value-level specs of the strong interning pipeline (`strong_intern_signature`
uses `get_key_value`/`insert` on the signature→block-index map) the two
*observable* semantics below are added at the boundary, exactly mirroring how
`std::collections::hash::map::HashMap` is used there: keys looked up through the
blanket `Borrow` (`verified.core.borrow.Borrow.Blanket`) and the passed-through
`Eq`/`Hash` instances.
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
