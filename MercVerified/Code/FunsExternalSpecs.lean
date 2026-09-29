import MercVerified.Code.Funs

/-!
Hand-written boundary specs for the opaque externals of `MercVerified/Code/FunsExternal.lean`
that must mention *generated* definitions (e.g. `core.borrow.Borrow.Blanket` from `Funs.lean`),
and so cannot live in `FunsExternal.lean` itself, which `Funs.lean` imports. Being named
`*External*.lean`, this file is covered by the boundary-axiom approval in
`scripts/check_axioms.py`.
-/

open Aeneas Aeneas.Std Result

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
