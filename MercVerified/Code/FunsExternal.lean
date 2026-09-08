import MercVerified.Code.FunsExternal_Template

open Aeneas Aeneas.Std Result

/--
I don't quite understand why this is necessary, but it seems that Aeneas derives
a (infinite) recursive definitions for the impl<T: Eq> Eq for TaggedIndex<T> {} case.
-/
@[trait_default]
def core.cmp.Eq.assert_fields_are_eq.default
  {Self : Type} (_ : core.cmp.Eq Self) (_ : Self) : Result Unit :=
  .ok ()

def
  merc_utilities.tagged_index.TagIndex.Insts.CoreCmpEq.assert_fields_are_eq
  {T : Type} (Tag : Type) (_corecmpEqInst : core.cmp.Eq T)
  (_self : merc_utilities.tagged_index.TagIndex T Tag) :
  Result Unit
  := do
  ok ()

/-- `[T]::sort_unstable` never fails, and its result is a permutation of its
    input - the only property of sorting that `MercVerified/Signatures/`
    needs (it deliberately does not characterize sortedness itself). -/
axiom core.slice.Slice.sort_unstable_spec
  {T : Type} (cmpOrdInst : core.cmp.Ord T) (s : Slice T) :
  ∃ s', core.slice.Slice.sort_unstable cmpOrdInst s = ok s' ∧ List.Perm s'.val s.val

/-- `Vec::dedup` never fails, and only removes *consecutive* duplicates, so
    (regardless of whether the input happens to be sorted) it never changes
    which elements are present - only how many times each one repeats. -/
axiom alloc.vec.Vec.dedup_spec
  {T : Type} (A : Type) (corecmpPartialEqInst : core.cmp.PartialEq T T)
  (v : alloc.vec.Vec T) :
  ∃ v', alloc.vec.Vec.dedup A corecmpPartialEqInst v = ok v' ∧
    ∀ x, x ∈ v'.val ↔ x ∈ v.val
