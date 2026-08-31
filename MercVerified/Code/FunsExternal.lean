import MercVerified.Code.FunsExternal_Template

open Aeneas Aeneas.Std Result

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
