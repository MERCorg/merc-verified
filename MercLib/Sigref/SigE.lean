module

public import MercLib.Sigref.SigData
public import MercLib.Sigref.RelBisim

@[expose] public section

/-!
# `Sig`-equality is `E π`

For a coherent fixed point `d : SigData lts π` of the paper's inductive signature, two
`π`-related states have equal signatures iff they are `E π`-related. This connects the abstract
algorithm (which splits by `E π`) to an implementation that splits by (hashed) signature equality.
-/

namespace MercLib.Sigref

open MercLib.LTS MercLib.Signatures

open Cslib

variable {State Label : Type} [HasTau Label]

end MercLib.Sigref
