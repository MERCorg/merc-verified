import Sigref.SigData
import Sigref.RelBisim

/-!
# `Sig`-equality is `E π`

For a coherent fixed point `d : SigData lts π` of the paper's inductive signature, two
`π`-related states have equal signatures iff they are `E π`-related. This connects the abstract
algorithm (which splits by `E π`) to an implementation that splits by (hashed) signature equality.
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label]

/-- **Signature equality is `E π`**: for `π`-related states of a finite τ-loop-free LTS, the
inductive signatures of a coherent fixed point are equal exactly when the states are related by
branching bisimilarity relative to `π`. -/
def SigEqualIffRelBisim [Finite State] (lts : LTS State Label) (π : Setoid State)
    (d : SigData lts π) : Prop :=
  TauLoopFree lts → ∀ s t : State, π.r s t → (d.sigFn s = d.sigFn t ↔ E lts π s t)

end Sigref
