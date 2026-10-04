import Sigref.Proofs.SigData_Proofs
import Sigref.Proofs.SigE_Proofs

open Cslib Sigref

-- Contract pin: fails to compile if `sigDataExists`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] [Finite State] (lts : LTS State Label)
    (π : Setoid State), TauLoopFree lts → Nonempty (SigData lts π) :=
  fun lts π => sigDataExists lts π

-- Contract pin: fails to compile if `sigEqualIffRelBisim`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] [Finite State] {lts : LTS State Label}
    {π : Setoid State} (d : SigData lts π), TauLoopFree lts →
      ∀ s t : State, π.r s t → (d.sigFn s = d.sigFn t ↔ E lts π s t) :=
  fun d => sigEqualIffRelBisim d
