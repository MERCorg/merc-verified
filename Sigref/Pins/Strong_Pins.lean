import Sigref.Proofs.Strong_Proofs

open Cslib Sigref

-- Contract pin: fails to compile if `strongSigrefCorrect`'s signature drifts.
example : ∀ {State Label : Type} (lts : LTS State Label),
    StrongInv lts (initConfig State) ∧
    (∀ c c' : Config State, StrongInv lts c → StrongStep lts c c' → StrongInv lts c') ∧
    (∀ c : Config State, StrongInv lts c → (∀ s, s ∉ c.X) →
      ∀ s t, c.π.r s t ↔ LTS.Bisimilarity lts lts s t) :=
  fun lts => strongSigrefCorrect lts

-- Contract pin: fails to compile if `strongSigrefTerminates`'s signature drifts.
example : ∀ {State Label : Type} [Finite State] (lts : LTS State Label),
    WellFounded (fun c' c : Config State => StrongStep lts c c') :=
  fun lts => strongSigrefTerminates lts
