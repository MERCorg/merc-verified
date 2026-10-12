import Rewriting.Termination
import Rewriting.Proofs.Termination_Proofs

open Rewriting

-- Contract pin: fails to compile if `terminating_of_measure`'s signature drifts (a measure into a
-- well-founded order that decreases with every step proves termination).
example {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι} {γ : Type _}
    (lt : γ → γ → Prop) (hwf : WellFounded lt) (μ : ∀ s, Term S W s → γ)
    (hdec : ∀ {s : S.Srt} {a b : Term S W s}, Step R s a b → lt (μ s b) (μ s a)) :
    Terminating R W :=
  terminating_of_measure lt hwf μ hdec

-- Contract pin: fails to compile if `terminating_of_interpretation`'s signature drifts (the
-- monotone-algebra criterion).
example {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι} {M : MonotoneAlgebra S}
    (hD : Decreasing R M) (ν : Valuation M.alg W) : Terminating R W :=
  terminating_of_interpretation hD ν
