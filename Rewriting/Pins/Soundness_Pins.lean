import Rewriting.Soundness
import Rewriting.Proofs.Soundness_Proofs

open Rewriting

-- Contract pin: fails to compile if `Steps.eval_eq`'s signature drifts (rewriting preserves the
-- value of a term in any model of the rewrite system).
example {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι} {A : Algebra S}
    (hM : Model R A) (ν : Valuation A W) {s : S.Srt} {a b : Term S W s}
    (h : Steps R s a b) : Term.eval A ν a = Term.eval A ν b :=
  Steps.eval_eq hM ν h
