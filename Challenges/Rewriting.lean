import MercLib.Rewriting.Confluence
import MercLib.Rewriting.Rewrite
import MercLib.Rewriting.Signature
import MercLib.Rewriting.Soundness
import MercLib.Rewriting.Termination

/-!
# Comparator challenge: conditional term rewriting (human-vetted)

The headline theorems of `MercLib/Rewriting/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`). Intermediate lemmas are not challenged.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Rewriting.Steps

/-! ## Soundness -/

/-- Soundness: in a model of the rewrite system, multi-step rewriting preserves the value of a term
    under every valuation. -/
theorem eval_eq {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι}
    {A : Algebra S} (hM : Model R A) (ν : Valuation A W) {s : S.Srt} {a b : Term S W s}
    (h : Steps R s a b) : Term.eval A ν a = Term.eval A ν b := sorry

end MercLib.Rewriting.Steps

namespace MercLib.Rewriting

/-! ## Termination -/

/-- Termination by a measure: a rewrite system is terminating if some measure into a
    well-founded order decreases with every rewrite step. -/
theorem terminating_of_measure {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {γ : Type*} (lt : γ → γ → Prop) (hwf : WellFounded lt)
    (μ : (s : S.Srt) → Term S W s → γ)
    (hdec : ∀ {s : S.Srt} {a b : Term S W s}, Step R s a b → lt (μ s b) (μ s a)) :
    Terminating R W := sorry

/-- Termination by a monotone algebra: a rewrite system all of whose rules decrease in a
    monotone algebra is terminating. -/
theorem terminating_of_interpretation {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {M : MonotoneAlgebra S} (hD : Decreasing R M) (ν : Valuation M.alg W) :
    Terminating R W := sorry

/-! ## Confluence -/

/-- Ground confluence from a model: a terminating rewrite system with a model in which distinct
    normal forms have distinct values is confluent at every sort. -/
theorem confluent_of_model {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {A : Algebra S} (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) (s : S.Srt) : Relation.Confluent (rel R W s) := sorry

/-- Under the same assumptions every term has a unique normal form; by soundness it is the
    normal form with the term's value in the model, so the rewrite system computes the model. -/
theorem existsUnique_normalForm {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {A : Algebra S} (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) {s : S.Srt} (t : Term S W s) :
    ∃! u, Steps R s t u ∧ Normal R u := sorry

end MercLib.Rewriting
