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

/-- **Soundness of rewriting.** If `A` is a model of the conditional rewrite system `R` (`Model`:
every rule holds in `A` whenever its conditions do) and `a →* b`, then `a` and `b` have the same
value in `A` under every valuation `ν`. -/
theorem eval_eq {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι}
    {A : Algebra S} (hM : Model R A) (ν : Valuation A W) {s : S.Srt} {a b : Term S W s}
    (h : Steps R s a b) : Term.eval A ν a = Term.eval A ν b := sorry

end MercLib.Rewriting.Steps

namespace MercLib.Rewriting

/-! ## Termination -/

/-- **Termination by a measure.** If a measure `μ` on terms into a well-founded order `lt`
strictly decreases with every rewrite step of `R`, then `R` is terminating on terms over the
variables `W`. -/
theorem terminating_of_measure {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {γ : Type*} (lt : γ → γ → Prop) (hwf : WellFounded lt)
    (μ : (s : S.Srt) → Term S W s → γ)
    (hdec : ∀ {s : S.Srt} {a b : Term S W s}, Step R s a b → lt (μ s b) (μ s a)) :
    Terminating R W := sorry

/-- **Termination by a monotone algebra.** If every rule of `R` strictly decreases under every
valuation in a monotone algebra `M` (`Decreasing`; conditions are ignored), and `W` has a
valuation `ν` in `M`, then `R` is terminating on terms over `W`. -/
theorem terminating_of_interpretation {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {M : MonotoneAlgebra S} (hD : Decreasing R M) (ν : Valuation M.alg W) :
    Terminating R W := sorry

/-! ## Confluence -/

/-- **Ground confluence from a model.** Let `R` be a terminating rewrite system with a model `A`
and a valuation `ν` under which distinct normal forms of the same sort have distinct values
(`NormalFormsInjective`: sufficient completeness and no confusion). Then rewriting at every sort
`s` is confluent. -/
theorem confluent_of_model {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {A : Algebra S} (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) (s : S.Srt) : Relation.Confluent (rel R W s) := sorry

/-- **Unique normal forms from a model.** Under the assumptions of `confluent_of_model`, every
term `t` has exactly one normal form `u` with `t →* u`. By soundness it is the normal form with
`t`'s value, so `R` computes the model. -/
theorem existsUnique_normalForm {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {A : Algebra S} (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) {s : S.Srt} (t : Term S W s) :
    ∃! u, Steps R s t u ∧ Normal R u := sorry

end MercLib.Rewriting
