import MercLib.Theory.Rewriting.Confluence
import MercLib.Theory.Rewriting.Rewrite
import MercLib.Theory.Rewriting.Signature
import MercLib.Theory.Rewriting.Termination

/-!
# Comparator challenge: conditional term rewriting (human-vetted)

The headline theorems of `MercLib/Theory/Rewriting/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`). Intermediate lemmas are not challenged.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

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

/-- **Termination by a monotone interpretation.** If every rule of `R` strictly decreases under
every valuation in a monotone interpretation `M` (`Decreasing`; conditions are ignored), and `W`
has a valuation `ν` in `M`, then `R` is terminating on terms over `W`. -/
theorem terminating_of_interpretation {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {M : MonotoneInterpretation S} (hD : Decreasing R M) (ν : Valuation M W) :
    Terminating R W := sorry

/-! ## Confluence -/

/-- **Newman's lemma.** A rewrite system that is terminating and locally confluent on the terms
over `W` is confluent on those terms. -/
theorem confluent_of_locallyConfluent {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} (ht : Terminating R W) (hl : LocallyConfluent R W) : Confluent R W := sorry

/-- **Unique normal forms.** In a rewrite system that is terminating and confluent on the terms over
`W`, every term `t` has exactly one normal form `u` with `t →* u`. -/
theorem existsUnique_normalForm {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} (ht : Terminating R W) (hc : Confluent R W) {s : S.Srt} (t : Term S W s) :
    ∃! u, Steps R s t u ∧ Normal R u := sorry

end MercLib.Rewriting
