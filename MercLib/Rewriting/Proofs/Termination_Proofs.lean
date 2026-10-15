module

public import MercLib.Rewriting.Termination
public import MercLib.Rewriting.Proofs.Signature_Proofs

@[expose] public section

/-!
# Proofs: Termination

`terminating_of_measure` (a measure that decreases with every step) and
`terminating_of_interpretation` (the monotone-algebra criterion), with the mutual lemmas
`lt_stepWith` / `lt_argsStepWith` showing that a step decreases the interpretation.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are stated in
`Challenges/Rewriting.lean` (human-vetted); the definitions of
`MonotoneAlgebra` and `Decreasing` live in `MercLib/Rewriting/Termination.lean`.
-/

namespace MercLib.Rewriting

variable {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι}

/-- A rewrite system is terminating if some measure into a well-founded order decreases with every
step. -/
theorem terminating_of_measure {γ : Type _} (lt : γ → γ → Prop) (hwf : WellFounded lt)
    (μ : ∀ s, Term S W s → γ)
    (hdec : ∀ {s : S.Srt} {a b : Term S W s}, Step R s a b → lt (μ s b) (μ s a)) :
    Terminating R W :=
  fun s => Subrelation.wf (fun {_ _} h => hdec h) (InvImage.wf (μ s) hwf)

variable {M : MonotoneAlgebra S}

mutual

/-- A step strictly decreases the interpretation. -/
theorem lt_stepWith (hD : Decreasing R M) (ν : Valuation M.alg W)
    {C : ∀ s, Term S W s → Term S W s → Prop} :
    ∀ {s : S.Srt} {a b : Term S W s}, StepWith R C s a b →
      M.lt s (Term.eval M.alg ν b) (Term.eval M.alg ν a)
  | _, _, _, .rule i σ _ => by
    rw [Term.eval_subst, Term.eval_subst]; exact hD i _
  | _, _, _, .op f h => by
    rw [Term.eval_op, Term.eval_op]
    exact M.mono f (lt_argsStepWith hD ν h)

/-- A step inside an argument list decreases exactly one position of the value list. -/
theorem lt_argsStepWith (hD : Decreasing R M) (ν : Valuation M.alg W)
    {C : ∀ s, Term S W s → Term S W s → Prop} :
    ∀ {ss : List S.Srt} {as bs : Args S W ss}, ArgsStepWith R C ss as bs →
      ValsLt M.alg.carrier M.lt (Args.eval M.alg ν as) (Args.eval M.alg ν bs)
  | _, _, _, .head h => Or.inl ⟨lt_stepWith hD ν h, rfl⟩
  | _, _, _, .tail h => Or.inr ⟨rfl, lt_argsStepWith hD ν h⟩

end

/-- **Monotone algebra criterion.** A rewrite system all of whose rules decrease in a monotone
algebra is terminating. -/
theorem terminating_of_interpretation (hD : Decreasing R M) (ν : Valuation M.alg W) :
    Terminating R W := by
  refine fun s => Subrelation.wf (r := InvImage (M.lt s) (Term.eval M.alg ν)) ?_
    (InvImage.wf _ (M.wf s))
  rintro a b ⟨n, hn⟩
  cases n with
  | zero => exact absurd hn (by simp [stepAt])
  | succ n => exact lt_stepWith hD ν hn

end MercLib.Rewriting
