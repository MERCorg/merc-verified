module

public import MercLib.Theory.Rewriting.Termination
public import MercLib.Theory.Rewriting.Proofs.Signature_Proofs
import all MercLib.Theory.Rewriting.Proofs.Signature_Proofs

@[expose] public section

/-!
# Proofs: Termination

`terminating_of_measure` (a measure that decreases with every step) and
`terminating_of_interpretation` (the monotone-interpretation criterion), with the mutual lemmas
`lt_stepWith` / `lt_argsStepWith` showing that a step decreases the interpretation.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are stated in
`Challenges/Rewriting.lean` (human-vetted); the definitions of
`MonotoneInterpretation` and `Decreasing` live in `MercLib/Theory/Rewriting/Termination.lean`.
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

namespace Term

open Term

@[simp] private theorem eval_var {V : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M V) {s : S.Srt} (x : V s) :
    eval M ν (.var x) = ν s x := rfl

@[simp] private theorem eval_op {V : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M V) {ss : List S.Srt}
    {s : S.Srt} (f : S.Op ss s) (args : Args S V ss) :
    eval M ν (.op f args) = M.interp f (Args.eval M ν args) := rfl

@[simp] private theorem _root_.MercLib.Rewriting.Args.eval_nil {V : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M V) :
    Args.eval M ν (.nil) = PUnit.unit := rfl

@[simp] private theorem _root_.MercLib.Rewriting.Args.eval_cons {V : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M V)
    {s : S.Srt} {ss : List S.Srt} (t : Term S V s) (ts : Args S V ss) :
    Args.eval M ν (.cons t ts) = (Term.eval M ν t, Args.eval M ν ts) := rfl

mutual

/-- Evaluating a substituted term is evaluating the term under the induced valuation.  -/
private theorem eval_subst {V W : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M W) (σ : Subst S V W) :
    ∀ {s : S.Srt} (t : Term S V s), eval M ν (subst σ t) = eval M (substValuation M ν σ) t
  | _, .var _ => rfl
  | _, .op _ args => by rw [subst_op, eval_op, eval_op, Args.eval_subst M ν σ args]

/-- `eval_subst` for argument lists. -/
private theorem _root_.MercLib.Rewriting.Args.eval_subst {V W : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M W)
    (σ : Subst S V W) :
    ∀ {ss : List S.Srt} (as : Args S V ss),
      Args.eval M ν (Args.subst σ as) = Args.eval M (substValuation M ν σ) as
  | _, .nil => rfl
  | _, .cons t ts => by
    rw [Args.subst_cons, Args.eval_cons, Args.eval_cons, Term.eval_subst M ν σ t,
      Args.eval_subst M ν σ ts]

end

end Term

variable {M : MonotoneInterpretation S}

mutual

/-- A step strictly decreases the interpretation. -/
private theorem lt_stepWith (hD : Decreasing R M) (ν : Valuation M W)
    {C : ∀ s, Term S W s → Term S W s → Prop} :
    ∀ {s : S.Srt} {a b : Term S W s}, StepWith R C s a b →
      M.lt s (Term.eval M ν b) (Term.eval M ν a)
  | _, _, _, .rule i σ _ => by
    rw [Term.eval_subst, Term.eval_subst]; exact hD i _
  | _, _, _, .op f h => by
    rw [Term.eval_op, Term.eval_op]
    exact M.mono f (lt_argsStepWith hD ν h)

/-- A step inside an argument list decreases exactly one position of the value list. -/
private theorem lt_argsStepWith (hD : Decreasing R M) (ν : Valuation M W)
    {C : ∀ s, Term S W s → Term S W s → Prop} :
    ∀ {ss : List S.Srt} {as bs : Args S W ss}, ArgsStepWith R C ss as bs →
      ValsLt M.carrier M.lt (Args.eval M ν as) (Args.eval M ν bs)
  | _, _, _, .head h => Or.inl ⟨lt_stepWith hD ν h, rfl⟩
  | _, _, _, .tail h => Or.inr ⟨rfl, lt_argsStepWith hD ν h⟩

end

/-- **Monotone interpretation criterion.** A rewrite system all of whose rules decrease in a
monotone interpretation is terminating. -/
theorem terminating_of_interpretation (hD : Decreasing R M) (ν : Valuation M W) :
    Terminating R W := by
  refine fun s => Subrelation.wf (r := InvImage (M.lt s) (Term.eval M ν)) ?_
    (InvImage.wf _ (M.wf s))
  rintro a b ⟨n, hn⟩
  cases n with
  | zero => exact absurd hn (by simp [stepAt])
  | succ n => exact lt_stepWith hD ν hn

end MercLib.Rewriting
