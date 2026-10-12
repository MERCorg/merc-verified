import Rewriting.Soundness
import Rewriting.Proofs.Signature_Proofs

/-!
# Proofs: Soundness

Rewriting preserves values in a model: every step (`eval_stepWith`, `eval_stepAt`, `Step.eval_eq`)
and hence every rewrite sequence (`Steps.eval_eq`).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The headline theorem
`Steps.eval_eq` is pinned in `Rewriting/Pins/Soundness_Pins.lean` (human-vetted); the definition
of `Model` lives in `Rewriting/Soundness.lean`.
-/

namespace Rewriting

variable {S : Signature} {V W : VarSet S} {ι : Type}

variable {R : TRS S V ι} {A : Algebra S}

mutual

/-- A step whose conditions are value-preserving is value-preserving. -/
theorem eval_stepWith (hM : Model R A) (ν : Valuation A W)
    {C : ∀ s, Term S W s → Term S W s → Prop}
    (hC : ∀ s a b, C s a b → Term.eval A ν a = Term.eval A ν b) :
    ∀ {s : S.Srt} {a b : Term S W s}, StepWith R C s a b →
      Term.eval A ν a = Term.eval A ν b
  | _, _, _, .rule i σ hc => by
    rw [Term.eval_subst, Term.eval_subst]
    exact hM i _ fun c hcm => by
      rw [← Term.eval_subst, ← Term.eval_subst]; exact hC _ _ _ (hc c hcm)
  | _, _, _, .op f h => by
    rw [Term.eval_op, Term.eval_op, eval_argsStepWith hM ν hC h]

/-- `eval_stepWith` for argument lists. -/
theorem eval_argsStepWith (hM : Model R A) (ν : Valuation A W)
    {C : ∀ s, Term S W s → Term S W s → Prop}
    (hC : ∀ s a b, C s a b → Term.eval A ν a = Term.eval A ν b) :
    ∀ {ss : List S.Srt} {as bs : Args S W ss}, ArgsStepWith R C ss as bs →
      Args.eval A ν as = Args.eval A ν bs
  | _, _, _, .head h => by
    rw [Args.eval_cons, Args.eval_cons, eval_stepWith hM ν hC h]
  | _, _, _, .tail h => by
    rw [Args.eval_cons, Args.eval_cons, eval_argsStepWith hM ν hC h]

end

/-- Every step at condition depth `n` preserves values. -/
theorem eval_stepAt (hM : Model R A) (ν : Valuation A W) :
    ∀ (n : Nat) {s : S.Srt} {a b : Term S W s}, stepAt R n s a b →
      Term.eval A ν a = Term.eval A ν b := by
  intro n
  induction n with
  | zero => intro s a b h; exact absurd h (by simp [stepAt])
  | succ n ih =>
    intro s a b h
    refine eval_stepWith hM ν (fun s a b hab => ?_) h
    induction hab with
    | refl => rfl
    | tail _ hstep ihs => exact ihs.trans (ih hstep)

/-- Rewriting preserves values: the algebra is a model of the equational theory. -/
theorem Step.eval_eq (hM : Model R A) (ν : Valuation A W) {s : S.Srt} {a b : Term S W s}
    (h : Step R s a b) : Term.eval A ν a = Term.eval A ν b := by
  obtain ⟨n, hn⟩ := h
  exact eval_stepAt hM ν n hn

/-- Multi-step rewriting preserves values. -/
theorem Steps.eval_eq (hM : Model R A) (ν : Valuation A W) {s : S.Srt} {a b : Term S W s}
    (h : Steps R s a b) : Term.eval A ν a = Term.eval A ν b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.eval_eq hM ν)

end Rewriting
