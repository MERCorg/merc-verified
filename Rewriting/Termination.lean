import Rewriting.Confluence

/-!
# Termination criteria

Termination is the one ingredient of the semantic confluence proof that the model does not give
for free. This file collects the criteria used to discharge it.

* `terminating_of_measure` — a measure into a well-founded order that decreases with every step.
  This is the general shape: every concrete termination argument below produces such a measure.
* `terminating_of_interpretation` — the classical *monotone algebra* criterion: interpret every
  operator by a strictly monotone function into `Nat`, and check that every rule decreases the
  interpretation for all valuations.

Note that a monotone algebra can only ever work for systems whose rules do not duplicate a
variable in a way that outweighs the decrease; see the discussion in `Rewriting.TRS.Pos` for
the mCRL2 `@addc` rules, which duplicate their `Bool` argument and therefore need a stronger
criterion than `terminating_of_interpretation`.
-/

namespace Rewriting

variable {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι}

/-- A rewrite system is terminating if some measure into a well-founded order decreases with every
step. -/
theorem terminating_of_measure {γ : Type _} (lt : γ → γ → Prop) (hwf : WellFounded lt)
    (μ : ∀ s, Term S W s → γ)
    (hdec : ∀ {s : S.Srt} {a b : Term S W s}, Step R s a b → lt (μ s b) (μ s a)) :
    Terminating R W :=
  fun s => Subrelation.wf (fun {_ _} h => hdec h) (InvImage.wf (μ s) hwf)

/-! ## Monotone algebras

An interpretation into `Nat` that is strictly monotone in every argument turns a rewrite step into
a strict decrease, provided every rule decreases under every valuation. The monotonicity condition
is what propagates a decrease at an inner position to the whole term.
-/

/-- One position of an argument list decreases, the others stay equal. -/
def ValsLt (A : S.Srt → Type) (lt : ∀ s, A s → A s → Prop) :
    ∀ {ss : List S.Srt}, Vals A ss → Vals A ss → Prop
  | [], _, _ => False
  | s :: _, (a, as), (b, bs) => (lt s b a ∧ as = bs) ∨ (a = b ∧ ValsLt A lt as bs)

/-- An algebra whose operators are strictly monotone in every argument, with a well-founded strict
order on each carrier. -/
structure MonotoneAlgebra (S : Signature) where
  /-- The underlying algebra. -/
  alg : Algebra S
  /-- The strict order on each carrier. -/
  lt : ∀ s, alg.carrier s → alg.carrier s → Prop
  /-- Each order is well founded, so there are no infinite descending chains. -/
  wf : ∀ s, WellFounded (lt s)
  /-- Every operator is strictly monotone in every argument. -/
  mono : ∀ {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) {as bs : Vals alg.carrier ss},
    ValsLt alg.carrier lt as bs → lt s (alg.interp f bs) (alg.interp f as)

/-- Every rule of `R` strictly decreases the interpretation, for every valuation. Conditions are
ignored, which is sound but can only prove more systems terminating than needed. -/
def Decreasing (R : TRS S V ι) (M : MonotoneAlgebra S) : Prop :=
  ∀ (i : ι) (ν : Valuation M.alg V),
    M.lt (R i).srt (Term.eval M.alg ν (R i).rhs) (Term.eval M.alg ν (R i).lhs)

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

end Rewriting
