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

variable {S : Signature} {V : VarSet S} {ι : Type}

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

end Rewriting
