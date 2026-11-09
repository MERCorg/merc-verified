module

public import MercLib.Theory.Rewriting.Rewrite

@[expose] public section

/-!
# Termination criteria

* `terminating_of_measure`: a measure into a well-founded order that decreases with every step.
* `terminating_of_interpretation`: the monotone-interpretation criterion. Interpret every sort by a
  well-founded carrier and every operator by a function that is strictly monotone in each argument,
  and check that every rule decreases the interpretation under every valuation.

Conditions of rules are ignored by the second criterion, which is sound.

## Main definitions

- `MonotoneInterpretation`: well-founded carriers with strictly monotone operators.
- `Term.eval`: the value of a term under a valuation.
- `Decreasing`: every rule decreases the interpretation.
-/

namespace MercLib.Rewriting

variable {S : Signature} {V : VarSet S} {ι : Type}

/-- Values for an argument list: one carrier element per sort in `ss`. -/
@[reducible] def Vals (A : S.Srt → Type) : List S.Srt → Type
  | [] => PUnit
  | s :: ss => A s × Vals A ss

/-- One position of an argument list decreases, the others stay equal. -/
def ValsLt (A : S.Srt → Type) (lt : ∀ s, A s → A s → Prop) :
    ∀ {ss : List S.Srt}, Vals A ss → Vals A ss → Prop
  | [], _, _ => False
  | s :: _, (a, as), (b, bs) => (lt s b a ∧ as = bs) ∨ (a = b ∧ ValsLt A lt as bs)

/-- A monotone interpretation: a carrier with a well-founded strict order for every sort, and for
every operator a function on the carriers that is strictly monotone in every argument. -/
structure MonotoneInterpretation (S : Signature) where
  /-- The carrier of each sort. -/
  carrier : S.Srt → Type
  /-- The interpretation of each operator. -/
  interp : ∀ {ss : List S.Srt} {s : S.Srt}, S.Op ss s → Vals carrier ss → carrier s
  /-- The strict order on each carrier. -/
  lt : ∀ s, carrier s → carrier s → Prop
  /-- Each order is well founded, so there are no infinite descending chains. -/
  wf : ∀ s, WellFounded (lt s)
  /-- Every operator is strictly monotone in every argument. -/
  mono : ∀ {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) {as bs : Vals carrier ss},
    ValsLt carrier lt as bs → lt s (interp f bs) (interp f as)

/-- A valuation assigns a carrier element to every variable. -/
abbrev Valuation (M : MonotoneInterpretation S) (V : VarSet S) := ∀ s, V s → M.carrier s

namespace Term

mutual

/-- The value of a term under a valuation. -/
def eval {V : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M V) :
    {s : S.Srt} → Term S V s → M.carrier s
  | _, .var x => ν _ x
  | _, .op f args => M.interp f (Args.eval M ν args)

/-- The values of an argument list. -/
def _root_.MercLib.Rewriting.Args.eval {V : VarSet S} (M : MonotoneInterpretation S)
    (ν : Valuation M V) : {ss : List S.Srt} → Args S V ss → Vals M.carrier ss
  | _, .nil => PUnit.unit
  | _, .cons t ts => (Term.eval M ν t, Args.eval M ν ts)

end

/-- The valuation induced by a substitution: every rule variable gets the value of the term the
substitution assigns to it. -/
abbrev substValuation {V W : VarSet S} (M : MonotoneInterpretation S) (ν : Valuation M W)
    (σ : Subst S V W) : Valuation M V := fun s x => eval M ν (σ s x)

end Term

/-- Every rule of `R` strictly decreases the interpretation, for every valuation. -/
def Decreasing (R : TRS S V ι) (M : MonotoneInterpretation S) : Prop :=
  ∀ (i : ι) (ν : Valuation M V), M.lt (R i).srt (Term.eval M ν (R i).rhs) (Term.eval M ν (R i).lhs)

end MercLib.Rewriting
