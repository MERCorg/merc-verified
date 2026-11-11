module

public import MercLib.Theory.Rewriting.Confluence
public import MercLib.Theory.Rewriting.Termination

@[expose] public section

/-!
# Semantics of conditional rewrite systems

Terms are interpreted in an `Algebra`, and an algebra is a model of a rewrite system when every rule,
read as a conditional equation, holds in it. Rewriting is sound for every model.

The question these definitions answer comes from control flow pruning in state space exploration:
when may a summand with guard `d == c` be skipped in a state in which `d` has the value `v`? The
data specifications of mCRL2 interpret `==` as equality, see `Equality.Respects`. In every such
model `v` and `c` are distinct when `v == c` rewrites to `false`, see `DistinctOfStepsFalse`. That
`v` and `c` are distinct normal forms is not enough, even for a terminating and confluent system,
see `NormalFormsNotDistinct`: confluence makes distinct normal forms non-convertible, while a rule
for `==` can still identify their values.

## Main definitions

- `Algebra`: a carrier for every sort and a function for every operator.
- `Term.denote`: the value of a term under an assignment of its variables.
- `Models`: every rule of a rewrite system holds in an algebra, as a conditional equation.
- `Equality`: a sort of booleans with `true`, `false`, and an operator `==` for every sort.
- `Equality.Respects`: an algebra in which `true` and `false` differ and `==` is equality.

## Main statements

- `StepsSound`: rewriting preserves the value of a term in every model.
- `DistinctOfStepsFalse`: when `a == b` rewrites to `false`, then `a` and `b` have distinct values in
  every model in which `==` is equality.
- `NormalFormsNotDistinct`: there are a terminating and confluent rewrite system and two distinct
  normal forms that have the same value in every such model.
-/

namespace MercLib.Rewriting

variable {S : Signature} {V : VarSet S} {ι : Type}

/-- An algebra for a signature: a carrier for every sort, and a function on the carriers for every
operator. -/
structure Algebra (S : Signature) where
  /-- The carrier of each sort. -/
  carrier : S.Srt → Type
  /-- The interpretation of each operator. -/
  interp : ∀ {ss : List S.Srt} {s : S.Srt}, S.Op ss s → Vals carrier ss → carrier s

/-- An assignment of a carrier element to every variable. -/
abbrev Assignment (A : Algebra S) (W : VarSet S) := ∀ s, W s → A.carrier s

namespace Term

mutual

/-- The value of a term in an algebra under an assignment. -/
def denote {W : VarSet S} (A : Algebra S) (ν : Assignment A W) :
    {s : S.Srt} → Term S W s → A.carrier s
  | _, .var x => ν _ x
  | _, .op f args => A.interp f (Args.denote A ν args)

/-- The values of an argument list in an algebra under an assignment. -/
def _root_.MercLib.Rewriting.Args.denote {W : VarSet S} (A : Algebra S) (ν : Assignment A W) :
    {ss : List S.Srt} → Args S W ss → Vals A.carrier ss
  | _, .nil => PUnit.unit
  | _, .cons t ts => (Term.denote A ν t, Args.denote A ν ts)

end

end Term

/-- The algebra `A` is a model of `R`: for every rule and every assignment of its variables that
makes both sides of every condition equal, both sides of the rule are equal. -/
def Models (A : Algebra S) (R : TRS S V ι) : Prop :=
  ∀ (i : ι) (ν : Assignment A V),
    (∀ c ∈ (R i).conds, Term.denote A ν c.lhs = Term.denote A ν c.rhs) →
      Term.denote A ν (R i).lhs = Term.denote A ν (R i).rhs

/-- The booleans of a signature: a sort with the constants `true` and `false`, and an operator `==`
on every sort. -/
structure Equality (S : Signature) where
  /-- The sort of the booleans. -/
  bool : S.Srt
  /-- The constant `true`. -/
  trueOp : S.Op [] bool
  /-- The constant `false`. -/
  falseOp : S.Op [] bool
  /-- The equality `==` on each sort. -/
  eqOp : ∀ s, S.Op [s, s] bool

namespace Equality

/-- The term `true`. -/
def trueTerm (E : Equality S) {W : VarSet S} : Term S W E.bool := .op E.trueOp .nil

/-- The term `false`. -/
def falseTerm (E : Equality S) {W : VarSet S} : Term S W E.bool := .op E.falseOp .nil

/-- The term `a == b`. -/
def eqTerm (E : Equality S) {W : VarSet S} {s : S.Srt} (a b : Term S W s) : Term S W E.bool :=
  .op (E.eqOp s) (.cons a (.cons b .nil))

/-- In the algebra `A`, `true` and `false` are distinct, and `x == y` is `true` exactly when `x` and
`y` are equal, as in the data specifications of mCRL2. -/
def Respects (E : Equality S) (A : Algebra S) : Prop :=
  A.interp E.trueOp PUnit.unit ≠ A.interp E.falseOp PUnit.unit ∧
    ∀ (s : S.Srt) (x y : A.carrier s),
      A.interp (E.eqOp s) (x, y, PUnit.unit) = A.interp E.trueOp PUnit.unit ↔ x = y

end Equality

/-- **Rewriting is sound.** In every model of `R`, a term over `W` and every term it rewrites to have
the same value under every assignment. -/
def StepsSound (R : TRS S V ι) (W : VarSet S) : Prop :=
  ∀ (A : Algebra S), Models A R → ∀ (ν : Assignment A W) {s : S.Srt} {a b : Term S W s},
    Steps R s a b → Term.denote A ν a = Term.denote A ν b

/-- **Distinct by rewriting.** When `a == b` rewrites to `false` with `R`, then `a` and `b` have
distinct values in every model of `R` in which `==` is equality, under every assignment. -/
def DistinctOfStepsFalse (E : Equality S) (R : TRS S V ι) (W : VarSet S) : Prop :=
  ∀ (A : Algebra S), Models A R → E.Respects A →
    ∀ (ν : Assignment A W) {s : S.Srt} (a b : Term S W s),
      Steps R E.bool (E.eqTerm a b) E.falseTerm → Term.denote A ν a ≠ Term.denote A ν b

/-- **Distinct normal forms need not be distinct values.** There are an unconditional rewrite system
`R` that is terminating and confluent on the ground terms, and two distinct ground normal forms `a`
and `b`, such that `R` has a model in which `==` is equality, and `a` and `b` have the same value in
every such model. -/
def NormalFormsNotDistinct : Prop :=
  ∃ (S : Signature) (E : Equality S) (V : VarSet S) (ι : Type) (R : TRS S V ι) (s : S.Srt)
    (a b : Term S (Ground S) s),
    Unconditional R ∧ Terminating R (Ground S) ∧ Confluent R (Ground S) ∧
      Normal R a ∧ Normal R b ∧ a ≠ b ∧
      (∃ A : Algebra S, Models A R ∧ E.Respects A) ∧
      ∀ (A : Algebra S), Models A R → E.Respects A →
        ∀ ν : Assignment A (Ground S), Term.denote A ν a = Term.denote A ν b

end MercLib.Rewriting
