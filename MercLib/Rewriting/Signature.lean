module

public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Many-sorted first-order terms

The syntactic layer of the `Rewriting` library: signatures, terms, substitution and evaluation
in an algebra. This is the vocabulary in which an mCRL2 `sort`/`cons`/`map`/`eqn` block is
expressed as a *rewrite system* (see `Rewriting.Rewrite`), as opposed to the functional port in
`MachineNumbers`, which models the same equations as total Lean functions.

A `Signature` fixes a type of sorts and a family of operator symbols indexed by their argument
sorts and result sort. Indexing the operators (rather than giving `dom`/`cod` functions) keeps the
sort indices of `Term` *variables* in the sense of dependent pattern matching, so `cases`/`match`
on a term of a concrete sort works without dependent-elimination trouble.
-/

namespace MercLib.Rewriting

/-- A many-sorted first-order signature: a type of sorts `Srt`, and for each argument-sort list
and result sort a type of operator symbols. -/
structure Signature where
  /-- The sorts of the signature. -/
  Srt : Type
  /-- `Op ss s` is the type of operators taking arguments of sorts `ss` and returning sort `s`. -/
  Op : List Srt → Srt → Type

variable {S : Signature}

/-- A sort-indexed family of variables. `Ground` (no variables) is `fun _ => Empty`. -/
abbrev VarSet (S : Signature) := S.Srt → Type

/-- The empty variable family: terms over `Ground` are the ground terms. -/
abbrev Ground (S : Signature) : VarSet S := fun _ => Empty

mutual

/-- Terms of sort `s` over the signature `S` with variables `V`. -/
inductive Term (S : Signature) (V : VarSet S) : S.Srt → Type where
  /-- A variable. -/
  | var {s : S.Srt} (x : V s) : Term S V s
  /-- An operator applied to arguments. -/
  | op {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) (args : Args S V ss) : Term S V s

/-- A list of arguments, one term per sort in `ss`. -/
inductive Args (S : Signature) (V : VarSet S) : List S.Srt → Type where
  /-- The empty argument list. -/
  | nil : Args S V []
  /-- One argument followed by the rest. -/
  | cons {s : S.Srt} {ss : List S.Srt} (t : Term S V s) (ts : Args S V ss) : Args S V (s :: ss)

end

namespace Term

/-- A substitution replaces every variable in `V` by a term over `W` of the same sort. -/
abbrev Subst (S : Signature) (V W : VarSet S) := ∀ s, V s → Term S W s

mutual

/-- Apply a substitution to a term. -/
def subst {V W : VarSet S} (σ : Subst S V W) : {s : S.Srt} → Term S V s → Term S W s
  | _, .var x => σ _ x
  | _, .op f args => .op f (Args.subst σ args)

/-- Apply a substitution to an argument list. -/
def _root_.MercLib.Rewriting.Args.subst {V W : VarSet S} (σ : Subst S V W) :
    {ss : List S.Srt} → Args S V ss → Args S W ss
  | _, .nil => .nil
  | _, .cons t ts => .cons (Term.subst σ t) (Args.subst σ ts)

end

end Term

/-! ## Algebras

An algebra interprets every sort by a carrier type and every operator by a function on carriers.
The model used for soundness of the `MachineNumbers` ports is the algebra whose carriers are the
Lean types (`Pos`, `Bool`, ...) and whose operators are the ported Lean functions; the model used
for termination is an algebra of natural numbers.
-/

/-- Values for an argument list: one carrier element per sort in `ss`. -/
@[reducible] def Vals (A : S.Srt → Type) : List S.Srt → Type
  | [] => PUnit
  | s :: ss => A s × Vals A ss

/-- An algebra for the signature `S`. -/
structure Algebra (S : Signature) where
  /-- The carrier of each sort. -/
  carrier : S.Srt → Type
  /-- The interpretation of each operator. -/
  interp : ∀ {ss : List S.Srt} {s : S.Srt}, S.Op ss s → Vals carrier ss → carrier s

/-- A valuation assigns a carrier element to every variable. -/
abbrev Valuation (A : Algebra S) (V : VarSet S) := ∀ s, V s → A.carrier s

namespace Term

mutual

/-- The value of a term in an algebra under a valuation. -/
def eval {V : VarSet S} (A : Algebra S) (ν : Valuation A V) :
    {s : S.Srt} → Term S V s → A.carrier s
  | _, .var x => ν _ x
  | _, .op f args => A.interp f (Args.eval A ν args)

/-- The values of an argument list. -/
def _root_.MercLib.Rewriting.Args.eval {V : VarSet S} (A : Algebra S) (ν : Valuation A V) :
    {ss : List S.Srt} → Args S V ss → Vals A.carrier ss
  | _, .nil => PUnit.unit
  | _, .cons t ts => (Term.eval A ν t, Args.eval A ν ts)

end

/-- The valuation induced by a substitution: every rule variable gets the value of the term the
substitution assigns to it. -/
abbrev substValuation {V W : VarSet S} (A : Algebra S) (ν : Valuation A W) (σ : Subst S V W) :
    Valuation A V := fun s x => eval A ν (σ s x)

end Term

end MercLib.Rewriting
