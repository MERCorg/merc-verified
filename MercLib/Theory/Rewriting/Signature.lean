module

public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Many-sorted first-order terms

The syntactic layer of the `Rewriting` library: signatures, terms and substitution. A many-sorted
signature with a single sort is the unsorted case.

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

end MercLib.Rewriting
