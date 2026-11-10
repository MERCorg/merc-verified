module

public import MercLib.Theory.Rewriting.Signature
public import MercLib.Theory.Rewriting.SetAutomaton

@[expose] public section

/-!
# Matching

A pattern `l` *matches* a term `t` if `t` is an instance of `l`. For a linear pattern this depends
only on the head symbols at the non-variable positions of `l`, which is why the set automaton of
`MercLib.SetAutomaton` can work on patterns over the single anonymous variable `ω`.

## Main definitions

- `Term.vars`: the variables of a term, with multiplicity.
- `Term.Linear`: no variable occurs twice.
- `Term.Matches`: `t` is an instance of `l`.
- `Term.toPat`: forget the sorts and the names of the variables.
- `LinearMatchIffHeads`: for a linear pattern, matching is the head-symbol condition `Pat.Matches`.
-/

namespace MercLib.Rewriting

variable {S : Signature}

mutual

/-- The variables of a term, in order and with multiplicity. -/
def Term.vars {V : VarSet S} : {s : S.Srt} → Term S V s → List (Σ s, V s)
  | s, .var x => [⟨s, x⟩]
  | _, .op _ args => Args.vars args

/-- The variables of an argument list, in order and with multiplicity. -/
def Args.vars {V : VarSet S} : {ss : List S.Srt} → Args S V ss → List (Σ s, V s)
  | _, .nil => []
  | _, .cons t ts => Term.vars t ++ Args.vars ts

end

/-- A term is linear if no variable occurs in it twice. -/
def Term.Linear {V : VarSet S} {s : S.Srt} (t : Term S V s) : Prop := t.vars.Nodup

/-- The pattern `l` matches the term `t`: `t` is an instance of `l`. -/
def Term.Matches {V W : VarSet S} {s : S.Srt} (l : Term S V s) (t : Term S W s) : Prop :=
  ∃ σ : Term.Subst S V W, Term.subst σ l = t

/-- The operator symbols of a signature, as an unsorted alphabet. -/
abbrev Sym (S : Signature) := Σ ss : List S.Srt, Σ s : S.Srt, S.Op ss s

open SetAutomaton in
mutual

/-- Forget the sorts and the names of the variables: every variable becomes `ω`. -/
def Term.toPat {V : VarSet S} : {s : S.Srt} → Term S V s → Pat (Sym S)
  | _, .var _ => .omega
  | _, @Term.op _ _ ss s f args => .app ⟨ss, s, f⟩ (Args.toPats args)

/-- `Term.toPat` on an argument list. -/
def Args.toPats {V : VarSet S} : {ss : List S.Srt} → Args S V ss → List (Pat (Sym S))
  | _, .nil => []
  | _, .cons t ts => Term.toPat t :: Args.toPats ts

end

/-- **Matching a linear pattern is a condition on head symbols.** For a linear pattern `l` and a term
`t` of the same sort, `l` matches `t` exactly when `t` has the head symbols of `l` at the
non-variable positions of `l`. Since a substitution is total, the variable family `V` of the pattern
must only contain variables of sorts that have a term over `W`. -/
def LinearMatchIffHeads (S : Signature) (V W : VarSet S) : Prop :=
  (∀ s, V s → Nonempty (Term S W s)) →
    ∀ (s : S.Srt) (l : Term S V s) (t : Term S W s), l.Linear →
      (l.Matches t ↔ SetAutomaton.Pat.Matches l.toPat t.toPat [])

end MercLib.Rewriting
