module

public import MercLib.Theory.Rewriting.Signature

@[expose] public section

/-!
# Contexts

A context is a term with one hole. In a many-sorted setting a position alone does not determine the
sort of the subterm there, so subterm occurrences are expressed through contexts: `C.fill u = t`
says that `u` occurs in `t` at the hole of `C`, and `C.fill v` is the replacement `t[v]`.

## Main definitions

- `Ctx S V h s`: terms of sort `s` with one hole of sort `h`.
- `Ctx.fill`: fill the hole.
- `Ctx.subst`: apply a substitution to a context; the hole stays.
-/

namespace MercLib.Rewriting

variable {S : Signature}

mutual

/-- A term of sort `s` over the variables `V` with one hole of sort `h`. -/
inductive Ctx (S : Signature) (V : VarSet S) (h : S.Srt) : S.Srt → Type where
  /-- The hole. -/
  | hole : Ctx S V h h
  /-- An operator with the hole in one of its arguments. -/
  | op {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) (c : ArgsCtx S V h ss) : Ctx S V h s

/-- An argument list with one hole of sort `h`. -/
inductive ArgsCtx (S : Signature) (V : VarSet S) (h : S.Srt) : List S.Srt → Type where
  /-- The hole is in the first argument. -/
  | head {s : S.Srt} {ss : List S.Srt} (c : Ctx S V h s) (ts : Args S V ss) :
      ArgsCtx S V h (s :: ss)
  /-- The hole is in one of the remaining arguments. -/
  | tail {s : S.Srt} {ss : List S.Srt} (t : Term S V s) (c : ArgsCtx S V h ss) :
      ArgsCtx S V h (s :: ss)

end

variable {V W : VarSet S} {h : S.Srt}

mutual

/-- Fill the hole of a context. -/
def Ctx.fill : {s : S.Srt} → Ctx S V h s → Term S V h → Term S V s
  | _, .hole, u => u
  | _, .op f c, u => .op f (ArgsCtx.fill c u)

/-- Fill the hole of an argument context. -/
def ArgsCtx.fill : {ss : List S.Srt} → ArgsCtx S V h ss → Term S V h → Args S V ss
  | _, .head c ts, u => .cons (Ctx.fill c u) ts
  | _, .tail t c, u => .cons t (ArgsCtx.fill c u)

end

mutual

/-- Apply a substitution to a context. -/
def Ctx.subst (σ : Term.Subst S V W) : {s : S.Srt} → Ctx S V h s → Ctx S W h s
  | _, .hole => .hole
  | _, .op f c => .op f (ArgsCtx.subst σ c)

/-- Apply a substitution to an argument context. -/
def ArgsCtx.subst (σ : Term.Subst S V W) : {ss : List S.Srt} → ArgsCtx S V h ss → ArgsCtx S W h ss
  | _, .head c ts => .head (Ctx.subst σ c) (Args.subst σ ts)
  | _, .tail t c => .tail (Term.subst σ t) (ArgsCtx.subst σ c)

end

end MercLib.Rewriting
