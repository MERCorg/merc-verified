module

public import MercLib.Rewriting.Signature

@[expose] public section

/-!
# Proofs: Signature

The `rfl` simp lemmas unfolding substitution and evaluation, and `eval_subst`, the bridge between
syntactic substitution and the semantic model.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The definitions live in
`Rewriting/Signature.lean` (human-vetted).
-/

namespace MercLib.Rewriting

variable {S : Signature}

namespace Term

@[simp] theorem subst_var {V W : VarSet S} (σ : Subst S V W) {s : S.Srt} (x : V s) :
    subst σ (.var x) = σ s x := rfl

@[simp] theorem subst_op {V W : VarSet S} (σ : Subst S V W) {ss : List S.Srt} {s : S.Srt}
    (f : S.Op ss s) (args : Args S V ss) :
    subst σ (.op f args) = .op f (Args.subst σ args) := rfl

@[simp] theorem _root_.MercLib.Rewriting.Args.subst_nil {V W : VarSet S} (σ : Subst S V W) :
    Args.subst σ (.nil) = .nil := rfl

@[simp] theorem _root_.MercLib.Rewriting.Args.subst_cons {V W : VarSet S} (σ : Subst S V W) {s : S.Srt}
    {ss : List S.Srt} (t : Term S V s) (ts : Args S V ss) :
    Args.subst σ (.cons t ts) = .cons (Term.subst σ t) (Args.subst σ ts) := rfl

@[simp] theorem eval_var {V : VarSet S} (A : Algebra S) (ν : Valuation A V) {s : S.Srt} (x : V s) :
    eval A ν (.var x) = ν s x := rfl

@[simp] theorem eval_op {V : VarSet S} (A : Algebra S) (ν : Valuation A V) {ss : List S.Srt}
    {s : S.Srt} (f : S.Op ss s) (args : Args S V ss) :
    eval A ν (.op f args) = A.interp f (Args.eval A ν args) := rfl

@[simp] theorem _root_.MercLib.Rewriting.Args.eval_nil {V : VarSet S} (A : Algebra S) (ν : Valuation A V) :
    Args.eval A ν (.nil) = PUnit.unit := rfl

@[simp] theorem _root_.MercLib.Rewriting.Args.eval_cons {V : VarSet S} (A : Algebra S) (ν : Valuation A V)
    {s : S.Srt} {ss : List S.Srt} (t : Term S V s) (ts : Args S V ss) :
    Args.eval A ν (.cons t ts) = (Term.eval A ν t, Args.eval A ν ts) := rfl

mutual

/-- Evaluating a substituted term is evaluating the term under the induced valuation. This is the
bridge between syntactic rewriting and the semantic model. -/
theorem eval_subst {V W : VarSet S} (A : Algebra S) (ν : Valuation A W) (σ : Subst S V W) :
    ∀ {s : S.Srt} (t : Term S V s), eval A ν (subst σ t) = eval A (substValuation A ν σ) t
  | _, .var _ => rfl
  | _, .op _ args => by rw [subst_op, eval_op, eval_op, Args.eval_subst A ν σ args]

/-- `eval_subst` for argument lists. -/
theorem _root_.MercLib.Rewriting.Args.eval_subst {V W : VarSet S} (A : Algebra S) (ν : Valuation A W)
    (σ : Subst S V W) :
    ∀ {ss : List S.Srt} (as : Args S V ss),
      Args.eval A ν (Args.subst σ as) = Args.eval A (substValuation A ν σ) as
  | _, .nil => rfl
  | _, .cons t ts => by
    rw [Args.subst_cons, Args.eval_cons, Args.eval_cons, Term.eval_subst A ν σ t,
      Args.eval_subst A ν σ ts]

end

end Term

end MercLib.Rewriting
