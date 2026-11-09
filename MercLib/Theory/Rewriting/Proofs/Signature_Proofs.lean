module

public import MercLib.Theory.Rewriting.Signature

@[expose] public section

/-!
# Proofs: Signature

The `rfl` simp lemmas unfolding substitution.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The definitions live in
`Theory/Rewriting/Signature.lean` (human-vetted).
-/

namespace MercLib.Rewriting

variable {S : Signature}

namespace Term

@[simp] private theorem subst_var {V W : VarSet S} (σ : Subst S V W) {s : S.Srt} (x : V s) :
    subst σ (.var x) = σ s x := rfl

@[simp] private theorem subst_op {V W : VarSet S} (σ : Subst S V W) {ss : List S.Srt} {s : S.Srt}
    (f : S.Op ss s) (args : Args S V ss) :
    subst σ (.op f args) = .op f (Args.subst σ args) := rfl

@[simp] private theorem _root_.MercLib.Rewriting.Args.subst_nil {V W : VarSet S} (σ : Subst S V W) :
    Args.subst σ (.nil) = .nil := rfl

@[simp] private theorem _root_.MercLib.Rewriting.Args.subst_cons {V W : VarSet S} (σ : Subst S V W) {s : S.Srt}
    {ss : List S.Srt} (t : Term S V s) (ts : Args S V ss) :
    Args.subst σ (.cons t ts) = .cons (Term.subst σ t) (Args.subst σ ts) := rfl

end Term

end MercLib.Rewriting
