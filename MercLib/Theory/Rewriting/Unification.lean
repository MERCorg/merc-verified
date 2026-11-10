module

public import MercLib.Theory.Rewriting.Signature

@[expose] public section

/-!
# Unification

A *most general unifier* of two terms, and the unification theorem: unifiable terms have one.

## Main definitions

- `Term.Unifies`: a substitution makes two terms equal.
- `Term.IsMGU`: a most general unifier of two terms.
- `UnificationTheorem`: unifiable terms have a most general unifier.
-/

namespace MercLib.Rewriting

variable {S : Signature}

namespace Term

/-- The substitution `τ` unifies `u` and `v`. -/
def Unifies {X Y : VarSet S} {s : S.Srt} (τ : Subst S X Y) (u v : Term S X s) : Prop :=
  subst τ u = subst τ v

/-- `μ` is a most general unifier of `u` and `v`: it unifies them, and every unifier factors
through it. -/
def IsMGU {X : VarSet S} {s : S.Srt} (μ : Subst S X X) (u v : Term S X s) : Prop :=
  Unifies μ u v ∧ ∀ (Y : VarSet S) (τ : Subst S X Y), Unifies τ u v →
    ∃ ρ : Subst S X Y, ∀ s' x, subst ρ (μ s' x) = τ s' x

end Term

/-- **The unification theorem**: two terms with a unifier have a most general unifier. -/
def UnificationTheorem (S : Signature) : Prop :=
  ∀ (X Y : VarSet S) (s : S.Srt) (u v : Term S X s) (τ : Term.Subst S X Y), Term.Unifies τ u v →
    ∃ μ, Term.IsMGU μ u v

end MercLib.Rewriting
