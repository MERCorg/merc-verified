module

public import MercLib.Rewriting.Soundness

@[expose] public section

/-!
# Ground confluence from a model

This file and `Rewriting/Proofs/Confluence_Proofs.lean` prove confluence of a rewrite system
*semantically*, avoiding critical pairs entirely.
The ingredients are:

* **termination** — every term has a normal form;
* **soundness** — rewriting preserves values in a model `A` (`Rewriting.Soundness`);
* **sufficient completeness with no confusion** — two normal forms with the same value are equal.

Then any two reducts of a term reduce to normal forms with the same value, hence to the *same*
normal form. Overlapping rules, non-left-linear rules and rules that only normalise a symbolic
subterm (mCRL2's `succ(p)`-rules) cost nothing here: they are simply extra value-preserving rules.

The abstract-rewriting vocabulary (`Relation.Normal`, `Relation.Normalizing`,
`Relation.Terminating`, `Relation.Confluent`, and the equivalence of confluence with uniqueness of
normal forms) is taken from `Cslib.Foundations.Relation`; this file only adds the model-based
criterion and its specialisation to terms.
-/

namespace MercLib.Rewriting

/-! ## Specialisation to rewrite systems -/

variable {S : Signature} {V W : VarSet S} {ι : Type}

/-- Distinct normal forms of the same sort have distinct values in `A`. This is the combination of
sufficient completeness (normal forms are constructor terms) and no confusion (the model has no
junk), and is the only property of the model that the confluence proof needs. -/
def NormalFormsInjective (R : TRS S V ι) (W : VarSet S) (A : Algebra S)
    (ν : Valuation A W) : Prop :=
  ∀ {s : S.Srt} {a b : Term S W s}, Normal R a → Normal R b →
    Term.eval A ν a = Term.eval A ν b → a = b

end MercLib.Rewriting
