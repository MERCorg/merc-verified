import Rewriting.Soundness

/-!
# Ground confluence from a model

This file proves confluence of a rewrite system *semantically*, avoiding critical pairs entirely.
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

namespace Rewriting

open Relation

/-! ## The abstract criterion -/

variable {α β : Type _} {r : α → α → Prop}

/-- Reachability preserves a value that every single step preserves. -/
theorem eq_of_reflTransGen (e : α → β) (hsound : ∀ ⦃a b⦄, r a b → e a = e b) :
    ∀ ⦃a b⦄, ReflTransGen r a b → e a = e b := by
  intro a b h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hsound hstep)

/-- If `r` normalises, preserves the value `e`, and distinct normal forms have distinct values,
then every element has a unique normal form. -/
theorem existsUnique_normal_of_value (hn : _root_.Relation.Normalizing r) (e : α → β)
    (hsound : ∀ ⦃a b⦄, r a b → e a = e b)
    (hinj : ∀ ⦃a b⦄, _root_.Relation.Normal r a → _root_.Relation.Normal r b →
      e a = e b → a = b) (a : α) :
    ∃! b, ReflTransGen r a b ∧ _root_.Relation.Normal r b := by
  obtain ⟨b, hab, hb⟩ := hn a
  refine ⟨b, ⟨hab, hb⟩, ?_⟩
  rintro c ⟨hac, hc⟩
  exact hinj hc hb (by rw [← eq_of_reflTransGen e hsound hac, eq_of_reflTransGen e hsound hab])

/-- **Confluence from a model.** A terminating, value-preserving relation whose normal forms are
determined by their value is confluent. -/
theorem confluent_of_value (ht : _root_.Relation.Terminating r) (e : α → β)
    (hsound : ∀ ⦃a b⦄, r a b → e a = e b)
    (hinj : ∀ ⦃a b⦄, _root_.Relation.Normal r a → _root_.Relation.Normal r b →
      e a = e b → a = b) : _root_.Relation.Confluent r :=
  ht.isConfluent_iff_all_unique_Normal.mpr
    (existsUnique_normal_of_value ht.isNormalizing e hsound hinj)

/-! ## Specialisation to rewrite systems -/

variable {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι} {A : Algebra S}

/-- Distinct normal forms of the same sort have distinct values in `A`. This is the combination of
sufficient completeness (normal forms are constructor terms) and no confusion (the model has no
junk), and is the only property of the model that the confluence proof needs. -/
def NormalFormsInjective (R : TRS S V ι) (W : VarSet S) (A : Algebra S)
    (ν : Valuation A W) : Prop :=
  ∀ {s : S.Srt} {a b : Term S W s}, Normal R a → Normal R b →
    Term.eval A ν a = Term.eval A ν b → a = b

/-- **Ground confluence of a rewrite system from its model.** -/
theorem confluent_of_model (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) (s : S.Srt) : Confluent (rel R W s) :=
  confluent_of_value (ht s) (Term.eval A ν)
    (fun _ _ h => h.eval_eq hM ν) (@fun _ _ ha hb h => hinj ha hb h)

/-- Every term has a unique normal form. Since rewriting preserves values (`Steps.eval_eq`), that
normal form is the term's value computed in the model: the rewrite system computes the model. -/
theorem existsUnique_normalForm (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) {s : S.Srt} (t : Term S W s) :
    ∃! u, Steps R s t u ∧ Normal R u :=
  existsUnique_normal_of_value (ht s).isNormalizing (Term.eval A ν)
    (fun _ _ h => h.eval_eq hM ν) (@fun _ _ ha hb h => hinj ha hb h) t

end Rewriting
