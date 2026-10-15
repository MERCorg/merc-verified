module

public import MercLib.Rewriting.Confluence
public import MercLib.Rewriting.Proofs.Soundness_Proofs

@[expose] public section

/-!
# Proofs: Confluence

The abstract model-based criterion (`confluent_of_value`) and its specialisation to rewrite systems
(`confluent_of_model`, `existsUnique_normalForm`).

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are stated in
`Challenges/Rewriting.lean` (human-vetted); the definition of
`NormalFormsInjective` lives in `MercLib/Rewriting/Confluence.lean`.
-/

namespace MercLib.Rewriting

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
private theorem confluent_of_value (ht : _root_.Relation.Terminating r) (e : α → β)
    (hsound : ∀ ⦃a b⦄, r a b → e a = e b)
    (hinj : ∀ ⦃a b⦄, _root_.Relation.Normal r a → _root_.Relation.Normal r b →
      e a = e b → a = b) : _root_.Relation.Confluent r :=
  ht.confluent_iff_forall_unique_normal.mpr
    (existsUnique_normal_of_value ht.to_normalizing e hsound hinj)

/-! ## Specialisation to rewrite systems -/

variable {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι} {A : Algebra S}

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
  existsUnique_normal_of_value (ht s).to_normalizing (Term.eval A ν)
    (fun _ _ h => h.eval_eq hM ν) (@fun _ _ ha hb h => hinj ha hb h) t

end MercLib.Rewriting
