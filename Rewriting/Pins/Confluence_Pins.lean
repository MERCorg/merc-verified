import Rewriting.Confluence
import Rewriting.Proofs.Confluence_Proofs

open Rewriting

-- Contract pin: fails to compile if `confluent_of_value`'s signature drifts (the abstract
-- model-based confluence criterion).
example {α β : Type _} {r : α → α → Prop} (ht : Relation.Terminating r) (e : α → β)
    (hsound : ∀ ⦃a b⦄, r a b → e a = e b)
    (hinj : ∀ ⦃a b⦄, Relation.Normal r a → Relation.Normal r b → e a = e b → a = b) :
    Relation.Confluent r :=
  confluent_of_value ht e hsound hinj

-- Contract pin: fails to compile if `confluent_of_model`'s signature drifts (ground confluence of
-- a rewrite system from its model).
example {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι} {A : Algebra S}
    (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) (s : S.Srt) : Relation.Confluent (rel R W s) :=
  confluent_of_model hM ν ht hinj s

-- Contract pin: fails to compile if `existsUnique_normalForm`'s signature drifts (every term has a
-- unique normal form).
example {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι} {A : Algebra S}
    (hM : Model R A) (ν : Valuation A W) (ht : Terminating R W)
    (hinj : NormalFormsInjective R W A ν) {s : S.Srt} (t : Term S W s) :
    ∃! u, Steps R s t u ∧ Normal R u :=
  existsUnique_normalForm hM ν ht hinj t
