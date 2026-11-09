module

public import MercLib.Theory.Rewriting.Rewrite
public import Cslib.Foundations.Relation.Confluence

@[expose] public section

/-!
# Confluence of rewrite systems

Local confluence and confluence of a rewrite system on the terms over a variable family `W`, sort by
sort. The abstract vocabulary (`Relation.LocallyConfluent`, `Relation.Confluent`, Newman's lemma) is
taken from `Cslib.Foundations.Relation`.

## Main definitions

- `LocallyConfluent`: every one-step peak of `R` is joinable.
- `Confluent`: every many-step peak of `R` is joinable.
-/

namespace MercLib.Rewriting

variable {S : Signature} {V : VarSet S} {ι : Type}

/-- `R` is locally confluent on the terms over `W`: at every sort, two one-step reducts of a term
have a common reduct. -/
def LocallyConfluent (R : TRS S V ι) (W : VarSet S) : Prop :=
  ∀ s, Relation.LocallyConfluent (rel R W s)

/-- `R` is confluent on the terms over `W`: at every sort, two many-step reducts of a term have a
common reduct. -/
def Confluent (R : TRS S V ι) (W : VarSet S) : Prop :=
  ∀ s, Relation.Confluent (rel R W s)

end MercLib.Rewriting
