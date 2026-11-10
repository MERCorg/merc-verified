module

public import MercLib.Theory.Rewriting.Context
public import MercLib.Theory.Rewriting.Rewrite
public import MercLib.Theory.Rewriting.Unification
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
- `Overlap`: a rule overlapping a non-variable subterm of the left-hand side of a rule.
- `CriticalPairsJoinable`: the critical pair of every overlap is joinable.
- `CriticalPairLemma`: an unconditional system is locally confluent iff its critical pairs are
  joinable.
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

/-- Two copies of the variables, to rename two rules apart. -/
abbrev Both (V : VarSet S) : VarSet S := fun s => V s ⊕ V s

/-- Rename the variables of a term into the left copy. -/
def renameL : Term.Subst S V (Both V) := fun _ x => .var (.inl x)

/-- Rename the variables of a term into the right copy. -/
def renameR : Term.Subst S V (Both V) := fun _ x => .var (.inr x)

/-- All rules are unconditional. -/
def Unconditional (R : TRS S V ι) : Prop := ∀ i, (R i).conds = []

/-- An overlap of the rule `j` on a non-variable subterm `u` of the left-hand side of the rule `i`,
with the two rules renamed apart and `μ` a most general unifier. The rules `i` and `j` may be the
same rule, and `C` may be the empty context. -/
structure Overlap (R : TRS S V ι) where
  /-- The rule whose left-hand side is overlapped. -/
  i : ι
  /-- The rule overlapping it. -/
  j : ι
  /-- The context of the overlapped subterm. -/
  C : Ctx S V (R j).srt (R i).srt
  /-- The overlapped subterm. -/
  u : Term S V (R j).srt
  /-- A most general unifier of the renamed subterm and the renamed left-hand side of `j`. -/
  μ : Term.Subst S (Both V) (Both V)
  fill_eq : C.fill u = (R i).lhs
  nonvar : ∀ x, u ≠ .var x
  mgu : Term.IsMGU μ (Term.subst renameL u) (Term.subst renameR (R j).lhs)

/-- The left term of the critical pair of an overlap: contract the rule `i` at the root. -/
def Overlap.left {R : TRS S V ι} (O : Overlap R) : Term S (Both V) (R O.i).srt :=
  Term.subst O.μ (Term.subst renameL (R O.i).rhs)

/-- The right term of the critical pair of an overlap: contract the rule `j` at the hole. -/
def Overlap.right {R : TRS S V ι} (O : Overlap R) : Term S (Both V) (R O.i).srt :=
  Term.subst O.μ ((O.C.subst renameL).fill (Term.subst renameR (R O.j).rhs))

/-- The critical pairs of `R` are joinable. -/
def CriticalPairsJoinable (R : TRS S V ι) : Prop :=
  ∀ O : Overlap R, Relation.Join (Steps (W := Both V) R (R O.i).srt) O.left O.right

/-- **The critical pair lemma.** An unconditional rewrite system whose critical pairs are joinable
is locally confluent on the terms over every variable family, and conversely a system that is
locally confluent on the terms over `Both V` has joinable critical pairs. -/
def CriticalPairLemma (R : TRS S V ι) : Prop :=
  Unconditional R →
    (CriticalPairsJoinable R → ∀ W, LocallyConfluent R W) ∧
    (LocallyConfluent R (Both V) → CriticalPairsJoinable R)

end MercLib.Rewriting
