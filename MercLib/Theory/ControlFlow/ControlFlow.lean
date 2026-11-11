module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Control flow graphs of predicate formulae

The control flow graphs of [J. J. A. Keiren, W. Wesselink and T. A. C. Willemse, *Improved Static
Analysis for Parameterised Boolean Equation Systems using Control Flow Reconstruction*][Keiren2014]
(Section 4), as they are used to prune the summands of an LPS during exploration: a predicate variable
instance (PVI) without an edge from the current location does not influence the truth of the formula,
so it can be replaced by `false`. This is Lemma 2 of that paper, restricted to the `source` part of a
unicity constraint, which is the only part that decides whether an edge exists.

The proof of Lemma 2 in [Keiren2014] uses two facts that the paper does not state:

1. A location is a vector of ground terms, and an edge requires `source(X, i, k) = v_k` as terms
   (Definitions 12 and 19), while the unicity constraint only says that the parameter has the *value*
   of `source(X, i, k)` (Definition 7). Lemma 2 needs that distinct terms in a location have distinct
   values; `syntacticPruningUnsound` shows that it fails otherwise.
2. A control flow parameter `d_k` must not be bound by a quantifier in the formula: `source` is a
   statement about the variable `d_k` *at the position of the PVI*, which is the bound variable there.
   The assumption of the paper that a bound variable does not also occur free does not exclude this;
   `shadowedPruningUnsound` shows that Lemma 2 fails under that assumption.

There is no page on the merc website for this theory yet.

## Main definitions

- `DataLanguage`: data terms with an interpretation, equality and `false` (Section 2).
- `Formula`, `Formula.eval`: predicate formulae and their semantics (Definition 1).
- `Formula.npred`, `Formula.replace`, `Formula.pviAt`: the PVIs of a formula, `ϕ[i ↦ ψ]` and
  `PVI(ϕ, i)` (Definition 6).
- `IsSource`: the `source` clause of a unicity constraint (Definition 7).
- `SemanticEdge`, `SyntacticEdge`: whether a PVI has an edge from a location (Definitions 12 and 19),
  comparing values or terms.

## Main statements

- `PruningSound`: a PVI without a semantic edge can be replaced by `false`.
- `SyntacticPruningSound`: the same for syntactic edges, when distinct terms have distinct values.
- `SyntacticPruningUnsound`: syntactic edges are unsound without that assumption.
- `ShadowedPruningUnsound`: pruning is unsound when a quantifier binds a control flow parameter.

## References

- [Keiren2014]
-/

namespace MercLib.ControlFlow

/-- The data language of [Keiren2014] (Section 2): terms over data variables with an interpretation
in a semantic domain, a term `x = y` for every two terms, and the term `false`. All sorts share one
domain, which suffices for the theory of control flow graphs. -/
structure DataLanguage where
  /-- Data variables. -/
  Var : Type
  /-- Data terms. -/
  Term : Type
  /-- The semantic domain. -/
  Val : Type
  /-- Equality of variables is decidable, to update environments. -/
  decEqVar : DecidableEq Var
  /-- The value of a term in a data environment. -/
  eval : (Var → Val) → Term → Val
  /-- A boolean term holds in a data environment. -/
  Holds : (Var → Val) → Term → Prop
  /-- The variable as a term. -/
  var : Var → Term
  /-- The term `x = y`. -/
  eq : Term → Term → Term
  /-- The term `false`. -/
  ff : Term
  /-- The variable occurs in the term. -/
  Occurs : Var → Term → Prop
  /-- The term is ground: no variable occurs in it. -/
  Ground : Term → Prop
  eval_var : ∀ δ x, eval δ (var x) = δ x
  holds_eq : ∀ δ x y, Holds δ (eq x y) ↔ eval δ x = eval δ y
  holds_ff : ∀ δ, ¬ Holds δ ff
  eval_ground : ∀ t, Ground t → ∀ δ δ', eval δ t = eval δ' t

instance (L : DataLanguage) : DecidableEq L.Var := L.decEqVar

variable {L : DataLanguage} {P : Type}

/-- Predicate formulae over the data language `L` and predicate variables `P` (Definition 1). -/
inductive Formula (L : DataLanguage) (P : Type) where
  /-- A boolean data term. -/
  | data (b : L.Term)
  /-- A predicate variable instance `X(e)`. -/
  | pvi (X : P) (e : List L.Term)
  /-- Conjunction. -/
  | and (φ ψ : Formula L P)
  /-- Disjunction. -/
  | or (φ ψ : Formula L P)
  /-- Universal quantification. -/
  | all (d : L.Var) (φ : Formula L P)
  /-- Existential quantification. -/
  | ex (d : L.Var) (φ : Formula L P)

namespace Formula

/-- The truth of a formula in a predicate environment `η` and a data environment `δ`. -/
def eval (η : P → List L.Val → Prop) : (L.Var → L.Val) → Formula L P → Prop
  | δ, .data b => L.Holds δ b
  | δ, .pvi X e => η X (e.map (L.eval δ))
  | δ, .and φ ψ => eval η δ φ ∧ eval η δ ψ
  | δ, .or φ ψ => eval η δ φ ∨ eval η δ ψ
  | δ, .all d φ => ∀ v, eval η (Function.update δ d v) φ
  | δ, .ex d φ => ∃ v, eval η (Function.update δ d v) φ

/-- The number of PVIs of a formula, `npred(ϕ)`. -/
def npred : Formula L P → ℕ
  | .data _ => 0
  | .pvi _ _ => 1
  | .and φ ψ => npred φ + npred ψ
  | .or φ ψ => npred φ + npred ψ
  | .all _ φ => npred φ
  | .ex _ φ => npred φ

/-- `ϕ[i ↦ ψ]`: the PVI at position `i` replaced by `ψ`, counting from `0` (Definition 6). -/
def replace : Formula L P → ℕ → Formula L P → Formula L P
  | .data b, _, _ => .data b
  | .pvi X e, i, ψ => if i = 0 then ψ else .pvi X e
  | .and φ₁ φ₂, i, ψ =>
    if i < npred φ₁ then .and (replace φ₁ i ψ) φ₂ else .and φ₁ (replace φ₂ (i - npred φ₁) ψ)
  | .or φ₁ φ₂, i, ψ =>
    if i < npred φ₁ then .or (replace φ₁ i ψ) φ₂ else .or φ₁ (replace φ₂ (i - npred φ₁) ψ)
  | .all d φ, i, ψ => .all d (replace φ i ψ)
  | .ex d φ, i, ψ => .ex d (replace φ i ψ)

/-- `PVI(ϕ, i)`: the PVI at position `i`, counting from `0`, if there is one. -/
def pviAt : Formula L P → ℕ → Option (Formula L P)
  | .data _, _ => none
  | .pvi X e, i => if i = 0 then some (.pvi X e) else none
  | .and φ₁ φ₂, i => if i < npred φ₁ then pviAt φ₁ i else pviAt φ₂ (i - npred φ₁)
  | .or φ₁ φ₂, i => if i < npred φ₁ then pviAt φ₁ i else pviAt φ₂ (i - npred φ₁)
  | .all _ φ, i => pviAt φ i
  | .ex _ φ, i => pviAt φ i

/-- A quantifier in the formula binds the variable `d`. -/
def Binds (d : L.Var) : Formula L P → Prop
  | .data _ => False
  | .pvi _ _ => False
  | .and φ ψ => Binds d φ ∨ Binds d ψ
  | .or φ ψ => Binds d φ ∨ Binds d ψ
  | .all x φ => x = d ∨ Binds d φ
  | .ex x φ => x = d ∨ Binds d φ

/-- The variable `d` occurs free in the formula. -/
def FreeIn (d : L.Var) : Formula L P → Prop
  | .data b => L.Occurs d b
  | .pvi _ e => ∃ t ∈ e, L.Occurs d t
  | .and φ ψ => FreeIn d φ ∨ FreeIn d ψ
  | .or φ ψ => FreeIn d φ ∨ FreeIn d ψ
  | .all x φ => x ≠ d ∧ FreeIn d φ
  | .ex x φ => x ≠ d ∧ FreeIn d φ

end Formula

/-- The assumption of [Keiren2014] (Section 2) that a variable bound by a quantifier in `φ` does not
also occur free in `φ`. -/
def BoundNotFree (φ : Formula L P) : Prop := ∀ d, φ.Binds d → ¬ φ.FreeIn d

/-- `source(X, i, d) = e` is part of a unicity constraint for `φ` (Definition 7): `e` is ground, and
`φ` is equivalent to `φ[i ↦ (d = e ∧ PVI(φ, i))]`. -/
def IsSource (φ : Formula L P) (i : ℕ) (d : L.Var) (e : L.Term) : Prop :=
  L.Ground e ∧ ∃ χ, φ.pviAt i = some χ ∧
    ∀ (η : P → List L.Val → Prop) (δ : L.Var → L.Val),
      (φ.eval η δ ↔ (φ.replace i (.and (.data (L.eq (L.var d) e)) χ)).eval η δ)

/-- In the data environment `δ`, every control flow parameter `c k` has the value of the source
`s k` of the PVI, where it has one: the PVI has an edge from the location given by `δ`. -/
def SemanticEdge {m : ℕ} (c : Fin m → L.Var) (s : Fin m → Option L.Term) (δ : L.Var → L.Val) :
    Prop :=
  ∀ k e, s k = some e → δ (c k) = L.eval δ e

/-- The PVI has an edge from the location `v`, a ground term for every control flow parameter,
compared as terms as in Definitions 12 and 19 of [Keiren2014]: every source is the term of `v`. -/
def SyntacticEdge {m : ℕ} (s : Fin m → Option L.Term) (v : Fin m → L.Term) : Prop :=
  ∀ k e, s k = some e → e = v k

/-- **Pruning is sound.** Let `s k` be the source of the PVI at position `i` of `φ` for the control
flow parameter `c k`, where defined, and let no quantifier of `φ` bind a control flow parameter. In
every data environment in which the PVI has no semantic edge, `φ` is equivalent to `φ` with that PVI
replaced by `false`. -/
def PruningSound {m : ℕ} (φ : Formula L P) (i : ℕ) (c : Fin m → L.Var) (s : Fin m → Option L.Term) :
    Prop :=
  (∀ k e, s k = some e → IsSource φ i (c k) e) → (∀ k, ¬ φ.Binds (c k)) →
    ∀ (η : P → List L.Val → Prop) (δ : L.Var → L.Val), ¬ SemanticEdge c s δ →
      (φ.eval η δ ↔ (φ.replace i (.data L.ff)).eval η δ)

/-- **Pruning with syntactic edges is sound for distinct values.** Under the assumptions of
`PruningSound`, let `δ` give every control flow parameter `c k` the value of the term `v k`, and let
every source that has the value of `v k` be the term `v k`. If the PVI has no syntactic edge from `v`,
then `φ` is equivalent to `φ` with that PVI replaced by `false` in `δ`. -/
def SyntacticPruningSound {m : ℕ} (φ : Formula L P) (i : ℕ) (c : Fin m → L.Var)
    (s : Fin m → Option L.Term) (v : Fin m → L.Term) : Prop :=
  (∀ k e, s k = some e → IsSource φ i (c k) e) → (∀ k, ¬ φ.Binds (c k)) →
    ∀ (η : P → List L.Val → Prop) (δ : L.Var → L.Val), (∀ k, δ (c k) = L.eval δ (v k)) →
      (∀ k e, s k = some e → L.eval δ e = L.eval δ (v k) → e = v k) →
      ¬ SyntacticEdge s v → (φ.eval η δ ↔ (φ.replace i (.data L.ff)).eval η δ)

/-- **Pruning with syntactic edges is unsound for equal values.** There is a formula with a PVI whose
source for the control flow parameter `d` is `e`, in which no quantifier binds `d`, a ground term `v`
other than `e` with the same value, and environments in which `d` has the value of `v`, such that the
PVI has no syntactic edge from `v` but replacing it by `false` changes the truth of the formula. -/
def SyntacticPruningUnsound : Prop :=
  ∃ (L : DataLanguage) (P : Type) (φ : Formula L P) (i : ℕ) (d : L.Var) (e v : L.Term)
    (η : P → List L.Val → Prop) (δ : L.Var → L.Val),
    IsSource φ i d e ∧ ¬ φ.Binds d ∧ L.Ground v ∧ δ d = L.eval δ v ∧ e ≠ v ∧
      ¬ (φ.eval η δ ↔ (φ.replace i (.data L.ff)).eval η δ)

/-- **Pruning is unsound when a quantifier binds a control flow parameter.** There is a formula in
which no bound variable occurs free, with a PVI whose source for `d` is `e`, and environments in
which `d` does not have the value of `e`, such that replacing the PVI by `false` changes the truth of
the formula. A quantifier of the formula then binds `d`. -/
def ShadowedPruningUnsound : Prop :=
  ∃ (L : DataLanguage) (P : Type) (φ : Formula L P) (i : ℕ) (d : L.Var) (e : L.Term)
    (η : P → List L.Val → Prop) (δ : L.Var → L.Val),
    IsSource φ i d e ∧ BoundNotFree φ ∧ δ d ≠ L.eval δ e ∧
      ¬ (φ.eval η δ ↔ (φ.replace i (.data L.ff)).eval η δ)

end MercLib.ControlFlow
