module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Defs.LinearOrder

@[expose] public section

/-!
# List decision diagrams

A list decision diagram (LDD) represents a set of vectors (lists) over a linearly ordered type of
values ([S.C.C. Blom and J.C. van de Pol, *Symbolic reachability for process algebras with
recursive data types*][Blom2008], ICTAC 2008). merc uses the LDDs of oxidd's
`oxidd-rules-ldd`, which are *quasi-reduced*: every position of a vector has a node on every
path, so a value absent from a spine means "not in the set", never "don't care".

The diagram is modelled as a tree; the sharing and the unique table of the implementation do not
change the represented set.

See [List decision diagrams](https://mercorg.github.io/merc-website/model-checking/symbolic/ldd/#definitions).

## Main definitions

- `Ldd`: the terminals `zero` (the empty set) and `one` (the set containing the empty vector),
  and the inner node `node v d r` with value `v`, down child `d` and right child `r`.
- `Ldd.denote`: the set of vectors an LDD represents.
- `Ldd.WellFormed`: the LDD is ordered, has no node with a `zero` down child, and represents
  vectors of length `n` only.

## Main statements

- `Canonical`: two well-formed LDDs of the same height that represent the same set are equal.
- `Complete`: every finite set of vectors of length `n` is represented by a well-formed LDD of
  height `n`.

## References

- [S.C.C. Blom and J.C. van de Pol, *Symbolic reachability for process algebras with recursive
  data types*][Blom2008]
-/

namespace MercLib.LDD

/-- A list decision diagram over values of type `α`. -/
inductive Ldd (α : Type*) where
  /-- The terminal representing the empty set (`Empty` in oxidd). -/
  | zero : Ldd α
  /-- The terminal representing the set containing only the empty vector (`True` in oxidd). -/
  | one : Ldd α
  /-- The inner node with value `v`, down child `d` and right child `r`. -/
  | node (v : α) (d r : Ldd α) : Ldd α
  deriving DecidableEq, Repr

namespace Ldd

variable {α : Type*}

/-- The set of vectors represented by an LDD: `node v d r` represents the vectors `v :: x` with
    `x` represented by `d`, together with the vectors represented by `r`. -/
def denote : Ldd α → Set (List α)
  | zero => ∅
  | one => {[]}
  | node v d r => (List.cons v '' denote d) ∪ denote r

/-- The value of the first node on the spine of `r`, if there is one, is greater than `v`. -/
def HeadAbove [LT α] (v : α) : Ldd α → Prop
  | node w _ _ => v < w
  | _ => True

/-- `a` is a well-formed LDD of height `n`: the values on every spine are strictly increasing,
    no inner node has the down child `zero`, and every path from the root to `one` passes `n`
    inner nodes along down edges (quasi-reducedness). The terminal `zero` has every height. -/
def WellFormed [LT α] : Ldd α → ℕ → Prop
  | zero, _ => True
  | one, n => n = 0
  | node _ _ _, 0 => False
  | node v d r, n + 1 => d ≠ zero ∧ WellFormed d n ∧ WellFormed r (n + 1) ∧ HeadAbove v r

end Ldd

variable (α : Type*) [LinearOrder α]

/-- Contract (canonicity): two well-formed LDDs of the same height that represent the same set of
    vectors are equal. So set equality of LDDs is equality of their (shared) roots. -/
def Canonical : Prop :=
  ∀ (n : ℕ) (a b : Ldd α), a.WellFormed n → b.WellFormed n → a.denote = b.denote → a = b

/-- Contract (completeness): every finite set of vectors of length `n` is represented by a
    well-formed LDD of height `n`. -/
def Complete : Prop :=
  ∀ (n : ℕ) (S : Set (List α)), S.Finite → (∀ x ∈ S, x.length = n) →
    ∃ a : Ldd α, a.WellFormed n ∧ a.denote = S

end MercLib.LDD
