module

public import MercLib.Theory.LDD.Ldd

@[expose] public section

/-!
# Set operations on list decision diagrams

The union, intersection and difference of two LDDs of the same height, as computed by
`apply_union`, `apply_intersection` and `apply_difference` of oxidd's `oxidd-rules-ldd`. Each
walks the two spines in lockstep like a merge of two sorted lists, and recurses into the down
children when both spines carry the same value.

See [List decision diagrams](https://mercorg.github.io/merc-website/model-checking/symbolic/ldd/#set-operations).

**Modelling choices**
* The diagrams are trees (see `Theory/LDD/Ldd.lean`). The implementation's operation cache and
  its shortcut for equal operands (`a ∪ a = a`, which is pointer equality there) do not change
  the result for well-formed operands, by canonicity, and are left out.
* A `zero` terminal against a `one` terminal, or a terminal against an inner node, only happens for
  operands of different heights, which the specifications exclude.

## Main definitions

- `Ldd.mk`: the node `node v d r`, or `r` if `d` is `zero`.
- `Ldd.union`, `Ldd.inter`, `Ldd.diff`.

## Main statements

- `UnionCorrect`, `InterCorrect`, `DiffCorrect`: for well-formed operands of height `n`, the
  result is well-formed of height `n` and represents the union, intersection or difference.
-/

namespace MercLib.LDD

namespace Ldd

variable {α : Type*} [LinearOrder α]

/-- The node `node v d r`, or `r` when `d = zero`, so that no node has an empty down child. -/
def mk (v : α) (d r : Ldd α) : Ldd α :=
  match d with
  | zero => r
  | _ => node v d r

/-- The union of two LDDs of the same height. -/
def union : Ldd α → Ldd α → Ldd α
  | zero, b => b
  | a, zero => a
  | one, _ => one
  | node v d r, one => node v d r
  | node v d r, node w e s =>
    if v < w then node v d (union r (node w e s))
    else if w < v then node w e (union (node v d r) s)
    else node v (union d e) (union r s)
termination_by a b => sizeOf a + sizeOf b

/-- The intersection of two LDDs of the same height. -/
def inter : Ldd α → Ldd α → Ldd α
  | zero, _ => zero
  | _, zero => zero
  | one, one => one
  | one, node _ _ _ => zero
  | node _ _ _, one => zero
  | node v d r, node w e s =>
    if v < w then inter r (node w e s)
    else if w < v then inter (node v d r) s
    else mk v (inter d e) (inter r s)
termination_by a b => sizeOf a + sizeOf b

/-- The difference of two LDDs of the same height. -/
def diff : Ldd α → Ldd α → Ldd α
  | zero, _ => zero
  | a, zero => a
  | one, one => zero
  | one, node _ _ _ => one
  | node v d r, one => node v d r
  | node v d r, node w e s =>
    if v < w then node v d (diff r (node w e s))
    else if w < v then diff (node v d r) s
    else mk v (diff d e) (diff r s)
termination_by a b => sizeOf a + sizeOf b

end Ldd

open Ldd

variable {α : Type*} [LinearOrder α]

/-- Contract: the union of two well-formed LDDs of height `n` is well-formed of height `n` and
    represents the union of their sets. -/
def UnionCorrect (a b : Ldd α) (n : ℕ) : Prop :=
  a.WellFormed n → b.WellFormed n →
    (union a b).WellFormed n ∧ (union a b).denote = a.denote ∪ b.denote

/-- Contract: the intersection of two well-formed LDDs of height `n` is well-formed of height `n`
    and represents the intersection of their sets. -/
def InterCorrect (a b : Ldd α) (n : ℕ) : Prop :=
  a.WellFormed n → b.WellFormed n →
    (inter a b).WellFormed n ∧ (inter a b).denote = a.denote ∩ b.denote

/-- Contract: the difference of two well-formed LDDs of height `n` is well-formed of height `n`
    and represents the difference of their sets. -/
def DiffCorrect (a b : Ldd α) (n : ℕ) : Prop :=
  a.WellFormed n → b.WellFormed n →
    (diff a b).WellFormed n ∧ (diff a b).denote = a.denote \ b.denote

end MercLib.LDD
