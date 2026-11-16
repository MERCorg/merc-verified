module

public import MercLib.Algorithms.LDD.SetOperations

@[expose] public section

/-!
# Adding one vector to a list decision diagram

The singleton LDD of a vector, and the union of an LDD with one vector, as computed by
`singleton_at` and `union_cube` of oxidd's `oxidd-rules-ldd`. `union_cube` only visits the path of
the vector, so learning can add every transition it finds directly to a relation.

See [List decision diagrams](https://mercorg.github.io/merc-website/model-checking/symbolic/ldd/#set-operations)
(the page does not describe `union_cube` yet).

**Modelling choices**
* The implementation passes the values of a spine that are smaller than the first value of the
  vector with a loop and rebuilds them afterwards; the recursion here builds the same nodes.
* When the vector is already in the set, the implementation returns the set itself; the recursion
  here rebuilds the same nodes, which by canonicity is the same LDD.

## Main definitions

- `Ldd.singleton`: the LDD of one vector.
- `Ldd.unionCube`: the union of an LDD with one vector.

## Main statements

- `SingletonCorrect`: the singleton of a vector of length `n` is well-formed of height `n` and
  represents just that vector.
- `UnionCubeCorrect`: the union of a well-formed LDD of height `n` with a vector of length `n` is
  well-formed of height `n` and represents the set with that vector added.
-/

namespace MercLib.LDD

namespace Ldd

variable {α : Type*} [LinearOrder α]

/-- The LDD that represents only the vector `x`. -/
def singleton : List α → Ldd α
  | [] => one
  | a :: x => node a (singleton x) zero

/-- The union of `X` with the vector `x`, which has the length of the vectors of `X`. -/
def unionCube : Ldd α → List α → Ldd α
  | _, [] => one
  | node v d r, a :: x =>
    if v < a then node v d (unionCube r (a :: x))
    else if v = a then node v (unionCube d x) r
    else node a (singleton x) (node v d r)
  | X, a :: x => node a (singleton x) X

end Ldd

open Ldd

variable {α : Type*} [LinearOrder α]

/-- Contract: the singleton of a vector `x` is well-formed of the height of `x` and represents only
    `x`. -/
def SingletonCorrect (x : List α) : Prop :=
  (singleton x).WellFormed x.length ∧ (singleton x).denote = {x}

/-- Contract: the union of a well-formed `X` of height `n` with a vector `x` of length `n` is
    well-formed of height `n` and represents the set of `X` with `x` added. -/
def UnionCubeCorrect (X : Ldd α) (x : List α) (n : ℕ) : Prop :=
  X.WellFormed n → x.length = n →
    (unionCube X x).WellFormed n ∧ (unionCube X x).denote = insert x X.denote

end MercLib.LDD
