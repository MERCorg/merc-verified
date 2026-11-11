module

public import MercLib.Algorithms.LDD.SetOperations

@[expose] public section

/-!
# Projection and relational successors on list decision diagrams

The projection of a set of vectors onto a subset of the positions, and the successors of a set of
vectors under a sparse relation, as computed by `apply_project` and `apply_relational_successors`
of oxidd's `oxidd-rules-ldd`. Both are guided per position by a *meta* description: for a
projection, whether a position is kept; for a relation, whether a position is skipped, read,
written, or both read and written. The relation only stores the positions it reads or writes.

See [Relations on LDDs](https://mercorg.github.io/merc-website/model-checking/symbolic/ldd-relations/).

**Modelling choices**
* The meta description is a list of `Bool` or `Access` values. The implementation encodes it as a
  singleton meta-LDD so that it can be part of an operation-cache key, and splits a read-and-write
  position into two meta levels, the *read half* and the *write half*.
* The recursion through the spine of a node is factored into the spine combinators `mapSpine`,
  `unionSpine`, `matchSpine` and `joinSpine`; a call on a down child drops the first meta entry,
  a call on a right child keeps it, as in the implementation.

## Main definitions

- `select`: the projection of one vector.
- `Access`, `Access.width`, `relWidth`: the access kinds of a relation, and the length of its
  vectors.
- `Apply`: a relation vector takes a source vector to a target vector.
- `Ldd.project`, `Ldd.successors`.

## Main statements

- `ProjectCorrect`: the projection of a well-formed LDD is well-formed and represents the image
  under `select`.
- `SuccessorsCorrect`: the successors of a well-formed LDD under a well-formed relation are
  well-formed and represent the relational image.
-/

namespace MercLib.LDD

variable {α : Type*}

/-- The projection of a vector onto the positions `i` with `m[i] = true`. Positions beyond the
    length of `m` are dropped. -/
def select : List Bool → List α → List α
  | true :: m, a :: x => a :: select m x
  | false :: m, _ :: x => select m x
  | _, _ => []

/-- How a relation accesses one position of the vectors. -/
inductive Access where
  /-- The position is neither read nor written; it is copied. -/
  | skip
  /-- The position is read; it is copied. -/
  | read
  /-- The position is written; its old value is ignored. -/
  | write
  /-- The position is read and written. -/
  | readWrite
  deriving DecidableEq, Repr

/-- The number of entries a position takes in a relation vector. -/
def Access.width : Access → ℕ
  | skip => 0
  | read => 1
  | write => 1
  | readWrite => 2

/-- The length of the relation vectors for the meta description `m`. -/
def relWidth (m : List Access) : ℕ := (m.map Access.width).sum

/-- `Apply m t x y`: under the meta description `m`, the relation vector `t` takes `x` to `y`.
    A read position of `x` must equal the read value of `t`, a written position of `y` is the
    written value of `t`, and every other position, including those beyond the length of `m`,
    is copied from `x`. -/
def Apply : List Access → List α → List α → List α → Prop
  | [], [], x, y => y = x
  | .skip :: m, t, a :: x, b :: y => b = a ∧ Apply m t x y
  | .read :: m, c :: t, a :: x, b :: y => a = c ∧ b = a ∧ Apply m t x y
  | .write :: m, c :: t, _ :: x, b :: y => b = c ∧ Apply m t x y
  | .readWrite :: m, c :: c' :: t, a :: x, b :: y => a = c ∧ b = c' ∧ Apply m t x y
  | _, _, _, _ => False

namespace Ldd

variable [LinearOrder α]

/-- Replaces every down child `d` on the spine by `f d`, and drops the values whose new down
    child is `zero`. -/
def mapSpine (f : Ldd α → Ldd α) : Ldd α → Ldd α
  | node v d r => mk v (f d) (mapSpine f r)
  | _ => zero

/-- The union of `f d` over the down children `d` on the spine. -/
def unionSpine (f : Ldd α → Ldd α) : Ldd α → Ldd α
  | node _ d r => union (unionSpine f r) (f d)
  | _ => zero

/-- Merges two spines and keeps the values on both, with down child `f d e`. -/
def matchSpine (f : Ldd α → Ldd α → Ldd α) : Ldd α → Ldd α → Ldd α
  | node v d r, node w e s =>
    if v < w then matchSpine f r (node w e s)
    else if w < v then matchSpine f (node v d r) s
    else mk v (f d e) (matchSpine f r s)
  | _, _ => zero
termination_by a b => sizeOf a + sizeOf b

/-- Merges two spines and takes the union of `f d e` over the values on both. -/
def joinSpine (f : Ldd α → Ldd α → Ldd α) : Ldd α → Ldd α → Ldd α
  | node v d r, node w e s =>
    if v < w then joinSpine f r (node w e s)
    else if w < v then joinSpine f (node v d r) s
    else union (f d e) (joinSpine f r s)
  | _, _ => zero
termination_by a b => sizeOf a + sizeOf b

/-- The projection of `X` onto the positions `i` with `m[i] = true`. A dropped position takes the
    union of the projections of its down children. -/
def project : List Bool → Ldd α → Ldd α
  | [], X => match X with
    | zero => zero
    | _ => one
  | true :: m, X => mapSpine (project m) X
  | false :: m, X => unionSpine (project m) X

/-- The successors of `X` under the relation `R` with meta description `m`.

* `skip`: keep each value of `X`.
* `read`: keep the values of `X` that `R` reads.
* `write`: take the union of the down children of `X` once, and continue it below every value
  that `R` writes.
* `readWrite`: for each value of `X` that `R` reads, continue below every value that `R` writes
  for it; the results for different read values can share written values, so they are united.

When `m` is exhausted the rest of `X` is copied, unless `R` is empty. -/
def successors : List Access → Ldd α → Ldd α → Ldd α
  | [], X, R => match R with
    | zero => zero
    | _ => X
  | .skip :: m, X, R => mapSpine (fun d => successors m d R) X
  | .read :: m, X, R => matchSpine (fun d e => successors m d e) X R
  | .write :: m, X, R => mapSpine (fun e => successors m (unionSpine id X) e) R
  | .readWrite :: m, X, R =>
    joinSpine (fun d e => mapSpine (fun e' => successors m d e') e) X R

end Ldd

open Ldd

variable [LinearOrder α]

/-- Contract: for a well-formed `X` of height `n` and a projection description `m` no longer than
    `n`, the projection is well-formed of height `m.count true` and represents the image of `X`
    under `select m`. -/
def ProjectCorrect (m : List Bool) (X : Ldd α) (n : ℕ) : Prop :=
  m.length ≤ n → X.WellFormed n →
    (project m X).WellFormed (m.count true) ∧ (project m X).denote = select m '' X.denote

/-- Contract: for a well-formed `X` of height `n`, a meta description `m` no longer than `n`, and
    a well-formed relation `R` of height `relWidth m`, the successors are well-formed of height `n`
    and represent the vectors `y` with `Apply m t x y` for some `x` in `X` and `t` in `R`. -/
def SuccessorsCorrect (m : List Access) (X R : Ldd α) (n : ℕ) : Prop :=
  m.length ≤ n → X.WellFormed n → R.WellFormed (relWidth m) →
    (successors m X R).WellFormed n ∧
      (successors m X R).denote = {y | ∃ x ∈ X.denote, ∃ t ∈ R.denote, Apply m t x y}

end MercLib.LDD
