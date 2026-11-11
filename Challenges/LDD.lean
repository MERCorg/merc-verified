import MercLib.Theory.LDD.Ldd
import MercLib.Algorithms.LDD.SetOperations
import MercLib.Algorithms.LDD.Relational

/-!
# Comparator challenge: list decision diagrams (human-vetted)

The headline theorems of `MercLib/Theory/LDD/` and `MercLib/Algorithms/LDD/`, stated with `sorry`
against the human-vetted spec files only; `lake comparator` checks them against the solution
module `MercLib` (see `Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.LDD

/-! ## List decision diagrams -/

/-- **LDDs are canonical.** For a linearly ordered type of values `α`, if `a` and `b` are
well-formed LDDs of the same height `n` (`Ldd.WellFormed`: strictly increasing values on every
spine, no inner node with the down child `zero`, every vector of length `n`) and they represent the
same set of vectors, then `a = b`. See `Canonical` (`Theory/LDD/Ldd.lean`). -/
theorem canonical (α : Type*) [LinearOrder α] : Canonical α := sorry

/-- **Every finite set of vectors is an LDD.** For a linearly ordered type of values `α`, every
finite set `S` of vectors that all have length `n` is represented by some well-formed LDD of
height `n`. With `canonical`, the well-formed LDDs of height `n` are in bijection with the finite
sets of vectors of length `n`. See `Complete` (`Theory/LDD/Ldd.lean`). -/
theorem complete (α : Type*) [LinearOrder α] : Complete α := sorry

/-! ## Set operations -/

variable {α : Type*} [LinearOrder α]

/-- **Union is correct.** If `a` and `b` are well-formed LDDs of height `n`, then `Ldd.union a b`
is a well-formed LDD of height `n` that represents the union of the sets of `a` and `b`. See
`UnionCorrect` (`Algorithms/LDD/SetOperations.lean`). -/
theorem unionCorrect (a b : Ldd α) (n : ℕ) : UnionCorrect a b n := sorry

/-- **Intersection is correct.** If `a` and `b` are well-formed LDDs of height `n`, then
`Ldd.inter a b` is a well-formed LDD of height `n` that represents the intersection of the sets of
`a` and `b`. See `InterCorrect` (`Algorithms/LDD/SetOperations.lean`). -/
theorem interCorrect (a b : Ldd α) (n : ℕ) : InterCorrect a b n := sorry

/-- **Difference is correct.** If `a` and `b` are well-formed LDDs of height `n`, then
`Ldd.diff a b` is a well-formed LDD of height `n` that represents the set of `a` minus the set of
`b`. See `DiffCorrect` (`Algorithms/LDD/SetOperations.lean`). -/
theorem diffCorrect (a b : Ldd α) (n : ℕ) : DiffCorrect a b n := sorry

/-! ## Projection and relational successors -/

/-- **Projection is correct.** If `X` is a well-formed LDD of height `n` and the projection
description `m` has at most `n` entries, then `Ldd.project m X` is a well-formed LDD whose height
is the number of `true` entries of `m`, and it represents the image of the set of `X` under
`select m` (keep position `i` iff `m[i] = true`, drop the positions beyond `m`). See
`ProjectCorrect` (`Algorithms/LDD/Relational.lean`). -/
theorem projectCorrect (m : List Bool) (X : Ldd α) (n : ℕ) : ProjectCorrect m X n := sorry

/-- **Relational successors are correct.** If `X` is a well-formed LDD of height `n`, the meta
description `m` has at most `n` entries, and `R` is a well-formed LDD of height `relWidth m` (one
entry per read and per written position), then `Ldd.successors m X R` is a well-formed LDD of
height `n` that represents the vectors `y` with `Apply m t x y` for some `x` in `X` and `t` in `R`:
`y` agrees with the read values of `t`, takes the written values of `t`, and copies `x` elsewhere.
See `SuccessorsCorrect` (`Algorithms/LDD/Relational.lean`). -/
theorem successorsCorrect (m : List Access) (X R : Ldd α) (n : ℕ) : SuccessorsCorrect m X R n :=
  sorry

end MercLib.LDD
