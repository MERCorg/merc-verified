import MercLib.Theory.LDD.Ldd
import MercLib.Algorithms.LDD.SetOperations
import MercLib.Algorithms.LDD.Cube
import MercLib.Algorithms.LDD.Relational
import MercLib.Algorithms.LDD.Reachability

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

/-! ## Adding one vector -/

/-- **The singleton is correct.** For every vector `x`, `Ldd.singleton x` is a well-formed LDD whose
height is the length of `x`, and it represents the set containing only `x`. See `SingletonCorrect`
(`Algorithms/LDD/Cube.lean`). -/
theorem singletonCorrect (x : List α) : SingletonCorrect x := sorry

/-- **Adding one vector is correct.** If `X` is a well-formed LDD of height `n` and the vector `x`
has length `n`, then `Ldd.unionCube X x` is a well-formed LDD of height `n` that represents the set
of `X` with `x` added. See `UnionCubeCorrect` (`Algorithms/LDD/Cube.lean`). -/
theorem unionCubeCorrect (X : Ldd α) (x : List α) (n : ℕ) : UnionCubeCorrect X x n := sorry

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

/-! ## Reachability -/

/-- **Breadth-first search is correct.** If every event of `E` is well-formed for vectors of length
`n` (`Event.WellFormed`: it accesses positions below `n` only, and its relation is a well-formed LDD
of the matching height), `X` is a well-formed LDD of height `n`, and only finitely many vectors are
reachable from those of `X`, then breadth-first search `Ldd.bfs E X` returns a well-formed LDD of
height `n` that represents the vectors reachable from those of `X` with the events of `E`. See
`BfsCorrect` (`Algorithms/LDD/Reachability.lean`). -/
theorem bfsCorrect (E : List (Event α)) (X : Ldd α) (n : ℕ) : BfsCorrect E X n := sorry

/-- **Breadth-first search terminates.** Under the hypotheses of `bfsCorrect` except finiteness, a
round of breadth-first search from a well-formed LDD `S` of height `n` between `X` and the vectors
reachable from `X` either changes nothing, which stops the loop, or yields a strictly larger set of
vectors reachable from `X`. See `BfsTerminates` (`Algorithms/LDD/Reachability.lean`). -/
theorem bfsTerminates (E : List (Event α)) (X : Ldd α) (n : ℕ) : BfsTerminates E X n := sorry

/-- **Chaining is correct.** Under the hypotheses of `bfsCorrect`, chaining `Ldd.chaining E X`
returns a well-formed LDD of height `n` that represents the vectors reachable from those of `X`.
See `ChainingCorrect` (`Algorithms/LDD/Reachability.lean`). -/
theorem chainingCorrect (E : List (Event α)) (X : Ldd α) (n : ℕ) : ChainingCorrect E X n := sorry

/-- **Chaining terminates.** As `bfsTerminates`, for a round of chaining. See
`ChainingTerminates` (`Algorithms/LDD/Reachability.lean`). -/
theorem chainingTerminates (E : List (Event α)) (X : Ldd α) (n : ℕ) : ChainingTerminates E X n :=
  sorry

/-- **Recursive saturation is correct.** If every event of `E` is well-formed for vectors of length
`n`, `p ≤ n`, `X` is a well-formed LDD of height `n - p` (the vectors from position `p` on), and only
finitely many vectors are reachable from those of `X` with the events whose `top` is at least `p`,
then the recursive saturation `Ldd.saturate E n p X` is a well-formed LDD of height `n - p` that
represents exactly those reachable vectors. With `p = 0` these are the reachable vectors. See
`SaturateCorrect` (`Algorithms/LDD/Reachability.lean`). -/
theorem saturateCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) : SaturateCorrect E n p X :=
  sorry

/-- **Recursive saturation terminates.** Under the hypotheses of `saturateCorrect` with `p < n`, a
round of the loop of the recursive saturation of `X` at `p`, from a well-formed `S` of height
`n - p` between `X` and its reachable vectors in which firing the events at `p` changes `S`, ends in
a strictly larger set of vectors reachable from `X`. See `SaturateTerminates`
(`Algorithms/LDD/Reachability.lean`). -/
theorem saturateTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateTerminates E n p X :=
  sorry

/-- **Node-wise saturation is correct.** Under the hypotheses of `saturateCorrect`, the node-wise
saturation `Ldd.saturateNodewise E n p X`, which fires the events at `p` value by value from a
frontier, is a well-formed LDD of height `n - p` that represents the vectors reachable from those of
`X` with the events whose `top` is at least `p`. See `SaturateNodewiseCorrect`
(`Algorithms/LDD/Reachability.lean`). -/
theorem saturateNodewiseCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateNodewiseCorrect E n p X :=
  sorry

/-- **Node-wise saturation terminates.** Under the hypotheses of `saturateCorrect` with `p < n`,
firing out of the first value of a non-empty frontier `F`, from a well-formed `S` of height `n - p`
between `X` and its reachable vectors, either leaves `S` unchanged and only removes that value from
the frontier, or yields a strictly larger set of vectors reachable from `X`. See
`SaturateNodewiseTerminates` (`Algorithms/LDD/Reachability.lean`). -/
theorem saturateNodewiseTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateNodewiseTerminates E n p X :=
  sorry

/-- **REACH is correct.** Under the hypotheses of `saturateCorrect`, REACH `Ldd.reach E n p X` is a
well-formed LDD of height `n - p` that represents the vectors reachable from those of `X` with the
events whose `top` is at least `p`. Below each value `v` at position `p`, REACH continues with the
events below `p` and with the diagonals for `v` of the events at `p` (`Event.diag`: their
transitions that keep the value `v`). See `ReachCorrect` (`Algorithms/LDD/Reachability.lean`). -/
theorem reachCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) : ReachCorrect E n p X := sorry

/-- **REACH terminates.** Under the hypotheses of `saturateCorrect` with `p < n`, a round of REACH
of `X` at `p` from a well-formed `S` of height `n - p` between `X` and its reachable vectors either
changes nothing, which stops the loop, or yields a strictly larger set of vectors reachable from
`X`. See `ReachTerminates` (`Algorithms/LDD/Reachability.lean`). -/
theorem reachTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) : ReachTerminates E n p X :=
  sorry

end MercLib.LDD
