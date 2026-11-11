import MercLib.Algorithms.LDD.Relational

/-!
# Tests for `MercLib.Algorithms.LDD`

Runs the LDD operations on small sets of vectors and compares the result with the LDD built
directly from an independently computed list of vectors. By canonicity (`MercLib.LDD.canonical`),
two well-formed LDDs of the same height are equal exactly when they represent the same set, so
the comparison is structural equality.
-/

namespace MercLibTest.LDD

open MercLib.LDD MercLib.LDD.Ldd

/-- The LDD containing only `x`. -/
def single : List ℕ → Ldd ℕ
  | [] => one
  | a :: x => node a (single x) zero

/-- The LDD of a list of vectors of equal length, as a union of singletons. -/
def ofList (xs : List (List ℕ)) : Ldd ℕ := xs.foldl (fun acc x => union acc (single x)) zero

/-- The relation vector `t` applied to `x`, computed directly from the description. -/
def applyB : List Access → List ℕ → List ℕ → Option (List ℕ)
  | [], [], x => some x
  | .skip :: m, t, a :: x => (a :: ·) <$> applyB m t x
  | .read :: m, c :: t, a :: x => if a = c then (a :: ·) <$> applyB m t x else none
  | .write :: m, c :: t, _ :: x => (c :: ·) <$> applyB m t x
  | .readWrite :: m, c :: c' :: t, a :: x => if a = c then (c' :: ·) <$> applyB m t x else none
  | _, _, _ => none

def post (m : List Access) (X R : List (List ℕ)) : List (List ℕ) :=
  X.flatMap fun x => R.filterMap fun t => applyB m t x

def selectAll (m : List Bool) (X : List (List ℕ)) : List (List ℕ) := X.map (select m)

def A : List (List ℕ) := [[0, 1, 2], [0, 2, 2], [1, 0, 0], [3, 1, 2]]
def B : List (List ℕ) := [[0, 1, 2], [1, 0, 1], [3, 1, 2], [3, 3, 3]]

/-! ## Set operations -/

#guard union (ofList A) (ofList B) == ofList (A ++ B)
#guard inter (ofList A) (ofList B) == ofList (A.filter (· ∈ B))
#guard diff (ofList A) (ofList B) == ofList (A.filter (· ∉ B))
#guard diff (ofList A) (ofList A) == zero
#guard ofList (A ++ B) == ofList (B.reverse ++ A)

/-! ## Projection -/

#guard project [true, false, true] (ofList A) == ofList (selectAll [true, false, true] A)
#guard project [false, true] (ofList A) == ofList (selectAll [false, true] A)
#guard project [false, false, false] (ofList A) == one
#guard project [] (ofList A) == one
#guard project [true] (zero : Ldd ℕ) == zero

/-! ## Relational successors -/

def X : List (List ℕ) := [[0, 0, 5], [0, 1, 5], [1, 1, 6], [2, 0, 7]]

-- read and write position 0, copy the rest
def R₁ : List (List ℕ) := [[0, 1], [1, 0], [2, 1]]
#guard successors [.readWrite] (ofList X) (ofList R₁) == ofList (post [.readWrite] X R₁)

-- read position 0, write position 1, skip position 2
def R₂ : List (List ℕ) := [[0, 3], [0, 4], [2, 0]]
#guard successors [.read, .write, .skip] (ofList X) (ofList R₂) ==
  ofList (post [.read, .write, .skip] X R₂)

-- skip position 0, read and write position 1
def R₃ : List (List ℕ) := [[0, 1], [1, 0], [1, 1]]
#guard successors [.skip, .readWrite] (ofList X) (ofList R₃) ==
  ofList (post [.skip, .readWrite] X R₃)

-- write position 0 and read position 2
def R₄ : List (List ℕ) := [[9, 5], [8, 7], [4, 4]]
#guard successors [.write, .skip, .read] (ofList X) (ofList R₄) ==
  ofList (post [.write, .skip, .read] X R₄)

-- two read-and-write positions; different reads write the same value
def R₅ : List (List ℕ) := [[0, 2, 0, 0], [1, 2, 1, 0], [0, 2, 1, 1]]
#guard successors [.readWrite, .readWrite] (ofList X) (ofList R₅) ==
  ofList (post [.readWrite, .readWrite] X R₅)

-- the empty relation has no successors, the relation of the empty vector is the identity
#guard successors [] (ofList X) (zero : Ldd ℕ) == zero
#guard successors [.skip, .skip] (ofList X) one == ofList X

end MercLibTest.LDD
