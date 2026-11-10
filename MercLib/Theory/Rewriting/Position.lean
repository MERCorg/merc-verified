module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Lattice

@[expose] public section

/-!
# Positions in terms

Positions are finite sequences of positive natural numbers, as in Section 2 and Definition 1 of
[R. Erkens and J. F. Groote, *A Set Automaton to Locate All Pattern Matches in a Term*][Erkens2021].

## Main definitions

- `Position`: a position; the empty list is the root and `p ++ q` is the concatenation `p.q`.
- `Position.Below`: `p ≤ q` iff `p = q.q'` for some `q'`.
- `Position.Comparable`: `p ≤ q` or `q ≤ p`.
- `Position.gcp`: the greatest common prefix of a finite set of positions.
-/

namespace MercLib.SetAutomaton

/-- A position: a list of positive natural numbers. -/
abbrev Position := List ℕ

namespace Position

/-- Position `p` is below position `q`: `p = q.q'` for some `q'` (Definition 1). -/
def Below (p q : Position) : Prop := q <+: p

instance : DecidableRel Below := fun p q => inferInstanceAs (Decidable (q <+: p))

/-- Two positions are comparable if one is below the other. -/
def Comparable (p q : Position) : Prop := Below p q ∨ Below q p

/-- The longest common prefix of two positions, the join `p ∨ q` of Definition 1. -/
def lcp : Position → Position → Position
  | a :: p, b :: q => if a = b then a :: lcp p q else []
  | _, _ => []

/-- The greatest common prefix of a finite set of positions (the root for the empty set). -/
def gcp (P : Finset Position) : Position :=
  match P.sort (· ≤ ·) with
  | [] => []
  | p :: ps => ps.foldl lcp p

end Position

end MercLib.SetAutomaton
