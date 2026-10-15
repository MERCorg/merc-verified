module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Basic
public import Mathlib.Basic.Finite.Defs

@[expose] public section

namespace MercLib.Graph

/-!
# Strongly connected components

SCCs of a graph given by an arbitrary edge relation `E : V → V → Prop`, taken inside a subset `X`
of the vertices: reachability only uses edges between vertices of `X` (Section 3.1 of
[O. Friedmann and M. Lange, *Solving Parity Games in Practice*][Friedmann2009], ATVA 2009, takes the
SCCs of a subgame in this way).

They are specified mathematically (not by an algorithm, see `Graph/Tarjan.lean` for that):
`IsSCC E X C` says `C` is a maximal strongly connected subset of `X`, and `IsFinalSCC` that no edge
of `X` leaves it.
-/

variable {V : Type*}

/-- Reachability inside `X`. -/
def Reach (E : V → V → Prop) (X : Set V) : V → V → Prop :=
  Relation.ReflTransGen fun a b => a ∈ X ∧ b ∈ X ∧ E a b

/-- `C` is a (maximal) strongly connected component of `X`. -/
def IsSCC (E : V → V → Prop) (X C : Set V) : Prop :=
  C.Nonempty ∧ C ⊆ X ∧ (∀ u ∈ C, ∀ v ∈ C, Reach E X u v) ∧
    ∀ u ∈ C, ∀ w ∈ X, Reach E X u w → Reach E X w u → w ∈ C

/-- `C` is a final SCC of `X`: no edge of `X` leaves `C`. -/
def IsFinalSCC (E : V → V → Prop) (X C : Set V) : Prop :=
  IsSCC E X C ∧ ∀ v ∈ C, ∀ w ∈ X, E v w → w ∈ C

open scoped Classical in
/-- Some final SCC of `X` (the empty set if there is none, which never happens for a non-empty
    subset of a finite graph, see `Graph.exists_isFinalSCC`). -/
noncomputable def finalSCC (E : V → V → Prop) (X : Set V) : Set V :=
  if h : ∃ C, IsFinalSCC E X C then h.choose else ∅

/-- Contract: every non-empty subset of a finite graph has a final SCC (the SCC decomposition
    always has a bottom component). -/
def FinalSCCExists (E : V → V → Prop) [Finite V] (X : Set V) : Prop :=
  X.Nonempty → ∃ C, IsFinalSCC E X C

end MercLib.Graph
