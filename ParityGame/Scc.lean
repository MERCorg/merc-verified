module

public import ParityGame.Defs

@[expose] public section Scc

namespace ParityGame

/-!
# Strongly connected components

Section 3.1 of O. Friedmann and M. Lange, *Solving Parity Games in Practice*, ATVA 2009.

SCCs are taken inside the subgame `X`: reachability only uses edges between nodes of `X`. They are
specified mathematically (not by Tarjan's algorithm): `IsSCC X C` says `C` is a maximal
strongly connected subset of `X`, and `IsFinalSCC` that no edge of `X` leaves it.
-/

variable {V : Type*}

/-- Reachability inside the subgame `X`. -/
def Game.Reach (G : Game V) (X : Set V) : V → V → Prop :=
  Relation.ReflTransGen fun a b => a ∈ X ∧ b ∈ X ∧ G.edge a b

/-- `C` is a (maximal) strongly connected component of the subgame `X`. -/
def Game.IsSCC (G : Game V) (X C : Set V) : Prop :=
  C.Nonempty ∧ C ⊆ X ∧ (∀ u ∈ C, ∀ v ∈ C, G.Reach X u v) ∧
    ∀ u ∈ C, ∀ w ∈ X, G.Reach X u w → G.Reach X w u → w ∈ C

/-- `C` is a final SCC of `X`: no edge of `X` leaves `C`. -/
def Game.IsFinalSCC (G : Game V) (X C : Set V) : Prop :=
  G.IsSCC X C ∧ ∀ v ∈ C, ∀ w ∈ X, G.edge v w → w ∈ C

open scoped Classical in
/-- Some final SCC of `X` (the empty set if there is none, which never happens for a non-empty
    subgame of a finite game, see `Game.exists_isFinalSCC`). -/
noncomputable def Game.finalSCC (G : Game V) (X : Set V) : Set V :=
  if h : ∃ C, G.IsFinalSCC X C then h.choose else ∅

/-- Contract: every non-empty subgame of a finite game has a final SCC (the decomposition of
    Section 3.1 always has a bottom component). -/
def Game.FinalSCCExists (G : Game V) [Finite V] (X : Set V) : Prop :=
  X.Nonempty → ∃ C, G.IsFinalSCC X C

end ParityGame

end Scc
