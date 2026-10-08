module

public import Cslib.Foundations.Data.OmegaSequence.InfOcc
public import Mathlib.Logic.Relation

open Cslib (ωSequence)

@[expose] public section Defs

namespace ParityGame

/-!
# Parity games, plays, positional strategies and winning

Section 2 of O. Friedmann and M. Lange, *Solving Parity Games in Practice*, ATVA 2009.

A parity game is a total directed graph whose nodes are owned by player `0` or `1` and carry
natural-number priorities. Plays are infinite paths (`Cslib.ωSequence`); the winner of a play is
decided by the parity of the greatest priority occurring infinitely often (`Cslib.ωSequence.infOcc`).

**Modeling choices**
* The paper's subgames `G \ U` are not represented as new games. Instead every notion below is
  relative to a node set `X : Set V` (the current subgame); `IsSubgame` says the subgame is still
  total. Moves leaving `X` are simply not available.
* A positional strategy is a *total* function `V → V` (the paper uses partial functions); only its
  values on the nodes of the player it belongs to matter, and a strategy only has to behave well
  on the nodes it is claimed to win from (`WinsFrom`).
-/

/-- The two players. Player `zero` wins plays whose greatest recurring priority is even. -/
inductive Player where
  | zero
  | one
  deriving DecidableEq

/-- The opponent `1 - i`. -/
def Player.opp : Player → Player
  | .zero => .one
  | .one => .zero

/-- The player a priority favours: `0` for even, `1` for odd priorities. -/
def Player.ofPrio (n : ℕ) : Player := if n % 2 = 0 then .zero else .one

/-- A parity game `G = (V, V₀, V₁, E, Ω)`: `owner` partitions the nodes into `V₀` and `V₁`, `edge`
    is the edge relation (required to be total: every node has a successor) and `prio` is the
    priority function `Ω`. -/
structure Game (V : Type*) where
  owner : V → Player
  edge : V → V → Prop
  prio : V → ℕ
  total : ∀ v, ∃ w, edge v w

/-- A positional strategy (Section 2). Only the values at the owner's nodes are ever consulted. -/
abbrev Strategy (V : Type*) := V → V

variable {V : Type*}

/-- `X` is a subgame of `G`, i.e. the game restricted to `X` is still total. -/
def Game.IsSubgame (G : Game V) (X : Set V) : Prop :=
  ∀ v ∈ X, ∃ w ∈ X, G.edge v w

/-- One move inside the subgame `X` conforming to player `i`'s strategy `σ`: an edge between
    nodes of `X`, taking `σ` whenever `i` owns the source. -/
def Game.Step (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) (v w : V) : Prop :=
  v ∈ X ∧ w ∈ X ∧ G.edge v w ∧ (G.owner v = i → w = σ v)

/-- `p` is a play in `X` conforming to `σ` (for player `i`): every move is a `Step`. -/
def Game.ConformingPlay (G : Game V) (X : Set V) (i : Player) (σ : Strategy V)
    (p : ωSequence V) : Prop :=
  ∀ n, G.Step X i σ (p n) (p (n + 1))

/-- `n` is the greatest priority occurring infinitely often along the play `p`. -/
def Game.MaxInfPrio (G : Game V) (p : ωSequence V) (n : ℕ) : Prop :=
  n ∈ (p.map G.prio).infOcc ∧ ∀ m ∈ (p.map G.prio).infOcc, m ≤ n

/-- Player `i` wins the play `p`: the greatest priority occurring infinitely often along `p` has
    the parity favouring `i`. -/
def Game.PlayWonBy (G : Game V) (i : Player) (p : ωSequence V) : Prop :=
  ∃ n, G.MaxInfPrio p n ∧ Player.ofPrio n = i

/-- `σ` is a winning strategy for player `i` from `v` in the subgame `X`: every conforming play
    from `v` is won by `i`, and conforming play never gets stuck (without the latter the first
    clause would hold vacuously for a strategy that leaves `X` or follows a non-edge). -/
def Game.WinsFrom (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) (v : V) : Prop :=
  (∀ w, Relation.ReflTransGen (G.Step X i σ) v w → ∃ u, G.Step X i σ w u) ∧
  ∀ p : ωSequence V, p 0 = v → G.ConformingPlay X i σ p → G.PlayWonBy i p

/-- The output of a solver: the winning regions `W₀, W₁` and the winning strategies `σ₀, σ₁`. -/
structure Solution (V : Type*) where
  win : Player → Set V
  strat : Player → Strategy V

/-- `r` solves the subgame `X`: the winning regions partition `X` and each player's strategy wins
    from every node of that player's region. -/
def Game.Solves (G : Game V) (X : Set V) (r : Solution V) : Prop :=
  r.win .zero ∪ r.win .one = X ∧ Disjoint (r.win .zero) (r.win .one) ∧
  ∀ i, ∀ v ∈ r.win i, G.WinsFrom X i (r.strat i) v

/-- Sanity check on the winning condition: in a finite game every play has exactly one winner. -/
def Game.PlayHasUniqueWinner (G : Game V) [Finite V] : Prop :=
  ∀ p : ωSequence V, ∃! i, G.PlayWonBy i p

end ParityGame

end Defs
