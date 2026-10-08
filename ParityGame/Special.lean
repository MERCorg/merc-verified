module

public import ParityGame.Defs
public import ParityGame.Attractor
public import ParityGame.Zielonka
public import ParityGame.Scc

@[expose] public section Special

namespace ParityGame

/-!
# Detection of special cases

Section 3.2 of O. Friedmann and M. Lange, *Solving Parity Games in Practice*, ATVA 2009: self-cycle
games, one-parity games and one-player games, each solved directly (without a backend).

**Modeling choices**
* Self-cycles: a node `v` with `vEv` is solved directly when taking the loop is *good* for its
  owner (`Ω(v) ≡₂ owner`), or when the loop is forced because it is the only move inside `X`.
  The paper additionally *removes* the bad loops from the graph; that only helps later phases and is
  not needed for correctness, so it is not modeled.
* One-player games are solved by the paper's recursion, written as an inductive relation
  `OnePlayerCore` (nondeterministic in the choice of sub-SCC): it finds a strongly connected
  `Y₀` whose greatest priority favours the player. If there is none, the other player wins
  everything (`onePlayerSolve`).
-/

variable {V : Type*}

/-- `v` is a self-cycle node that can be solved directly in `X` (Section 3.2). Its winner is the
    player favoured by `Ω(v)`. -/
def Game.IsSelfCycle (G : Game V) (X : Set V) (v : V) : Prop :=
  v ∈ X ∧ G.edge v v ∧ (G.owner v = Player.ofPrio (G.prio v) ∨ ∀ w ∈ X, G.edge v w → w = v)

/-- The solution of a self-cycle node: the favoured player wins `{v}` by looping. -/
def Game.selfCycleSolve (G : Game V) (v : V) : Solution V where
  win := fun p => if p = Player.ofPrio (G.prio v) then {v} else ∅
  strat := fun _ _ => v

/-- All nodes of `C` have priorities favouring player `i` (a one-parity game). -/
def Game.OneParity (G : Game V) (C : Set V) (i : Player) : Prop :=
  ∀ v ∈ C, Player.ofPrio (G.prio v) = i

/-- A one-parity game is won by the favoured player, with arbitrary moves. -/
noncomputable def Game.oneParitySolve (G : Game V) (C : Set V) (i : Player) : Solution V where
  win := fun p => if p = i then C else ∅
  strat := fun p v => if p = i then G.anyMove C v else v

/-- `C` is a one-player game for `i`: the opponent never has a choice (Section 3.2). -/
def Game.OnePlayer (G : Game V) (C : Set V) (i : Player) : Prop :=
  ∀ v ∈ C, G.owner v ≠ i → ∀ w ∈ C, ∀ w' ∈ C, G.edge v w → G.edge v w' → w = w'

/-- The paper's recursion for one-player games (Section 3.2): `OnePlayerCore i Y Y₀` says the
    search in `Y` ends with the strongly connected `Y₀`, in which `i` can reach nodes of the
    greatest priority (which favours `i`) forever.
    * If the greatest priority of `Y` favours `i`, `Y` itself is such a set (`Y` is a proper SCC).
    * Otherwise remove the attractor `A` of the greatest priority for the opponent, and recurse
      into an SCC of `Y \ A`. -/
inductive Game.OnePlayerCore (G : Game V) (i : Player) : Set V → Set V → Prop
  | base {Y : Set V} : Y.Nonempty → (∃ v ∈ Y, ∃ w ∈ Y, G.edge v w) →
      Player.ofPrio (G.maxPrio Y) = i → OnePlayerCore G i Y Y
  | step {Y D Y₀ : Set V} : Y.Nonempty → Player.ofPrio (G.maxPrio Y) ≠ i →
      G.IsSCC (Y \ G.attr Y i.opp {v | v ∈ Y ∧ G.prio v = G.maxPrio Y}) D →
      OnePlayerCore G i D Y₀ → OnePlayerCore G i Y Y₀

open scoped Classical in
/-- Solving a one-player game directly: `i` wins everything if the recursion finds a good
    strongly connected set `Y₀`, the strategy being the attractor strategy towards the greatest
    priority of `Y₀` inside `Y₀` and towards `Y₀` outside; otherwise the opponent wins everything. -/
noncomputable def Game.onePlayerSolve (G : Game V) (C : Set V) (i : Player) : Solution V :=
  if h : ∃ Y₀, G.OnePlayerCore i C Y₀ then
    { win := fun p => if p = i then C else ∅
      strat := fun p v =>
        if p = i then
          (if v ∈ h.choose then
            (if v ∈ {u | u ∈ h.choose ∧ G.prio u = G.maxPrio h.choose} then
              G.anyMove h.choose v
            else G.attrStrategy h.choose i {u | u ∈ h.choose ∧ G.prio u = G.maxPrio h.choose} v)
          else G.attrStrategy C i h.choose v)
        else v }
  else
    { win := fun p => if p = i.opp then C else ∅
      strat := fun p v => if p = i.opp then G.anyMove C v else v }

/-- Contract: a self-cycle node is won by the player its priority favours, by looping. -/
def Game.SelfCycleCorrect (G : Game V) (X : Set V) (v : V) : Prop :=
  G.IsSubgame X → G.IsSelfCycle X v →
    G.WinsFrom X (Player.ofPrio (G.prio v))
      ((G.selfCycleSolve v).strat (Player.ofPrio (G.prio v))) v

/-- Contract: a one-parity subgame is solved by `oneParitySolve`. -/
def Game.OneParitySolveCorrect (G : Game V) [Finite V] (C : Set V) (i : Player) : Prop :=
  G.IsSubgame C → G.OneParity C i → G.Solves C (G.oneParitySolve C i)

/-- Contract: a strongly connected one-player subgame is solved by `onePlayerSolve`. -/
def Game.OnePlayerSolveCorrect (G : Game V) [Finite V] (C : Set V) (i : Player) : Prop :=
  G.IsSubgame C → (∀ u ∈ C, ∀ v ∈ C, G.Reach C u v) → G.OnePlayer C i →
    G.Solves C (G.onePlayerSolve C i)

end ParityGame

end Special
