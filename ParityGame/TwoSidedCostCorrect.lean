module

public import ParityGame.TwoSidedCost
public import ParityGame.TwoSidedAlgorithm

@[expose] public section TwoSidedCostCorrect

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean

/-!
# Functional correctness of the computable two-sided lifting solver

`ParityGame.TwoSidedCost` defines a computable solver `solve G fuel` for games `PGame n` and
proves cost bounds only. This file states that the winners it returns (when it does not run out
of fuel) are exactly the winning regions of the corresponding library game (`PGame.toGame`,
max-parity, `Game.Wins` as in `ParityGame.TwoSidedAlgorithm`), together with the main
intermediate claims of the proof.

## Interpretation of the program's objects
* `PGame.toGame`: owners `false ↦ 0`, `true ↦ 1` (`toPlayer`), edges = successor lists,
  priorities unchanged. The library requires a total edge relation, so the game must have no dead
  ends (`PGame.Total`); the solver is only claimed correct for such games.
* A lifter context `c : Ctx n` is player `toPlayer c.p`'s view of the subgame `c.X` of alive
  vertices: `Ctx.game c` is `Game.forPlayer` of the library game (the dual game for Odd, matching
  `Ctx.prio` and `Ctx.mine`).
* A program value `some x` (a list of `(component index, counter)` pairs) is interpreted as the
  interleaved tuple `tup x = (k₀, c₀, k₁, c₁, …)` (zero beyond the list), the format of the
  library chain tree (`ParityGame.TwoSidedLifting`); `none` is `⊤`.
* The program numbers sibling components by least vertex: `Ctx.nb c R q` is the list of child
  regions that the program's `children` computes for the region `R` at odd level `q`. The
  library chain tree is used with this numbering (`Game.IsChainLeafBy`).

## Headlines
`SolveCorrect`: if `solve G fuel` returns `some w`, then `w v` is the winner of `v`.
`SolveTerminates`: with fuel `≥ fuelBound G = (n + 2) ^ (4 d + 6)` the solver returns winners.
Intermediate claims: `LevelsCorrect`, `ChildrenComplete`, `ChainBoundDominates`, `ProgSound`,
`ProgLeast` (tree navigation against the library chain tree with the program's numbering),
`AttractorComputesAttr`, and `LiftingCorrect` (one player's lifting with acceleration reaches
exactly its winning region when its queue empties; certified sets are progress-measure
domains).
-/

variable {n : ℕ}

/-- The library player of a program owner bit (`false` = Even = player `0`). -/
def toPlayer : Bool → Player
  | false => .zero
  | true => .one

/-- The game has no dead ends (required by the library's total games). -/
def PGame.Total (G : PGame n) : Prop := ∀ v, G.succ v ≠ []

/-- The library game of a program game without dead ends. -/
def PGame.toGame (G : PGame n) (h : G.Total) : Game (Fin n) where
  owner v := toPlayer (G.owner v)
  edge v w := w ∈ G.succ v
  prio := G.prio
  total v := ⟨(G.succ v).head (h v), List.head_mem _⟩

/-- A program vertex set as a set. -/
def VSet.toSet (S : VSet n) : Set (Fin n) := {v | S v = true}

/-- The alive vertices of a lifter context: the current subgame. -/
def Ctx.X (c : Ctx n) : Set (Fin n) := c.alive.toSet

/-- The lifting player's view of the game: the library game for `toPlayer c.p` (the dual game
    for Odd). -/
def Ctx.game (c : Ctx n) (h : c.G.Total) : Game (Fin n) :=
  (c.G.toGame h).forPlayer (toPlayer c.p)

/-- The interleaved tuple `(k₀, c₀, k₁, c₁, …)` of a list of pairs (zero beyond the list). -/
def tup (x : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  if i % 2 = 0 then (x.getD (i / 2) (0, 0)).1 else (x.getD (i / 2) (0, 0)).2

open scoped Classical in
/-- The program's numbering of child regions: the region list computed by `children` for the
    region `R` at odd level `q` (by least vertex, `[∅]` if there are no components). -/
noncomputable def Ctx.nb (c : Ctx n) (R : Set (Fin n)) (q : ℕ) : List (Set (Fin n)) :=
  ((children { c with levels := [q], levels_le := by simp } 0
    (fun v => decide (v ∈ R))).ret).map VSet.toSet

/-- The levels of a context are those `mkLevels` computes for its player and alive vertices
    (true for every lifter created by `mkLifter`). -/
def Ctx.LevelsOK (c : Ctx n) : Prop := c.levels = (mkLevels c.G c.p c.alive).ret.1

/-! ## Intermediate claims -/

/-- Contract (levels): the program's levels are the library's odd levels of the alive subgame,
    and `depthOf` is the library's truncation depth `Game.levelDepth`. -/
def LevelsCorrect (c : Ctx n) (h : c.G.Total) : Prop :=
  c.LevelsOK → c.height = (c.game h).height c.X ∧ (∀ l, c.level l = (c.game h).level c.X l) ∧
    ∀ v, depthOf c v = (c.game h).levelDepth c.X ((c.game h).prio v)

/-- Contract (numbering): the child lists computed by the program (`Ctx.nb`, components by least
    vertex) contain every weakly connected component of every region of alive vertices. -/
def ChildrenComplete (c : Ctx n) (h : c.G.Total) : Prop := (c.game h).CompNumbering c.X c.nb

/-- Contract (chain bound): the program's bound (longest path through the SCC condensation,
    weighted by priority-`q` counts) is at least the library's `Game.chainBound`, for every
    region of alive vertices. -/
def ChainBoundDominates (c : Ctx n) (h : c.G.Total) : Prop :=
  ∀ R : VSet n, (∀ v, R v = true → c.alive v = true) → ∀ q,
    (c.game h).chainBound R.toSet q ≤ (chainBound c R q).ret

/-- Contract (`prog` is sound): its result progresses from the target at the depth of `v`
    (compared on the interleaved tuples), strictly for odd priorities. -/
def ProgSound (c : Ctx n) : Prop :=
  ∀ v x r, (prog c v (some x)).ret = some r → c.height ≤ x.length →
    LexLE (2 * depthOf c v) (tup x) (tup r) ∧
      (c.prio v % 2 = 1 → ¬ LexLE (2 * depthOf c v) (tup r) (tup x))

/-- Contract (`prog` is least for the chain tree): if the chain leaf `aw` progresses to the chain
    leaf `av` at `v` (leaves for the program's numbering), then `prog` of any value below `aw`
    is a value below `av`. -/
def ProgLeast (c : Ctx n) (h : c.G.Total) : Prop :=
  c.LevelsOK → ∀ v (aw av : ℕ → ℕ), (c.game h).IsChainLeafBy c.X c.nb av →
    LexLE (2 * depthOf c v) aw av → (c.prio v % 2 = 1 → ¬ LexLE (2 * depthOf c v) av aw) →
    ∀ x, x.length = c.height → LexLE (2 * c.height) (tup x) aw →
      ∃ r, (prog c v (some x)).ret = some r ∧ ∀ m, LexLE m (tup r) av

/-- Contract (attractor): on a subgame, the program's attractor is the library's `Game.attr`
    (of the target restricted to the alive vertices). -/
def AttractorComputesAttr (G : PGame n) (h : G.Total) : Prop :=
  ∀ alive player target, (G.toGame h).IsSubgame alive.toSet →
    (attractor G alive player target).ret.toSet =
      (G.toGame h).attr alive.toSet (toPlayer player) (alive.toSet ∩ target.toSet)

/-- Contract (lifting, one player on one subgame): there is an invariant of the lifter states,
    holding initially and preserved by `run` (lifts with acceleration), such that `run` reports an
    empty queue only when it is empty, an empty queue means the alive vertices with a proper value
    are exactly player `toPlayer p`'s winning region of the subgame, and the certified set is
    always the domain of a progress measure of that player. -/
def LiftingCorrect (G : PGame n) (h : G.Total) (alive : VSet n) (p : Bool) : Prop :=
  (G.toGame h).IsSubgame alive.toSet →
  ∃ Inv : LState n → Prop, Inv (mkLifter G alive p).ret.2 ∧
    (∀ budget fuel st, Inv st → Inv (run (mkLifter G alive p).ret.1 budget fuel st).ret.1) ∧
    (∀ budget fuel st, Inv st → (run (mkLifter G alive p).ret.1 budget fuel st).ret.2.1 = true →
      (run (mkLifter G alive p).ret.1 budget fuel st).ret.1.queue = []) ∧
    (∀ st, Inv st → st.queue = [] → ∀ v, alive v = true →
      ((st.measure v).isSome ↔ (G.toGame h).Wins alive.toSet (toPlayer p) v)) ∧
    (∀ st, Inv st → ∃ (C : Codomain (ℕ → ℕ)) (μ : Fin n → ℕ → ℕ) (σ : Strategy (Fin n)),
      ((G.toGame h).forPlayer (toPlayer p)).IsProgressMeasure alive.toSet C
        (certified (mkLifter G alive p).ret.1 st).ret.toSet μ σ)

/-! ## Headline -/

/-- Contract (headline): for a game without dead ends, whenever the solver returns winners
    (`some w`, i.e. it did not run out of fuel), `w v` names the player winning from `v` in the
    whole library game. -/
def SolveCorrect (G : PGame n) (fuel : ℕ) : Prop :=
  ∀ (h : G.Total) (w : VSet n), (solve G fuel).ret.winner = some w →
    ∀ v i, toPlayer (w v) = i ↔ (G.toGame h).Wins Set.univ i v

/-- An explicit (exponential) fuel bound, `(n + 2) ^ (4 d + 6)`: it bounds the number of
    iterations of one `run` call and the number of rounds of one restart (the steps of a restart
    are bounded by the number of program values, `≤ n · (n (n + 1) + 1) ^ (2 (d + 1))`). -/
def fuelBound (G : PGame n) : ℕ := (n + 2) ^ (4 * G.d + 6)

/-- Contract (fuel suffices): with fuel at least `fuelBound G` the solver returns winners (for
    every game, with or without dead ends). -/
def SolveTerminates (G : PGame n) (fuel : ℕ) : Prop :=
  fuelBound G ≤ fuel → (solve G fuel).ret.winner.isSome

end ParityGame.TwoSidedCost

end TwoSidedCostCorrect
