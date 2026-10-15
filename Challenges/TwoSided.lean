import MercLib.ParityGame.Game
import MercLib.ParityGame.Attractor
import MercLib.ParityGame.Zielonka
import MercLib.TwoSided.Certificate
import MercLib.TwoSided.Generic
import MercLib.TwoSided.Lifting
import MercLib.TwoSided.ProgressMeasure
import MercLib.TwoSided.Special
import MercLib.TwoSided.Transform
import MercLib.TwoSided.TwoSidedAlgorithm
import MercLib.TwoSided.TwoSidedCost
import MercLib.TwoSided.TwoSidedCostCorrect
import MercLib.TwoSided.TwoSidedLifting
import MercLib.TwoSided.TwoSidedSteps

/-!
# Comparator challenge: two-sided parity game solving (human-vetted)

The headline theorems of `MercLib/TwoSided/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`). Intermediate lemmas are not challenged.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.ParityGame

open Cslib

/-! ## Special cases (Section 3.2 of [Friedmann2009]) -/

/-- A self-cycle node is won by the player its priority favours, by looping. -/
theorem Game.selfCycleSolve_correct {V : Type*} (G : Game V) (X : Set V)
    (v : V) : G.SelfCycleCorrect X v := sorry

/-- A subgame in which all priorities have the same parity is solved by `oneParitySolve`. -/
theorem Game.oneParitySolve_correct {V : Type*} (G : Game V) [Finite V]
    (C : Set V) (i : Player) : G.OneParitySolveCorrect C i := sorry

/-- A strongly connected one-player subgame is solved by `onePlayerSolve`. -/
theorem Game.onePlayerSolve_correct {V : Type*} (G : Game V) [Finite V]
    (C : Set V) (i : Player) : G.OnePlayerSolveCorrect C i := sorry

/-! ## Priority compression and propagation (Sections 3.3 and 3.4 of [Friedmann2009]) -/

/-- Compressing the priorities occurring in `X` preserves the winner of every play in `X`. -/
theorem Game.compressionSound {V : Type*} (G : Game V) [Finite V]
    (X : Set V) : G.CompressionSound X := sorry

/-- Priority propagation preserves the winner of every play in `X`. -/
theorem Game.propagationSound {V : Type*} (G : Game V) [Finite V]
    (X : Set V) : G.PropagationSound X := sorry

/-! ## The generic solver (Section 3.5 of [Friedmann2009]) -/

/-- The generic solver with a sound backend solves every finite parity game. -/
theorem Game.genericSolve_correct {V : Type*} (G : Game V) [Finite V]
    (S : Backend V) : G.GenericCorrect S := sorry

/-- The generic solver with Zielonka's algorithm as backend solves every finite parity game. -/
theorem Game.genericSolve_zielonka_correct {V : Type*} (G : Game V)
    [Finite V] : G.Solves Set.univ (G.genericSolve zielonkaBackend) := sorry

/-! ## Progress measures -/

/-- Soundness of progress measures: in a finite game, a progress measure over any codomain
    certifies that its witnessing strategy wins for player `0` from every node of its domain. -/
theorem Game.progressMeasureSound {V : Type*} {M : Type*}
    [Finite V] (G : Game V) (X : Set V) (C : Codomain M) (D : Set V) (μ : V → M)
    (σ : Strategy V) : G.ProgressMeasureSound X C D μ σ := sorry

/-! ## Lifting -/

/-- For values complete for the subgame `X`, the lifting operator has a least fixpoint, and every
    least fixpoint is not `⊤` exactly at the nodes won by player `0` in `X`. -/
theorem Game.liftingLfpCorrect {V : Type*} {M : Type*}
    {T : Type*} [CompleteLinearOrder T] [Finite V] [WellFoundedLT T] (G : Game V) (X : Set V)
    (C : Codomain M) (val : T → M) : G.LiftingLfpCorrect X C val := sorry

/-- Lifting over the chain-tree leaves of `X` (plus `⊤`) has a least fixpoint, and every least
    fixpoint is not `⊤` exactly on player `0`'s winning region in `X`. -/
theorem Game.chainLiftingCorrect.{u_1, u_3} {V : Type u_1} {T : Type u_3}
    [Finite V] [CompleteLinearOrder T] [WellFoundedLT T] (G : Game V) (X : Set V)
    (C : Codomain (ℕ → ℕ)) (val : T → ℕ → ℕ) : G.ChainLiftingCorrect X C val := sorry

/-! ## Two-sided lifting -/

/-- Every run of removal steps from the initial state that ends in a completion step returns
    exactly the winning regions of the whole game. -/
theorem Game.twoSidedCorrect {V : Type*} [Finite V] (G : Game V) :
    G.TwoSidedCorrect := sorry

/-- Every run of removal steps from the initial state has at most `|V|` steps. -/
theorem Game.removalBound {V : Type*} [Finite V] (G : Game V) :
    G.RemovalBound := sorry

/-! ## Certificates -/

/-- A valid certificate determines both winning regions of the whole game. -/
theorem Game.certSound {V : Type*} [Finite V] (G : Game V)
    (c : Game.Cert V) : G.CertSound c := sorry

/-- Every finite game has a valid certificate of polynomial size. -/
theorem Game.certComplete {V : Type*} [Finite V] (G : Game V) :
    G.CertComplete := sorry

end MercLib.ParityGame

namespace MercLib.ParityGame.TwoSidedCost

open Cslib

/-! ## The computable solver -/

/-- For a game without dead ends, whenever the solver returns winners (it did not run out of
    fuel), they are the winners of the corresponding parity game. -/
theorem solveCorrect {n : ℕ} (G : PGame n) (fuel : ℕ) :
    SolveCorrect G fuel := sorry

/-- With fuel at least `fuelBound G` the solver returns winners. -/
theorem solveTerminates {n : ℕ} (G : PGame n) (fuel : ℕ) :
    SolveTerminates G fuel := sorry

/-- The running time is at most `(steps + n + 1) · costPoly N`, and the solver restarts at most
    `n + 1` times. -/
theorem solveTimeBound {n : ℕ} (G : PGame n) (fuel : ℕ) :
    SolveTimeBound G fuel := sorry

/-- If the number of lift steps is bounded by `Q n`, the running time is at most
    `(Q n + n + 1) · costPoly N`: the solver is polynomial whenever the number of steps is. -/
theorem solvePolyOfSteps {n : ℕ} (G : PGame n) (fuel : ℕ)
    (Q : ℕ → ℕ) : SolvePolyOfSteps G fuel Q := sorry

end MercLib.ParityGame.TwoSidedCost
