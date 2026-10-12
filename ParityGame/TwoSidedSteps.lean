module

public import ParityGame.TwoSidedCost

@[expose] public section TwoSidedSteps

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean

/-!
# A step bound for the computable two-sided lifting solver: polynomial for fixed `d`

`ParityGame.TwoSidedCost` bounds the running time of `solve G fuel` by
`(steps + n + 1) · costPoly N`. This file states an explicit bound on `steps` itself, for every
game and every fuel: `steps ≤ stepsBound G = (n + 2) ^ (4 d + 7)`. Hence the solver runs in
polynomial time for every fixed bound on the number of priorities `d`.

The bound comes from the rank argument of the termination proof
(`ParityGame.Proofs.TwoSidedCostCorrect_Fuel_Proofs`): within one restart, every lift and every
accelerated raise strictly increases the base-`(n (n + 1) + 1)` rank of one vertex's value, so
each of the two lifters makes at most `n · (n (n + 1) + 1) ^ (2 (d + 1)) ≤ n · (n + 2) ^ (4 d + 4)`
steps; there are at most `n + 1` restarts, each with fresh lifters, and
`(n + 1) · 2 n ≤ (n + 2) ^ 3`.

## Headlines (proved in `ParityGame.Proofs.TwoSidedSteps_Proofs`)
`StepsBound`, `SolveTimeFixedPrio`, and `SolvePolyFixedPrio` (for every bound `D` on `d` there is
an exponent `k` with `time ≤ (n + m + 2) ^ k` for all games with `d ≤ D`).
-/

variable {n : ℕ}

/-- The explicit step bound `(n + 2) ^ (4 d + 7)`. -/
def stepsBound (G : PGame n) : ℕ := (n + 2) ^ (4 * G.d + 7)

/-- Contract (steps): for every game and every fuel, the solver makes at most `stepsBound G`
    steps (successful lifts plus accelerated raises, summed over all restarts). -/
def StepsBound (G : PGame n) (fuel : ℕ) : Prop :=
  (solve G fuel).ret.steps ≤ stepsBound G

/-- Contract (time, fixed number of priorities): for every game and every fuel, the running time
    is at most `(stepsBound G + n + 1) · costPoly N`, a polynomial in `N` for every fixed `d`. -/
def SolveTimeFixedPrio (G : PGame n) (fuel : ℕ) : Prop :=
  (solve G fuel).time ≤ (stepsBound G + n + 1) * costPoly G.size

/-- Contract (polynomial for fixed `d`): for every bound `D` on `d` there is an exponent `k` such
    that every game with `d ≤ D` is solved, for every fuel, within `(n + m + 2) ^ k` time. -/
def SolvePolyFixedPrio (D : ℕ) : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (G : PGame n) (fuel : ℕ), G.d ≤ D →
    (solve G fuel).time ≤ (n + G.m + 2) ^ k

end ParityGame.TwoSidedCost

end TwoSidedSteps
