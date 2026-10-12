import ParityGame.TwoSidedCost
import ParityGame.Proofs.TwoSidedCost_Proofs

open ParityGame.TwoSidedCost Cslib.Algorithms.Lean

-- Contract pin: fails to compile if `navigationCost`'s signature drifts: `leftmost` and value
-- comparison cost at most `N`, `nextNode` on a prefix of length `≤ h` at most `30 · N⁴`, `prog`
-- at most `32 · N⁴`.
example {n : ℕ} (c : Ctx n) :
    (∀ pre, (leftmost c pre).time ≤ c.N) ∧
    (∀ a b, (cmpVal c a b).time ≤ c.N) ∧
    (∀ pre, pre.length ≤ c.height → (nextNode c pre).time ≤ 30 * c.N ^ 4) ∧
    (∀ v t, (prog c v t).time ≤ 32 * c.N ^ 4) :=
  navigationCost c

-- Contract pin: fails to compile if `regionInfoCost`'s signature drifts: weak components
-- `≤ 9 · N³`, child regions `≤ 10 · N³`, chain bound `≤ 8 · N³`.
example {n : ℕ} (c : Ctx n) :
    (∀ S, (weakComponents c S).time ≤ 9 * c.N ^ 3) ∧
    (∀ l R, (children c l R).time ≤ 10 * c.N ^ 3) ∧
    (∀ R q, (chainBound c R q).time ≤ 8 * c.N ^ 3) :=
  regionInfoCost c

-- Contract pin: fails to compile if `evaluateCost`'s signature drifts: evaluating `v` costs at
-- most `(deg v + 1) · 35 · N⁴`.
example {n : ℕ} (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n)) :
    (evaluate c μ v allowed).time ≤ ((c.G.succ v).length + 1) * (35 * c.N ^ 4) :=
  evaluateCost c μ v allowed

-- Contract pin: fails to compile if `accelerateCost`'s signature drifts: one acceleration costs
-- at most `175 · N⁷` and adds at most `n + 1` queue entries per raised vertex.
example {n : ℕ} (c : Ctx n) (st : LState n) (v : Fin n) :
    (accelerate c st v).time ≤ 175 * c.N ^ 7 ∧
      (accelerate c st v).ret.1.queue.length ≤
        st.queue.length + (accelerate c st v).ret.2 * (n + 1) :=
  accelerateCost c st v

-- Contract pin: fails to compile if `liftingAmortised`'s signature drifts: with potential
-- `37 · N⁵ · |queue|`, the lifting loop costs at most `250 · N⁷` per step.
example {n : ℕ} (c : Ctx n) (B f : ℕ) (st : LState n) :
    (runLoop c B f st).time + 37 * c.N ^ 5 * (runLoop c B f st).ret.1.queue.length +
        250 * c.N ^ 7 * st.steps ≤
      37 * c.N ^ 5 * st.queue.length + 250 * c.N ^ 7 * (runLoop c B f st).ret.1.steps :=
  liftingAmortised c B f st

-- Contract pin: fails to compile if `certifiedCost`'s signature drifts: certification costs at
-- most `43 · N⁷`.
example {n : ℕ} (c : Ctx n) (st : LState n) : (certified c st).time ≤ 43 * c.N ^ 7 :=
  certifiedCost c st

-- Contract pin: fails to compile if `attractorCost`'s signature drifts: an attractor costs at
-- most `2 · N³`.
example {n : ℕ} (G : PGame n) (alive : VSet n) (player : Bool) (target : VSet n) :
    (attractor G alive player target).time ≤ 2 * G.size ^ 3 :=
  attractorCost G alive player target

-- Contract pin: fails to compile if `solveTimeBound`'s signature drifts: for every game and
-- fuel, time `≤ (steps + n + 1) · 340 · (n + m + d + 2)⁷`, and at most `n + 1` restarts.
example {n : ℕ} (G : PGame n) (fuel : ℕ) :
    (solve G fuel).time ≤
        ((solve G fuel).ret.steps + n + 1) * (340 * (n + G.m + G.d + 2) ^ 7) ∧
      (solve G fuel).ret.restarts ≤ n + 1 :=
  solveTimeBound G fuel

-- Contract pin: fails to compile if `solvePolyOfSteps`'s signature drifts: a bound `Q n` on the
-- steps gives time `≤ (Q n + n + 1) · 340 · (n + m + d + 2)⁷`.
example {n : ℕ} (G : PGame n) (fuel : ℕ) (Q : ℕ → ℕ) :
    (solve G fuel).ret.steps ≤ Q n →
      (solve G fuel).time ≤ (Q n + n + 1) * (340 * (n + G.m + G.d + 2) ^ 7) :=
  solvePolyOfSteps G fuel Q

-- Contract pin: fails to compile if `restartProgress`'s signature drifts: a restart on the alive
-- set of `s` that ends by removal (`Outcome.next s'`) strictly shrinks the alive set.
example {n : ℕ} (G : PGame n) (fuel rem f : ℕ) (s s' : SState n) (l0 l1 : LState n) :
    (roundLoop G rem fuel (mkLifter G s.alive false).ret.1 (mkLifter G s.alive true).ret.1 f s l0
      l1).ret = .next s' →
    s'.alive.count < s.alive.count :=
  restartProgress G fuel rem f s s' l0 l1

-- Contract pin: fails to compile if `outerFuelSuffices`'s signature drifts: if no restart runs
-- out of lifting/round fuel, the solver returns winners (the outer fuel `n + 1` suffices).
example {n : ℕ} (G : PGame n) (fuel : ℕ) :
    (∀ s s' : SState n, (roundLoop G s.alive.count fuel (mkLifter G s.alive false).ret.1
      (mkLifter G s.alive true).ret.1 fuel s (mkLifter G s.alive false).ret.2
      (mkLifter G s.alive true).ret.2).ret ≠ .oof s') →
    (solve G fuel).ret.winner.isSome :=
  outerFuelSuffices G fuel
