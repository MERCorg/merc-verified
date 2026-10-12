import ParityGame.TwoSidedCostCorrect
import ParityGame.Proofs.TwoSidedCostCorrect_Proofs

open ParityGame ParityGame.TwoSidedCost Cslib.Algorithms.Lean

-- Contract pin: fails to compile if `solveCorrect`'s signature drifts: for a game without dead
-- ends, if the solver returns `some w` (it did not run out of fuel), then `w v` names exactly the
-- player who wins from `v` in the whole library game (`false` = player 0 = Even).
example {n : ℕ} (G : PGame n) (fuel : ℕ) :
    ∀ (h : ∀ v, G.succ v ≠ []) (w : Fin n → Bool), (solve G fuel).ret.winner = some w →
      ∀ v i, (match w v with | false => Player.zero | true => Player.one) = i ↔
        ∃ σ, (G.toGame h).WinsFrom Set.univ i σ v :=
  solveCorrect G fuel

-- Contract pin: fails to compile if `solveTerminates`' signature drifts: with fuel at least
-- `(n + 2) ^ (4 d + 6)` (`d` = greatest priority + 1) the solver returns winners.
example {n : ℕ} (G : PGame n) (fuel : ℕ) :
    (n + 2) ^ (4 * G.d + 6) ≤ fuel → (solve G fuel).ret.winner.isSome :=
  solveTerminates G fuel

-- Contract pin: the library game of a program game: owners via `toPlayer`, edges = successor
-- lists, priorities unchanged.
example {n : ℕ} (G : PGame n) (h : G.Total) (v w : Fin n) :
    (G.toGame h).owner v = (match G.owner v with | false => Player.zero | true => Player.one) ∧
      ((G.toGame h).edge v w ↔ w ∈ G.succ v) ∧ (G.toGame h).prio v = G.prio v :=
  ⟨rfl, Iff.rfl, rfl⟩

-- Contract pin: a lifter context's game is `Game.forPlayer` of the library game.
example {n : ℕ} (c : Ctx n) (h : c.G.Total) :
    c.game h = (c.G.toGame h).forPlayer (toPlayer c.p) ∧ c.X = {v | c.alive v = true} :=
  ⟨rfl, rfl⟩

-- Contract pin: fails to compile if `liftingCorrect`'s signature drifts: on a subgame, some
-- invariant of the lifter states holds initially and is preserved by `run`; `run` reports an
-- empty queue only when it is empty; with an empty queue the alive vertices with a proper value
-- are exactly the lifting player's winning region; the certified set is always a progress-measure
-- domain of the lifting player.
example {n : ℕ} (G : PGame n) (h : G.Total) (alive : VSet n) (p : Bool) :
    (G.toGame h).IsSubgame {v | alive v = true} →
    ∃ Inv : LState n → Prop, Inv (mkLifter G alive p).ret.2 ∧
      (∀ budget fuel st, Inv st → Inv (run (mkLifter G alive p).ret.1 budget fuel st).ret.1) ∧
      (∀ budget fuel st, Inv st → (run (mkLifter G alive p).ret.1 budget fuel st).ret.2.1 = true →
        (run (mkLifter G alive p).ret.1 budget fuel st).ret.1.queue = []) ∧
      (∀ st, Inv st → st.queue = [] → ∀ v, alive v = true →
        ((st.measure v).isSome ↔ ∃ σ, (G.toGame h).WinsFrom {v | alive v = true} (toPlayer p) σ v)) ∧
      (∀ st, Inv st → ∃ (C : Codomain (ℕ → ℕ)) (μ : Fin n → ℕ → ℕ) (σ : Fin n → Fin n),
        ((G.toGame h).forPlayer (toPlayer p)).IsProgressMeasure {v | alive v = true} C
          {v | (certified (mkLifter G alive p).ret.1 st).ret v = true} μ σ) :=
  liftingCorrect G h alive p

-- Contract pin: fails to compile if `attractorComputesAttr`'s signature drifts: on a subgame the
-- program's attractor is `Game.attr` of the alive part of the target.
example {n : ℕ} (G : PGame n) (h : G.Total) (alive : VSet n) (player : Bool) (target : VSet n) :
    (G.toGame h).IsSubgame {v | alive v = true} →
    {v | (attractor G alive player target).ret v = true} =
      (G.toGame h).attr {v | alive v = true} (toPlayer player)
        ({v | alive v = true} ∩ {v | target v = true}) :=
  attractorComputesAttr G h alive player target

-- Contract pin: fails to compile if `levelsCorrect`'s signature drifts: the program's levels are
-- the library's odd levels and `depthOf` is the library's truncation depth.
example {n : ℕ} (c : Ctx n) (h : c.G.Total) :
    c.levels = (mkLevels c.G c.p c.alive).ret.1 →
    c.height = (c.game h).height c.X ∧ (∀ l, c.level l = (c.game h).level c.X l) ∧
      ∀ v, depthOf c v = (c.game h).levelDepth c.X ((c.game h).prio v) :=
  levelsCorrect c h

-- Contract pin: fails to compile if `childrenComplete`'s signature drifts: the program's child
-- lists contain every component of every region of alive vertices.
example {n : ℕ} (c : Ctx n) (h : c.G.Total) :
    ∀ R ⊆ c.X, ∀ q, ∀ K ∈ (c.game h).lowComps R q, K ∈ c.nb R q :=
  childrenComplete c h

-- Contract pin: fails to compile if `chainBoundDominates`'s signature drifts: the program's chain
-- bound is at least the library's on every region of alive vertices.
example {n : ℕ} (c : Ctx n) (h : c.G.Total) :
    ∀ R : VSet n, (∀ v, R v = true → c.alive v = true) → ∀ q,
      (c.game h).chainBound {v | R v = true} q ≤ (chainBound c R q).ret :=
  chainBoundDominates c h

-- Contract pin: fails to compile if `progSound`'s signature drifts.
example {n : ℕ} (c : Ctx n) :
    ∀ v x r, (prog c v (some x)).ret = some r → c.height ≤ x.length →
      LexLE (2 * depthOf c v) (tup x) (tup r) ∧
        (c.prio v % 2 = 1 → ¬ LexLE (2 * depthOf c v) (tup r) (tup x)) :=
  progSound c

-- Contract pin: fails to compile if `progLeast`'s signature drifts.
example {n : ℕ} (c : Ctx n) (h : c.G.Total) :
    c.levels = (mkLevels c.G c.p c.alive).ret.1 →
    ∀ v (aw av : ℕ → ℕ), (c.game h).IsChainLeafBy c.X c.nb av →
      LexLE (2 * depthOf c v) aw av → (c.prio v % 2 = 1 → ¬ LexLE (2 * depthOf c v) av aw) →
      ∀ x, x.length = c.height → LexLE (2 * c.height) (tup x) aw →
        ∃ r, (prog c v (some x)).ret = some r ∧ ∀ m, LexLE m (tup r) av :=
  progLeast c h
