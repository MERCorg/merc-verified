# HybridSI

Hybrid strategy improvement for parity games: the rule H-B (Even's half of symmetric strategy
improvement with Odd at an exact best response), on the exact Vöge–Jurdziński valuation, built on
the library games of `MercLib.ParityGame`. The definitions it formalises are given at
[Strategy improvement](https://mercorg.github.io/merc-website/developer/parity/strategy-improvement/)
and
[Hybrid strategy improvement (H-B)](https://mercorg.github.io/merc-website/developer/parity/hybrid-strategy-improvement/).
General-k lemmas beyond what is listed below are not yet formalised.

All proof files compile without `sorry`, using only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Every headline is registered in `Basic.lean` and has a challenge in
`Challenges/HybridSI.lean`.

## The algorithm and its correctness (any game)

* `Valuation.lean`: the relevance order (`Game.Relabelled`) and play values as integer keys
  (`key`).
* `Algorithm.lean`: best responses (`respond`), one H-B iteration (`hbStep`) and the solver
  (`hbRun`). It is computable, following the `BestResponse` and `StrategyImprovement`
  pseudocode of the website pages linked above.
* `Correctness.lean`: `HBCorrect`, `HBTerminates` and `FilterNonempty` are proved.
  `HBPolyIterations` and `RespondPolyRounds` are the open targets. Experiments
  (`scripts/hybrid-si/`, family `E_k`) indicate that `HBPolyIterations` is false: from the
  initial profile, H-B takes about `2^(n/18)` iterations there (checked up to `n = 282`, not
  proved).
* `Epoch.lean`: `EpochBound`. An epoch (iterations with the same Odd response) has at most `n_E`
  iterations.
* `BestResponse.lean` and `AlgorithmPoly.lean`: a polynomial best response (cycle-maximum classes
  by reachability, Bellman–Ford inside classes), and H-B built on it in `TimeM`. The cost and
  correctness contracts are proved.

## Bounds along a run (any game)

These are the facts F1–F6 of the paper analysis, plus a decomposition into closed subgames.

* `Potential.lean` (`RunTrace`):
  - P2 (F1), the valuation is monotone;
  - P3, changes of cycle maxima (`n(n−1)` in total, `n−1` per vertex);
  - TOP, changes of the cycle maximum or of membership of the top vertex in `B` (the top-vertex
    split, website H-B Definition 9).
* `Bounds.lean`:
  - the saddle point, existence and uniqueness;
  - the sandwich `Ξ_k ≤ K° ≤ K*_j` (F2);
  - autonomy of closed subgames and O1.
* `Counting.lean`:
  - `EpochIterations`, at most `(E+1)·n_E` iterations;
  - `KStarBlock` (F6), constant `K*` lasts at most `n_E` iterations;
  - `KStarCount`, at most `C + n_E(C+1)` iterations, where `C` counts `K*` changes. A polynomial
    bound on `C` is the Lean form of the open target.
  - `ExactCount`, the set of vertices whose value is already optimal (`exactSet`) only grows, so
    stretches of at most `c` iterations with the same exact set give at most `n + c(n+1)`
    iterations. Stretches can themselves take `Θ(n²)` iterations (`scripts/hybrid-si/`), so this
    route alone gives at best `O(n³)`.
  - `SwitchCount`, every iteration switches some Even vertex, so at most `c` switches per vertex
    give at most `n_E · c` iterations.

Removed on 2026-10-31 as obsolete routes: the k = 1 development `SingleOdd/` (`upPoly`, MW),
ENT (`EntryPoly`), RED/PXLc (crossings), and the decisive-element bounds (M, P4, EDEC2, ESEP,
LOC, `StretchCount`).

## Proofs

`Proofs/*_Proofs.lean` are machine-generated, one file per
spec area. The master improvement lemma is `K_le_of_dom` (VJ 5.5 for profiles) in
`Improvement_Proofs.lean`. The NI lemma (a profile whose changed edges are all
non-improving is not better) is derived from it inside `epoch_round` (`Epoch_Proofs.lean`), but
it is not yet a standalone statement.
