# HybridSI

Hybrid strategy improvement for parity games: the rule H-B (Even's half of symmetric strategy
improvement with Odd at an exact best response), on the exact Vöge–Jurdziński valuation, built on
the library games of `MercLib.ParityGame`. The paper side, including the general-k lemmas that
are not yet formalised, is in `~/parity-polynomial/proof/hb_general.md`.

All proof files compile without `sorry`, using only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Every headline is registered in `Basic.lean` and has a challenge in
`Challenges/HybridSI.lean`.

## The algorithm and its correctness (any game)

* `Valuation.lean`: the relevance order (`Game.Relabelled`) and play values as integer keys
  (`key`).
* `Algorithm.lean`: best responses (`respond`), one H-B iteration (`hbStep`) and the solver
  (`hbRun`). It is computable, and it agrees with the Python reference
  (`~/parity-polynomial/experiments/hybrid/`) on iteration counts and winners.
* `Correctness.lean`: `HBCorrect`, `HBTerminates` and `FilterNonempty` are proved.
  `HBPolyIterations` and `RespondPolyRounds` are the open targets.
* `Epoch.lean`: `EpochBound`. An epoch (iterations with the same Odd response) has at most `n_E`
  iterations.
* `BestResponse.lean` and `AlgorithmPoly.lean`: a polynomial best response (cycle-maximum classes
  by reachability, Bellman–Ford inside classes), and H-B built on it in `TimeM`. The cost and
  correctness contracts are proved.

## Bounds along a run (any game)

These are the facts F1–F6 that the paper proof uses (`hb_general.md` §1), plus the subgame
decomposition behind its Theorem 28.

* `Potential.lean` (`RunTrace`):
  - P2 (F1), the valuation is monotone;
  - P3, changes of cycle maxima (`n(n−1)` in total, `n−1` per vertex);
  - TOP, changes of the cycle maximum or of membership of the top vertex in `B` (the top-vertex
    split of §3).
* `Bounds.lean`:
  - the saddle point, existence and uniqueness;
  - the sandwich `Ξ_k ≤ K° ≤ K*_j` (F2);
  - autonomy of closed subgames and O1.
* `Counting.lean`:
  - `EpochIterations`, at most `(E+1)·n_E` iterations;
  - `KStarBlock` (F6), constant `K*` lasts at most `n_E` iterations;
  - `KStarCount`, at most `C + n_E(C+1)` iterations, where `C` counts `K*` changes. A polynomial
    bound on `C` is the Lean form of the open target.

Removed on 2026-10-31 as obsolete routes (archived in
`~/parity-polynomial/archive/lean_hybridsi_2026-10-31/`): the k = 1 development `SingleOdd/`
(`upPoly`, MW), ENT (`EntryPoly`), RED/PXLc (crossings), and the decisive-element bounds
(M, P4, EDEC2, ESEP, LOC, `StretchCount`).

## Proofs

`Proofs/*_Proofs.lean` are machine-generated, one file per
spec area. The master improvement lemma is `K_le_of_dom` (VJ 5.5 for profiles) in
`Improvement_Proofs.lean`. The paper notes' NI lemma (a profile whose changed edges are all
non-improving is not better) is derived from it inside `epoch_round` (`Epoch_Proofs.lean`), but
it is not yet a standalone statement.
