# HybridSI

Hybrid strategy improvement for parity games: the rule H-B (Even's half of symmetric strategy
improvement with Odd at an exact best response), on the exact Vöge–Jurdziński valuation, built on
the library games of `MercLib.ParityGame`.

* `Valuation.lean`: relevance order (`Game.Relabelled`), play values as integer keys (`key`).
* `Algorithm.lean`: best responses (`respond`), one H-B iteration (`hbStep`), the solver (`hbRun`).
  Computable; agrees with the Python reference (`~/parity-polynomial/experiments/hybrid/`) on
  iteration counts and winners.
* `Correctness.lean`: contracts `HBCorrect`, `HBTerminates`, `FilterNonempty`, and the open
  statements `HBPolyIterations`, `RespondPolyRounds`.
* `Epoch.lean`: contract `EpochBound` (an epoch of H-B, i.e. iterations with the same Odd
  response, has at most `n_E` iterations).
* `BestResponse.lean`: a polynomial best response `bestResponse` (cycle-maximum classes by
  reachability, Bellman–Ford inside classes), contracts `BestResponseOptimal`, `BestResponseCost`.
* `AlgorithmPoly.lean`: H-B with `bestResponse` (`hbStepPoly`, `hbRunPoly`) in `TimeM`, contracts
  `HBStepCost`, `HBRunCost`, `HBPolyCorrect`.
* `Potential.lean`: potential bounds along a run (`RunTrace`): monotone valuation (P2), changes of
  cycle maxima (P3, PXLc), top-level changes (TOP), epoch changes vs. sibling crossings (RED),
  entries into Even edges bound iterations, and the open `EvenEntryConjecture` (ENT) with
  `EntryPoly : EvenEntryConjecture → HBPolyIterations`.
* `Proofs/`: machine-generated proofs.
