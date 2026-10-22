# Progress: polynomial best response (done)

All files compile, no sorry; headlines depend only on propext, Classical.choice, Quot.sound.

## Spec files
* `BestResponse.lean`: `bestResponseT` / `bestResponse` (cycle-maximum classes by reachability,
  Bellman–Ford inside classes with weight `M·[λ<v]·(±2^rank v) ± 1`, `M = 4n+1`, argmax moves),
  contracts `BestResponseOptimal`, `BestResponseCost` (`≤ 4(n+1)²(m+2n+1)`).
* `AlgorithmPoly.lean`: `keyTableT`, `hbStepPoly`, `hbRunPoly`, `hbStepBound`, contracts
  `HBStepCost`, `HBRunCost`, `HBPolyCorrect`.

## Proofs
* `Proofs/BestResponse_Graph_Proofs.lean`: reachability, Bellman–Ford fixpoint under `NegCyc`.
* `Proofs/BestResponse_Classes_Proofs.lean`: phase-1 invariant and class properties.
* `Proofs/BestResponse_Proofs.lean`: `negCyc_classes`, values/moves, `moves_reach`,
  `cycMax_moves`, `value_eq`, `moves_stable`, `bestResponse_eq`, **`bestResponse_optimal`**,
  **`bestResponse_cost`**.
* `Proofs/AlgorithmPoly_Proofs.lean`: **`hbPolyCorrect`**, **`hbStepPoly_cost`**,
  **`hbRunPoly_cost`**.

## Not done (coordinator)
* Register the new modules in `MercLib/HybridSI/Basic.lean`, challenges in
  `Challenges/HybridSI.lean`, names in `comparator.json`.
* Open: polynomial iteration count (`HBPolyIterations`) is untouched.
