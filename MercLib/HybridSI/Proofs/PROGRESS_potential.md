# Potential bounds for H-B: progress

Spec: `MercLib/HybridSI/Potential.lean`; proofs: `Proofs/Potential_Proofs.lean` (builds, no sorry, axioms
propext / Classical.choice / Quot.sound only). Not yet registered in `Basic.lean`, `Challenges/HybridSI.lean`,
`comparator.json` (coordinator's job).

## Proved (headline theorems, each `: <Spec> G bf` unless noted)
* `runTraceOfRun : RunTraceOfRun G bf` — a returning `hbRun` from an edge-following profile unrolls into a
  `RunTrace` of length `it - it₀` ending in `.done kt`.
* `valuationMonotone : ValuationMonotone G bf` (P2) — `key G (ps j) ≤ key G (ps k)` pointwise, `j ≤ k ≤ L`.
* `cycleMaxChanges : CycleMaxChanges G bf` (P3) — `#{k < L | ∃ v, cycMax (ps k) v ≠ cycMax (ps (k+1)) v} ≤ n(n-1)`.
* `vertexCycMaxChanges` — per vertex `≤ n - 1` such changes.
* `crossCycMaxChanges` (PXLc) — crossings of a pair at a change of either cycle maximum `≤ 2(n-1)`.
* `epochCrossings` (RED) — `#epoch changes ≤ #tie rounds + Σ_{(u,a,b) sibling, a<b} #crossings(a,b)`.
* `topChanges` (TOP) — `t` top vertex: `#{k | some (cycMax, t ∈ B) changes} ≤ n(2n-1)`.
* `entryIterations : EntryIterations G bf p₀ c` — `EvenEntryBound G bf p₀ c → L ≤ c · numEvenEdges G`.
* `entryPoly : EntryPoly` — `EvenEntryConjecture → HBPolyIterations` (exponent 3).

Key helper lemmas: `runTrace_edge`, `runTrace_step_le` (one step of P2 via `improvement`), `card_changes_le`
(a monotone ℤ-sequence with values in `S` changes ≤ |S|-1 times), `rI_le_of_key_le`, `sum_le_of_key_le`,
`topPot` / `topPot_mono` / `topPot_inj` (TOP potential `2·rI(l) + [t∈B preferred by Even]`), `cross_of_event`.

## Open
* `EvenEntryConjecture` (ENT, hb_elim): tested only. Stated for runs from `initProfile`, `c = n`.
* O1 (closed subgame autonomy, hb_nest sec. 2): not formalised. Needs: subgame `Game D` on a closed subtype,
  rank-independence of key comparisons (only the order matters: `upper_le_of_le`-style argument), commutation of
  `respond`/`hbStep` with restriction (tie-breaking via `univList` order is preserved by the subtype order;
  the global `done`/`useF` tests differ, so the statement must be "the D-part of p k is the subgame run, frozen
  after it ends"). Resume plan: first prove `key` restricted = subgame key up to order-isomorphism.
* P4 (decisive-element intervals), P6 (Bellman-Ford inside an epoch), sandwich `Ξ_k ≤ K*_k`: not started.
