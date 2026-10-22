# Structural bounds for H-B: progress

Spec: `MercLib/HybridSI/Bounds.lean`. Proofs:
* `Proofs/Bounds_Proofs.lean`: sandwich, lemma M, P4.
* `Proofs/Bounds_Subgame_Proofs.lean`: keys on closed subgames (`sum_lt_iff`, `key_le_val`, ...).
* `Proofs/Bounds_Autonomy_Proofs.lean`: autonomy, O1.
* `Proofs/Bounds_Epoch_Proofs.lean`: lemma B, EDEC2, ESEP, LOC.
All build warning-free, no sorry; axioms propext / Classical.choice / Quot.sound.
Not registered in `Basic.lean`, `Challenges/HybridSI.lean`, `comparator.json` (coordinator's job).

## Proved headlines (G : Game V, [DecidableRel G.edge], bf : ℕ)
* `saddleUnique G : SaddleUnique G`, `saddleExists G : SaddleExists G`
* `lowerBelowUpper G bf : LowerBelowUpper G bf` (Ξ_k ≤ K*_j), `sandwich G bf : Sandwich G bf` (Ξ_k ≤ v* ≤ K*_j)
* `autonomy G bf : Autonomy G bf`, `closedIterations G bf : ClosedIterations G bf` (O1)
* `truncationMonotone G bf : TruncationMonotone G bf` (M), `decisiveRounds G bf : DecisiveRounds G bf` (P4)
* `epochDecisive G bf : EpochDecisive G bf` (EDEC2), `epochNoReset G bf : EpochNoReset G bf` (ESEP),
  `resetLocal G bf : ResetLocal G bf` (LOC)

## Notes
* `Autonomy`, `ClosedIterations`, `EpochDecisive`, `EpochNoReset`, `ResetLocal` carry `G.Relabelled` only because the
  existing contract `FilterNonempty` (used via `hbStep_eq`) has it as a hypothesis (its proof does not use it).
* P4 is stated with the decisive element expressed by memberships (`δ ≤ x`: nothing above `x` changes in any `B`;
  `δ = x`: membership of `x` changes for some vertex); the proof shows each vertex contributes at most one round.
* Not formalised: P6 (Bellman–Ford inside an epoch), CL, SEPvc.
