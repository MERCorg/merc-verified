# Progress: VJ improvement theory, termination, filter, epochs (HybridSI)

All files compile (`lake build MercLib.HybridSI.Proofs.Epoch_Proofs MercLib.HybridSI.Proofs.Termination_Proofs`),
no `sorry`, axioms `propext, Classical.choice, Quot.sound` only.

## Proved
* `Improvement_Proofs.lean`
  * `K_le_of_dom` (master lemma, VJ 5.5 for profiles): `(∀ u, K G f i (f u) ≤ K G f i (g u)) → K G f i v ≤ K G g i v`.
    Helpers: `tail_lt_false`, `tail_upper_false` (the two tail arguments of `winsFrom_of_saddle`), `K_le_path`.
  * (a) `respond_odd_optimal`, `respond_even_optimal`: a returned best response beats every other strategy of its player.
  * (b) `improvement` (VJ 5.7): keys dominate pointwise, against *any* Odd counter-strategy; the key of the chosen
    successor increases strictly at every switched vertex. The valuation itself need NOT increase strictly
    (counterexample in the file header; VJ Lemma 5.8, 2⇒3, fails for these keys), so the strict part is stated on
    the chosen successors, which is what termination uses.
* `Termination_Proofs.lean`: `hbTerminates : HBTerminates G bf fuel` (potentials `respondPot`, `hbPot`; `chain_bound`).
* `Filter_Proofs.lean`: `filterNonempty : FilterNonempty G bf p`.
* `Epoch.lean` (new spec, `EpochBound`, `numEven`) and `Epoch_Proofs.lean`: `epochBound : EpochBound G bf`.

## Open / for the coordinator
* Register in `Challenges/HybridSI.lean` + `comparator.json`: `hbTerminates`, `filterNonempty`, `epochBound`
  (challenge file needs `import MercLib.HybridSI.Epoch`).
* Not attempted: `HBPolyIterations`, `RespondPolyRounds` (open problems).
