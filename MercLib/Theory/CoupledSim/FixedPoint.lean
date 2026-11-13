module

public import MercLib.Theory.CoupledSim.CoupledSimilarity

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.CoupledSim

/-!
# Fixed-point algorithm for coupled similarity

This module formalises the greatest-fixed-point characterisation underlying the fixed-point
algorithm for the coupled simulation preorder (Section 3 of [B. Bisping and U. Nestmann,
*Computing Coupled Similarity*][Bisping2019]): starting from the full relation and repeatedly
removing pairs that violate one of the three clauses of a coupled delay simulation, the
iteration stabilises at the greatest fixed point of `fpStep`, which by Lemma 1 (transfered to
delay simulations) is exactly the coupled simulation preorder.

## Main definitions

- `fpStep`: one pruning step; `fpStep r` keeps those pairs of `r` that satisfy a clause of
  `IsCoupledDelaySimulation`.
- `fpIter`: the `n`-fold iteration of `fpStep` on the full relation.
- `IsGreatestFixedPt`: `r` is the greatest fixed point of `fpStep`.

## Main statements

See the `Proofs/` files next to this module; the headline theorems are restated in
`Challenges/CoupledSim.lean`.

## References

- [B. Bisping and U. Nestmann, *Computing Coupled Similarity*][Bisping2019]
-/

/-! ## The pruning operator -/

/-- One pruning step of the fixed-point algorithm (Sect. 3 of [Bisping2019]): a pair `(p, q)` of
relation `r` survives iff the sim challenge of a coupled delay simulation can still be met
within `r`, and the coupling clause can still be met within `r`. -/
def fpStep [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) :
    State → State → Prop :=
  fun p q =>
    r p q ∧
    (∀ μ p', lts.Tr p μ p' → ∃ q', r p' q' ∧ DTr lts q μ q') ∧
    (∃ q', lts.τSTr q q' ∧ r q' p)

/-- The `n`-fold iteration of `fpStep` on the full relation (the state after `n` rounds of the
algorithm of Sect. 3 of [Bisping2019]). -/
def fpIter [HasTau Label] (lts : LTS State Label) (n : ℕ) : State → State → Prop :=
  (fpStep lts)^[n] (fun _ _ => True)

/-- `r` is the greatest fixed point of `fpStep lts` (Lemma 7 of [Bisping2019] formalises that the
coupled simulation preorder is such a greatest fixed point). -/
def IsGreatestFixedPt [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  fpStep lts r = r ∧ ∀ s, fpStep lts s = s → ∀ ⦃p q⦄, s p q → r p q

end MercLib.CoupledSim
