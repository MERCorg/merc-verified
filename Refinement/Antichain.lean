module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Refinement.Semantics
public import Refinement.Product

open Cslib (LTS HasTau)

@[expose] public section Antichain

/-!
# The antichain order

Section 4-5 of M. Laveaux, J. F. Groote, T. A. C. Willemse, *Correct and Efficient Antichain
Algorithms for Refinement Checking*, LMCS 17(1:8), 2021.

`NormTr`/`FdrNormTr` states are sets `U : Set State1`; both share the key property that their
transition relation is a *monotone functional image operator* (`IsMonotoneNormalForm`, capturing
Lemma 5.7 abstractly so it is proved once and reused for both, in
`Refinement/Proofs/Antichain_Proofs.lean`, which also has Proposition 5.8 and Lemma 5.9).
-/

/-- The order on product states (Section 4): `(U, s) ≤ (V, t)` iff they agree on the
    implementation state and `U ⊆ V`. -/
def ProductLE (p q : Set State1 × State2) : Prop := p.2 = q.2 ∧ p.1 ⊆ q.1

/-- `L1`'s transition relation over `Set State1` is a monotone functional image operator
    (Lemma 5.7): whenever `U ⊆ V` and `V` has an `a`-derivative `V'`, `U` has *some* `a`-derivative
    `U' ⊆ V'` too. Stated abstractly so it is proved once and reused for both `NormTr` and
    `FdrNormTr` (`normTr_isMonotone`, `fdrNormTr_isMonotone`), which are the only instances this
    development needs. -/
def IsMonotoneNormalForm [HasTau Label] (L1 : LTS (Set State1) Label) : Prop :=
  ∀ ⦃U V : Set State1⦄ ⦃a : Label⦄ ⦃V' : Set State1⦄,
    U ⊆ V → L1.Tr V a V' → ∃ U', L1.Tr U a U' ∧ U' ⊆ V'

/-- Antichain membership test (Section 4, `⊑`): `x` is "contained" in antichain `A` iff some
    member of `A` is `≤ x`. -/
def AntichainMem (A : Set (Set State1 × State2)) (x : Set State1 × State2) : Prop :=
  ∃ y ∈ A, ProductLE y x

/-- Antichain insertion (Section 4, `⊎`): extending `A` with `x`, discarding the members of `A`
    that `x` now dominates. Only yields an antichain when `x ∉ A` in the `AntichainMem` sense
    (Section 4); callers only ever insert after a failed `AntichainMem` test, so that side
    condition is not baked into the definition itself. -/
def AntichainInsert (A : Set (Set State1 × State2)) (x : Set State1 × State2) :
    Set (Set State1 × State2) :=
  { y | y = x ∨ (y ∈ A ∧ ¬ ProductLE x y) }

end Antichain
