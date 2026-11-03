module

public import MercLib.HybridSI.Potential

@[expose] public section HybridSICounting

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Counting iterations along a trace (any game)

Bounds on the length of a `RunTrace` in terms of events along it, for every game:

* `EpochIterations`: at most `(E + 1) · n_E` iterations, `E` the number of epoch changes
  (`EpochBound` for each epoch).
* `KStarBlock`: a stretch with constant keys `K*` of Even's best response (`kstarOf`) has at most
  `n_E` iterations; the epoch-bound argument needs only that `K*` is constant, not Odd's moves.
* `KStarCount`: at most `C + n_E (C + 1)` iterations, `C` the number of changes of `K*`.

Proofs go to `HybridSI/Proofs/Counting_Proofs.lean`.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The keys `K*` at state `k`: the keys of Even's best response to `ps k`, or `keyDefault`. -/
def kstarOf (G : Game V) [DecidableRel G.edge] (bf : ℕ) (ps : ℕ → V → V) (k : ℕ) (v : V) : Key :=
  ((respond G false bf (ps k)).map fun q => key G q v).getD keyDefault

/-- The iterations `k` with `k + 1 < L` after which `K*` changes. -/
def kstarChangeRounds (G : Game V) [DecidableRel G.edge] (bf L : ℕ) (ps : ℕ → V → V) :
    Finset ℕ :=
  (Finset.range L).filter fun k => k + 1 < L ∧ kstarOf G bf ps (k + 1) ≠ kstarOf G bf ps k

/-- Contract (iterations per epoch): a trace has at most `E + 1` epochs of at most `n_E`
    iterations each, `E` the number of epoch changes. -/
def EpochIterations (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    L ≤ ((oddChangeRounds G L ps).card + 1) * numEven G

/-- Contract (blocks of constant `K*`): along a trace, a stretch of iterations `j ≤ k < j' ≤ L`
    with the same keys `K*` has at most `n_E` iterations. -/
def KStarBlock (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ j j', j' ≤ L →
    (∀ k, j ≤ k → k < j' → kstarOf G bf ps k = kstarOf G bf ps j) → j' - j ≤ numEven G

/-- Contract (changes of `K*`): a trace has at most `C + n_E (C + 1)` iterations, `C` the number
    of changes of `K*`. -/
def KStarCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    L ≤ (kstarChangeRounds G bf L ps).card +
      numEven G * ((kstarChangeRounds G bf L ps).card + 1)

end MercLib.HybridSI

end HybridSICounting
