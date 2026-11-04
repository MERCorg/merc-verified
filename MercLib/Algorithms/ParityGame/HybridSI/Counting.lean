module

public import MercLib.Algorithms.ParityGame.HybridSI.Bounds

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
* `ExactCount`: the set of vertices whose value is already optimal (`exactSet`, with the optimal
  valuation the keys of a saddle profile) only grows, so it changes at most `n` times; if it is
  constant for at most `c` iterations at a time, there are at most `n + c (n + 1)` iterations.
* `SwitchCount`: every iteration switches some Even vertex, so if every vertex is switched at most
  `c` times there are at most `n_E · c` iterations.

Proofs go to `Algorithms/ParityGame/HybridSI/Proofs/Counting_Proofs.lean`.
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

/-- The vertices whose value at state `k` is already optimal: their key under Odd's best response
    `ps k` equals their key under the saddle profile `q`. -/
def exactSet (G : Game V) (ps : ℕ → V → V) (q : V → V) (k : ℕ) : Finset V :=
  Finset.univ.filter fun v => key G (ps k) v = key G q v

/-- The iterations `k < L` after which the set of exact vertices changes. -/
def exactChangeRounds (G : Game V) (L : ℕ) (ps : ℕ → V → V) (q : V → V) : Finset ℕ :=
  (Finset.range L).filter fun k => exactSet G ps q (k + 1) ≠ exactSet G ps q k

/-- Contract (stretches with the same exact set): along a trace and for a saddle profile `q`, if
    every stretch of iterations `j ≤ k < j' ≤ L` with the same exact set has at most `c`
    iterations, then the trace has at most `n + c (n + 1)` iterations. -/
def ExactCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ q, Saddle G q → ∀ c : ℕ,
    (∀ j j', j' ≤ L → (∀ k, j ≤ k → k < j' → exactSet G ps q k = exactSet G ps q j) →
      j' - j ≤ c) →
    L ≤ Fintype.card V + c * (Fintype.card V + 1)

/-- The iterations `k < L` of a trace at which the move of `v` changes. -/
def switchRounds (L : ℕ) (p : ℕ → V → V) (v : V) : Finset ℕ :=
  (Finset.range L).filter fun k => p (k + 1) v ≠ p k v

/-- Contract (switches per vertex): along a trace, if the move of every vertex changes at most
    `c` times, then the trace has at most `n_E · c` iterations. -/
def SwitchCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ c : ℕ,
    (∀ v, (switchRounds L p v).card ≤ c) → L ≤ numEven G * c

end MercLib.HybridSI

end HybridSICounting
