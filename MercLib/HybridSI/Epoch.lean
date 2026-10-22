module

public import MercLib.HybridSI.Correctness

@[expose] public section HybridSIEpoch

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# The epoch-length bound for H-B

An *epoch* of an H-B run is a maximal stretch of consecutive iterations in which Odd's best
response `σ̄ = ps k` (the result of `respond G true bf (p k)` inside `hbStep`) plays the same moves.
`EpochBound` says that an epoch has at most `n_E` iterations, `n_E` the number of Even vertices
(`experiments/hb_epoch/README.md`, theorem A5). Within an epoch, the vertices whose move is
optimal in the one-player game against the fixed Odd strategy form a strictly growing set that
never contains every Even vertex.

Nothing here is proved; the proof is in `HybridSI/Proofs/Epoch_Proofs.lean`.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The number of Even vertices. -/
def numEven (G : Game V) : ℕ := (Finset.univ.filter fun v => G.owner v = .zero).card

/-- Contract (epoch length): if `p 0, …, p L` are the profiles of `L` consecutive H-B iterations
    (each a non-final iteration, `p (k + 1)` the next profile computed from `p k`, starting from a
    profile that follows edges), and Odd's best responses `ps k` in these iterations agree at every
    Odd vertex, then `L` is at most the number of Even vertices. -/
def EpochBound (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), (∀ v, G.edge v (p 0 v)) →
    (∀ k < L, respond G true bf (p k) = some (ps k) ∧
      ∃ qt, hbStep G bf (p k) = .next qt ∧ p (k + 1) = fun v => look qt v v) →
    (∀ k < L, ∀ v, G.owner v = .one → ps k v = ps 0 v) →
    L ≤ numEven G

end MercLib.HybridSI

end HybridSIEpoch
