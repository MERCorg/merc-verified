module

public import MercLib.Algorithms.ParityGame.HybridSI.Epoch

@[expose] public section HybridSIPotential

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Potential bounds for H-B runs

Claims about the sequence of profiles of an H-B run (`hbRun`, `hbStep` of `HybridSI.Algorithm`):
the run keeps Odd's moves of the initial profile in `p k` (the "restart" variant: every best
response of Odd is computed from the initial Odd moves), Even's moves change by the H-B rule.
Proofs go to `Algorithms/ParityGame/HybridSI/Proofs/Potential_Proofs.lean`.

* `RunTrace`: the profiles `p 0, …, p L` and Odd's best responses `ps 0, …, ps L` of `L`
  consecutive non-final iterations; `RunTraceOfRun`: a returning `hbRun` has such a trace.
* `ValuationMonotone` (P2): the valuations `Ξ_k = key G (ps k)` are pointwise non-decreasing.
* `CycleMaxChanges` (P3): at most `n (n - 1)` iterations change some vertex's cycle maximum.
* `VertexCycMaxChanges`: per vertex at most `n - 1` changes of the cycle maximum.
* `oddChangeRounds`: the iterations at which Odd's best response changes (epoch changes).
* `TopChanges` (TOP): at most `n (2n - 1)` iterations change, for some vertex, the cycle maximum
  or whether the most relevant vertex lies in the set `B` of its play value.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- `p 0, …, p L` are the profiles and `ps 0, …, ps L` Odd's best responses (the result of
    `respond G true bf (p k)` inside `hbStep`) of an H-B run: `p 0` follows edges and each of the
    first `L` iterations is non-final, `p (k + 1)` the profile it computes from `p k`. The
    iteration from `p L` may be final or not. -/
def RunTrace (G : Game V) [DecidableRel G.edge] (bf L : ℕ) (p ps : ℕ → V → V) : Prop :=
  (∀ v, G.edge v (p 0 v)) ∧
  (∀ k ≤ L, respond G true bf (p k) = some (ps k)) ∧
  ∀ k < L, ∃ qt, hbStep G bf (p k) = .next qt ∧ p (k + 1) = fun v => look qt v v

/-- Contract (traces of runs): if H-B, started with iteration counter `it₀` from a profile `p₀`
    that follows edges, returns after `it` iterations with key table `kt`, then its profiles
    form a trace of length `it - it₀` from `p₀` whose last iteration is final with result `kt`. -/
def RunTraceOfRun (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (fuel it₀ : ℕ) (p₀ : V → V) (it : ℕ) (kt : List (V × Key)), (∀ v, G.edge v (p₀ v)) →
    hbRun G bf fuel it₀ p₀ = some (it, kt) →
    ∃ L p ps, it = it₀ + L ∧ p 0 = p₀ ∧ RunTrace G bf L p ps ∧ hbStep G bf (p L) = .done kt

/-- Contract (P2, monotonicity of the valuation): along a trace the keys of Odd's best responses
    are pointwise non-decreasing (for Even, who prefers larger keys). -/
def ValuationMonotone (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ j k, j ≤ k → k ≤ L → ∀ v, key G (ps j) v ≤ key G (ps k) v

/-- The iterations `k < L` of a trace at which the cycle maximum of some vertex changes. -/
def cycMaxChangeRounds (L : ℕ) (ps : ℕ → V → V) : Finset ℕ :=
  (Finset.range L).filter fun k => ∃ v, cycMax (ps k) v ≠ cycMax (ps (k + 1)) v

/-- Contract (P3): along a trace at most `n (n - 1)` iterations change the cycle maximum of some
    vertex (per vertex the reward of the cycle maximum is non-decreasing and takes at most `n`
    values). -/
def CycleMaxChanges (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    (cycMaxChangeRounds L ps).card ≤ Fintype.card V * (Fintype.card V - 1)

/-- Contract (P3 per vertex): along a trace the cycle maximum of a fixed vertex changes at most
    `n - 1` times. -/
def VertexCycMaxChanges (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ v,
    ((Finset.range L).filter fun k => cycMax (ps k) v ≠ cycMax (ps (k + 1)) v).card ≤
      Fintype.card V - 1

/-- The iterations `k < L` of a trace at which Odd's best response changes (epoch changes). -/
def oddChangeRounds (G : Game V) (L : ℕ) (ps : ℕ → V → V) : Finset ℕ :=
  (Finset.range L).filter fun k => ∃ u, G.owner u = .one ∧ ps k u ≠ ps (k + 1) u

/-- The coarse value of the play from `v` under `f` at the top level `t`: the cycle maximum and
    whether `t` lies in the set `B` of the play value. -/
def topClass (t : V) (f : V → V) (v : V) : V × Bool := (cycMax f v, decide (t ∈ bSet f v))

/-- The iterations `k < L` of a trace at which the top-level class of some vertex changes. -/
def topChangeRounds (t : V) (L : ℕ) (ps : ℕ → V → V) : Finset ℕ :=
  (Finset.range L).filter fun k => ∃ v, topClass t (ps k) v ≠ topClass t (ps (k + 1)) v

/-- Contract (TOP): if `t` is the most relevant vertex, at most `n (2n - 1)` iterations of a trace
    change the cycle maximum of some vertex or whether `t` lies in its `B`. -/
def TopChanges (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (t : V), (∀ x, x ≤ t) → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    (topChangeRounds t L ps).card ≤ Fintype.card V * (2 * Fintype.card V - 1)

end MercLib.HybridSI

end HybridSIPotential
