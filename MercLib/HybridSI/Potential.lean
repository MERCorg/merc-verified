module

public import MercLib.HybridSI.Epoch

@[expose] public section HybridSIPotential

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Potential bounds for H-B runs

Claims about the sequence of profiles of an H-B run (`hbRun`, `hbStep` of `HybridSI.Algorithm`):
the run keeps Odd's moves of the initial profile in `p k` (the "restart" variant: every best
response of Odd is computed from the initial Odd moves), Even's moves change by the H-B rule.
The paper proofs are in `~/parity-polynomial/experiments/hb_bound/README.md` (P2, P3),
`hb_amort/README.md` (TOP) and `hb_elim/README.md` (ENT). Nothing here is proved; proofs go to
`HybridSI/Proofs/Potential_Proofs.lean`.

* `RunTrace`: the profiles `p 0, …, p L` and Odd's best responses `ps 0, …, ps L` of `L`
  consecutive non-final iterations; `RunTraceOfRun`: a returning `hbRun` has such a trace.
* `ValuationMonotone` (P2): the valuations `Ξ_k = key G (ps k)` are pointwise non-decreasing.
* `CycleMaxChanges` (P3): at most `n (n - 1)` iterations change some vertex's cycle maximum.
* `VertexCycMaxChanges`: per vertex at most `n - 1` changes of the cycle maximum.
* `EpochCrossings` (RED): epoch changes are at most tie rounds plus crossings of sibling pairs
  (`crossRounds`, `siblingPairs`); `CrossCycMaxChanges` (PXLc): at most `2 (n - 1)` crossings of
  a pair coincide with a change of one of the two cycle maxima.
* `TopChanges` (TOP): at most `n (2n - 1)` iterations change, for some vertex, the cycle maximum
  or whether the most relevant vertex lies in the set `B` of its play value.
* `EvenEntryBound`, `EntryIterations`: if every Even edge is switched into at most `c` times, the
  run has at most `c · m_E` iterations (`m_E` = `numEvenEdges`).
* `EvenEntryConjecture` (ENT): **open** (not a contract): `c = |V|` works on every relabelled
  game, for the run from the initial profile. `EntryPoly` reduces `HBPolyIterations` to it.
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

/-- The tie rounds: epoch changes at which every changed Odd move `a = ps k u ↦ b = ps (k+1) u`
    is between successors of equal keys, both before and after the iteration. -/
def tieRounds (G : Game V) (L : ℕ) (ps : ℕ → V → V) : Finset ℕ :=
  (oddChangeRounds G L ps).filter fun k => ∀ u, G.owner u = .one → ps k u ≠ ps (k + 1) u →
    key G (ps k) (ps k u) = key G (ps k) (ps (k + 1) u) ∧
      key G (ps (k + 1)) (ps k u) = key G (ps (k + 1)) (ps (k + 1) u)

/-- The crossings of the pair `(a, b)`: iterations `k < L` at which the comparison of the keys of
    `a` and `b` changes. -/
def crossRounds (G : Game V) (L : ℕ) (ps : ℕ → V → V) (a b : V) : Finset ℕ :=
  (Finset.range L).filter fun k =>
    compare (key G (ps k) a) (key G (ps k) b) ≠ compare (key G (ps (k + 1)) a) (key G (ps (k + 1)) b)

/-- The sibling pairs: triples `(u, a, b)` of an Odd vertex `u` and two successors `a < b`. -/
def siblingPairs (G : Game V) [DecidableRel G.edge] : Finset (V × V × V) :=
  Finset.univ.filter fun x => G.owner x.1 = .one ∧ G.edge x.1 x.2.1 ∧ G.edge x.1 x.2.2 ∧ x.2.1 < x.2.2

/-- Contract (RED): the number of epoch changes of a trace is at most the number of tie rounds
    plus the total number of crossings of sibling pairs. -/
def EpochCrossings (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    (oddChangeRounds G L ps).card ≤
      (tieRounds G L ps).card + ∑ x ∈ siblingPairs G, (crossRounds G L ps x.2.1 x.2.2).card

/-- Contract (PXLc): the crossings of any pair at which the cycle maximum of one of the two
    vertices changes are at most `2 (n - 1)`. -/
def CrossCycMaxChanges (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ a b,
    ((crossRounds G L ps a b).filter fun k =>
      cycMax (ps k) a ≠ cycMax (ps (k + 1)) a ∨ cycMax (ps k) b ≠ cycMax (ps (k + 1)) b).card ≤
      2 * (Fintype.card V - 1)

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

/-- The iterations `k < L` of a trace at which vertex `v` is switched into the edge `(v, w)`. -/
def entryRounds (L : ℕ) (p : ℕ → V → V) (v w : V) : Finset ℕ :=
  (Finset.range L).filter fun k => p (k + 1) v = w ∧ p k v ≠ w

/-- The number of edges leaving Even vertices. -/
def numEvenEdges (G : Game V) [DecidableRel G.edge] : ℕ :=
  (Finset.univ.filter fun e : V × V => G.owner e.1 = .zero ∧ G.edge e.1 e.2).card

/-- Every trace from `p₀` switches into every Even edge at most `c` times. -/
def EvenEntryBound (G : Game V) [DecidableRel G.edge] (bf : ℕ) (p₀ : V → V) (c : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), p 0 = p₀ → RunTrace G bf L p ps →
    ∀ v w, G.owner v = .zero → G.edge v w → (entryRounds L p v w).card ≤ c

/-- Contract (entries bound iterations): if every Even edge is switched into at most `c` times,
    every trace from `p₀` has at most `c · m_E` iterations (each non-final iteration switches
    some Even vertex). -/
def EntryIterations (G : Game V) [DecidableRel G.edge] (bf : ℕ) (p₀ : V → V) (c : ℕ) : Prop :=
  EvenEntryBound G bf p₀ c → ∀ (L : ℕ) (p ps : ℕ → V → V), p 0 = p₀ → RunTrace G bf L p ps →
    L ≤ c * numEvenEdges G

/-- **Open** (not a contract; ENT of `experiments/hb_elim`, tested, not proved): on every
    relabelled game the run of H-B from the initial profile switches into each Even edge at most
    `|V|` times. -/
def EvenEntryConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled →
    EvenEntryBound G (hbFuel (Fin n)) (initProfile G) n

/-- Contract (ENT would give polynomially many iterations): `EvenEntryConjecture` implies
    `HBPolyIterations` (with exponent `3`: `n · n²` iterations). -/
def EntryPoly : Prop := EvenEntryConjecture → HBPolyIterations

end MercLib.HybridSI

end HybridSIPotential
