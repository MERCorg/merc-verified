import MercLib.Algorithms.ParityGame.HybridSI.Correctness
import MercLib.Algorithms.ParityGame.HybridSI.Epoch
import MercLib.Algorithms.ParityGame.HybridSI.BestResponse
import MercLib.Algorithms.ParityGame.HybridSI.AlgorithmPoly
import MercLib.Algorithms.ParityGame.HybridSI.Potential
import MercLib.Algorithms.ParityGame.HybridSI.Bounds
import MercLib.Algorithms.ParityGame.HybridSI.Counting

/-!
# Comparator challenge: hybrid strategy improvement (human-vetted)

The headline theorems of `MercLib/Algorithms/ParityGame/HybridSI/` (the valuation is in `MercLib/Theory/ParityGame/Valuation.lean`), stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib`.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding. Each theorem below is
documented with what it proves, including the hypotheses hidden in its spec definition, and the
spec definition it unfolds to.

**Terms used below.**
* *Game*: `G : Game V` on a finite, linearly ordered vertex type `V`, with `n = |V|` vertices,
  `n_E` Even vertices (`numEven`) and `m` edges (`edgeCount`). *Relabelled* (`G.Relabelled`):
  the priority is monotone in the vertex order, so the order is the relevance order used by the
  keys. Every game can be relabelled by sorting its vertices.
* *Profile*: `p : V → V`, one move per vertex for both players. It *follows edges* if
  `G.edge v (p v)` for all `v`.
* *Key*: `key G p v`, the Vöge–Jurdziński value of the play from `v` under `p` (the cycle maximum,
  the more relevant vertices visited before it, the distance), encoded so that Even prefers
  larger keys and Odd smaller ones. Its *winner* (`keyWinner`) is Even iff the cycle maximum has
  even priority.
* *H-B*: one iteration (`hbStep`) computes Odd's best response `ps` to Even's moves, Even's best
  response `pstar` to Odd's moves of `ps`, and switches Even vertices along improving edges that
  are optimal for the keys of `pstar` (the *filter*). `hbRun G bf fuel` runs at most `fuel`
  iterations from the first-successor profile `initProfile G`; each best response (`respond`)
  gets at most `bf` rounds. Either fuel can run out, in which case the result is `none`.
* *Trace*: `RunTrace G bf L p ps` says that `p 0, …, p L` are the profiles of `L` consecutive
  non-final H-B iterations from a profile that follows edges, and `ps k` is Odd's best response
  computed in iteration `k`. The valuation of iteration `k` is `Ξ_k = key G (ps k)`, and `K*_k`
  is the key of Even's best response to `ps k`.
* *Cost*: the `…T` and `…Poly` functions run in the `TimeM` cost model; `.time` counts its steps.
-/

namespace MercLib.HybridSI

open MercLib.ParityGame

/-- **Correctness of H-B.** Let `G` be a relabelled game and suppose the run
`hbRun G bf fuel 0 (initProfile G)` returns `some (it, kt)` (for any fuel; a run that runs out of
fuel is not constrained). Then for every vertex `v` and player `i`, the winner read off `v`'s key
in the returned table `kt` is `i` iff `i` has a winning strategy from `v` in the whole game
(`G.WinsFrom`). See `HBCorrect` (`Algorithms/ParityGame/HybridSI/Correctness.lean`). -/
theorem hbCorrect {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf fuel : ℕ) : HBCorrect G bf fuel := sorry

/-- **Termination of H-B.** For a relabelled game and both fuels at least `hbFuel V = n^n + 1`,
`hbRun G bf fuel 0 (initProfile G)` returns a result (is not `none`). The fuel is exponential; a
polynomial bound is the open `HBPolyIterations`. See `HBTerminates`
(`Algorithms/ParityGame/HybridSI/Correctness.lean`). -/
theorem hbTerminates {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf fuel : ℕ) : HBTerminates G bf fuel := sorry

/-- **The filter is never empty while Even can still improve.** Let `G` be a relabelled game, `p`
a profile that follows edges, `ps` Odd's best response to `p` and `pstar` Even's best response to
`ps`, both computed with fuel `bf` without running out. If some Even vertex has an improving edge
(a successor with a larger key under `ps`), then some Even vertex has a *filtered* edge: improving,
and of maximal key under `pstar`. So H-B never needs its fallback to plain improving switches. See
`FilterNonempty` (`Algorithms/ParityGame/HybridSI/Correctness.lean`). -/
theorem filterNonempty {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) (p : V → V) : FilterNonempty G bf p := sorry

/-- **An epoch has at most `n_E` iterations.** If `L` consecutive non-final H-B iterations from a
profile that follows edges all have the same Odd best response at every Odd vertex, then
`L ≤ n_E`. See `EpochBound` (`Algorithms/ParityGame/HybridSI/Epoch.lean`). -/
theorem epochBound {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EpochBound G bf := sorry

/-- **The polynomial best response is a best response.** Let `pl` be a player (`true` = Odd,
`false` = Even), `p` a profile and `q = bestResponse G pl p`. Then (1) `q` keeps `p`'s moves at the
vertices of the other player; (2) if `p` follows edges, so does `q`; and (3) no vertex of `pl` has
a successor with a strictly better key under `q` (for Odd: smaller, for Even: larger). For
one-player games, (3) means that `q` is optimal. See `BestResponseOptimal`
(`Algorithms/ParityGame/HybridSI/BestResponse.lean`). -/
theorem bestResponse_optimal {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (pl : Bool) (p : V → V) : BestResponseOptimal G pl p := sorry

/-- **The polynomial best response takes polynomial time.** For every player `pl` and profile
`p`, `bestResponseT G pl p` takes at most `4 (n + 1)² (m + 2n + 1)` steps. See `BestResponseCost`
(`Algorithms/ParityGame/HybridSI/BestResponse.lean`). -/
theorem bestResponse_cost {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (pl : Bool) (p : V → V) : BestResponseCost G pl p := sorry

/-- **One iteration of polynomial H-B takes polynomial time.** For every profile `p`,
`hbStepPoly G p` takes at most `hbStepBound n m` steps: two best responses plus
`2n (n + 1)³ + 5 (m + n)`. See `HBStepCost` (`Algorithms/ParityGame/HybridSI/AlgorithmPoly.lean`). -/
theorem hbStepPoly_cost {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (p : V → V) : HBStepCost G p := sorry

/-- **A run of polynomial H-B costs polynomial time per iteration.** If the run
`hbRunPoly G fuel 0 (initProfile G)` returns after `it` iterations, it takes at most
`(it + 1) · (hbStepBound n m + 1)` steps. Together with a polynomial bound on `it` (open), this
would put H-B in P. See `HBRunCost` (`Algorithms/ParityGame/HybridSI/AlgorithmPoly.lean`). -/
theorem hbRunPoly_cost {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (fuel : ℕ) : HBRunCost G fuel := sorry

/-- **Correctness of polynomial H-B.** Let `G` be a relabelled game and suppose the run
`hbRunPoly G fuel 0 (initProfile G)` returns `some (it, kt)`. Then, as in `hbCorrect`, for every
`v` and `i` the winner read off `v`'s key in `kt` is `i` iff `i` has a winning strategy from `v`.
See `HBPolyCorrect` (`Algorithms/ParityGame/HybridSI/AlgorithmPoly.lean`). -/
theorem hbPolyCorrect {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (fuel : ℕ) : HBPolyCorrect G fuel := sorry

/-- **A returning run has a trace.** If `p₀` follows edges and the run `hbRun G bf fuel it₀ p₀`
returns `some (it, kt)`, then there is a trace `RunTrace G bf L p ps` with `p 0 = p₀` and
`it = it₀ + L` whose last iteration (from `p L`) is final with result `kt`. This connects the run
to the trace-based bounds below. See `RunTraceOfRun` (`Algorithms/ParityGame/HybridSI/Potential.lean`). -/
theorem runTraceOfRun {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : RunTraceOfRun G bf := sorry

/-- **The valuation never decreases (F1).** Along a trace of length `L`, `Ξ_j(v) ≤ Ξ_k(v)` for
all `j ≤ k ≤ L` and every vertex `v`. See `ValuationMonotone` (`Algorithms/ParityGame/HybridSI/Potential.lean`). -/
theorem valuationMonotone {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : ValuationMonotone G bf := sorry

/-- **Cycle maxima change at most `n (n − 1)` times in total.** Along a trace of length `L`, at
most `n (n − 1)` of the iterations `k < L` change the cycle maximum of the play from some vertex
under Odd's best response (`ps k` versus `ps (k + 1)`). See `CycleMaxChanges`
(`Algorithms/ParityGame/HybridSI/Potential.lean`). -/
theorem cycleMaxChanges {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : CycleMaxChanges G bf := sorry

/-- **The cycle maximum of one vertex changes at most `n − 1` times.** Along a trace of length
`L`, at most `n − 1` iterations `k < L` change the cycle maximum of the play from a given vertex
`v` under Odd's best response. See `VertexCycMaxChanges` (`Algorithms/ParityGame/HybridSI/Potential.lean`). -/
theorem vertexCycMaxChanges {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : VertexCycMaxChanges G bf := sorry

/-- **Changes at the top vertex are bounded (TOP).** Let `t` be the most relevant vertex of the
game. Along a trace of length `L`, at most `n (2n − 1)` iterations `k < L` change, for some vertex
`v`, the cycle maximum of its play under Odd's best response or whether that play visits `t` before
its cycle maximum. This is the top-vertex split of the paper proof. See `TopChanges`
(`Algorithms/ParityGame/HybridSI/Potential.lean`). -/
theorem topChanges {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : TopChanges G bf := sorry

/-- **The optimal valuation is unique.** Any two *saddle* profiles `q`, `q'` (`Saddle`: they
follow edges, and under their own keys no Odd vertex has a successor with a smaller key and no
Even vertex one with a larger key) satisfy `key G q = key G q'`. See `SaddleUnique`
(`Algorithms/ParityGame/HybridSI/Bounds.lean`). -/
theorem saddleUnique {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge] :
    SaddleUnique G := sorry

/-- **The optimal valuation exists.** Every relabelled game has a saddle profile. See
`SaddleExists` (`Algorithms/ParityGame/HybridSI/Bounds.lean`). -/
theorem saddleExists {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge] :
    SaddleExists G := sorry

/-- **`Ξ_k ≤ K*_j` along a trace.** Along a trace of length `L`, let `k, j ≤ L` and let `pstar`
be Even's best response to `ps j` (computed with fuel `bf` without running out). Then
`Ξ_k(v) ≤ key G pstar v` for every vertex `v`. See `LowerBelowUpper` (`Algorithms/ParityGame/HybridSI/Bounds.lean`). -/
theorem lowerBelowUpper {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : LowerBelowUpper G bf := sorry

/-- **The sandwich `Ξ_k ≤ K° ≤ K*_j` (F2).** Let `q` be a saddle profile (its keys are the
optimal valuation `K°`). Along a trace of length `L`, `Ξ_k ≤ key G q` pointwise for all `k ≤ L`,
and `key G q ≤ key G pstar` pointwise for Even's best response `pstar` to `ps j`, for all `j ≤ L`.
See `Sandwich` (`Algorithms/ParityGame/HybridSI/Bounds.lean`). -/
theorem sandwich {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : Sandwich G bf := sorry

/-- **H-B runs independently on a closed subgame.** Let `G` be a relabelled game and `D` a set
that no edge leaves (`Closed`). For a trace of length `L`, the restrictions of the profiles and of
Odd's best responses to `D` form a trace of H-B on the subgame on `D`, of some length `LD ≤ L`. If
`LD < L`, the subgame's iteration from `pD LD` is final, and the restriction to `D` stays the same
until `L`. See `Autonomy` (`Algorithms/ParityGame/HybridSI/Bounds.lean`). -/
theorem autonomy {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : Autonomy G bf := sorry

/-- **A closed subgame adds at most the number of outside profiles (O1).** Let `G` be a
relabelled game, `bf ≥ hbFuel V` the best-response fuel and `D` a closed set. Given a trace of
length `L` on `G`, and a trace of length `LD` on the subgame on `D` that starts from the
restriction of `p 0` and ends in a final iteration, `L ≤ LD + ∏_{v ∉ D} deg v`. See
`ClosedIterations` (`Algorithms/ParityGame/HybridSI/Bounds.lean`). -/
theorem closedIterations {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : ClosedIterations G bf := sorry

/-- **Iterations are bounded by epochs.** For a trace of length `L`, let `E` be the number of
iterations `k < L` after which Odd's best response changes at some Odd vertex
(`oddChangeRounds`). Then `L ≤ (E + 1) · n_E`. See `EpochIterations`
(`Algorithms/ParityGame/HybridSI/Counting.lean`). -/
theorem epochIterations {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EpochIterations G bf := sorry

/-- **A stretch with constant `K*` has at most `n_E` iterations (F6).** Along a trace of length
`L`, if `j ≤ j' ≤ L` and the keys `K*_k` (`kstarOf`) are the same for all `j ≤ k < j'`, then
`j' − j ≤ n_E`. See `KStarBlock` (`Algorithms/ParityGame/HybridSI/Counting.lean`). -/
theorem kstarBlock {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : KStarBlock G bf := sorry

/-- **Iterations are bounded by changes of `K*`.** For a trace of length `L`, let `C` be the
number of iterations `k` with `k + 1 < L` at which `K*_{k+1} ≠ K*_k` (`kstarChangeRounds`). Then
`L ≤ C + n_E · (C + 1)`. A polynomial bound on `C` is the Lean form of the open problem. See
`KStarCount` (`Algorithms/ParityGame/HybridSI/Counting.lean`). -/
theorem kstarCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : KStarCount G bf := sorry

end MercLib.HybridSI
