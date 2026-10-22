import MercLib.HybridSI.Correctness
import MercLib.HybridSI.Epoch
import MercLib.HybridSI.BestResponse
import MercLib.HybridSI.AlgorithmPoly
import MercLib.HybridSI.Potential
import MercLib.HybridSI.Bounds
import MercLib.HybridSI.SingleOdd

/-!
# Comparator challenge: hybrid strategy improvement (human-vetted)

The headline theorems of `MercLib/HybridSI/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib`.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.HybridSI

open MercLib.ParityGame

/-- Correctness of H-B: whenever it returns, the winners read off the returned valuation are the
    winners of the game. -/
theorem hbCorrect {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf fuel : ℕ) : HBCorrect G bf fuel := sorry

/-- With fuel `|V|^|V| + 1` H-B returns. -/
theorem hbTerminates {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf fuel : ℕ) : HBTerminates G bf fuel := sorry

/-- The filter is never empty while `σ` is not optimal. -/
theorem filterNonempty {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) (p : V → V) : FilterNonempty G bf p := sorry

/-- An epoch (constant Odd best response) has at most `n_E` iterations. -/
theorem epochBound {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EpochBound G bf := sorry

/-- The polynomial best response is a best response: it changes only `pl`'s moves, follows edges,
    and no `pl`-vertex has a strictly better successor. -/
theorem bestResponse_optimal {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (pl : Bool) (p : V → V) : BestResponseOptimal G pl p := sorry

/-- The polynomial best response takes at most `4 (n + 1)² (m + 2n + 1)` steps. -/
theorem bestResponse_cost {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (pl : Bool) (p : V → V) : BestResponseCost G pl p := sorry

/-- One iteration of the polynomial H-B variant takes at most `hbStepBound n m` steps. -/
theorem hbStepPoly_cost {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (p : V → V) : HBStepCost G p := sorry

/-- A run of the polynomial H-B variant returning after `it` iterations costs at most
    `(it + 1) · (hbStepBound n m + 1)`. -/
theorem hbRunPoly_cost {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (fuel : ℕ) : HBRunCost G fuel := sorry

/-- Correctness of the polynomial H-B variant. -/
theorem hbPolyCorrect {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (fuel : ℕ) : HBPolyCorrect G fuel := sorry

/-- A returning run yields a trace of its iterations. -/
theorem runTraceOfRun {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : RunTraceOfRun G bf := sorry

/-- Along a run the valuation (keys of Odd's best responses) is pointwise non-decreasing. -/
theorem valuationMonotone {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : ValuationMonotone G bf := sorry

/-- At most `n (n - 1)` iterations change some vertex's cycle maximum. -/
theorem cycleMaxChanges {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : CycleMaxChanges G bf := sorry

/-- Each vertex's cycle maximum changes at most `n - 1` times. -/
theorem vertexCycMaxChanges {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : VertexCycMaxChanges G bf := sorry

/-- At most `2 (n - 1)` crossings of a pair coincide with a change of either cycle maximum. -/
theorem crossCycMaxChanges {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : CrossCycMaxChanges G bf := sorry

/-- Epoch changes are bounded by tie rounds plus sibling-pair crossings. -/
theorem epochCrossings {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EpochCrossings G bf := sorry

/-- Rounds changing some vertex's (cycle maximum, top membership) are at most `n (2n - 1)`. -/
theorem topChanges {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : TopChanges G bf := sorry

/-- If every Even edge is switched into at most `c` times, a run has at most `c · m_E` iterations. -/
theorem entryIterations {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) (p₀ : V → V) (c : ℕ) : EntryIterations G bf p₀ c := sorry

/-- The open conjecture ENT (each Even edge entered at most `|V|` times) implies polynomially
    many iterations. -/
theorem entryPoly : EntryPoly := sorry

/-- Any two saddle profiles have the same keys (the optimal valuation is unique). -/
theorem saddleUnique {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge] :
    SaddleUnique G := sorry

/-- Every relabelled game has a saddle profile. -/
theorem saddleExists {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge] :
    SaddleExists G := sorry

/-- Along a trace `Ξ_k ≤ K*_j`. -/
theorem lowerBelowUpper {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : LowerBelowUpper G bf := sorry

/-- The sandwich `Ξ_k ≤ v* ≤ K*_j` (P2). -/
theorem sandwich {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : Sandwich G bf := sorry

/-- Autonomy: on a closed subgame the trace restricts to a trace of the subgame. -/
theorem autonomy {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : Autonomy G bf := sorry

/-- O1: a closed subgame adds at most the number of profiles outside it. -/
theorem closedIterations {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : ClosedIterations G bf := sorry

/-- Lemma M: truncations of `B` are monotone while the cycle maximum is fixed. -/
theorem truncationMonotone {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : TruncationMonotone G bf := sorry

/-- P4: at most `n` iterations with decisive element `x` in a stable stretch. -/
theorem decisiveRounds {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : DecisiveRounds G bf := sorry

/-- EDEC2: inside an epoch and an `l`-interval the decisive bound propagates. -/
theorem epochDecisive {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EpochDecisive G bf := sorry

/-- ESEP: no reset of the decisive element inside an epoch and an `l`-interval. -/
theorem epochNoReset {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EpochNoReset G bf := sorry

/-- LOC: a jump of the decisive element is adjacent to a change of Odd's best response. -/
theorem resetLocal {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : ResetLocal G bf := sorry

/-- K2: a vertex and its successor have the same cycle maximum. -/
theorem cycMaxSucc {V : Type*} [Fintype V] [LinearOrder V] : CycMaxSucc V := sorry

/-- K1: Odd's move at every state is a successor of minimal key. -/
theorem oddOptimal {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : OddOptimal G bf := sorry

/-- K3: a cycle-maximum-stable Odd switch is between successors of equal cycle maximum. -/
theorem stableOddChange {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : StableOddChange G bf := sorry

/-- MMON: the key of Odd's chosen successor never decreases. -/
theorem escapeMonotone {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EscapeMonotone G bf := sorry

/-- K4: with one Odd choice vertex, epoch changes are at most `deg u · (n - 1)` plus the local ones. -/
theorem singleOddEpochs {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : SingleOddEpochs G bf := sorry

/-- Local epoch changes switch `u` between successors with `u`'s cycle maximum. -/
theorem locSameTop {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : LocSameTop G bf := sorry

end MercLib.HybridSI
