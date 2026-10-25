import MercLib.HybridSI.Correctness
import MercLib.HybridSI.Epoch
import MercLib.HybridSI.BestResponse
import MercLib.HybridSI.AlgorithmPoly
import MercLib.HybridSI.Potential
import MercLib.HybridSI.Bounds
import MercLib.HybridSI.SingleOdd
import MercLib.HybridSI.SingleOddPoly
import MercLib.HybridSI.SingleOddStretch
import MercLib.HybridSI.SingleOddCore

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

/-- A trace has at most `(E + 1) · n_E` iterations, `E` the number of epoch changes. -/
theorem epochIterations {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EpochIterations G bf := sorry

/-- Epoch changes raise the escape value of any Odd vertex to a new value or are escape ties. -/
theorem escapeCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EscapeCount G bf := sorry

/-- The escape values split by the cycle maximum of the chosen successor. -/
theorem escapeClasses {V : Type*} [Fintype V] [LinearOrder V] : EscapeClasses V := sorry

/-- Per cycle maximum, at most `2n + 1` escape values have `B`-sum `0`. -/
theorem escapeClassSplit {V : Type*} [Fintype V] [LinearOrder V] : EscapeClassSplit V := sorry

/-- The escape of an Odd vertex has at most `n² - 1` cut rounds. -/
theorem escapeCutCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : EscapeCutCount G bf := sorry

/-- At most `c` non-final epoch changes per cut-free stretch give at most `(c + 1) n²` epoch
    changes plus those reaching the final escape value. -/
theorem segmentCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : SegmentCount G bf := sorry

/-- `SegmentConjecture` implies `SingleOddPoly`. -/
theorem segmentReduction : SegmentReduction := sorry

/-- At most `c` iterations per stretch without a cycle-maximum change bound the iterations. -/
theorem stretchCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : StretchCount G bf := sorry

/-- At most `c` iterations per stretch without a downward move bound the iterations. -/
theorem downCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : DownCount G bf := sorry

/-- `DownConjecture` implies `SingleOddPoly`. -/
theorem downReduction : DownReduction := sorry

/-- `StretchConjecture` implies `SingleOddPoly`. -/
theorem stretchReduction : StretchReduction := sorry

/-- `SingleOddEscapeConjecture` implies `SingleOddPoly`. -/
theorem singleOddReduction : SingleOddReduction := sorry

/-- Lemma NT: in an `l`-stable iteration a switched non-top Even vertex strictly raises its key. -/
theorem nonTopStrict {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : NonTopStrict G bf := sorry

/-- Lemma SK: an iteration without key change, followed by a non-final one, is an escape tie. -/
theorem sameKeysTie {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : SameKeysTie G bf := sorry

/-- Theorem DR: a stretch has at most `(R + 1) · n(2n - 1) + Tie + 1` iterations. -/
theorem decisiveStretch {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : DecisiveStretch G bf := sorry

/-- Uniform DR: at most `r` rises per stretch and `t` escape ties bound every stretch. -/
theorem decisiveStretchBound {V : Type*} [Fintype V] [LinearOrder V] (G : Game V)
    [DecidableRel G.edge] (bf : ℕ) : DecisiveStretchBound G bf := sorry

/-- At most `r` rises per stretch and `t` escape ties bound the iterations. -/
theorem decisiveIterations {V : Type*} [Fintype V] [LinearOrder V] (G : Game V)
    [DecidableRel G.edge] (bf : ℕ) : DecisiveIterations G bf := sorry

/-- `RiseConjecture` implies `SingleOddRisePoly`. -/
theorem riseReduction : RiseReduction := sorry

/-- A stretch with constant keys `K*` has at most `n_E` iterations. -/
theorem kstarBlock {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : KStarBlock G bf := sorry

/-- A trace has at most `C + n_E (C + 1)` iterations, `C` the number of changes of `K*`. -/
theorem kstarCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : KStarCount G bf := sorry

/-- `KChangeConjecture` implies `SingleOddPoly`. -/
theorem kChangeReduction : KChangeReduction := sorry

/-- R2: the profiles freeze on the vertices that cannot reach `u` within `numEvenIn` iterations. -/
theorem unreachFreeze {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : UnreachFreeze G bf := sorry

/-- At most `(#up + 1)(r - 1)` downward moves of the world value. -/
theorem upDownCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : UpDownCount G bf := sorry

/-- At most `deg u` distinct world values if `K*` depends only on Odd's choice at `u`. -/
theorem worldsBound {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : WorldsBound G bf := sorry

/-- If equal world values give equal `K*`, then `K*` changes only at up and down moves. -/
theorem kstarUpDown {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : KStarUpDown G bf := sorry

/-- `#K*-changes + 1 ≤ deg u · (#up + 1)`. -/
theorem kstarUpCount {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]
    (bf : ℕ) : KStarUpCount G bf := sorry

/-- `MonotoneWorlds` and `UpConjecture` imply `KChangeConjecture`. -/
theorem upReduction : UpReduction := sorry

/-- MW: with a single Odd choice vertex, `K*` depends only on Odd's choice at `u`, and world
    values compare like the keys `K*`. -/
theorem monotoneWorlds : MonotoneWorlds := sorry

/-- `UpConjecture` alone implies `SingleOddPoly`. -/
theorem upPoly : UpPoly := sorry

end MercLib.HybridSI
