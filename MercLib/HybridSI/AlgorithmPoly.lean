module

public import MercLib.HybridSI.BestResponse
public import MercLib.HybridSI.Correctness

@[expose] public section HybridSIAlgorithmPoly

namespace MercLib.HybridSI

open MercLib.ParityGame Cslib.Algorithms.Lean

/-!
# H-B with polynomial best responses

`hbStepPoly` is one iteration of H-B (`hbStep`, `HybridSI.Algorithm`) with both best responses
computed by `bestResponse` (`HybridSI.BestResponse`) instead of fuel-driven strategy improvement,
so it never gets stuck; `hbRunPoly` iterates it. Both are in `TimeM ℕ`, with the cost model of
`HybridSI.BestResponse`, and in addition:
* a key table (`keyTableT`) costs `n (n + 1)³`: `key` is evaluated naively at each of the `n`
  vertices (`O(n)` candidate positions, each recomputing `O(n)`-step iterates and the `O(n²)`
  cycle maximum);
* the optimality test (all improving sets empty) scans every successor list once:
  `roundCost (succList G)`;
* computing the filter and the switched profile scans every successor list four times (the
  values `kstar` of the successors, their maximum, the improving edges, the filter, and the
  `ks`-argmax): `4 · roundCost (succList G)`;
* one tick per iteration of `hbRunPoly`'s loop.

Contracts (proved in `HybridSI/Proofs/AlgorithmPoly_Proofs.lean`):
* `HBStepCost`: one iteration costs at most `hbStepBound n m`, a polynomial in `n = |V|` and the
  number of edges `m`;
* `HBRunCost`: a run that returns after `it` iterations costs at most
  `(it + 1) · (hbStepBound n m + 1)`
  (H-B is polynomial up to its iteration count);
* `HBPolyCorrect`: whenever the run returns, the winners read off the returned valuation are the
  winners of the game.
-/

variable {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]

/-- The key table of a profile, timed. -/
def keyTableT (f : V → V) : TimeM ℕ (List (V × Key)) := do
  ✓[Fintype.card V * (Fintype.card V + 1) ^ 3] return keyTable G f

/-- One H-B iteration from profile `p` with polynomial best responses. -/
def hbStepPoly (p : V → V) : TimeM ℕ (Step V) := do
  let ps ← bestResponseT G true p
  let kst ← keyTableT G ps
  let ks : V → Key := fun v => look kst keyDefault v
  ✓[roundCost (succList G)] let opt := (univList V).all fun v => (improving G ks p v).isEmpty
  if opt then return .done kst
  else do
    let pstar ← bestResponseT G false ps
    let kt ← keyTableT G pstar
    let kstar : V → Key := fun v => look kt keyDefault v
    ✓[4 * roundCost (succList G)] let useF := (univList V).any fun v => !(filtered G ks kstar p v).isEmpty
    let src := if useF then filtered G ks kstar p else improving G ks p
    return .next (tabulate fun v => if (src v).isEmpty then p v else argmaxKey ks (p v) (src v))

/-- H-B from profile `p` with at most `fuel` iterations, counting iterations from `it`. -/
def hbRunPoly : ℕ → ℕ → (V → V) → TimeM ℕ (Option (ℕ × List (V × Key)))
  | 0, _, _ => return none
  | fuel + 1, it, p => do
    ✓ let r ← hbStepPoly G p
    match r with
    | .done ks => return some (it, ks)
    | .next qt => hbRunPoly fuel (it + 1) fun v => look qt v v
    | .stuck => return none

/-- The cost bound of one iteration. -/
def hbStepBound (n m : ℕ) : ℕ := 2 * bestResponseBound n m + 2 * n * (n + 1) ^ 3 + 5 * (m + n)

/-- Contract (cost of one iteration). -/
def HBStepCost (p : V → V) : Prop :=
  (hbStepPoly G p).time ≤ hbStepBound (Fintype.card V) (edgeCount G)

/-- Contract (cost of a run): polynomial in the size of the game times the number of
    iterations. -/
def HBRunCost (fuel : ℕ) : Prop :=
  ∀ it kt, (hbRunPoly G fuel 0 (initProfile G)).ret = some (it, kt) →
    (hbRunPoly G fuel 0 (initProfile G)).time ≤ (it + 1) * (hbStepBound (Fintype.card V) (edgeCount G) + 1)

/-- Contract (correctness): if the run returns the key table `kt`, then player `i` wins from `v`
    exactly when `i` is the winner of `v`'s key. -/
def HBPolyCorrect (fuel : ℕ) : Prop :=
  G.Relabelled → ∀ it kt, (hbRunPoly G fuel 0 (initProfile G)).ret = some (it, kt) →
    ∀ v i, keyWinner (look kt keyDefault v) = i ↔ ∃ σ, G.WinsFrom Set.univ i σ v

end MercLib.HybridSI

end HybridSIAlgorithmPoly
