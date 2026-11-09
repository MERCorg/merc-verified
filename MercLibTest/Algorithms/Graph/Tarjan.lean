import MercLib.Algorithms.Graph.Tarjan

/-!
# Tests for `MercLib.Algorithms.Graph.Tarjan`

Runs the iterative Tarjan search on small graphs and checks the result against an independent
computation: two states share a block exactly when they reach each other along the flagged (`true`)
transitions. Transitions flagged `false` are not edges and must not merge components.
-/

namespace MercLibTest.Tarjan

open MercLib.Tarjan

/-- Run `step` from `init` with at most `fuel` steps: the final context, or `none` on failure or
when the fuel runs out. -/
def run {n : ℕ} (g : Graph n) : ℕ → Ctx n → Option (Ctx n)
  | 0, _ => none
  | fuel + 1, c =>
    match step g c with
    | .next c' => run g fuel c'
    | .stop => some c
    | .fail => none

/-- A graph on `Fin n` from adjacency lists, with sentinel `n + 1`. -/
def mk (n : ℕ) (adj : Fin n → List (Bool × Fin n)) : Graph n := ⟨adj, n + 1, by omega⟩

/-- Reachability along flagged transitions, by `n` rounds of relaxation (reflexive). -/
def reach {n : ℕ} (g : Graph n) : Fin n → Fin n → Bool :=
  let step (r : Fin n → Fin n → Bool) (u v : Fin n) : Bool :=
    r u v || (List.finRange n).any fun w => r u w && (g.adj w).contains (true, v)
  (List.range n).foldl (fun r _ => step r) (fun u v => decide (u = v))

/-- The test: the run stops, and same block ⇔ mutual reachability, and the blocks are `0 … eq-1`. -/
def check {n : ℕ} (g : Graph n) : Bool :=
  match run g (10 * (n + 1) * (n + 1)) (init g) with
  | none => false
  | some c =>
    let pairs := (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)
    pairs.all (fun (u, v) => (c.blk u == c.blk v) == (reach g u v && reach g v u)) &&
      (List.finRange n).all (fun u => decide (c.blk u < c.eq)) &&
      (List.range c.eq).all fun b => (List.finRange n).any fun u => c.blk u == b

/-- A cycle `0 → 1 → 2 → 0` with an exit `2 → 3`: blocks `{0, 1, 2}` and `{3}`. -/
def g1 : Graph 4 := mk 4 fun
  | 0 => [(true, 1)] | 1 => [(true, 2)] | 2 => [(true, 0), (true, 3)] | 3 => []

/-- The same, but `2 → 0` is not flagged: four singleton blocks. -/
def g2 : Graph 4 := mk 4 fun
  | 0 => [(true, 1)] | 1 => [(true, 2)] | 2 => [(false, 0), (true, 3)] | 3 => []

/-- Two cycles joined one way, with self-loops and an isolated state:
`{0, 1}`, `{2, 3, 4}`, `{5}`. -/
def g3 : Graph 6 := mk 6 fun
  | 0 => [(true, 1), (true, 0)] | 1 => [(true, 0), (true, 2)] | 2 => [(true, 3)]
  | 3 => [(true, 4), (false, 1)] | 4 => [(true, 2), (true, 4)] | 5 => []

/-- The empty graph. -/
def g4 : Graph 0 := mk 0 fun i => i.elim0

#guard check g1
#guard check g2
#guard check g3
#guard check g4

/-- The same test for the do-notation version `tarjan`, which must agree with the step machine. -/
def checkRun {n : ℕ} (g : Graph n) : Bool :=
  match tarjan g, run g (10 * (n + 1) * (n + 1)) (init g) with
  | some c, some c' =>
    let pairs := (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)
    pairs.all (fun (u, v) => (c.blk u == c.blk v) == (reach g u v && reach g v u)) &&
      c.eq == c'.eq && (List.finRange n).all fun u => c.blk u == c'.blk u
  | _, _ => false

#guard checkRun g1
#guard checkRun g2
#guard checkRun g3
#guard checkRun g4

/-- The number of blocks found. -/
def blocks {n : ℕ} (g : Graph n) : Option ℕ := (run g 1000 (init g)).map (·.eq)

#guard blocks g1 = some 2
#guard blocks g2 = some 4
#guard blocks g3 = some 3
#guard blocks g4 = some 0

end MercLibTest.Tarjan
