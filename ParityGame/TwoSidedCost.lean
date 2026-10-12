module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section TwoSidedCost

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean

/-!
# A time-complexity model of two-sided lifting over instance-derived trees

A concrete, computable solver for finite parity games in cslib's `TimeM ℕ` monad, mirroring the
Rust prototype `merc/crates/vpg/src/two_sided_lifting.rs` (`solve_game`, `Lifter::{run, evaluate,
certified, accelerate, even_cycle_maxima}`, `ChainTree::{info, chain_bound, weak_components,
leftmost, next_node}`, `attractor`; write-up `experiments/FINDINGS.md` §5). Correctness of the
returned winners is *not* stated here (see `ParityGame.TwoSidedAlgorithm` for the abstract
algorithm); this file only states cost bounds. The program counts `steps` = successful lifts plus
vertices raised by acceleration (the Rust `Stats.steps`), and the headline `SolveTimeBound` says
that the running time is at most `(steps + n + 1) · P(n, m, d)` for an explicit polynomial `P`
(`costPoly`): the solver is polynomial whenever the number of lift steps is. Whether `steps` is
polynomial is open (`Game.PolyLiftingConjecture` in `ParityGame.Lifting`).

## Representation
* `PGame n`: vertices `Fin n`, priorities `prio : Fin n → ℕ` (max-parity: player `0`/Even wins
  plays whose greatest recurring priority is even), owners `owner : Fin n → Bool`
  (`false` = Even, `true` = Odd), successor lists `succ : Fin n → List (Fin n)`.
  `PGame.m` = total number of edges, `PGame.d` = greatest priority + 1, and
  `PGame.size` = `N = n + m + d + 2` is the single size parameter of all bounds.
* Vertex sets are bit vectors `VSet n = Fin n → Bool` (`Function.update` for single changes,
  `materialize` after a set comprehension so that `#eval` stays fast).
* `Ctx n` is one player's view of the remaining subgame (Rust `View`): `p = true` is the dual
  game for Odd (priority `+ 1`, owner swapped, i.e. "mine" = owned by `p`); successors and
  predecessors are restricted to the alive vertices; `levels` are the odd view priorities of the
  alive vertices in decreasing order (`height = levels.length ≤ d + 1`).
* Tree values `Val = Option (List (ℕ × ℕ))`, `none` = ⊤. A leaf is a list of `h` pairs
  (component index, counter), one per odd level. The Rust element also carries the region id;
  that is determined by the preceding elements, so it is not stored here but recomputed on demand
  (`regionsOf`; root region = alive vertices, the region of element `l + 1` is the `k_{l+1}`-th
  child of the region of element `l`).

## Cost model
`TimeM` time annotations are trusted (cslib design principle 2), so here is exactly what is
charged. The unit is one elementary RAM operation on the representation above.
* **One tick** per iteration of every loop (each element visited by a fold, each pop of a
  worklist, each lexicographic element comparison, each round of a fixpoint iteration), covering
  the constant-time work done in that iteration.
* **Non-constant pure work is charged explicitly** with `✓[c]`, where `c` is the length of what
  it traverses: building a vertex-set comprehension, scanning all vertices once (a filter
  followed by a fold over its result counts as one pass), or counting a set costs `n`; filtering
  the successor list of `v` costs `|succ v| + 1`; computing the alive predecessors of `v` (a scan
  of all edges) costs `n + m`; pushing or testing the elements of a list costs its length;
  `leftmost` costs one tick per appended element; `prog` pays `h + 1` for looking up the depth of
  the vertex (a precomputed array in Rust, `Lifter::depth`; recomputed here from `levels`) and
  copying the target's prefix; the bookkeeping of one `next_node` iteration costs `h + 1`.
* **Free**: reading or writing one entry of a bit vector / array (`VSet`, `measure`, `choice`,
  modelled by functions and `Function.update`), creating a fresh empty set or map (Rust's
  `StampSet::clear` / `FxHashMap::default`), indexing into a children list (a `Vec` in Rust),
  pattern matching, arithmetic on counters, pushing or popping one element of a queue or stack,
  and returning. `materialize`, closures and `Function.update` chains are artefacts of the
  functional encoding.
* **Recursion**: a call itself is free; every recursive loop is driven by explicit fuel, and its
  body pays one tick per iteration as above.
* Values are compared lexicographically on their first `h` elements only (`lexCmp h`, one tick per
  compared element). All values built by the program have length `≤ h`, so this agrees with the
  Rust `Vec` comparison.

## Headlines (proved in `ParityGame.Proofs.TwoSidedCost_Proofs`)
With `N = n + m + d + 2`: `NavigationCost` (`leftmost`, comparison `≤ N`, `nextNode ≤ 30 N⁴`,
`prog ≤ 32 N⁴`), `RegionInfoCost` (`≤ 10 N³`), `EvaluateCost` (`≤ (deg v + 1) · 35 N⁴`),
`AccelerateCost` (`≤ 175 N⁷`), `LiftingAmortised` (`250 N⁷` per step, potential
`37 N⁵ · |queue|`), `CertifiedCost` (`≤ 43 N⁷`), `AttractorCost` (`≤ 2 N³`), and the main
theorem `SolveTimeBound`: `time ≤ (steps + n + 1) · 340 N⁷` and `restarts ≤ n + 1`, with the
corollary `SolvePolyOfSteps`. `RestartProgress` and `OuterFuelSuffices` show that the outer fuel
`n + 1` never runs out: every non-final restart removes a vertex.

## Deviations from the Rust code (behaviour-preserving unless stated)
* Termination: every loop has explicit fuel. Lifting (`runLoop`) and the round loop of a restart
  (`roundLoop`) share the fuel parameter `fuel` of `solve`; running out yields `winner = none`
  ("out of fuel"). The outer loop has fuel `n + 1`, which suffices because each non-final restart
  removes at least one vertex (`RestartProgress`, `OuterFuelSuffices`). Inner loops whose
  iteration count is bounded by the Rust logic get that bound as fuel (`n + 1` for graph
  searches, the acceleration restriction loop and attractor passes, `n² + n + 1` for
  certification); exhausting it is treated conservatively (no acceleration, nothing certified).
* Region information is recomputed on demand instead of interned and memoised.
* SCCs are computed via pairwise reachability, the chain bound by a longest-path DP over the
  reachability order (`n + 1` Jacobi rounds), weak components by repeated DFS from the roots in
  index order (so they come out sorted by least vertex, as Rust sorts them).
* `evenCycleMaxima` returns the same set as Rust's peeling recursion, computed directly: an
  even-priority member `u` is a maximum of an even-maximum cycle iff `u` reaches itself through
  kept edges inside `{w ∈ members | prio w ≤ prio u}`.
* `attractor` is the same set as Rust's, computed by `n + 1` passes over all vertices instead of
  the backward worklist with successor counters.
* Acceleration iterates over the members in vertex-index order (Rust: discovery order of the
  backward search). Final values are the same, but the order of re-queued vertices, and hence
  the subsequent schedule and `steps`, may differ.
* Successors are scanned in list order; pushing successors onto a DFS stack uses `pushNew`
  (all unvisited at once), which changes the visiting order but not the visited set.
-/

/-! ## Games, sets, views -/

/-- A finite parity game on vertices `Fin n` (max-parity; `owner v = false` is Even). -/
structure PGame (n : ℕ) where
  prio : Fin n → ℕ
  owner : Fin n → Bool
  succ : Fin n → List (Fin n)

namespace PGame

variable {n : ℕ} (G : PGame n)

/-- Total number of edges. -/
def m : ℕ := ((List.finRange n).map fun v => (G.succ v).length).sum

/-- Greatest priority + 1 (an upper bound on the number of distinct priorities). -/
def d : ℕ := ((List.finRange n).map G.prio).foldr max 0 + 1

/-- The size parameter `N = n + m + d + 2` of all cost bounds. -/
def size : ℕ := n + G.m + G.d + 2

end PGame

/-- A set of vertices as a bit vector. -/
abbrev VSet (n : ℕ) := Fin n → Bool

/-- The empty set. -/
def VSet.empty {n : ℕ} : VSet n := fun _ => false

/-- The singleton `{v}`. -/
def VSet.single {n : ℕ} (v : Fin n) : VSet n := fun u => decide (u = v)

/-- Evaluate a set once into an array (only for `#eval` speed; extensionally the identity). -/
def materialize {n : ℕ} (S : VSet n) : VSet n :=
  let a := Vector.ofFn S
  fun i => a[i]

/-- The number of elements of a set. -/
def VSet.count {n : ℕ} (S : VSet n) : ℕ := ((List.finRange n).filter S).length

/-- A measure value: a leaf of the chain tree, `none` = ⊤. -/
abbrev Val := Option (List (ℕ × ℕ))

/-- One player's view of the remaining subgame (Rust `View` + the levels of its `ChainTree`). -/
structure Ctx (n : ℕ) where
  G : PGame n
  /-- The lifting player (`true`: Odd, lifting in the dual game). -/
  p : Bool
  alive : VSet n
  /-- The odd view priorities of the alive vertices, decreasing. -/
  levels : List ℕ
  levels_le : levels.length ≤ G.d + 1

namespace Ctx

variable {n : ℕ} (c : Ctx n)

/-- View priority: `+ 1` in the dual game. -/
def prio (v : Fin n) : ℕ := c.G.prio v + if c.p then 1 else 0

/-- Is `v` owned by the lifting player? -/
def mine (v : Fin n) : Bool := c.G.owner v == c.p

/-- The height `h` of the chain tree (number of odd levels). -/
def height : ℕ := c.levels.length

/-- The odd priority of level `l`. -/
def level (l : ℕ) : ℕ := c.levels.getD l 0

/-- The size parameter of the underlying game. -/
def N : ℕ := c.G.size

end Ctx

variable {n : ℕ}

/-- Alive successors of `v`. -/
def succT (c : Ctx n) (v : Fin n) : TimeM ℕ (List (Fin n)) := do
  ✓[(c.G.succ v).length + 1] return (c.G.succ v).filter c.alive

/-- Alive predecessors of `v` (a scan of all edges). -/
def predT (c : Ctx n) (v : Fin n) : TimeM ℕ (List (Fin n)) := do
  ✓[n + c.G.m] return (List.finRange n).filter fun u => c.alive u && (c.G.succ u).contains v

/-! ## Generic loops -/

/-- Timed filter. -/
def filterT {α : Type} (p : α → TimeM ℕ Bool) : List α → TimeM ℕ (List α)
  | [] => pure []
  | x :: xs => do
    let b ← p x
    let r ← filterT p xs
    return if b then x :: r else r

/-- `k` iterations of a timed step. -/
def iterT {α : Type} (f : α → TimeM ℕ α) : ℕ → α → TimeM ℕ α
  | 0, a => pure a
  | k + 1, a => do
    let a' ← f a
    iterT f k a'

/-- Push the elements of `ys` that satisfy `ok` and are not yet `seen`, marking them seen. -/
def pushNew (ok : VSet n) : List (Fin n) → VSet n → List (Fin n) → VSet n × List (Fin n)
  | [], seen, st => (seen, st)
  | y :: ys, seen, st =>
    if ok y && !seen y then pushNew ok ys (Function.update seen y true) (y :: st)
    else pushNew ok ys seen st

/-- Depth-first exploration with a worklist `stack`, threading a state `σ` through the
    neighbour function (fuel = number of pops). Returns the final state and the visited set. -/
def explore {σ : Type} (nbrs : σ → Fin n → TimeM ℕ (σ × List (Fin n))) (ok : VSet n) :
    ℕ → σ → VSet n → List (Fin n) → TimeM ℕ (σ × VSet n)
  | 0, s, seen, _ => pure (s, seen)
  | _ + 1, s, seen, [] => pure (s, seen)
  | k + 1, s, seen, x :: stack => do
    ✓ let r ← nbrs s x
    ✓[r.2.length] let ps := pushNew ok r.2 seen stack
    explore nbrs ok k r.1 ps.1 ps.2

/-- The vertices reachable from `v` (inclusive) via `nbrs`, within `ok`. -/
def reachSet (nbrs : Fin n → TimeM ℕ (List (Fin n))) (ok : VSet n) (v : Fin n) :
    TimeM ℕ (VSet n) := do
  let r ← explore (fun (_ : Unit) x => do let ys ← nbrs x; return ((), ys)) ok (n + 1) ()
    (VSet.single v) [v]
  return r.2

/-! ## The chain tree (Rust `ChainTree`) -/

/-- Neighbours of `x` in the undirected graph restricted to `S`. -/
def undirected (c : Ctx n) (S : VSet n) (x : Fin n) : TimeM ℕ (List (Fin n)) := do
  let s ← succT c x
  let p ← predT c x
  ✓[s.length + p.length] return (s ++ p).filter S

/-- One root of `weakComponents`: visited vertices and the components so far. -/
def wcStep (c : Ctx n) (S : VSet n) (acc : VSet n × List (VSet n)) (root : Fin n) :
    TimeM ℕ (VSet n × List (VSet n)) := do
  ✓ if S root && !acc.1 root then do
      let comp ← reachSet (undirected c S) S root
      ✓[n] return (materialize fun v => acc.1 v || comp v, acc.2 ++ [comp])
    else return acc

/-- Weakly connected components of `S`, ordered by least vertex (Rust `weak_components`). -/
def weakComponents (c : Ctx n) (S : VSet n) : TimeM ℕ (List (VSet n)) := do
  let r ← (List.finRange n).foldlM (wcStep c S) (VSet.empty, [])
  return r.2

/-- The child regions of a region `R` at level `l`: the weak components of `R` restricted to
    priorities below the level's odd priority; a single empty child if there is none
    (Rust `info(..).components`). -/
def children (c : Ctx n) (l : ℕ) (R : VSet n) : TimeM ℕ (List (VSet n)) := do
  ✓[n] let S : VSet n := materialize fun v => R v && decide (c.prio v < c.level l)
  let comps ← weakComponents c S
  return if comps.isEmpty then [VSet.empty] else comps

/-- The DP entry of `u`: its weight plus the best value of a strictly later SCC. -/
def chainEntry (S : VSet n) (reach : Fin n → VSet n) (weight : Fin n → ℕ) (best : Fin n → ℕ)
    (b : Fin n → ℕ) (u : Fin n) : TimeM ℕ (Fin n → ℕ) := do
  let later := (List.finRange n).filter fun w => S w && reach u w && !reach w u
  ✓[n] return Function.update b u (weight u + later.foldr (fun w a => max (best w) a) 0)

/-- One Jacobi round of the longest-path DP over the condensation. -/
def chainRound (S : VSet n) (reach : Fin n → VSet n) (weight : Fin n → ℕ) (best : Fin n → ℕ) :
    TimeM ℕ (Fin n → ℕ) :=
  (List.finRange n).foldlM (chainEntry S reach weight best) (fun _ => 0)

/-- Successors inside `S`. -/
def succIn (c : Ctx n) (S : VSet n) (x : Fin n) : TimeM ℕ (List (Fin n)) := do
  let s ← succT c x
  ✓[s.length] return s.filter S

/-- Record the vertices reachable from `u` inside `S`. -/
def reachStep (c : Ctx n) (S : VSet n) (r : Fin n → VSet n) (u : Fin n) :
    TimeM ℕ (Fin n → VSet n) := do
  let ru ← reachSet (succIn c S) S u
  return Function.update r u ru

/-- Record the weight of the SCC of `u`: its number of priority-`q` vertices. -/
def weightStep (c : Ctx n) (S : VSet n) (q : ℕ) (reach : Fin n → VSet n) (w : Fin n → ℕ)
    (u : Fin n) : TimeM ℕ (Fin n → ℕ) := do
  let k := (List.finRange n).filter fun x => S x && reach u x && reach x u && c.prio x == q
  ✓[n] return Function.update w u k.length

/-- Longest path through the SCC condensation of `R ∩ {prio ≤ q}`, each SCC weighted by its
    number of priority-`q` vertices (Rust `chain_bound`). -/
def chainBound (c : Ctx n) (R : VSet n) (q : ℕ) : TimeM ℕ ℕ := do
  ✓[n] let S : VSet n := materialize fun v => R v && decide (c.prio v ≤ q)
  let reach ← (List.finRange n).foldlM (reachStep c S) (fun _ => VSet.empty)
  let weight ← (List.finRange n).foldlM (weightStep c S q reach) (fun _ => 0)
  let best ← iterT (chainRound S reach weight) (n + 1) (fun _ => 0)
  ✓[n] return ((List.finRange n).filter S).foldr (fun u a => max (best u) a) 0

/-- The regions of the elements of a path whose first element lies in region `R` at level `l`. -/
def regionsOf (c : Ctx n) : ℕ → VSet n → List (ℕ × ℕ) → TimeM ℕ (List (VSet n))
  | _, _, [] => pure []
  | l, R, _ :: rest =>
    match rest with
    | [] => pure [R]
    | (k, _) :: _ => do
      let ch ← children c l R
      ✓ let R' := ch.getD k VSet.empty
      let rs ← regionsOf c (l + 1) R' rest
      return R :: rs

/-- The loop of Rust `next_node`, from the last element backwards (fuel = path length). -/
def nextAux (c : Ctx n) (regs : List (VSet n)) : ℕ → List (ℕ × ℕ) →
    TimeM ℕ (Option (List (ℕ × ℕ)))
  | 0, _ => pure none
  | f + 1, path =>
    match path.getLast? with
    | none => pure none
    | some (k, cnt) => do
      let depth := path.length - 1
      let b ← chainBound c (regs.getD depth VSet.empty) (c.level depth)
      ✓[c.height + 1] if cnt < b then return some (path.set depth (k, cnt + 1))
      else if 0 < depth then do
        let sib ← children c (depth - 1) (regs.getD (depth - 1) VSet.empty)
        if k + 1 < sib.length then return some (path.set depth (k + 1, 0))
        else nextAux c regs f path.dropLast
      else nextAux c regs f path.dropLast

/-- The next node at the same depth in lexicographic order, if any (Rust `next_node`). -/
def nextNode (c : Ctx n) (pre : List (ℕ × ℕ)) : TimeM ℕ (Option (List (ℕ × ℕ))) := do
  let regs ← regionsOf c 0 c.alive pre
  nextAux c regs pre.length pre

/-- Extend a prefix with the first child at every remaining level (Rust `leftmost`). -/
def leftmost (c : Ctx n) (pre : List (ℕ × ℕ)) : TimeM ℕ (List (ℕ × ℕ)) := do
  ✓[c.height - pre.length] return pre ++ List.replicate (c.height - pre.length) (0, 0)

/-- Lexicographic comparison on the first `k` elements, one tick per compared element. -/
def lexCmp : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → TimeM ℕ Ordering
  | 0, _, _ => pure .eq
  | _ + 1, [], [] => pure .eq
  | _ + 1, [], _ :: _ => pure .lt
  | _ + 1, _ :: _, [] => pure .gt
  | k + 1, x :: xs, y :: ys => do
    ✓ match (compare x.1 y.1).then (compare x.2 y.2) with
    | .eq => lexCmp k xs ys
    | o => return o

/-- Comparison of values, `none` = ⊤ (Rust `cmp_value`). -/
def cmpVal (c : Ctx n) : Val → Val → TimeM ℕ Ordering
  | none, none => pure .eq
  | none, some _ => pure .gt
  | some _, none => pure .lt
  | some a, some b => lexCmp c.height a b

/-- Number of tree levels compared by the progress condition of `v` (Rust `Lifter::depth`). -/
def depthOf (c : Ctx n) (v : Fin n) : ℕ :=
  (c.levels.filter fun q => if c.prio v % 2 == 0 then decide (c.prio v < q)
    else decide (c.prio v ≤ q)).length

/-- The least value for `v` progressing towards a successor with value `target` (Rust `prog`). -/
def prog (c : Ctx n) (v : Fin n) (target : Val) : TimeM ℕ Val := do
  ✓[c.height + 1] match target with
  | none => return none
  | some t =>
    let pre := t.take (depthOf c v)
    if c.prio v % 2 == 0 then do
      let l ← leftmost c pre
      return some l
    else do
      match ← nextNode c pre with
      | none => return none
      | some nx => do
        let l ← leftmost c nx
        return some l

/-! ## Lifting (Rust `Lifter`) -/

/-- The state of one player's lifting. -/
structure LState (n : ℕ) where
  measure : Fin n → Val
  choice : Fin n → Option (Fin n)
  queue : List (Fin n)
  inq : VSet n
  steps : ℕ

/-- One successor `w` in `evaluate`: the best value and successor so far. -/
def evalStep (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n))
    (acc : Option (Val × Fin n)) (w : Fin n) : TimeM ℕ (Option (Val × Fin n)) := do
  ✓ if (allowed.map fun a => a w).getD true then do
      let val ← prog c v (μ w)
      match acc with
      | none => return some (val, w)
      | some (cur, cw) => do
        let o ← cmpVal c val cur
        let better := if c.mine v then o == .lt else o != .lt
        return if better then some (val, w) else some (cur, cw)
    else return acc

/-- The value `v` must have given its successors' values `μ` (optionally restricted to
    `allowed`), and the successor attaining it; ties towards the first successor for the lifting
    player and the last otherwise (Rust `evaluate`). -/
def evaluate (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n)) :
    TimeM ℕ (Val × Option (Fin n)) := do
  let ws ← succT c v
  let r ← ws.foldlM (evalStep c μ v allowed) none
  return match r with
    | some (val, w) => (val, some w)
    | none => (none, none)

/-- The recorded choice of `x`, evaluated if there is none yet (Rust `current_choice`). -/
def currentChoice (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (x : Fin n) :
    TimeM ℕ ((Fin n → Option (Fin n)) × Option (Fin n)) := do
  ✓ match ch x with
  | some w => return (ch, some w)
  | none => do
    let r ← evaluate c μ x none
    return (Function.update ch x r.2, r.2)

/-- Put `v` at the back of the queue unless it is queued (Rust `requeue`). -/
def requeue (st : LState n) (v : Fin n) : LState n :=
  if st.inq v then st
  else { st with inq := Function.update st.inq v true, queue := st.queue ++ [v] }

/-- Re-queue the predecessors of `v` (Rust `requeue_predecessors`). -/
def requeuePreds (c : Ctx n) (st : LState n) (v : Fin n) : TimeM ℕ (LState n) := do
  let ps ← predT c v
  ✓[ps.length] return ps.foldl requeue st

/-- The kept edges of `u` for acceleration: all of the lifting player's edges, the recorded
    choice of the opponent (Rust `kept`). -/
def keptT (c : Ctx n) (ch : Fin n → Option (Fin n)) (u : Fin n) : TimeM ℕ (List (Fin n)) :=
  if c.mine u then succT c u else do ✓ return (ch u).toList

/-- Rust `accelerate`, pump test: do the current choices return to `v` within `n` steps? -/
def pumpTest (c : Ctx n) (μ : Fin n → Val) (v : Fin n) : ℕ → (Fin n → Option (Fin n)) → Fin n →
    TimeM ℕ ((Fin n → Option (Fin n)) × Bool)
  | 0, ch, _ => pure (ch, false)
  | k + 1, ch, x => do
    let r ← currentChoice c μ ch x
    match r.2 with
    | none => return (r.1, false)
    | some y => if y = v then return (r.1, true) else pumpTest c μ v k r.1 y

/-- Forward step of acceleration: compute the opponent's current choice, follow kept edges. -/
def fwdNbrs (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (x : Fin n) :
    TimeM ℕ ((Fin n → Option (Fin n)) × List (Fin n)) := do
  let ch' ← if c.mine x then pure ch else do
    let r ← currentChoice c μ ch x
    pure r.1
  let ks ← keptT c ch' x
  return (ch', ks)

/-- Is `u ∈ fwd` with a kept edge `u → x`? -/
def keptEdge (c : Ctx n) (ch : Fin n → Option (Fin n)) (fwd : VSet n) (x u : Fin n) :
    TimeM ℕ Bool :=
  if fwd u then do
    let ks ← keptT c ch u
    ✓[ks.length] return ks.contains x
  else pure false

/-- Backward step of acceleration: kept predecessors of `x` inside `fwd`. -/
def bwdNbrs (c : Ctx n) (ch : Fin n → Option (Fin n)) (fwd : VSet n) (_ : Unit) (x : Fin n) :
    TimeM ℕ (Unit × List (Fin n)) := do
  let ps ← predT c x
  let us ← filterT (keptEdge c ch fwd x) ps
  return ((), us)

/-- Kept successors, as a neighbour function with trivial state. -/
def keptNbrs (c : Ctx n) (ch : Fin n → Option (Fin n)) (_ : Unit) (x : Fin n) :
    TimeM ℕ (Unit × List (Fin n)) := do
  let ys ← keptT c ch x
  return ((), ys)

/-- Is the even-priority member `u` on a kept cycle inside `{w ∈ M | prio w ≤ prio u}`? -/
def ecmStep (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (bad : VSet n) (u : Fin n) :
    TimeM ℕ (VSet n) := do
  ✓ if M u && c.prio u % 2 == 0 then do
      ✓[n] let S : VSet n := materialize fun w => M w && decide (c.prio w ≤ c.prio u)
      let ks ← keptT c ch u
      ✓[ks.length] let s0 := pushNew S ks VSet.empty []
      let r ← explore (keptNbrs c ch) S (n + 1) () s0.1 s0.2
      return if r.2 u then Function.update bad u true else bad
    else return bad

/-- The maxima of all cycles with an even maximum among the kept edges inside `M`
    (Rust `even_cycle_maxima`, computed per vertex; see the module doc). -/
def evenCycleMaxima (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) : TimeM ℕ (VSet n) :=
  (List.finRange n).foldlM (ecmStep c ch M) VSet.empty

/-- The restriction loop of Rust `accelerate`: the strongly connected set of `v` in the kept
    graph (within `allowed`), with the maxima of even-maximum cycles peeled off. `none`: no
    acceleration. -/
def sccLoop (c : Ctx n) (μ : Fin n → Val) (v : Fin n) : ℕ → (Fin n → Option (Fin n)) →
    Option (VSet n) → TimeM ℕ ((Fin n → Option (Fin n)) × Option (VSet n))
  | 0, ch, _ => pure (ch, none)
  | k + 1, ch, allowed => do
    let fw ← explore (fwdNbrs c μ) (fun y => (allowed.map fun a => a y).getD true) (n + 1) ch
      (VSet.single v) [v]
    let ch := fw.1
    let bw ← explore (bwdNbrs c ch fw.2) (fun _ => true) (n + 1) () (VSet.single v) [v]
    let M := bw.2
    ✓[n] let cnt := M.count
    let ks ← keptT c ch v
    ✓[ks.length] if cnt == 1 && !ks.contains v then return (ch, none) else do
    let bad ← evenCycleMaxima c ch M
    ✓[2 * n] if bad.count == 0 then return (ch, some M) else
    if bad v then return (ch, none) else
    sccLoop c μ v k ch (some (materialize fun u => M u && !bad u))

/-- One kept edge `s → w` in `exitBound`. -/
def exitStep (c : Ctx n) (μ : Fin n → Val) (M : VSet n) (s : Fin n) (acc : Val) (w : Fin n) :
    TimeM ℕ Val := do
  ✓ if M w then return acc else do
    let val ← prog c s (μ w)
    let o ← cmpVal c val acc
    return if o == .lt then val else acc

/-- Cheapest exit of `s` out of `M` (initial Bellman–Ford bound). -/
def exitBound (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (s : Fin n) : TimeM ℕ Val := do
  let ks ← keptT c ch s
  ks.foldlM (exitStep c μ M s) none

/-- Relax the bound of `s` along a kept edge `s → w` inside `M`. -/
def bfEdge (c : Ctx n) (M : VSet n) (s : Fin n) (acc : (Fin n → Val) × Bool) (w : Fin n) :
    TimeM ℕ ((Fin n → Val) × Bool) := do
  ✓ if M w then do
    let val ← prog c s (acc.1 w)
    let o ← cmpVal c val (acc.1 s)
    return if o == .lt then (Function.update acc.1 s val, true) else acc
  else return acc

/-- Relax all kept edges of the member `s`. -/
def bfStep (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (acc : (Fin n → Val) × Bool)
    (s : Fin n) : TimeM ℕ ((Fin n → Val) × Bool) := do
  ✓ if M s then do
    let ks ← keptT c ch s
    ks.foldlM (bfEdge c M s) acc
  else return acc

/-- One Bellman–Ford round inside `M`; also reports whether a bound changed. -/
def bfRound (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (b : Fin n → Val) :
    TimeM ℕ ((Fin n → Val) × Bool) :=
  (List.finRange n).foldlM (bfStep c ch M) (b, false)

/-- At most `k` Bellman–Ford rounds, stopping early when nothing changes. -/
def bfLoop (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) :
    ℕ → (Fin n → Val) → TimeM ℕ (Fin n → Val)
  | 0, b => pure b
  | k + 1, b => do
    let r ← bfRound c ch M b
    if r.2 then bfLoop c ch M k r.1 else return r.1

/-- Raise the member `s` to its bound if that is larger. -/
def raiseStep (c : Ctx n) (M : VSet n) (b : Fin n → Val) (acc : LState n × ℕ) (s : Fin n) :
    TimeM ℕ (LState n × ℕ) := do
  ✓ if M s then do
    let o ← cmpVal c (b s) (acc.1.measure s)
    if o == .gt then do
      let st ← requeuePreds c { acc.1 with measure := Function.update acc.1.measure s (b s) } s
      return (requeue st s, acc.2 + 1)
    else return acc
  else return acc

/-- Raise every member to its bound if that is larger; returns the number of raised vertices. -/
def raise (c : Ctx n) (M : VSet n) (b : Fin n → Val) (st : LState n) : TimeM ℕ (LState n × ℕ) :=
  (List.finRange n).foldlM (raiseStep c M b) (st, 0)

/-- The initial Bellman–Ford bound of the member `s`. -/
def initStep (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (b : Fin n → Val) (s : Fin n) : TimeM ℕ (Fin n → Val) := do
  ✓ if M s then do
    let e ← exitBound c μ ch M s
    return Function.update b s e
  else return b

/-- The second half of acceleration on the set `M`: cheapest exits, Bellman–Ford, raise. -/
def accelRaise (c : Ctx n) (st : LState n) (M : VSet n) : TimeM ℕ (LState n × ℕ) := do
  ✓[n] let cnt := M.count
  let b0 ← (List.finRange n).foldlM (initStep c st.measure st.choice M) (fun _ => none)
  let b ← bfLoop c st.choice M cnt b0
  raise c M b st

/-- Pump acceleration after a successful lift of `v` (Rust `accelerate`); returns the new state
    and the number of raised vertices. -/
def accelerate (c : Ctx n) (st : LState n) (v : Fin n) : TimeM ℕ (LState n × ℕ) := do
  let pt ← pumpTest c st.measure v n st.choice v
  if !pt.2 then return ({ st with choice := pt.1 }, 0) else do
  let sc ← sccLoop c st.measure v (n + 1) pt.1 none
  match sc.2 with
  | none => return ({ st with choice := sc.1 }, 0)
  | some M => accelRaise c { st with choice := sc.1 } M

/-- At most `fuel` iterations of the lifting loop, until the lifter's steps reach `budgetEnd` or
    the queue is empty (Rust `run`). Returns the state, whether the queue is empty, and whether
    the fuel ran out. -/
def runLoop (c : Ctx n) (budgetEnd : ℕ) : ℕ → LState n → TimeM ℕ (LState n × Bool × Bool)
  | 0, st => pure (st, false, true)
  | k + 1, st =>
    if budgetEnd ≤ st.steps then pure (st, st.queue.isEmpty, false) else
    match st.queue with
    | [] => pure (st, true, false)
    | v :: q => do
      ✓ let st := { st with queue := q, inq := Function.update st.inq v false }
      let e ← evaluate c st.measure v none
      let st := { st with choice := Function.update st.choice v e.2 }
      let o ← cmpVal c e.1 (st.measure v)
      if o == .gt then do
        let s1 := st.steps + 1
        let st := { st with measure := Function.update st.measure v e.1, steps := s1 }
        let st ← requeuePreds c st v
        let a ← accelerate c st v
        runLoop c budgetEnd k { a.1 with steps := s1 + a.2 }
      else runLoop c budgetEnd k st

/-- Perform lifts until `budget` more steps are done or the queue is empty (Rust `run`). -/
def run (c : Ctx n) (budget fuel : ℕ) (st : LState n) : TimeM ℕ (LState n × Bool × Bool) :=
  runLoop c (st.steps + budget) fuel st

/-- Queue a predecessor `u` that is still in the domain and not queued. -/
def certPush (dom : VSet n) (acc : VSet n × List (Fin n)) (u : Fin n) : VSet n × List (Fin n) :=
  if dom u && !acc.1 u then (Function.update acc.1 u true, acc.2 ++ [u]) else acc

/-- The removal loop of certification (fuel = number of pops); `none` if the fuel runs out. -/
def certLoop (c : Ctx n) (μ : Fin n → Val) :
    ℕ → VSet n → VSet n → List (Fin n) → TimeM ℕ (Option (VSet n))
  | 0, _, _, _ => pure none
  | _ + 1, dom, _, [] => pure (some dom)
  | k + 1, dom, queued, v :: q => do
    ✓ let queued := Function.update queued v false
    if !dom v then certLoop c μ k dom queued q else do
    let ws ← succT c v
    ✓[ws.length] let leaves := !c.mine v && ws.any fun w => !dom w
    let consistent ← if leaves then pure false else do
      let r ← evaluate c μ v (some dom)
      let o ← cmpVal c (μ v) r.1
      pure (o != .lt)
    if consistent then certLoop c μ k dom queued q else do
    let dom := Function.update dom v false
    let ps ← predT c v
    ✓[ps.length] let nq := ps.foldl (certPush dom) (queued, q)
    certLoop c μ k dom nq.1 nq.2

/-- The largest set on which the current values form a progress measure (Rust `certified`). -/
def certified (c : Ctx n) (st : LState n) : TimeM ℕ (VSet n) := do
  ✓[n] let dom : VSet n := materialize fun v => c.alive v && (st.measure v).isSome
  let r ← certLoop c st.measure (n * n + n + 1) dom dom ((List.finRange n).filter dom)
  ✓[n] return match r with
    | some D => materialize fun v => c.alive v && D v
    | none => VSet.empty

/-! ## The outer loop (Rust `attractor`, `solve_game`) -/

/-- Try to attract `u`. -/
def attrStep (G : PGame n) (alive : VSet n) (player : Bool) (A : VSet n) (u : Fin n) :
    TimeM ℕ (VSet n) := do
  ✓[(G.succ u).length + 1] if alive u && !A u then do
    let ws := (G.succ u).filter alive
    let attract := if G.owner u == player then ws.any A else ws.any A && ws.all A
    return if attract then Function.update A u true else A
  else return A

/-- One pass of the attractor computation over all vertices. -/
def attrPass (G : PGame n) (alive : VSet n) (player : Bool) (A : VSet n) : TimeM ℕ (VSet n) :=
  (List.finRange n).foldlM (attrStep G alive player) A

/-- The `player`-attractor of `target` within `alive` (Rust `attractor`). -/
def attractor (G : PGame n) (alive : VSet n) (player : Bool) (target : VSet n) :
    TimeM ℕ (VSet n) := do
  ✓[n] let A0 : VSet n := materialize fun v => alive v && target v
  iterT (attrPass G alive player) (n + 1) A0

/-- The odd view priorities of the alive vertices, decreasing (Rust `ChainTree::new`). -/
def mkLevels (G : PGame n) (p : Bool) (alive : VSet n) :
    TimeM ℕ {l : List ℕ // l.length ≤ G.d + 1} := do
  ✓[(G.d + 1) * (n + 1)] return ⟨(List.range (G.d + 1)).reverse.filter fun q =>
      q % 2 == 1 && (List.finRange n).any fun v => alive v && G.prio v + (if p then 1 else 0) == q,
    by
      refine Nat.le_trans (List.length_filter_le _ _) ?_
      simp⟩

/-- A fresh lifter for `p` on the alive vertices (Rust `Lifter::new`). -/
def mkLifter (G : PGame n) (alive : VSet n) (p : Bool) : TimeM ℕ (Ctx n × LState n) := do
  let lv ← mkLevels G p alive
  let c : Ctx n := ⟨G, p, alive, lv.1, lv.2⟩
  let bottom ← leftmost c []
  ✓[n] let q := (List.finRange n).filter alive
  return (c, ⟨fun _ => some bottom, fun _ => none, q, alive, 0⟩)

/-- The state of the outer loop. `winner v = true`: Odd wins `v`. -/
structure SState (n : ℕ) where
  alive : VSet n
  winner : VSet n
  steps : ℕ
  rounds : ℕ
  restarts : ℕ

/-- How a restart ends. -/
inductive Outcome (n : ℕ) where
  /-- One lifting reached its fixpoint; the game is solved. -/
  | done (s : SState n)
  /-- The fuel ran out. -/
  | oof (s : SState n)
  /-- Certified sets were removed; restart on the remainder. -/
  | next (s : SState n)

/-- The state carried by an outcome. -/
def Outcome.state {n : ℕ} : Outcome n → SState n
  | .done s => s
  | .oof s => s
  | .next s => s

/-- A complete least fixpoint of player `c.p` decides the whole subgame. -/
def complete (c : Ctx n) (st : LState n) (winner : VSet n) : TimeM ℕ (VSet n) := do
  ✓[n] return materialize fun v =>
    if c.alive v then (if (st.measure v).isSome then c.p else !c.p) else winner v

/-- Remove the attractors of both certified sets (Even first, then Odd in the remainder). -/
def removal (G : PGame n) (alive winner cert0 cert1 : VSet n) : TimeM ℕ (VSet n × VSet n) := do
  let A0 ← attractor G alive false cert0
  ✓[n] let alive1 : VSet n := materialize fun v => alive v && !A0 v
  let A1 ← attractor G alive1 true cert1
  ✓[n] return (materialize fun v => alive1 v && !A1 v,
    materialize fun v => if A0 v then false else if A1 v then true else winner v)

/-- The rounds of one restart (Rust `loop` in `solve_game`), with round fuel `f` and lifting fuel
    `fuel`; `rem` is the number of alive vertices (the per-round budget). -/
def roundLoop (G : PGame n) (rem fuel : ℕ) (c0 c1 : Ctx n) :
    ℕ → SState n → LState n → LState n → TimeM ℕ (Outcome n)
  | 0, s, l0, l1 => pure (.oof { s with steps := s.steps + l0.steps + l1.steps })
  | f + 1, s, l0, l1 => do
    let s := { s with rounds := s.rounds + 1 }
    let r0 ← run c0 rem fuel l0
    let l0 := r0.1
    if r0.2.2 then return .oof { s with steps := s.steps + l0.steps + l1.steps } else
    if r0.2.1 then do
      let w ← complete c0 l0 s.winner
      return .done { s with winner := w, steps := s.steps + l0.steps + l1.steps }
    else do
    let r1 ← run c1 rem fuel l1
    let l1 := r1.1
    if r1.2.2 then return .oof { s with steps := s.steps + l0.steps + l1.steps } else
    if r1.2.1 then do
      let w ← complete c1 l1 s.winner
      return .done { s with winner := w, steps := s.steps + l0.steps + l1.steps }
    else do
    let cert0 ← certified c0 l0
    let cert1 ← certified c1 l1
    ✓[2 * n] if cert0.count == 0 && cert1.count == 0 then roundLoop G rem fuel c0 c1 f s l0 l1
    else do
      let rm ← removal G s.alive s.winner cert0 cert1
      return .next { s with
        alive := rm.1, winner := rm.2, steps := s.steps + l0.steps + l1.steps }

/-- The outer loop: restart on the remaining vertices until none remain (Rust `solve_game`). -/
def outer (G : PGame n) (fuel : ℕ) : ℕ → SState n → TimeM ℕ (SState n × Bool)
  | 0, s => pure (s, false)
  | k + 1, s => do
    ✓[n] let rem := s.alive.count
    if rem == 0 then return (s, true) else do
    let s := { s with restarts := s.restarts + 1 }
    let L0 ← mkLifter G s.alive false
    let L1 ← mkLifter G s.alive true
    let o ← roundLoop G rem fuel L0.1 L1.1 fuel s L0.2 L1.2
    match o with
    | .done s' => return (s', true)
    | .oof s' => return (s', false)
    | .next s' => outer G fuel k s'

/-- The result of the solver. -/
structure Result (n : ℕ) where
  /-- `some w`: `w v = true` iff Odd wins `v`; `none`: out of fuel. -/
  winner : Option (VSet n)
  /-- Successful lifts plus vertices raised by acceleration (Rust `Stats.steps`). -/
  steps : ℕ
  rounds : ℕ
  restarts : ℕ

/-- Two-sided lifting over instance-derived trees, with lifting/round fuel `fuel`. -/
def solve (G : PGame n) (fuel : ℕ) : TimeM ℕ (Result n) := do
  let r ← outer G fuel (n + 1) ⟨fun _ => true, fun _ => false, 0, 0, 0⟩
  return ⟨if r.2 then some r.1.winner else none, r.1.steps, r.1.rounds, r.1.restarts⟩

/-! ## Cost specifications

All bounds are explicit polynomials in `N = c.N = G.size = n + m + d + 2`. -/

/-- The polynomial of the headline bound, `P(n, m, d) = 340 · (n + m + d + 2)⁷`. -/
def costPoly (N : ℕ) : ℕ := 340 * N ^ 7

/-- Contract (tree navigation and value comparison): `leftmost` and a value comparison cost at
    most `N`; `nextNode` on a prefix of a leaf (length `≤ h`) at most `30 · N⁴`; `prog` (truncate
    to the depth, `nextNode` for odd priorities, `leftmost`) at most `32 · N⁴`. -/
def NavigationCost (c : Ctx n) : Prop :=
  (∀ pre, (leftmost c pre).time ≤ c.N) ∧
  (∀ a b, (cmpVal c a b).time ≤ c.N) ∧
  (∀ pre, pre.length ≤ c.height → (nextNode c pre).time ≤ 30 * c.N ^ 4) ∧
  (∀ v t, (prog c v t).time ≤ 32 * c.N ^ 4)

/-- Contract (region information, Rust `ChainTree::info`): weak components `≤ 9 · N³`, the child
    regions `≤ 10 · N³`, the chain bound `≤ 8 · N³`. -/
def RegionInfoCost (c : Ctx n) : Prop :=
  (∀ S, (weakComponents c S).time ≤ 9 * c.N ^ 3) ∧
  (∀ l R, (children c l R).time ≤ 10 * c.N ^ 3) ∧
  (∀ R q, (chainBound c R q).time ≤ 8 * c.N ^ 3)

/-- Contract (evaluating one vertex): at most `(deg v + 1) · 35 · N⁴`. -/
def EvaluateCost (c : Ctx n) : Prop :=
  ∀ μ v allowed, (evaluate c μ v allowed).time ≤ ((c.G.succ v).length + 1) * (35 * c.N ^ 4)

/-- Contract (one acceleration): at most `175 · N⁷`, and it adds at most `n + 1` queue entries
    per raised vertex. -/
def AccelerateCost (c : Ctx n) : Prop :=
  ∀ st v, (accelerate c st v).time ≤ 175 * c.N ^ 7 ∧
    (accelerate c st v).ret.1.queue.length ≤ st.queue.length + (accelerate c st v).ret.2 * (n + 1)

/-- Contract (amortised lifting loop): with potential `37 · N⁵ · |queue|`, the lifting loop costs
    at most `250 · N⁷` per step (successful lift or accelerated raise), whatever the budget and
    fuel. -/
def LiftingAmortised (c : Ctx n) : Prop :=
  ∀ B f st, (runLoop c B f st).time + 37 * c.N ^ 5 * (runLoop c B f st).ret.1.queue.length +
      250 * c.N ^ 7 * st.steps ≤
    37 * c.N ^ 5 * st.queue.length + 250 * c.N ^ 7 * (runLoop c B f st).ret.1.steps

/-- Contract (certification): at most `43 · N⁷`. -/
def CertifiedCost (c : Ctx n) : Prop :=
  ∀ st, (certified c st).time ≤ 43 * c.N ^ 7

/-- Contract (attractor): at most `2 · N³`. -/
def AttractorCost (G : PGame n) : Prop :=
  ∀ alive player target, (attractor G alive player target).time ≤ 2 * G.size ^ 3

/-- Contract (headline): for every game and every fuel, the running time is at most
    `(steps + n + 1) · costPoly N`, and the solver restarts at most `n + 1` times. -/
def SolveTimeBound (G : PGame n) (fuel : ℕ) : Prop :=
  (solve G fuel).time ≤ ((solve G fuel).ret.steps + n + 1) * costPoly G.size ∧
    (solve G fuel).ret.restarts ≤ n + 1

/-- Contract (corollary): if the number of steps is bounded by `Q n`, the running time is at
    most `(Q n + n + 1) · costPoly N` — polynomial whenever `Q` is. -/
def SolvePolyOfSteps (G : PGame n) (fuel : ℕ) (Q : ℕ → ℕ) : Prop :=
  (solve G fuel).ret.steps ≤ Q n → (solve G fuel).time ≤ (Q n + n + 1) * costPoly G.size

/-- Contract (progress of restarts): a restart on the alive set of `s` that ends by removing
    certified sets (`Outcome.next`) strictly shrinks the alive set. -/
def RestartProgress (G : PGame n) (fuel : ℕ) : Prop :=
  ∀ (rem f : ℕ) (s s' : SState n) (l0 l1 : LState n),
    (roundLoop G rem fuel (mkLifter G s.alive false).ret.1 (mkLifter G s.alive true).ret.1 f s l0
      l1).ret = .next s' →
    s'.alive.count < s.alive.count

/-- Contract (the outer fuel `n + 1` suffices): if no restart runs out of lifting/round fuel, the
    solver returns winners. -/
def OuterFuelSuffices (G : PGame n) (fuel : ℕ) : Prop :=
  (∀ s s' : SState n, (roundLoop G s.alive.count fuel (mkLifter G s.alive false).ret.1
      (mkLifter G s.alive true).ret.1 fuel s (mkLifter G s.alive false).ret.2
      (mkLifter G s.alive true).ret.2).ret ≠ .oof s') →
  (solve G fuel).ret.winner.isSome

end ParityGame.TwoSidedCost
