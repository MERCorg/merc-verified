import Sigref.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.List.Chain

/-!
# Strongly connected components by an iterative Tarjan search (abstract model)

Models `tau_scc_decomposition_iterative` of `merc_reduction` (the `lean` variant): an iterative version
of Tarjan's algorithm, with an explicit work stack of `(state, resume offset)` entries, on the graph
whose edges are the hidden (τ) transitions. The states are `Fin n`; `adj s` lists *all* outgoing
transitions of `s` as `(hidden, target)`, because the resume offsets index that list.

The model is a deterministic small-step function `step`, one step being one iteration of
`scc_process_work` (`scc_step`, with `scc_next_child`, `scc_finish`, `scc_pop_component`) or of
`scc_visit_roots` (`ri` is its counter). The sentinel `unv` is `usize::MAX`; `disc v = 0` is also used
by the implementation to mark a state that is queued but not yet initialised.

Claims: `TarjanCorrect` (the result numbers the states by their SCC, with `eq` blocks; the run never
fails), `TarjanTerminates` (a measure decreases at every step).
-/

namespace Sigref.Tarjan

/-- The graph: all outgoing transitions of every state, as `(hidden, target)`, and the sentinel. -/
structure Graph (n : ℕ) where
  adj : Fin n → List (Bool × Fin n)
  unv : ℕ
  unv_gt : n < unv

variable {n : ℕ}

/-- `SccContext` together with the counter of `scc_visit_roots`. -/
structure Ctx (n : ℕ) where
  low : Fin n → ℕ
  disc : Fin n → ℕ
  onSt : Fin n → Bool
  stk : List (Fin n)
  work : List (Fin n × ℕ)
  time : ℕ
  eq : ℕ
  blk : Fin n → ℕ
  ri : ℕ

/-- The initial context of `tau_scc_decomposition_iterative`. -/
def init (g : Graph n) : Ctx n :=
  ⟨fun _ => g.unv, fun _ => g.unv, fun _ => false, [], [], 0, 0, fun _ => 0, 0⟩

/-- `scc_next_child`: scan the remaining transitions `ts` of `s` (the first one at position `idx`);
returns the first unvisited hidden target (marking it queued), the position to resume at and the
updated context. -/
def scan (g : Graph n) (s : Fin n) : List (Bool × Fin n) → ℕ → Ctx n → Option (Fin n) × ℕ × Ctx n
  | [], idx, c => (none, idx, c)
  | (h, v) :: ts, idx, c =>
    if h then
      if c.disc v = g.unv then
        (some v, idx + 1, { c with disc := Function.update c.disc v 0 })
      else if c.onSt v && decide (c.disc v < c.low s) then
        scan g s ts (idx + 1) { c with low := Function.update c.low s (c.disc v) }
      else scan g s ts (idx + 1) c
    else scan g s ts (idx + 1) c

/-- `scc_pop_component`: pop the stack down to and including `s`, assigning the block `e`.
`none` if the stack runs empty (an `unwrap` on `None`). -/
def popComp (s : Fin n) (e : ℕ) :
    List (Fin n) → (Fin n → Bool) → (Fin n → ℕ) → Option (List (Fin n) × (Fin n → Bool) × (Fin n → ℕ))
  | [], _, _ => none
  | u :: rest, onSt, blk =>
    if u = s then some (rest, Function.update onSt u false, Function.update blk u e)
    else popComp s e rest (Function.update onSt u false) (Function.update blk u e)

/-- `scc_finish` (the work stack no longer contains the entry of `s`). -/
def finish (s : Fin n) (c : Ctx n) : Option (Ctx n) :=
  let c1 : Option (Ctx n) :=
    if c.disc s = c.low s then
      (popComp s c.eq c.stk c.onSt c.blk).map fun r =>
        { c with
          stk := r.1
          onSt := r.2.1
          blk := r.2.2
          eq := c.eq + 1 }
    else some c
  c1.map fun c1 =>
    match c1.work with
    | [] => c1
    | (p, _) :: _ =>
      if c1.low s < c1.low p then { c1 with low := Function.update c1.low p (c1.low s) } else c1

/-- Initialise `s` if it has not been initialised yet (the first lines of `scc_step`). -/
def initNode (g : Graph n) (s : Fin n) (c : Ctx n) : Ctx n :=
  if c.low s = g.unv then
    { c with
      disc := Function.update c.disc s c.time
      low := Function.update c.low s c.time
      time := c.time + 1
      stk := s :: c.stk
      onSt := Function.update c.onSt s true }
  else c

/-- The outcome of one step. -/
inductive Out (n : ℕ)
  | next (c : Ctx n)
  | stop
  | fail

/-- One iteration of `scc_process_work`, or of `scc_visit_roots` when the work stack is empty. -/
def step (g : Graph n) (c : Ctx n) : Out n :=
  match c.work with
  | (s, off) :: W =>
    let c1 := initNode g s { c with work := W }
    match scan g s ((g.adj s).drop off) off c1 with
    | (some ch, off', c2) => Out.next { c2 with work := (ch, 0) :: (s, off') :: W }
    | (none, _, c2) =>
      match finish s c2 with
      | none => Out.fail
      | some c3 => Out.next c3
  | [] =>
    if h : c.ri < n then
      if c.low ⟨c.ri, h⟩ = g.unv then Out.next { c with work := [(⟨c.ri, h⟩, 0)], ri := c.ri + 1 }
      else Out.next { c with ri := c.ri + 1 }
    else Out.stop

/-- A step of the machine. -/
def Step (g : Graph n) (c c' : Ctx n) : Prop := step g c = Out.next c'

/-- A termination measure: the number of unvisited states and the work stack. -/
def measure (g : Graph n) (c : Ctx n) : ℕ :=
  2 * (n - c.ri) + 2 * (Finset.univ.filter (fun v => c.disc v = g.unv)).card + c.work.length

/-- The τ-edge relation: `u → v` iff `u` has a hidden transition to `v`. -/
def Edge (g : Graph n) (u v : Fin n) : Prop := (true, v) ∈ g.adj u

/-- `blk` numbers the states by their SCC with the numbers `0, …, k - 1`. -/
def IsSccPartition (g : Graph n) (blk : Fin n → ℕ) (k : ℕ) : Prop :=
  (∀ s, blk s < k) ∧ (∀ b, b < k → ∃ s, blk s = b) ∧
    ∀ s t, blk s = blk t ↔ (Relation.ReflTransGen (Edge g) s t ∧ Relation.ReflTransGen (Edge g) t s)

/-- **Correctness of the SCC decomposition**: when the run stops, `blk` numbers the states by their
SCC with `eq` blocks, and no step of the run fails. -/
def TarjanCorrect (g : Graph n) : Prop :=
  ∀ c, Relation.ReflTransGen (Step g) (init g) c →
    (step g c = Out.stop → IsSccPartition g c.blk c.eq) ∧ step g c ≠ Out.fail

/-- **Termination of the SCC decomposition**: the measure decreases at every step of a run. -/
def TarjanTerminates (g : Graph n) : Prop :=
  ∀ c, Relation.ReflTransGen (Step g) (init g) c → ∀ c', Step g c c' → measure g c' < measure g c

end Sigref.Tarjan
