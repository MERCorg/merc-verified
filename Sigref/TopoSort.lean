import Sigref.Basic
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Topological sort by an iterative depth-first search (abstract model)

Models `sort_topological_hidden` of `merc_reduction` (the `lean` variant): a depth-first search along
the hidden (τ) transitions with an explicit stack, marks `None / Temporary / Permanent`, the order of
finishing (`order`) and an `acyc` flag that is cleared when a target is found that is still
`Temporary`. The states are `Fin n`; `succ s` lists the targets of the hidden transitions of `s` that
are not self-loops, in the order of the transitions.

The model is a deterministic small-step function `step`; one step is one iteration of the loop of
`sort_topological_visit_hidden`, or one iteration of the outer loop of `sort_topological_visit_all`
(`idx` is its counter). Claims:

* `TopoSortCorrect`: on an acyclic graph the run ends with `acyc = true`, and `order` lists every state
  once, every state after all its successors (so the permutation `order_to_permutation out`
  decreases along the hidden transitions);
* `TopoSortTerminates`: a measure decreases at every step.
-/

namespace Sigref.Topo

variable {n : ℕ}

/-- The mark of a state in the depth-first search (`None` = unvisited). -/
inductive Mark
  | temp
  | perm
  deriving DecidableEq

/-- A configuration of the search. `depth` is the stack of `depth_stack` (head = top), `order` the
finishing order `stack` (last = newest), `idx` the next root tried by `sort_topological_visit_all`. -/
structure Cfg (n : ℕ) where
  marks : Fin n → Option Mark
  depth : List (Fin n)
  order : List (Fin n)
  acyc : Bool
  idx : ℕ

/-- `push_unvisited_successors`: scan the targets `ts`; unmarked ones are pushed, a `Temporary` one
clears the flag. -/
def pushSuccs (marks : Fin n → Option Mark) :
    List (Fin n) → List (Fin n) → Bool → List (Fin n) × Bool
  | [], D, a => (D, a)
  | w :: ts, D, a =>
    match marks w with
    | some Mark.temp => pushSuccs marks ts D false
    | none => pushSuccs marks ts (w :: D) a
    | some Mark.perm => pushSuccs marks ts D a

/-- One iteration of the search. `none` once the stack is empty and all roots have been tried. -/
def step (succ : Fin n → List (Fin n)) (c : Cfg n) : Option (Cfg n) :=
  match c.depth with
  | x :: D =>
    match c.marks x with
    | none =>
      let marks' := Function.update c.marks x (some Mark.temp)
      let r := pushSuccs marks' (succ x) (x :: D) c.acyc
      some { c with marks := marks', depth := r.1, acyc := r.2 }
    | some Mark.temp =>
      some { marks := Function.update c.marks x (some Mark.perm), depth := D,
             order := c.order ++ [x], acyc := c.acyc, idx := c.idx }
    | some Mark.perm => some { c with depth := D }
  | [] =>
    if h : c.idx < n then
      if c.marks ⟨c.idx, h⟩ = none then
        some { c with depth := [⟨c.idx, h⟩], idx := c.idx + 1 }
      else some { c with idx := c.idx + 1 }
    else none

/-- The initial configuration: nothing marked, empty stack. -/
def init (n : ℕ) : Cfg n := ⟨fun _ => none, [], [], true, 0⟩

/-- A termination measure: it decreases at every step. -/
def measure (succ : Fin n → List (Fin n)) (c : Cfg n) : ℕ :=
  2 * (n - c.idx) + (Finset.univ.filter (fun u => c.marks u = none)).card + c.depth.length +
    ∑ u ∈ Finset.univ.filter (fun u => c.marks u = none), (succ u).length

/-- The graph has no cycle. -/
def Acyclic (succ : Fin n → List (Fin n)) : Prop :=
  ∀ v, ¬ Relation.TransGen (fun a b => b ∈ succ a) v v

/-- **Correctness of the topological sort.** -/
def TopoSortCorrect (succ : Fin n → List (Fin n)) : Prop :=
  Acyclic succ → ∀ c, Relation.ReflTransGen (fun a b => step succ a = some b) (init n) c →
    step succ c = none →
      c.acyc = true ∧ c.order.Nodup ∧ (∀ v, v ∈ c.order) ∧
      ∀ l1 a l2, c.order = l1 ++ a :: l2 → ∀ b ∈ succ a, b ∈ l1

/-- **Termination of the topological sort.** -/
def TopoSortTerminates (succ : Fin n → List (Fin n)) : Prop :=
  ∀ c c', step succ c = some c' → measure succ c' < measure succ c

end Sigref.Topo
