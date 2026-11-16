module

public import MercLib.Algorithms.LDD.Relational

@[expose] public section

/-!
# Symbolic reachability on list decision diagrams

The reachability strategies of merc's `merc_symbolic` crate and of oxidd, on the LDD operations of
`Algorithms/LDD/SetOperations.lean` and `Algorithms/LDD/Relational.lean`:

* breadth-first search and chaining;
* the node-wise saturation of [G. Ciardo, G. Lüttgen and R. Siminiceanu, *Saturation: an efficient
  iteration strategy for symbolic state-space generation*][Ciardo2001], as merc implemented it
  before;
* the recursive saturation of oxidd's `saturate.rs` ([T. van Dijk, J. Meijer and J. van de Pol,
  *Multi-core on-the-fly saturation*][vanDijk2019], Algorithm 1);
* the REACH operation of [S. Brand, T. Bäck and A. Laarman, *A Decision Diagram Operation for
  Reachability*][Brand2023] (Algorithm 3), for a relation given as a list of events as in the
  mCRL2 implementation.

A transition group is an *event*: a relation over the positions it reads or writes, from its
`top` position on, described by a meta description as in `Relational.lean`. On vectors that start
at position `p ≤ top`, the event copies the positions before `top`.

See [Symbolic reachability](https://mercorg.github.io/merc-website/model-checking/symbolic/reachability/)
and, for the node-wise saturation,
[Saturation](https://mercorg.github.io/merc-website/model-checking/symbolic/saturation/#the-recursion).

**Modelling choices**
* The loops are `while` loops. The reachable set can be infinite, and then the algorithms do not
  terminate; the contracts assume that it is finite, and the termination contracts state that
  every round that does not stop adds a reachable vector (or, for the node-wise saturation,
  removes a value from the frontier).
* Learning the relations on the fly, the operation cache and the parallel recursion of the
  implementations are left out: the relations are fixed, and a cached result equals the result of
  the call it caches. The implementation repeats saturation passes until the relations stop
  growing; one pass with the final relations is what is modelled here.
* The recursion stops at position `n`, the length of the vectors; the implementation stops below
  the deepest `top` already, which only saves work since no event changes those positions.
* The node-wise saturation keeps the node under construction as an LDD rather than as a map from
  values to children; adding a continuation `f` for value `j` is the union with the node `j ↦ f`,
  which is the map update of the paper.

## Main definitions

- `Event`: a transition group with its `top` position, meta description and relation.
- `Event.metaAt`, `Event.Fires`: the event on vectors that start at position `p`.
- `Reach`, `Sat`: the vectors reachable from a set with the events whose `top` is at least `p`.
- `Ldd.fixLoop`: repeat a round until it changes nothing.
- `Ldd.bfs`, `Ldd.chaining`, `Ldd.saturate`, `Ldd.saturateNodewise` (with `Event.rows`,
  `Ldd.addRow` and `Ldd.fireValue`), `Ldd.reach`.

## Main statements

- `BfsCorrect`, `ChainingCorrect`, `SaturateCorrect`, `SaturateNodewiseCorrect`, `ReachCorrect`:
  when the reachable set is finite, the result is well-formed and represents the reachable vectors.
- `BfsTerminates`, `ChainingTerminates`, `SaturateTerminates`, `SaturateNodewiseTerminates`,
  `ReachTerminates`: every round of the loop that does not stop makes progress within the finite
  reachable set.

## References

- [G. Ciardo, G. Lüttgen and R. Siminiceanu, *Saturation: an efficient iteration strategy for
  symbolic state-space generation*][Ciardo2001]
- [T. van Dijk, J. Meijer and J. van de Pol, *Multi-core on-the-fly saturation*][vanDijk2019]
- [S. Brand, T. Bäck and A. Laarman, *A Decision Diagram Operation for Reachability*][Brand2023]
-/

namespace MercLib.LDD

/-- A transition group: the relation `rel` over the positions it reads or writes, described by
    `access` from position `top` on. -/
structure Event (α : Type*) where
  /-- The first position the event reads or writes. -/
  top : ℕ
  /-- How the event accesses the positions from `top` on. -/
  access : List Access
  /-- The relation vectors of the event. -/
  rel : Ldd α

namespace Event

variable {α : Type*}

/-- The meta description of `e` on vectors that start at position `p`: the positions before `top`
    are skipped. -/
def metaAt (e : Event α) (p : ℕ) : List Access :=
  List.replicate (e.top - p) .skip ++ e.access

/-- `e.Fires p x y`: on vectors that start at position `p`, the event takes `x` to `y`. -/
def Fires (e : Event α) (p : ℕ) (x y : List α) : Prop :=
  ∃ t ∈ e.rel.denote, Apply (e.metaAt p) t x y

/-- `e` is a well-formed event for vectors of length `n`: its accesses fit in the vectors, and its
    relation is a well-formed LDD of the matching height. -/
def WellFormed [LT α] (e : Event α) (n : ℕ) : Prop :=
  e.top + e.access.length ≤ n ∧ e.rel.WellFormed (relWidth e.access)

end Event

namespace Ldd

variable {α : Type*}

/-- The pairs `(value, down child)` on the spine of `X`. -/
def entries : Ldd α → List (α × Ldd α)
  | node v d r => (v, d) :: entries r
  | _ => []

/-- The down child of the value `v` on the spine of `R`, or `zero` when `v` is not on it: the
    vectors `t` with `v :: t` in `R`. -/
def lookup [DecidableEq α] (v : α) : Ldd α → Ldd α
  | node w d r => if w = v then d else lookup v r
  | _ => zero

end Ldd

namespace Event

variable {α : Type*} [DecidableEq α]

/-- The *diagonal* of an event `e` at its `top` for the value `v`: the transitions of `e` that keep
    the value `v` at position `top`, as an event that starts one position lower. -/
def diag (e : Event α) (v : α) : Event α :=
  match e.access with
  | [] => ⟨e.top + 1, [], e.rel⟩
  | .skip :: m => ⟨e.top + 1, m, e.rel⟩
  | .read :: m => ⟨e.top + 1, m, e.rel.lookup v⟩
  | .write :: m => ⟨e.top + 1, m, e.rel.lookup v⟩
  | .readWrite :: m => ⟨e.top + 1, m, (e.rel.lookup v).lookup v⟩

/-- The *rows* of an event `e` at its `top` for the source value `i`: the target values `j` at
    `top` with the relation of the positions below `top` for `i ↦ j` (`FireTop` of the node-wise
    saturation). An event that accesses nothing has no rows: it adds nothing. -/
def rows (e : Event α) (i : α) : List (α × Ldd α) :=
  match e.access with
  | [] => []
  | .skip :: _ => [(i, e.rel)]
  | .read :: _ => [(i, e.rel.lookup i)]
  | .write :: _ => e.rel.entries
  | .readWrite :: _ => (e.rel.lookup i).entries

end Event

variable {α : Type*}

/-- `Reach E p X y`: `y` is reachable from a vector in `X` by firing events of `E` whose `top` is
    at least `p`, on vectors that start at position `p`. -/
inductive Reach (E : List (Event α)) (p : ℕ) (X : Set (List α)) : List α → Prop
  | base {x : List α} : x ∈ X → Reach E p X x
  | step {x y : List α} (e : Event α) : e ∈ E → p ≤ e.top → Reach E p X x → e.Fires p x y →
      Reach E p X y

/-- The vectors reachable from `X` with the events of `E` whose `top` is at least `p`: the
    smallest superset of `X` closed under those events. -/
def Sat (E : List (Event α)) (p : ℕ) (X : Set (List α)) : Set (List α) :=
  {y | Reach E p X y}

namespace Ldd

variable [LinearOrder α]

/-- `X` together with the successors of `X` under `e`, for `X` at position `p`. -/
def fire (p : ℕ) (X : Ldd α) (e : Event α) : Ldd α :=
  union X (successors (e.metaAt p) X e.rel)

/-- Fires the events whose `top` is `p` on `X`, one after the other. -/
def fireTop (E : List (Event α)) (p : ℕ) (X : Ldd α) : Ldd α :=
  (E.filter (fun e => e.top == p)).foldl (fire p) X

/-- Repeats the round `S := h (g S)` from `S₀` until `g S = S`, and returns that `S`. -/
def fixLoop (g h : Ldd α → Ldd α) (S₀ : Ldd α) : Ldd α := Id.run do
  let mut S := S₀
  let mut T := g S
  while T ≠ S do
    S := h T
    T := g S
  return S

/-- One round of breadth-first search: the successors of `S` under every event at once. -/
def bfsStep (E : List (Event α)) (S : Ldd α) : Ldd α :=
  E.foldl (fun T e => union T (successors (e.metaAt 0) S e.rel)) S

/-- Breadth-first search: add the successors under every event at once, until nothing is added. -/
def bfs (E : List (Event α)) (X : Ldd α) : Ldd α :=
  fixLoop (bfsStep E) id X

/-- One round of chaining: fire the events one after the other, each on the result of the previous
    one. -/
def chainStep (E : List (Event α)) (S : Ldd α) : Ldd α :=
  E.foldl (fire 0) S

/-- Chaining: repeat rounds of chaining until nothing is added. -/
def chaining (E : List (Event α)) (X : Ldd α) : Ldd α :=
  fixLoop (chainStep E) id X

/-- Recursive saturation of `X` at position `p`, for vectors of length `n` (`saturate` in oxidd's
    `saturate.rs`): saturate the children; then, until firing the events at `p` adds nothing, fire
    them and saturate the children again. -/
def saturate (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Ldd α :=
  if h : p < n then
    let below := mapSpine (fun d => saturate E n (p + 1) d)
    fixLoop (fireTop E p) below (below X)
  else X
termination_by n - p

/-- Adds the continuation of one row `(j, R)` of event `e`, fired from the continuation `A` and
    saturated with `sat`, below the value `j` of `S`; when that changes `S`, the value `j` joins the
    frontier `F`. -/
def addRow (sat : Ldd α → Ldd α) (e : Event α) (A : Ldd α) (s : Ldd α × List α)
    (row : α × Ldd α) : Ldd α × List α :=
  let S' := union s.1 (mk row.1 (sat (successors e.access.tail A row.2)) zero)
  if S' ≠ s.1 then (S', if row.1 ∉ s.2 then s.2 ++ [row.1] else s.2) else s

/-- Fires the events at position `p` out of the value `i` of `S`, as in the inner loops of the
    node-wise saturation: for every event, every row of the event from the current continuation of
    `i` is added with `addRow`. -/
def fireValue (sat : Ldd α → Ldd α) (E : List (Event α)) (p : ℕ) (i : α) (S : Ldd α)
    (F : List α) : Ldd α × List α := Id.run do
  let mut S := S
  let mut F := F
  for e in E.filter (fun e => e.top == p) do
    let A := S.lookup i
    for row in e.rows i do
      (S, F) := addRow sat e A (S, F) row
  return (S, F)

/-- Node-wise saturation of `X` at position `p`, for vectors of length `n`: saturate the children;
    then, while the frontier `F` of values whose continuation still has to be fired is not empty,
    fire the events at `p` out of its first value. -/
def saturateNodewise (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Ldd α :=
  if h : p < n then Id.run do
    let sat := fun d => saturateNodewise E n (p + 1) d
    let mut S := mapSpine sat X
    let mut F := (entries S).map Prod.fst
    while hF : F ≠ [] do
      let r := fireValue sat E p (F.head hF) S F.tail
      S := r.1
      F := r.2
    return S
  else X
termination_by n - p

/-- Replaces every down child `d` of a value `v` on the spine by `f v d`, and drops the values whose
    new down child is `zero`. -/
def mapSpineWith (f : α → Ldd α → Ldd α) : Ldd α → Ldd α
  | node v d r => mk v (f v d) (mapSpineWith f r)
  | _ => zero

/-- The events with which REACH continues below the value `v` at position `p`: those below `p`,
    and the diagonals for `v` of those at `p`. -/
def reachEvents (E : List (Event α)) (p : ℕ) (v : α) : List (Event α) :=
  E.filter (fun e => p < e.top) ++ (E.filter (fun e => e.top == p)).map (·.diag v)

/-- REACH of `X` at position `p`, for vectors of length `n`: until a round changes nothing, reach
    the children below every value `v` with the events for `v`, and fire the events at `p`. -/
def reach (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Ldd α :=
  if h : p < n then
    fixLoop
      (fun S => fireTop E p (mapSpineWith (fun v d => reach (reachEvents E p v) n (p + 1) d) S))
      id X
  else X
termination_by n - p

end Ldd

open Ldd

variable [LinearOrder α]

/-- Contract: from a well-formed `X` of height `n`, with events that are well-formed for vectors of
    length `n` and finitely many reachable vectors, breadth-first search returns a well-formed LDD
    of height `n` that represents the vectors reachable from `X`. -/
def BfsCorrect (E : List (Event α)) (X : Ldd α) (n : ℕ) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → X.WellFormed n → (Sat E 0 X.denote).Finite →
    (bfs E X).WellFormed n ∧ (bfs E X).denote = Sat E 0 X.denote

/-- Contract (termination): a round of breadth-first search from a well-formed set between `X` and
    its reachable vectors either changes nothing, which stops the loop, or adds a vector that is
    reachable from `X`. So with finitely many reachable vectors the loop stops. -/
def BfsTerminates (E : List (Event α)) (X : Ldd α) (n : ℕ) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → X.WellFormed n → ∀ S : Ldd α, S.WellFormed n →
    X.denote ⊆ S.denote → S.denote ⊆ Sat E 0 X.denote → bfsStep E S ≠ S →
      S.denote ⊂ (bfsStep E S).denote ∧ (bfsStep E S).denote ⊆ Sat E 0 X.denote

/-- Contract: as `BfsCorrect`, for chaining. -/
def ChainingCorrect (E : List (Event α)) (X : Ldd α) (n : ℕ) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → X.WellFormed n → (Sat E 0 X.denote).Finite →
    (chaining E X).WellFormed n ∧ (chaining E X).denote = Sat E 0 X.denote

/-- Contract (termination): as `BfsTerminates`, for a round of chaining. -/
def ChainingTerminates (E : List (Event α)) (X : Ldd α) (n : ℕ) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → X.WellFormed n → ∀ S : Ldd α, S.WellFormed n →
    X.denote ⊆ S.denote → S.denote ⊆ Sat E 0 X.denote → chainStep E S ≠ S →
      S.denote ⊂ (chainStep E S).denote ∧ (chainStep E S).denote ⊆ Sat E 0 X.denote

/-- Contract: for vectors of length `n`, events that are well-formed for them, a position
    `p ≤ n`, a well-formed `X` of height `n - p` (the vectors from position `p` on) and finitely
    many vectors reachable from it, the recursive saturation of `X` at `p` is well-formed of height
    `n - p` and represents the vectors reachable from `X` with the events whose `top` is at least
    `p`. With `p = 0` this is reachability. -/
def SaturateCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → p ≤ n → X.WellFormed (n - p) → (Sat E p X.denote).Finite →
    (saturate E n p X).WellFormed (n - p) ∧ (saturate E n p X).denote = Sat E p X.denote

/-- Contract (termination): in the loop of the recursive saturation of `X` at `p < n`, a round from
    a well-formed set `S` between `X` and its reachable vectors, in which firing the events at `p`
    changes `S`, ends in a strictly larger set of vectors that are still reachable from `X`. -/
def SaturateTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → p < n → X.WellFormed (n - p) → (Sat E p X.denote).Finite →
    ∀ S : Ldd α, S.WellFormed (n - p) → X.denote ⊆ S.denote → S.denote ⊆ Sat E p X.denote →
      fireTop E p S ≠ S →
        let S' := mapSpine (fun d => saturate E n (p + 1) d) (fireTop E p S)
        S.denote ⊂ S'.denote ∧ S'.denote ⊆ Sat E p X.denote

/-- Contract: as `SaturateCorrect`, for the node-wise saturation. -/
def SaturateNodewiseCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → p ≤ n → X.WellFormed (n - p) → (Sat E p X.denote).Finite →
    (saturateNodewise E n p X).WellFormed (n - p) ∧
      (saturateNodewise E n p X).denote = Sat E p X.denote

/-- Contract (termination): in the loop of the node-wise saturation of `X` at `p < n`, firing out
    of the first value of a non-empty frontier `F`, from a well-formed set `S` between `X` and its
    reachable vectors, either leaves `S` unchanged and only removes that value from the frontier,
    or ends in a strictly larger set of vectors that are still reachable from `X`. -/
def SaturateNodewiseTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → p < n → X.WellFormed (n - p) → (Sat E p X.denote).Finite →
    ∀ (S : Ldd α) (F : List α) (hF : F ≠ []), S.WellFormed (n - p) → X.denote ⊆ S.denote →
      S.denote ⊆ Sat E p X.denote →
        let r := fireValue (fun d => saturateNodewise E n (p + 1) d) E p (F.head hF) S F.tail
        (r.1 = S ∧ r.2 = F.tail) ∨ (S.denote ⊂ r.1.denote ∧ r.1.denote ⊆ Sat E p X.denote)

/-- Contract: as `SaturateCorrect`, for REACH. -/
def ReachCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → p ≤ n → X.WellFormed (n - p) → (Sat E p X.denote).Finite →
    (reach E n p X).WellFormed (n - p) ∧ (reach E n p X).denote = Sat E p X.denote

/-- Contract (termination): a round of REACH of `X` at `p < n`, from a well-formed set `S` between
    `X` and its reachable vectors, either changes nothing, which stops the loop, or ends in a
    strictly larger set of vectors that are still reachable from `X`. -/
def ReachTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) : Prop :=
  (∀ e ∈ E, e.WellFormed n) → p < n → X.WellFormed (n - p) → (Sat E p X.denote).Finite →
    ∀ S : Ldd α, S.WellFormed (n - p) → X.denote ⊆ S.denote → S.denote ⊆ Sat E p X.denote →
      let S' := fireTop E p
        (mapSpineWith (fun v d => reach (reachEvents E p v) n (p + 1) d) S)
      S' ≠ S → S.denote ⊂ S'.denote ∧ S'.denote ⊆ Sat E p X.denote

end MercLib.LDD
