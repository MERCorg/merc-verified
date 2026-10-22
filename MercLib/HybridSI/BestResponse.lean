module

public import MercLib.HybridSI.Algorithm
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.WithBot
public import Mathlib.Algebra.Order.Monoid.WithTop

@[expose] public section HybridSIBestResponse

namespace MercLib.HybridSI

open MercLib.ParityGame Cslib.Algorithms.Lean

/-!
# A polynomial best response

`respond` (`HybridSI.Algorithm`) computes a best response by one-player strategy improvement, whose
number of rounds has no proved polynomial bound. `bestResponse G pl p` computes, for player `pl`
(`false` = Even maximises keys, `true` = Odd minimises them) against the other player's moves in
`p`, a profile with the same guarantee as a returned `respond` (`BestResponseOptimal`, the
conclusion of `respond_spec`), in polynomially many steps (`BestResponseCost`). It is a variant of
the algorithm of Section 6 of [Vöge and Jurdziński, *A discrete strategy improvement algorithm for
solving parity games*][Voege2000] in which the edge deletions of their Proposition 6.1 are replaced
by a Bellman–Ford computation with integer weights.

All work is in the one-player graph `H`: an owned vertex keeps all its edges (`succList`), every
other vertex has the single edge to `p v` (`hsucc`).

1. **Cycle-maximum classes.** The candidates `λ` are taken best first for the player (`cands`:
   favourable priorities from the most relevant down, then unfavourable ones from the least
   relevant up). With `R` the vertices not yet classified, `λ ∈ R` opens a class iff `λ` reaches
   itself in at least one step through `R ∩ {x ≤ λ}`; the class is then every vertex of `R` that
   reaches `λ` through `R` (`classStep`, `classes`). Reachability is a backward fixpoint with
   `|V|` rounds (`reachFrom`).
2. **Paths to the class maximum.** Inside every class (edges between vertices of the same class,
   `allowed`) the target `λ` gets value `0` and every other vertex the best value of a path to
   `λ`, a path weighing `Σ (M · w x + e)` over its vertices `x ≠ λ`, with `w x = ±2^rank x` for
   `x > λ` (sign: favourable or not), `w x = 0` otherwise, `e = -1` if `λ` is favourable and `+1`
   otherwise, and `M = 4|V| + 1`: lexicographically, the signed sum over the set `B` and the signed
   step count of the play value. Bellman–Ford with `|V|` rounds (`bfVal`); all cycles avoiding
   the target are negative, which the proofs show.
3. **Moves.** An owned vertex moves to its first allowed successor of greatest value
   (`argmaxBy`); the other vertices keep `p`.

## Cost model
`TimeM ℕ` annotations are trusted (cslib design principle 2); this is what is charged, with
`n = |V|` and `m = edgeCount G` the number of edges.
* **One tick** per iteration of every loop: each candidate of phase 1, each round of a fixpoint
  iteration (`iterT`).
* **Non-constant work is charged explicitly** with `✓[c]`: one round of a backward-reachability
  or Bellman–Ford iteration, building the `allowed` lists, or choosing all moves scans every vertex
  and its successor list once and costs `roundCost nb = Σ_v (|nb v| + 1)` for the successor lists
  `nb` in use (adjacency lists are assumed given; `|hsucc v| ≤ |succList G v| + 1`); building a
  class (a table over all vertices) costs `n`; the self-loop test of a candidate costs
  `|hsucc λ| + 1`; tabulating the class weights costs `n`.
* **Free**: reading one entry of a table (`look` on a `tabulate`, standing for an array),
  arithmetic and comparisons of integers (unit-cost RAM; the weights have `O(n)` bits),
  pattern matching, closures, and returning.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### Tables and loops -/

/-- `f` evaluated once into a table (extensionally `f`; keeps `#eval` polynomial). -/
def mat {α : Type*} (d : α) (f : V → α) : V → α := let t := tabulate f; fun v => look t d v

/-- A profile evaluated once into a table. -/
def matV (f : V → V) : V → V := let t := tabulate f; fun v => look t v v

/-- `k` iterations of a timed step. -/
def iterT {α : Type*} (f : α → TimeM ℕ α) : ℕ → α → TimeM ℕ α
  | 0, a => pure a
  | k + 1, a => do let b ← f a; iterT f k b

/-- The cost of scanning every vertex and its successor list `nb` once. -/
def roundCost (nb : V → List V) : ℕ := ((univList V).map fun v => (nb v).length + 1).sum

/-! ### Generic graph computations over successor lists `nb` -/

/-- One backward-reachability round: add the vertices of `S` with a successor in `X`. -/
def reachRound (nb : V → List V) (S X : V → Bool) : V → Bool :=
  mat false fun v => X v || (S v && (nb v).any X)

/-- The vertices that reach `x` along `nb`-edges whose sources lie in `S` (`|V|` rounds). -/
def reachFrom (nb : V → List V) (S : V → Bool) (x : V) : V → Bool :=
  (reachRound nb S)^[Fintype.card V] fun v => decide (v = x)

/-- `reachFrom`, timed: one `roundCost` per round. -/
def reachFromT (nb : V → List V) (S : V → Bool) (x : V) : TimeM ℕ (V → Bool) :=
  iterT (fun X => do ✓[roundCost nb] return reachRound nb S X) (Fintype.card V)
    fun v => decide (v = x)

/-- The initial Bellman–Ford values: `0` at targets, `⊥` (no path) elsewhere. -/
def bfInit (tgt : V → Bool) : V → WithBot ℤ := fun v => if tgt v then 0 else ⊥

/-- One Bellman–Ford round for the best path to a target, a path weighing the sum of `c` over
    its vertices before the target. -/
def bfRound (nb : V → List V) (tgt : V → Bool) (c : V → ℤ) (D : V → WithBot ℤ) :
    V → WithBot ℤ :=
  mat ⊥ fun v => if tgt v then 0 else (nb v).foldr (fun w a => max ((c v : WithBot ℤ) + D w) a) ⊥

/-- Bellman–Ford with `|V|` rounds. -/
def bfVal (nb : V → List V) (tgt : V → Bool) (c : V → ℤ) : V → WithBot ℤ :=
  (bfRound nb tgt c)^[Fintype.card V] (bfInit tgt)

/-- `bfVal`, timed: one `roundCost` per round. -/
def bfValT (nb : V → List V) (tgt : V → Bool) (c : V → ℤ) : TimeM ℕ (V → WithBot ℤ) :=
  iterT (fun D => do ✓[roundCost nb] return bfRound nb tgt c D) (Fintype.card V) (bfInit tgt)

/-- The first element of `ws` of greatest value `D` (`d` for the empty list). -/
def argmaxBy (D : V → WithBot ℤ) (d : V) (ws : List V) : V :=
  ws.foldl (fun b x => if D b < D x then x else b) (ws.headD d)

/-! ### The best response -/

variable (G : Game V) [DecidableRel G.edge] (pl : Bool) (p : V → V)

/-- The number of edges. -/
def edgeCount : ℕ := ((univList V).map fun v => (succList G v).length).sum

/-- Does priority of `x` favour the player `pl` (`false` = Even, `true` = Odd)? -/
def favours (x : V) : Bool := (G.prio x % 2 == 0) != pl

/-- The successors of `v` in the one-player graph: all edges at owned vertices, the move of `p`
    elsewhere. -/
def hsucc (v : V) : List V := if ownedBy G pl v then succList G v else [p v]

/-- The candidate cycle maxima, best first for the player. -/
def cands : List V :=
  (univList V).reverse.filter (favours G pl) ++ (univList V).filter fun x => !favours G pl x

/-- The unclassified vertices. -/
def unclassified (cls : V → Option V) : V → Bool := fun v => (cls v).isNone

/-- Does candidate `x` open a class: it is unclassified and reaches itself in at least one step
    through unclassified vertices `≤ x`? -/
def opens (cls : V → Option V) (x : V) : Bool :=
  unclassified cls x && (hsucc G pl p x).any
    (reachFrom (hsucc G pl p) (fun v => unclassified cls v && decide (v ≤ x)) x)

/-- Process one candidate `x`: if it opens a class, every unclassified vertex reaching `x`
    through unclassified vertices joins the class of `x`. -/
def classStep (cls : V → Option V) (x : V) : V → Option V :=
  if opens G pl p cls x then
    let A := reachFrom (hsucc G pl p) (unclassified cls) x
    mat none fun v => if unclassified cls v && A v then some x else cls v
  else cls

/-- `classStep`, timed. -/
def classStepT (cls : V → Option V) (x : V) : TimeM ℕ (V → Option V) := do
  ✓ let S := fun v => unclassified cls v && decide (v ≤ x)
  let Y ← reachFromT (hsucc G pl p) S x
  ✓[(hsucc G pl p x).length + 1] let o := unclassified cls x && (hsucc G pl p x).any Y
  if o then do
    let A ← reachFromT (hsucc G pl p) (unclassified cls) x
    ✓[Fintype.card V] return mat none fun v => if unclassified cls v && A v then some x else cls v
  else return cls

/-- The cycle-maximum class of every vertex (`none` never occurs, see the proofs). -/
def classes : V → Option V := (cands G pl).foldl (classStep G pl p) fun _ => none

/-- `classes`, timed. -/
def classesT : TimeM ℕ (V → Option V) := (cands G pl).foldlM (classStepT G pl p) fun _ => none

/-- The successors in the same class. -/
def allowed (cls : V → Option V) (v : V) : List V := (hsucc G pl p v).filter fun w => cls w == cls v

/-- The class maxima (Bellman–Ford targets). -/
def isTarget (cls : V → Option V) (v : V) : Bool := cls v == some v

/-- The scale separating the signed sum from the step count. -/
def scale (V : Type*) [Fintype V] : ℤ := 4 * Fintype.card V + 1

/-- The signed weight `±2^rank x` for the player. -/
def pw (x : V) : ℤ := if favours G pl x then 2 ^ rank x else -(2 ^ rank x)

/-- The Bellman–Ford weight of `v` in its class. -/
def bfWeight (cls : V → Option V) (v : V) : ℤ :=
  match cls v with
  | some l => (if l < v then scale V * pw G pl v else 0) + (if favours G pl l then -1 else 1)
  | none => 0

/-- The moves from the class table and the path values. -/
def movesOf (al : V → List V) (D : V → WithBot ℤ) : V → V :=
  matV fun v => if ownedBy G pl v then argmaxBy D (p v) (al v) else p v

/-- The best response of player `pl` to the other player's moves in `p`, timed. -/
def bestResponseT : TimeM ℕ (V → V) := do
  let cls ← classesT G pl p
  ✓[roundCost (hsucc G pl p)] let al := mat [] (allowed G pl p cls)
  ✓[Fintype.card V] let c := mat 0 (bfWeight G pl cls)
  let D ← bfValT al (isTarget cls) c
  ✓[roundCost al] return movesOf G pl p al D

/-- The best response of player `pl` to the other player's moves in `p`. -/
def bestResponse : V → V := (bestResponseT G pl p).ret

/-- Contract (optimality): `bestResponse` changes only `pl`'s moves, follows edges when `p`
    does, and no vertex of `pl` has a strictly better successor under its keys (the conclusion
    of `respond_spec`). -/
def BestResponseOptimal : Prop :=
  let q := bestResponse G pl p
  (∀ v, ownedBy G pl v = false → q v = p v) ∧
    ((∀ v, G.edge v (p v)) → ∀ v, G.edge v (q v)) ∧
    (∀ v, ownedBy G pl v = true → ∀ w, G.edge v w →
      if pl then key G q (q v) ≤ key G q w else key G q w ≤ key G q (q v))

/-- The cost bound of `bestResponse`, with `n = |V|` and `m` edges. -/
def bestResponseBound (n m : ℕ) : ℕ := 4 * (n + 1) ^ 2 * (m + 2 * n + 1)

/-- Contract (cost): `bestResponse` takes at most `4 (n + 1)² (m + 2n + 1)` steps. -/
def BestResponseCost : Prop :=
  (bestResponseT G pl p).time ≤ bestResponseBound (Fintype.card V) (edgeCount G)

end MercLib.HybridSI

end HybridSIBestResponse
