module

public import MercLib.ParityGame.Game
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section HybridSIValuation

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# The Vöge–Jurdziński valuation of a positional profile

Games are the library games `ParityGame.Game V` on a finite, linearly ordered vertex type with
decidable edges. The linear order is the *relevance order* of Vöge and Jurdziński; it must extend
the priority order (`Game.Relabelled`), which every game satisfies after sorting its vertices by
(priority, name).

A *profile* `f : V → V` fixes one move per vertex (both players' positional strategies at once).
From every vertex the play under `f` is a lasso. Its *play value* is `(λ, B, k)`: `λ` the most
relevant vertex of the cycle, `B` the vertices more relevant than `λ` visited before `λ` is first
reached, `k` the number of steps until `λ` is first reached. The order on play values is encoded
exactly by an integer triple compared lexicographically (`Key`), with `r x` the rank of `x` in the
relevance order:
* `reward λ = r λ + 1` if `prio λ` is even, `-(r λ + 1)` otherwise;
* `Σ_{x ∈ B} sgn x · 2^(r x)`, `sgn x = +1` for even and `-1` for odd priority;
* `-k` if `prio λ` is even, `k` otherwise.
Even prefers larger keys, Odd smaller ones; player `0` wins the play from `v` iff the reward is
positive. This is the encoding of the Python reference implementation
(`experiments/hybrid/scripts/vj.py`).
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The priorities are monotone in the relevance order. -/
def _root_.MercLib.ParityGame.Game.Relabelled (G : Game V) : Prop := Monotone G.prio

/-- Play values, ordered lexicographically. -/
abbrev Key := Lex (ℤ × Lex (ℤ × ℤ))

/-- The vertices in relevance order. -/
def univList (V : Type*) [Fintype V] [LinearOrder V] : List V := Finset.univ.sort (· ≤ ·)

/-- The rank of `x` in the relevance order. -/
def rank (x : V) : ℕ := ((univList V).filter (· < x)).length

/-- `f` applied `k` times. -/
def iter (f : V → V) : ℕ → V → V
  | 0, v => v
  | k + 1, v => iter f k (f v)

/-- The first `k` vertices of the play from `v`: `v, f v, …, f^(k-1) v`. -/
def playPrefix (f : V → V) (k : ℕ) (v : V) : List V :=
  (List.range k).map fun i => iter f i v

/-- The most relevant vertex of the cycle reached from `v` (after `|V|` steps the play is on its
    cycle, whose length is at most `|V|`). -/
def cycMax (f : V → V) (v : V) : V :=
  let c := iter f (Fintype.card V) v
  (playPrefix f (Fintype.card V) c).foldl max c

/-- The number of steps until the play from `v` first reaches `cycMax f v` (at most `2 |V|`). -/
def stepsTo (f : V → V) (v : V) : ℕ :=
  ((List.range (2 * Fintype.card V + 1)).find? fun i => iter f i v == cycMax f v).getD 0

/-- The signed weight of a vertex: `+2^r` for even, `-2^r` for odd priority. -/
def weight (G : Game V) (x : V) : ℤ :=
  if G.prio x % 2 = 0 then 2 ^ rank x else -(2 ^ rank x)

/-- The vertices more relevant than the cycle maximum that the play from `v` visits before it
    first reaches the cycle maximum: the set `B` of the play value. -/
def bSet (f : V → V) (v : V) : Finset V :=
  ((playPrefix f (stepsTo f v) v).filter fun x => cycMax f v < x).toFinset

/-- The key of the play value of the play from `v` under `f`. -/
def key (G : Game V) (f : V → V) (v : V) : Key :=
  let l := cycMax f v
  let k := stepsTo f v
  let even := G.prio l % 2 = 0
  toLex ((if even then (rank l : ℤ) + 1 else -((rank l : ℤ) + 1)),
    toLex ((bSet f v).sum (weight G), if even then -(k : ℤ) else k))

/-- The values of `f` on all vertices, in relevance order (a table computed once). -/
def tabulate {α : Type*} (f : V → α) : List (V × α) := (univList V).map fun v => (v, f v)

/-- Look up `v` in a table made by `tabulate` (`d` is never used for such tables). -/
def look {α : Type*} (t : List (V × α)) (d : α) (v : V) : α := (t.lookup v).getD d

/-- The winner of a play value: player `0` iff the reward is positive. -/
def keyWinner (κ : Key) : Player := if 0 < (ofLex κ).1 then .zero else .one

end MercLib.HybridSI

end HybridSIValuation
