import MercLib.Theory.Graph.Scc
import MercLib.Algorithms.Graph.Tarjan

/-!
# Comparator challenge: graphs (human-vetted)

The headline theorems of `MercLib/Theory/Graph/` and `MercLib/Algorithms/Graph/`, stated with `sorry` against the human-vetted spec files
only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Graph

variable {V : Type*}

/-! ## Strongly connected components -/

/-- **Every non-empty set of vertices contains a final SCC.** For a relation `E` on a finite
type `V` and a non-empty set `X ⊆ V`, `X` contains an SCC `C` of `E` restricted to `X` that no
edge inside `X` leaves (`IsFinalSCC`, a bottom component). See `FinalSCCExists`
(`Theory/Graph/Scc.lean`). -/
theorem finalSCCExists (E : V → V → Prop) [Finite V] (X : Set V) : FinalSCCExists E X := sorry

end MercLib.Graph

namespace MercLib.Tarjan

variable {n : ℕ}

/-! ## The iterative Tarjan search -/

/-- **Tarjan's algorithm is correct.** For every graph `g` on `n` states, the do-notation algorithm
`tarjan g` terminates without failing, and its result numbers the states by their strongly
connected components: `c.blk` with `c.eq` blocks is an SCC partition (`IsSccPartition`: two states
get the same number iff they reach each other along the edges of `g`). See `TarjanRunCorrect`
(`Algorithms/Graph/Tarjan.lean`). -/
theorem tarjanRunCorrect {n : ℕ} (g : Graph n) : TarjanRunCorrect g := sorry

/-- **The iterative Tarjan search is correct.** Let `g` be a graph on `n` states and `c` a
configuration reachable from `init g` by steps of the search. The next step from `c` never fails,
and if it stops, the numbering `c.blk` with `c.eq` blocks is an SCC partition (`IsSccPartition`:
two states get the same number iff they reach each other). See `TarjanCorrect`
(`Algorithms/Graph/Tarjan.lean`). -/
theorem tarjanCorrect {n : ℕ} (g : Graph n) : TarjanCorrect g := sorry

/-- **The iterative Tarjan search terminates.** For a graph `g`, every step `c → c'` from a
configuration `c` reachable from `init g` decreases the measure, `measure g c' < measure g c`, so
every run is finite. See `TarjanTerminates` (`Algorithms/Graph/Tarjan.lean`). -/
theorem tarjanTerminates {n : ℕ} (g : Graph n) : TarjanTerminates g := sorry

/-- **The blocks of an SCC numbering are SCCs.** If `blk` is an SCC numbering of `g` with `k`
blocks (`IsSccPartition g blk k`), then for every state `s` the block `{t | blk t = blk s}` is a
strongly connected component of the edge relation of `g` in the sense of `MercLib.Graph.IsSCC`
(on the whole state space). `IsSccPartition` is defined in `Algorithms/Graph/Tarjan.lean`. -/
theorem IsSccPartition.isSCC {g : Graph n} {blk : Fin n → ℕ} {k : ℕ} (h : IsSccPartition g blk k)
    (s : Fin n) : MercLib.Graph.IsSCC (Edge g) Set.univ {t | blk t = blk s} := sorry

end MercLib.Tarjan
