import MercLib.Graph.Scc
import MercLib.Graph.Tarjan

/-!
# Comparator challenge: graphs (human-vetted)

The headline theorems of `MercLib/Graph/`, stated with `sorry` against the human-vetted spec files
only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Graph

variable {V : Type*}

/-! ## Strongly connected components -/

/-- Every non-empty subset of a finite graph has a final SCC. -/
theorem finalSCCExists (E : V → V → Prop) [Finite V] (X : Set V) : FinalSCCExists E X := sorry

end MercLib.Graph

namespace MercLib.Tarjan

variable {n : ℕ}

/-! ## The iterative Tarjan search -/

/-- When the run stops, `blk` numbers the states by their SCC with `eq` blocks, and no step of the
    run fails. -/
theorem tarjanCorrect {n : ℕ} (g : Graph n) : TarjanCorrect g := sorry

/-- The measure decreases at every step of a run. -/
theorem tarjanTerminates {n : ℕ} (g : Graph n) : TarjanTerminates g := sorry

/-- Every block of an SCC numbering is an SCC of the graph. -/
theorem IsSccPartition.isSCC {g : Graph n} {blk : Fin n → ℕ} {k : ℕ} (h : IsSccPartition g blk k)
    (s : Fin n) : MercLib.Graph.IsSCC (Edge g) Set.univ {t | blk t = blk s} := sorry

end MercLib.Tarjan
