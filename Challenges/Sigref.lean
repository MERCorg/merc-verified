import MercLib.Algorithms.Sigref.Branching
import MercLib.Algorithms.Sigref.Defs
import MercLib.Algorithms.Sigref.Iteration
import MercLib.Algorithms.Sigref.KeyComp
import MercLib.Algorithms.Sigref.Refinable
import MercLib.Theory.Sigref.RelBisim
import MercLib.Algorithms.Sigref.Scc
import MercLib.Theory.Sigref.SigData
import MercLib.Theory.Sigref.SigE
import MercLib.Algorithms.Sigref.Strong
import MercLib.Algorithms.Sigref.TopoSort
import MercLib.Algorithms.Sigref.Worklist

/-!
# Comparator challenge: signature refinement (human-vetted)

The headline theorems of `MercLib/{Theory,Algorithms}/Sigref/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`). Intermediate lemmas are not challenged.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Sigref

open Cslib MercLib.LTS MercLib.Signatures

/-! ## Strong signature refinement -/

/-- **Abstract strong signature refinement is correct.** For any LTS, the invariant `StrongInv`
(partition coarser than bisimilarity; dirty states closed under bisimilarity; clean states of a
block have equal signatures) holds for the initial configuration and is preserved by every step.
In any configuration that satisfies it and has no dirty states, the partition is exactly strong
bisimilarity. See `StrongSigrefCorrect` (`Algorithms/Sigref/Strong.lean`). -/
theorem strongSigrefCorrect {State Label : Type} (lts : LTS State Label) :
    StrongSigrefCorrect lts := sorry

/-- **Abstract strong signature refinement terminates.** For an LTS on a finite state space, the
step relation is well-founded: every sequence of steps is finite. See `StrongSigrefTerminates`
(`Algorithms/Sigref/Strong.lean`). -/
theorem strongSigrefTerminates {State Label : Type} [Finite State]
    (lts : LTS State Label) : StrongSigrefTerminates lts := sorry

/-! ## Branching signature refinement -/

/-- **Abstract branching signature refinement is correct.** For an LTS with a silent action, the
invariant `BranchingInv` holds initially, and it is preserved by every step if the LTS is
τ-loop-free. In any configuration that satisfies it and has no dirty states, the partition is
exactly branching bisimilarity. See `BranchingSigrefCorrect` (`Algorithms/Sigref/Branching.lean`). -/
theorem branchingSigrefCorrect {State Label : Type} [HasTau Label]
    (lts : LTS State Label) : BranchingSigrefCorrect lts := sorry

/-- **Abstract branching signature refinement terminates.** For an LTS with a silent action on a
finite state space, every sequence of steps is finite. See `BranchingSigrefTerminates`
(`Algorithms/Sigref/Branching.lean`). -/
theorem branchingSigrefTerminates {State Label : Type} [HasTau Label] [Finite State]
    (lts : LTS State Label) : BranchingSigrefTerminates lts := sorry

/-- **Abstract branching signature refinement reaches the answer.** For a finite τ-loop-free
LTS, some run from the initial configuration reaches a configuration without dirty states whose
partition is exactly branching bisimilarity. See `BranchingSigrefTotal`
(`Algorithms/Sigref/Branching.lean`). -/
theorem branchingSigrefTotal {State Label : Type} [HasTau Label] [Finite State]
    (lts : LTS State Label) : BranchingSigrefTotal lts := sorry

end MercLib.Sigref

namespace MercLib.Sigref.RP

open Cslib MercLib.LTS MercLib.Signatures

/-! ## The algorithm on the refinable partition -/

/-- **The refinable-partition algorithm is partially correct.** Let `lts` be a τ-loop-free LTS on
`Fin n` (`0 < n`), with `inc u` listing exactly the incoming transitions `(y, a)` of `u` and
`preds x` exactly the silent predecessors of `x`. Then in every configuration reachable from the
initial partition whose worklist is empty, two states share a block iff they are branching
bisimilar. See `RPSigrefCorrect` (`Algorithms/Sigref/Iteration.lean`). -/
theorem rpSigrefCorrect {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefCorrect lts inc preds hn := sorry

/-- **The refinable-partition algorithm terminates.** Under the hypotheses of `rpSigrefCorrect`,
every run from the initial partition is finite. See `RPSigrefTerminates`
(`Algorithms/Sigref/Iteration.lean`). -/
theorem rpSigrefTerminates {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefTerminates lts inc preds hn := sorry

/-- **The refinable-partition algorithm is totally correct.** Under the hypotheses of
`rpSigrefCorrect`, some run from the initial partition reaches an empty worklist, and then two
states share a block iff they are branching bisimilar. See `RPSigrefTotal`
(`Algorithms/Sigref/Iteration.lean`). -/
theorem rpSigrefTotal {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefTotal lts inc preds hn := sorry

/-! ## The algorithm with implementation keys -/

/-- **The algorithm with implementation keys is partially correct.** Let `lts` be an LTS on
`Fin n` (`0 < n`) whose states are topologically sorted along silent steps (`TopoSorted`), with
`inc u` listing exactly the incoming transitions `(y, a)` of `u` and `preds x` exactly the silent
predecessors of `x`. Then in every configuration reachable from the initial partition whose
worklist is empty, two states share a block iff they are branching bisimilar. See
`RPSigrefKCorrect` (`Algorithms/Sigref/KeyComp.lean`). -/
theorem rpSigrefKCorrect {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKCorrect lts inc preds hn := sorry

/-- **The algorithm with implementation keys terminates.** Under the hypotheses of
`rpSigrefKCorrect`, every run from the initial partition is finite. See `RPSigrefKTerminates`
(`Algorithms/Sigref/KeyComp.lean`). -/
theorem rpSigrefKTerminates {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKTerminates lts inc preds hn := sorry

/-- **The algorithm with implementation keys is totally correct.** Under the hypotheses of
`rpSigrefKCorrect`, some run from the initial partition reaches an empty worklist, and then two
states share a block iff they are branching bisimilar. See `RPSigrefKTotal`
(`Algorithms/Sigref/KeyComp.lean`). -/
theorem rpSigrefKTotal {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKTotal lts inc preds hn := sorry

end MercLib.Sigref.RP
