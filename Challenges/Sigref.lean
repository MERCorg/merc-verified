import MercLib.Sigref.Branching
import MercLib.Sigref.Defs
import MercLib.Sigref.Iteration
import MercLib.Sigref.KeyComp
import MercLib.Sigref.Refinable
import MercLib.Sigref.RelBisim
import MercLib.Sigref.Scc
import MercLib.Sigref.SigData
import MercLib.Sigref.SigE
import MercLib.Sigref.Strong
import MercLib.Sigref.TopoSort
import MercLib.Sigref.Worklist

/-!
# Comparator challenge: signature refinement (human-vetted)

The headline theorems of `MercLib/Sigref/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`). Intermediate lemmas are not challenged.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Sigref

open Cslib MercLib.LTS MercLib.Signatures

/-! ## Strong signature refinement -/

/-- Correctness of abstract strong signature refinement: the invariant holds initially, is
    preserved by every step, and a configuration without dirty states is exactly bisimilarity. -/
theorem strongSigrefCorrect {State Label : Type} (lts : LTS State Label) :
    StrongSigrefCorrect lts := sorry

/-- Termination of abstract strong signature refinement on a finite state space. -/
theorem strongSigrefTerminates {State Label : Type} [Finite State]
    (lts : LTS State Label) : StrongSigrefTerminates lts := sorry

/-! ## Branching signature refinement -/

/-- Correctness of abstract branching signature refinement: the invariant holds initially, is
    preserved by every step on a τ-loop-free LTS, and a configuration without dirty states is
    exactly branching bisimilarity. -/
theorem branchingSigrefCorrect {State Label : Type} [HasTau Label]
    (lts : LTS State Label) : BranchingSigrefCorrect lts := sorry

/-- Termination of abstract branching signature refinement on a finite state space. -/
theorem branchingSigrefTerminates {State Label : Type} [HasTau Label] [Finite State]
    (lts : LTS State Label) : BranchingSigrefTerminates lts := sorry

/-- On a finite τ-loop-free LTS abstract branching signature refinement always reaches a
    configuration without dirty states whose partition is branching bisimilarity. -/
theorem branchingSigrefTotal {State Label : Type} [HasTau Label] [Finite State]
    (lts : LTS State Label) : BranchingSigrefTotal lts := sorry

end MercLib.Sigref

namespace MercLib.Sigref.RP

open Cslib MercLib.LTS MercLib.Signatures

/-! ## The algorithm on the refinable partition -/

/-- Partial correctness: whenever the worklist is empty after a run from the initial partition,
    the partition is exactly branching bisimilarity. -/
theorem rpSigrefCorrect {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefCorrect lts inc preds hn := sorry

/-- Termination: every run from the initial partition is finite. -/
theorem rpSigrefTerminates {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefTerminates lts inc preds hn := sorry

/-- Total correctness: from the initial partition the algorithm always reaches an empty worklist,
    and the resulting partition is exactly branching bisimilarity. -/
theorem rpSigrefTotal {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefTotal lts inc preds hn := sorry

/-! ## The algorithm with implementation keys -/

/-- Partial correctness with implementation keys: whenever the worklist is empty after a run from
    the initial partition, the partition is exactly branching bisimilarity. -/
theorem rpSigrefKCorrect {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKCorrect lts inc preds hn := sorry

/-- Termination with implementation keys: every run from the initial partition is finite. -/
theorem rpSigrefKTerminates {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKTerminates lts inc preds hn := sorry

/-- Total correctness with implementation keys: from the initial partition the algorithm
    always reaches an empty worklist, and the resulting partition is exactly branching
    bisimilarity. -/
theorem rpSigrefKTotal {n : ℕ} {Label : Type} [HasTau Label]
    (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKTotal lts inc preds hn := sorry

end MercLib.Sigref.RP
