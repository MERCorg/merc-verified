module

public import MercLib.Theory.Rewriting.SetAutomatonPartition
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonEval_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The headline theorems of the set automaton; the proofs are in `SetAutomatonEval_Proofs`, for every
admissible partition. The paper's partition is the instance `Depends`. -/

namespace MercLib.SetAutomaton

/-- **Correctness of the set automaton (Theorem 1).** -/
public theorem setAutomatonCorrect {F : Type} [DecidableEq F] (ar : F → ℕ) (Ls : Finset (Pat F))
    (L : State F → Position) : Correct ar Ls L := by
  intro hL hne hLs t hc hw
  rw [output_eq]
  exact correct_aux depR_admissible hL hne hLs t hc hw

/-- **Every position is inspected exactly once (Corollary 4).** -/
public theorem setAutomatonInspectsOnce {F : Type} [DecidableEq F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position) : InspectsOnce ar Ls L := by
  intro hL hne hLs t hc hw
  have e : {n | Node ar Ls L t n} = {n | NodeBy depR ar Ls L t n} := Set.ext fun _ => node_iff
  rw [e]
  exact inspectsOnce_aux depR_admissible hL hne hLs t hc hw

/-- **The automaton has finitely many states (Corollary 2).** -/
public theorem setAutomatonFinite {F : Type} [DecidableEq F] [Finite F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position) : FinitelyManyStates ar Ls L := by
  intro hL hLs
  have e : {s | Reachable ar Ls L s} = {s | ReachableBy depR ar Ls L s} :=
    Set.ext fun _ => reachable_iff
  rw [e]
  exact finite_aux depR_admissible hL hLs

/-- **The theorems hold for every admissible partition.** -/
public theorem partitionTheorems {F : Type} [DecidableEq F]
    (R : Position → F → Goal F → Goal F → Prop) [∀ l f, DecidableRel (R l f)] (ar : F → ℕ)
    (Ls : Finset (Pat F)) : PartitionTheorems R ar Ls :=
  fun hR _ => ⟨correct_aux hR, inspectsOnce_aux hR, finite_aux hR⟩

/-- **merc's partition is admissible.** -/
public theorem mercPartitionAdmissible {F : Type} [DecidableEq F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) : MercPartitionAdmissible ar Ls :=
  merc_admissible

end MercLib.SetAutomaton
