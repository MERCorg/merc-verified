import Sigref.Basic
import Cslib.Foundations.Semantics.LTS.HasTau

/-!
# τ-SCC quotient: the abstract specification

The preprocessing of the branching-bisimulation algorithm (`tau_cycle_elimination_and_reorder` in
`merc_reduction`) replaces every strongly connected component of the τ-graph by one state and
removes the τ-steps that stay inside a component. This file states, abstractly, what that
construction has to satisfy:

* `TauScc`/`IsTauSccPartition`: a numbering of the states by their τ-SCC;
* `quotientTau`: the existential quotient without the τ-steps inside a block (this includes the τ
  self-loops, and is the quotient of `quotient_lts_naive` with both elimination flags set);
* `IsCrossBB`: branching bisimulation between two (possibly different) LTSs;
* `QuotientCrossBisimulation`: the graph of a *sound* partition is a branching bisimulation from the
  LTS to its quotient (so the initial state is preserved up to branching bisimilarity);
* `QuotientTauAcyclic`: the quotient by the τ-SCCs has no τ-cycle (so it can be sorted
  topologically).
-/

namespace Sigref

open Cslib

variable {State State' Label : Type} [HasTau Label]

/-- Two states of the same τ-SCC: each reaches the other by τ-steps. -/
def TauScc (lts : LTS State Label) (s t : State) : Prop :=
  lts.τSTr s t ∧ lts.τSTr t s

/-- `blk` numbers the states by their τ-SCC with the numbers `0, …, k - 1`. -/
def IsTauSccPartition (lts : LTS State Label) (blk : State → ℕ) (k : ℕ) : Prop :=
  (∀ s, blk s < k) ∧ (∀ b, b < k → ∃ s, blk s = b) ∧ ∀ s t, blk s = blk t ↔ TauScc lts s t

/-- The existential quotient of `lts` by `blk`, without the τ-steps inside a block:
`[s] -a→ [t]` iff `s -a→ t` for some members, unless `a = τ` and `[s] = [t]`. -/
def quotientTau (lts : LTS State Label) (blk : State → ℕ) : LTS ℕ Label where
  Tr b μ c := ∃ s t, blk s = b ∧ blk t = c ∧ lts.Tr s μ t ∧ ¬ (μ = HasTau.τ ∧ b = c)

/-- A branching bisimulation between two LTSs (the two-LTS version of
`LTS.IsBranchingBisimulation`). -/
def IsCrossBB (l1 : LTS State Label) (l2 : LTS State' Label) (r : State → State' → Prop) : Prop :=
  ∀ ⦃s t⦄, r s t → ∀ μ,
    (∀ s', l1.Tr s μ s' →
      (μ = HasTau.τ ∧ r s' t) ∨
      ∃ t' t'', l2.STr t HasTau.τ t' ∧ l2.Tr t' μ t'' ∧ r s t' ∧ r s' t'') ∧
    (∀ t', l2.Tr t μ t' →
      (μ = HasTau.τ ∧ r s t') ∨
      ∃ s' s'', l1.STr s HasTau.τ s' ∧ l1.Tr s' μ s'' ∧ r s' t ∧ r s'' t')

/-- **The quotient is branching bisimilar to the LTS.** If every block only contains states of one
τ-SCC (soundness), the relation `s ↦ blk s` is a branching bisimulation from `lts` to the quotient. -/
def QuotientCrossBisimulation (lts : LTS State Label) (blk : State → ℕ) : Prop :=
  (∀ s t, blk s = blk t → lts.τSTr s t) →
    IsCrossBB lts (quotientTau lts blk) (fun s b => blk s = b)

/-- **The quotient by the τ-SCCs has no τ-cycle.** -/
def QuotientTauAcyclic (lts : LTS State Label) (blk : State → ℕ) (k : ℕ) : Prop :=
  IsTauSccPartition lts blk k →
    ∀ b, ¬ Relation.TransGen (fun b c => (quotientTau lts blk).Tr b HasTau.τ c) b b

end Sigref
