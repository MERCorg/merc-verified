module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau

open Cslib (LTS HasTau)

public section BranchingBisimulation

/-! ## Branching bisimulation and branching bisimilarity -/

/-- A branching bisimulation is similar to a `WeakBisimulation` in that it allows for a saturation
of internal transitions, but it is a stronger equivalence in that it is able to distinguish
when internal work constitutes a choice. There are several (equivalent) definitions used in
literature. The original one can be found in [R.J. van Glabbeek and W.P. Weijland,
"Branching Time and Abstraction in Bisimulation Semantics", 1990]. But we follow the slightly
more popular definition of [de Nicola and Vaandrager, 1995, https://doi.org/10.1145/201019.201032].
-/
def LTS.IsBranchingBisimulation [HasTau Label] (lts : LTS State Label)
  (r : State → State → Prop) :=
  ∀ ⦃s1 s2⦄, r s1 s2 → ∀ μ,
    /- In case of a transition on the left -/
    (∀ s1', lts.Tr s1 μ s1' →
       /- A single tau transition can be mimicked by doing nothing. -/
       (μ = HasTau.τ ∧ r s1' s2) ∨
       /- Any transition can be mimicked by first performing a number of
       τ transitions while relating to the original state, and then mimicking
       the intended transition. -/
       ∃ s2' s2'', lts.STr s2 HasTau.τ s2' ∧ lts.Tr s2' μ s2'' ∧ r s1 s2' ∧ r s1' s2'')
    ∧
    /- The symmetric case of a transition on the right -/
    (∀ s2', lts.Tr s2 μ s2' →
       (μ = HasTau.τ ∧ r s1 s2') ∨
       ∃ s1' s1'', lts.STr s1 HasTau.τ s1' ∧ lts.Tr s1' μ s1'' ∧ r s1' s2 ∧ r s1'' s2')

/-- Two states are branching bisimilar if they are related by some branching bisimulation. -/
def BranchingBisimilarity [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 =>
    ∃ r : State → State → Prop, r s1 s2 ∧ LTS.IsBranchingBisimulation lts r

/-- Notation for branching bisimilarity. -/
notation s:max " ≈br[" lts "] " s':max => BranchingBisimilarity lts s s'

end BranchingBisimulation
