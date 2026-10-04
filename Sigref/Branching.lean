import Mathlib.Logic.Relation
import Signatures.InductiveSignatures
import Sigref.Strong
import Sigref.RelBisim

/-!
# Abstract branching-bisimulation signature refinement

Pseudocode (Algorithm 2 of the paper) for a τ-loop-free LTS:

```
π := {S};  X := S
while some block B of π contains a dirty state:
  Bd := { s ∈ B | s reaches some d ∈ B ∩ X by an inert τ-path }          -- backward inert closure
  split B into  B \ Bd  and the E_π-classes of Bd                          -- E_π ≈ Sig_π-equality
  keep one part under the old identity; U := B \ keep
  X := (X \ Bd) ∪ Pred(U),   Pred(U) = {sp | sp -μ→ u, u ∈ U, μ = τ → sp ∉ U}
```

The signature equality `Sig_π(s) = Sig_π(t)` of the paper is the relation `E π` of `RelBisim.lean`
(branching bisimilarity relative to `π`). Brute force on 40000 random LTSs found that the two
coincide for every partition (`scripts/sigref_bruteforce.py` and its siblings), so the hash-based
signature of an implementation is only a way to compute `E π`; relating them is a separate, static
lemma. The *flat* signature is not a valid abstraction: it forgets the inert τ-edges that turn
non-inert after a split.

`BranchingInv` is the invariant, preserved by every non-deterministic step (`branchingInv_step`)
and decisive at the fixpoint (`branchingInv_final`). Termination is as for the strong algorithm.
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label]

/-- States that reach `D` by an inert τ-path (every step stays in one block of `π`). -/
def inertClosure (lts : LTS State Label) (π : Setoid State) (D : Set State) : Set State :=
  {s | ∃ d ∈ D, InertReach lts π s d}

/-- `Pred(U)` of the paper: states with a transition into `U`, except τ-transitions inside `U`. -/
def predB (lts : LTS State Label) (U : Set State) : Set State :=
  {sp | ∃ μ u, u ∈ U ∧ lts.Tr sp μ u ∧ (μ = HasTau.τ → sp ∉ U)}

/-- The relation after splitting the class `cls π s0`: its dirty part `D` is regrouped by `E π`,
and its clean part stays together. -/
def branchRel (lts : LTS State Label) (π : Setoid State) (X : Set State) (s0 : State)
    (s t : State) : Prop :=
  π.r s t ∧ (s ∈ cls π s0 → ((s ∈ inertClosure lts π (cls π s0 ∩ X) ↔
      t ∈ inertClosure lts π (cls π s0 ∩ X)) ∧
    (s ∈ inertClosure lts π (cls π s0 ∩ X) → E lts π s t)))

/-- The facts that make `c'` the result of one iteration of `c` on the class of `s0`, keeping the
`π'`-class of `s1`. -/
structure StepFacts (lts : LTS State Label) (c c' : Config State) (s0 s1 : State) : Prop where
  dirty : ∃ s, s ∈ cls c.π s0 ∧ s ∈ c.X
  mem : s1 ∈ cls c.π s0
  rel : ∀ s t, c'.π.r s t ↔ branchRel lts c.π c.X s0 s t
  dX : c'.X = (c.X \ inertClosure lts c.π (cls c.π s0 ∩ c.X)) ∪
      predB lts (cls c.π s0 \ cls c'.π s1)

/-- One non-deterministic iteration of the branching algorithm. -/
def BranchingStep (lts : LTS State Label) (c c' : Config State) : Prop :=
  ∃ s0 s1, StepFacts lts c c' s0 s1

/-- The invariant. `Y` is the *effective* dirty set (dirty plus inert backward closure).
* `R`: the partition is coarser than branching bisimilarity;
* `M`: `Y` is closed under branching bisimilarity;
* `U`: clean states of a block are `E π`-related (the paper's Lemma 6);
* `S`: a clean and a dirty state of one block are not `E π`-related (separation). -/
structure BranchingInv (lts : LTS State Label) (c : Config State) : Prop where
  R : ∀ s t, BranchingBisimilarity lts s t → c.π.r s t
  M : ∀ s t, BranchingBisimilarity lts s t →
        (s ∈ inertClosure lts c.π c.X ↔ t ∈ inertClosure lts c.π c.X)
  U : ∀ s t, c.π.r s t → s ∉ inertClosure lts c.π c.X → t ∉ inertClosure lts c.π c.X →
        E lts c.π s t
  S : ∀ s t, c.π.r s t → s ∉ inertClosure lts c.π c.X → t ∈ inertClosure lts c.π c.X →
        ¬ E lts c.π s t

/-- **Correctness of the abstract branching signature refinement.** The invariant (R: partition
coarser than branching bisimilarity, M: dirty closure closed under bisimilarity, U: clean states of a
block are `E π`-related, S: clean and dirty states are separated) holds initially, is preserved by
every non-deterministic step on a τ-loop-free LTS, and a configuration without dirty states is
exactly branching bisimilarity. -/
def BranchingSigrefCorrect (lts : LTS State Label) : Prop :=
  BranchingInv lts (initConfig State) ∧
  (TauLoopFree lts → ∀ c c' : Config State,
    BranchingInv lts c → BranchingStep lts c c' → BranchingInv lts c') ∧
  (∀ c : Config State, BranchingInv lts c → (∀ s, s ∉ c.X) →
    ∀ s t, c.π.r s t ↔ BranchingBisimilarity lts s t)

/-- **Termination of the abstract branching signature refinement.** -/
def BranchingSigrefTerminates [Finite State] (lts : LTS State Label) : Prop :=
  WellFounded (fun c' c : Config State => BranchingStep lts c c')

/-- **Progress**: a configuration with a dirty state can always take a step (the split relation is
an equivalence). -/
def BranchingSigrefProgress (lts : LTS State Label) : Prop :=
  ∀ (c : Config State) (s : State), s ∈ c.X → ∃ c', BranchingStep lts c c'

/-- **Totality**: on a finite τ-loop-free LTS the algorithm reaches, whatever choices it makes, a
configuration without dirty states whose partition is branching bisimilarity. -/
def BranchingSigrefTotal [Finite State] (lts : LTS State Label) : Prop :=
  TauLoopFree lts →
    ∃ c : Config State, Relation.ReflTransGen (BranchingStep lts) (initConfig State) c ∧
      (∀ s, s ∉ c.X) ∧ ∀ s t, c.π.r s t ↔ BranchingBisimilarity lts s t

end Sigref
