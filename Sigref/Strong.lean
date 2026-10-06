import Signatures.Signature
import Sigref.Basic

/-!
# Abstract strong-bisimulation signature refinement

Pseudocode (Algorithm 1 of the paper, strong signature `{(μ, π t) | s -μ→ t}`):

```
π := {S};  X := S                                  -- everything dirty
while X ∩ B ≠ ∅ for some block B of π:              -- any block with a dirty state
  split B into  B \ X  and the Sig_π-classes of  B ∩ X       (signatures taken w.r.t. old π)
  keep one part under the old identity; U := B \ keep
  X := (X \ B) ∪ Pred(U)                             -- Pred(U) = {sp | sp -μ→ u, u ∈ U}
```

`StrongStep` is the non-deterministic one-iteration relation; `StrongInv` is the invariant. The main
results are `strongInv_init`, `strongInv_step`, `strongStep_wf` (termination) and `strongInv_final`
(no dirty states ⇒ the partition is exactly bisimilarity).
-/

namespace Sigref

open Cslib

variable {State Label : Type}

/-- Predecessors of `U`: the states with a transition into `U`. -/
def predS (lts : LTS State Label) (U : Set State) : Set State :=
  {sp | ∃ μ u, u ∈ U ∧ lts.Tr sp μ u}

/-- The strong signature of `s` with respect to the partition `π`. -/
def sigS (lts : LTS State Label) (π : Setoid State) (s : State) : Set (Label × Quotient π) :=
  StrongSignature lts s (Quotient.mk π)

/-- The `π`-class of `s0`. -/
def cls (π : Setoid State) (s0 : State) : Set State := {t | π.r s0 t}

theorem cls_saturated (π : Setoid State) (s0 : State) : Saturated π (cls π s0) :=
  fun _ _ h => ⟨fun hs => π.trans hs h, fun ht => π.trans ht (π.symm h)⟩

/-- The partition after splitting the class of `s0`: dirty states regrouped by `sigS`. -/
def stepSetoid (lts : LTS State Label) (π : Setoid State) (X : Set State) (s0 : State) :
    Setoid State :=
  splitSetoid π (cls π s0) (cls π s0 ∩ X) (sigS lts π) (cls_saturated π s0)

/-- One non-deterministic iteration: any class `cls s0` with a dirty state is split, and any part
(the `π'`-class of `s1 ∈ cls s0`) keeps the old identity. -/
def StrongStep (lts : LTS State Label) (c c' : Config State) : Prop :=
  ∃ s0 s1 : State, (∃ s, s ∈ cls c.π s0 ∧ s ∈ c.X) ∧ s1 ∈ cls c.π s0 ∧
    c'.π = stepSetoid lts c.π c.X s0 ∧
    c'.X = (c.X \ cls c.π s0) ∪ predS lts (cls c.π s0 \ cls c'.π s1)

/-- The initial configuration: one block, every state dirty. -/
def topSetoid (State : Type) : Setoid State :=
  ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

def initConfig (State : Type) : Config State := ⟨topSetoid State, Set.univ⟩

/-- The invariant.
* `R`: the partition is coarser than bisimilarity (soundness of every split);
* `M`: dirtiness is closed under bisimilarity (marked states really changed, so separating them
  from the clean states never separates bisimilar states);
* `U`: clean states of a block have equal signatures (the paper's Lemma 6). -/
structure StrongInv (lts : LTS State Label) (c : Config State) : Prop where
  R : ∀ s t, LTS.Bisimilarity lts lts s t → c.π.r s t
  M : ∀ s t, LTS.Bisimilarity lts lts s t → (s ∈ c.X ↔ t ∈ c.X)
  U : ∀ s t, c.π.r s t → s ∉ c.X → t ∉ c.X → sigS lts c.π s = sigS lts c.π t

/-- **Correctness of the abstract strong signature refinement.** The invariant (partition coarser
than bisimilarity, dirtiness closed under bisimilarity, clean states of a block have equal
signatures) holds initially, is preserved by every non-deterministic step, and a configuration
without dirty states is exactly bisimilarity. -/
def StrongSigrefCorrect (lts : LTS State Label) : Prop :=
  StrongInv lts (initConfig State) ∧
  (∀ c c' : Config State, StrongInv lts c → StrongStep lts c c' → StrongInv lts c') ∧
  (∀ c : Config State, StrongInv lts c → (∀ s, s ∉ c.X) →
    ∀ s t, c.π.r s t ↔ LTS.Bisimilarity lts lts s t)

/-- **Termination of the abstract strong signature refinement**: every sequence of steps on a
finite state space is finite. -/
def StrongSigrefTerminates [Finite State] (lts : LTS State Label) : Prop :=
  WellFounded (fun c' c : Config State => StrongStep lts c c')

end Sigref
