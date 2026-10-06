module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Refinement.Semantics
public import Refinement.Product
public import Refinement.Antichain

open Cslib (LTS HasTau)

@[expose] public section Algorithm

namespace Refinement

/-!
# The antichain-based exploration algorithm (Algorithms 4-6)

Section 5 of M. Laveaux, J. F. Groote, T. A. C. Willemse, *Correct and Efficient Antichain
Algorithms for Refinement Checking*, LMCS 17(1:8), 2021.

The algorithms explore `L1 ⋉ L2` (for `L1 := NormTr lts1` or `FdrNormTr lts1`), pruning via the
antichain. We model the triple `(working, antichain, done)` as `AlgState` and one loop iteration
as `AlgStep`; a *run* (`AlgRun`) is a `Relation.ReflTransGen` chain of steps from the initial
state.

**Modeling choice**: the real algorithm returns `false` and *halts* the instant it pops a witness
(line 9/12/19 for TR/SF/FD). We don't bake that early exit into `AlgStep` - a step always fully
processes whichever element of `working` it picks, regardless of whether that element is a
witness. Instead, "the algorithm would have returned `false`" is captured by `FoundWitness`:
whether a witness is *ever* popped into `done` along some run. This is equivalent for the
question Theorem 5.14 actually asks (does a witness turn up during exploration at all); it is not
equivalent as a *runtime* model (the real algorithm does strictly less work), but runtime cost is
not something this development reasons about. -/

/-- The algorithm's state: the frontier still to explore, the antichain of all discovered states,
    and the states already fully processed. -/
structure AlgState (State1 State2 : Type*) where
  /-- States discovered but not yet processed. -/
  working : Set (Set State1 × State2)
  /-- All states discovered so far (Section 4's antichain, `⊎`-extended on discovery). -/
  antichain : Set (Set State1 × State2)
  /-- States already popped and processed (the paper's ghost variable, Algorithm 6 line 4/23). -/
  done : Set (Set State1 × State2)

/-- The initial state (Algorithms 4-6, lines 2-3): a single starting pair, already in both
    `working` and `antichain`. -/
def AlgState.initial (p0 : Set State1 × State2) : AlgState State1 State2 where
  working := {p0}
  antichain := {p0}
  done := ∅

/-- The `a`-successors of `p` (for any visible `a`) not yet covered by `A` - exactly the set a
    loop iteration (lines 13-22) adds to `working` and `antichain`. -/
def newSuccessors [HasTau Label]
    (L1 : LTS (Set State1) Label) (lts2 : LTS State2 Label)
    (A : Set (Set State1 × State2)) (p : Set State1 × State2) : Set (Set State1 × State2) :=
  { q | (∃ a, (product L1 lts2).Tr p a q) ∧ ¬ AntichainMem A q }

/-- One loop iteration (Algorithms 4-6, lines 5-23, minus the witness check - see the module
    docstring): pop some `p ∈ working`, move it to `done`, and extend `working`/`antichain` with
    its not-yet-covered successors. -/
def AlgStep [HasTau Label] (L1 : LTS (Set State1) Label) (lts2 : LTS State2 Label)
    (s s' : AlgState State1 State2) : Prop :=
  ∃ p ∈ s.working,
    s'.working = (s.working \ {p}) ∪ newSuccessors L1 lts2 s.antichain p ∧
    s'.antichain = s.antichain ∪ newSuccessors L1 lts2 s.antichain p ∧
    s'.done = insert p s.done

/-- A run of the algorithm: zero or more loop iterations from `c0`. -/
def AlgRun [HasTau Label] (L1 : LTS (Set State1) Label) (lts2 : LTS State2 Label) :
    AlgState State1 State2 → AlgState State1 State2 → Prop :=
  Relation.ReflTransGen (AlgStep L1 lts2)

/-- A state is terminal once there is nothing left in `working` (the `while working ≠ ∅`
    loop condition has become false). -/
def AlgState.Terminal (s : AlgState State1 State2) : Prop := s.working = ∅

/-- The algorithm, started from `p0`, finds a witness: some witness state is popped into `done`
    along some run (see the module docstring for why this - rather than "the algorithm halts
    returning `false`" - is the notion Theorem 5.14 is proved about). -/
def FoundWitness [HasTau Label] (L1 : LTS (Set State1) Label) (lts2 : LTS State2 Label)
    (IsWitness : Set State1 → State2 → Prop) (p0 : Set State1 × State2) : Prop :=
  ∃ c, AlgRun L1 lts2 (AlgState.initial p0) c ∧ ∃ p ∈ c.done, IsWitness p.1 p.2

end Refinement

end Algorithm
