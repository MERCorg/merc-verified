module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Refinement.Semantics
public import Refinement.Product
public import Refinement.Antichain
public import Refinement.Algorithm
public import Refinement.ImpossibleFutures

open Cslib (LTS HasTau)

@[expose] public section AlgorithmOpt

namespace Refinement

/-!
# The optimised impossible futures algorithms (Algorithms 5 and 6)

Section 4.2 of M. Laveaux and T. A. C. Willemse, *Deciding Impossible Futures*, LNCS 16365, 2026.

**Algorithm 5** (`WeakTraceOpt`) is the inner weak trace inclusion check `t ⊑wt impl` between a
specification state `t : State1` and an implementation state `impl : State2`. It is the
exploration of Algorithm 3 on the product `NormTr lts2 ⋉ lts1` (roles swapped w.r.t. the outer
check, hence pairs `(Set State2 × State1)`), additionally given a *positive* antichain `pos`
(pairs from which no TR-witness is reachable) and a *negative* antichain `neg` (pairs from which one
is). Pairs covered by `pos` are not explored, and pairs covered by `neg` (or a TR-witness
itself) abort the search with verdict `false`.

**Algorithm 6** (`OptAlgStep`, `OptFoundFailure`) is the outer exploration of `lts1 ⋉ lts2`
that calls Algorithm 5 only at stable implementation states, threading `pos`/`neg` through the
calls (`CheckLoop`).

As in `Refinement/Algorithm.lean`, the early `return false` is not baked into the step relation:
`OptFails` says that the algorithm *would* return `false` at the current configuration.
-/

/-! ## Positive and negative antichains -/

/-- A positive antichain is sound (Proposition 3, first hypothesis) iff no TR-witness is reachable
    from any pair it covers, in the inner product `NormTr lts2 ⋉ lts1`. -/
def PosSound [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (P : Set (Set State2 × State1)) : Prop :=
  ∀ x, AntichainMem P x →
    ¬ ∃ q, (product (NormTr lts2) lts1).CanReach x q ∧ IsTRWitness q.1 q.2

/-- Membership in a negative antichain: its order is the converse of `AntichainMem`'s, a pair is
    covered iff it is `ProductLE` some member (smaller spec sets are *more* likely to be failing). -/
def NegMem (N : Set (Set State2 × State1)) (x : Set State2 × State1) : Prop :=
  ∃ y ∈ N, ProductLE x y

/-- Insertion into a negative antichain, discarding members that `x` now dominates. -/
def NegInsert (N : Set (Set State2 × State1)) (x : Set State2 × State1) :
    Set (Set State2 × State1) :=
  { y | y = x ∨ (y ∈ N ∧ ¬ ProductLE y x) }

/-- A negative antichain is sound (Proposition 3, second hypothesis) iff a TR-witness is reachable
    from every pair it covers. -/
def NegSound [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (N : Set (Set State2 × State1)) : Prop :=
  ∀ x, NegMem N x →
    ∃ q, (product (NormTr lts2) lts1).CanReach x q ∧ IsTRWitness q.1 q.2

/-! ## Algorithm 5 -/

/-- Pairs of the inner product that Algorithm 5 aborts on (line 15): a TR-witness (`spec' = ∅`)
    or a pair covered by the negative antichain. -/
def InnerFailing
    (neg : Set (Set State2 × State1)) (q : Set State2 × State1) : Prop :=
  NegMem neg q ∨ IsTRWitness q.1 q.2

/-- The successors a loop iteration of Algorithm 5 adds (line 17): not covered by the current
    antichain nor by the positive antichain. -/
def optNewSuccessors [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos A : Set (Set State2 × State1)) (p : Set State2 × State1) :
    Set (Set State2 × State1) :=
  { q | (∃ a, (product (NormTr lts2) lts1).Tr p a q) ∧ ¬ AntichainMem A q ∧ ¬ AntichainMem pos q }

/-- One loop iteration of Algorithm 5 that does not abort: pop `p`, none of whose successors is
    `InnerFailing`, and extend `working`/`antichain`. -/
def OptInnerStep [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Set (Set State2 × State1))
    (s s' : AlgState State2 State1) : Prop :=
  ∃ p ∈ s.working,
    (∀ q, (∃ a, (product (NormTr lts2) lts1).Tr p a q) → ¬ InnerFailing neg q) ∧
    s'.working = (s.working \ {p}) ∪ optNewSuccessors lts1 lts2 pos s.antichain p ∧
    s'.antichain = s.antichain ∪ optNewSuccessors lts1 lts2 pos s.antichain p ∧
    s'.done = insert p s.done

/-- The result relation of Algorithm 5: `WeakTraceOpt lts1 lts2 pos neg t impl b pos' neg'` holds
    iff the call `Weak-Trace_{ac-opt}(t, impl, pos, neg)` can return `(b, pos', neg')`
    (`pos'` resp. `neg'` being the extended antichain that is returned on a `true` resp. `false`
    verdict, the other one being unchanged). -/
inductive WeakTraceOpt [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Set (Set State2 × State1)) (t : State1) (impl : State2) :
    Bool → Set (Set State2 × State1) → Set (Set State2 × State1) → Prop where
  /-- Lines 2-3: the initial pair is already covered by the positive antichain. -/
  | cachedTrue : AntichainMem pos (NormInit lts2 impl, t) →
      WeakTraceOpt lts1 lts2 pos neg t impl true pos neg
  /-- Lines 4-5: the initial pair is covered by the negative antichain. -/
  | cachedFalse : ¬ AntichainMem pos (NormInit lts2 impl, t) →
      NegMem neg (NormInit lts2 impl, t) →
      WeakTraceOpt lts1 lts2 pos neg t impl false pos neg
  /-- Line 20: the exploration ran dry without aborting; the antichain is merged into `pos`. -/
  | exploredTrue {c : AlgState State2 State1} :
      ¬ AntichainMem pos (NormInit lts2 impl, t) →
      ¬ NegMem neg (NormInit lts2 impl, t) →
      Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg)
        (AlgState.initial (NormInit lts2 impl, t)) c →
      c.Terminal →
      WeakTraceOpt lts1 lts2 pos neg t impl true (pos ∪ c.antichain) neg
  /-- Lines 15-16: some pair being expanded has a failing successor; the initial pair is
      recorded in the negative antichain. -/
  | exploredFalse {c : AlgState State2 State1} {p : Set State2 × State1} :
      ¬ AntichainMem pos (NormInit lts2 impl, t) →
      ¬ NegMem neg (NormInit lts2 impl, t) →
      Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg)
        (AlgState.initial (NormInit lts2 impl, t)) c →
      p ∈ c.working →
      (∃ q, (∃ a, (product (NormTr lts2) lts1).Tr p a q) ∧ InnerFailing neg q) →
      WeakTraceOpt lts1 lts2 pos neg t impl false pos
        (NegInsert neg (NormInit lts2 impl, t))

/-! ## Algorithm 6 -/

/-- Lines 8-14 of Algorithm 6: the loop over the (enumerated) specification states `ts`, calling
    Algorithm 5 against the implementation state `s` and threading the antichains. The `Bool` is
    the final value of `b`: `false` iff some check passed (the loop exits early with the updated
    positive antichain), `true` iff all checks failed. -/
inductive CheckLoop [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (s : State2) :
    List State1 → Set (Set State2 × State1) → Set (Set State2 × State1) →
    Bool → Set (Set State2 × State1) → Set (Set State2 × State1) → Prop where
  | nil {pos neg} : CheckLoop lts1 lts2 s [] pos neg true pos neg
  | pass {t ts pos neg pos' neg'} :
      WeakTraceOpt lts1 lts2 pos neg t s true pos' neg' →
      CheckLoop lts1 lts2 s (t :: ts) pos neg false pos' neg'
  | fail {t ts pos neg pos' neg' b pos'' neg''} :
      WeakTraceOpt lts1 lts2 pos neg t s false pos' neg' →
      CheckLoop lts1 lts2 s ts pos' neg' b pos'' neg'' →
      CheckLoop lts1 lts2 s (t :: ts) pos neg b pos'' neg''

/-- Configuration of Algorithm 6: the exploration state of `Algorithm.lean` plus the two
    antichains shared by all inner calls. -/
structure OptState (State1 State2 : Type*) where
  /-- `working`, `antichain`, `done` of the outer exploration. -/
  core : AlgState State1 State2
  /-- The positive antichain (`antichain⁺`). -/
  pos : Set (Set State2 × State1)
  /-- The negative antichain (`antichain⁻`). -/
  neg : Set (Set State2 × State1)

/-- The initial configuration (lines 2-4). -/
def OptState.initial (p0 : Set State1 × State2) : OptState State1 State2 where
  core := AlgState.initial p0
  pos := ∅
  neg := ∅

/-- `ts` enumerates the set `U` without repetition. -/
def Enumerates (ts : List State1) (U : Set State1) : Prop :=
  ts.Nodup ∧ ∀ t, t ∈ ts ↔ t ∈ U

/-- The pair `p` makes Algorithm 6 return `false` in configuration `s`: either a successor has an
    empty specification set (line 22), or `p.2` is stable and every check of the loop failed
    (lines 8, 15-16; this includes `p.1 = ∅`). -/
def OptFailsAt [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (s : OptState State1 State2) (p : Set State1 × State2) : Prop :=
  (∃ q, (∃ a, (product (NormTr lts1) lts2).Tr p a q) ∧ q.1 = ∅) ∨
  (Stable lts2 p.2 ∧ ∃ ts, Enumerates ts p.1 ∧ ∃ pos' neg',
    CheckLoop lts1 lts2 p.2 ts s.pos s.neg true pos' neg')

/-- Algorithm 6 would return `false` in configuration `s`. -/
def OptFails [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (s : OptState State1 State2) : Prop :=
  ∃ p ∈ s.core.working, OptFailsAt lts1 lts2 s p

/-- One iteration of the outer loop (lines 6-26) at a pair `p` that does not make the algorithm
    return: the inner checks (if `p.2` is stable) run with `CheckLoop` and one of them passes,
    then `working`/`antichain` are extended with the uncovered successors as in `AlgStep`. -/
def OptAlgStep [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (s s' : OptState State1 State2) : Prop :=
  ∃ p ∈ s.core.working, ¬ OptFailsAt lts1 lts2 s p ∧
    (Stable lts2 p.2 →
      ∃ ts, Enumerates ts p.1 ∧ CheckLoop lts1 lts2 p.2 ts s.pos s.neg false s'.pos s'.neg) ∧
    (¬ Stable lts2 p.2 → s'.pos = s.pos ∧ s'.neg = s.neg) ∧
    s'.core.working =
      (s.core.working \ {p}) ∪ newSuccessors (NormTr lts1) lts2 s.core.antichain p ∧
    s'.core.antichain = s.core.antichain ∪ newSuccessors (NormTr lts1) lts2 s.core.antichain p ∧
    s'.core.done = insert p s.core.done

/-- A run of Algorithm 6. -/
def OptAlgRun [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    OptState State1 State2 → OptState State1 State2 → Prop :=
  Relation.ReflTransGen (OptAlgStep lts1 lts2)

/-- Algorithm 6, started from `p0`, returns `false` along some run. -/
def OptFoundFailure [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (p0 : Set State1 × State2) : Prop :=
  ∃ c, OptAlgRun lts1 lts2 (OptState.initial p0) c ∧ OptFails lts1 lts2 c

/-! ## Contract specs -/

/-- **Proposition 3.** Algorithm 5 terminates from sound antichains, its verdict is exactly weak
    trace inclusion `t ⊑wt impl` (written as trace refinement of `t` by... of `impl` in `lts2`
    against `lts1`), and the returned antichains stay sound. -/
def WeakTraceOptCorrectSpec [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Set (Set State2 × State1)) (_hpos : PosSound lts1 lts2 pos)
    (_hneg : NegSound lts1 lts2 neg) (t : State1) (impl : State2) : Prop :=
  (∃ b pos' neg', WeakTraceOpt lts1 lts2 pos neg t impl b pos' neg') ∧
  ∀ b pos' neg', WeakTraceOpt lts1 lts2 pos neg t impl b pos' neg' →
    (b = true ↔ (impl ⊑tr[lts2,lts1] t)) ∧ PosSound lts1 lts2 pos' ∧ NegSound lts1 lts2 neg'

/-- **Theorem 3.** For finite LTSs with a convergent implementation, Algorithm 6 never returns
    `false` iff impossible futures refinement holds. -/
def OptImpossibleFuturesCorrectSpec [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (_hconv : Convergent lts2) : Prop :=
  (s1 ⊑if[lts1,lts2] s2) ↔ ¬ OptFoundFailure lts1 lts2 (NormInit lts1 s1, s2)

end Refinement

end AlgorithmOpt
