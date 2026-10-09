import Refinement.Semantics
import Refinement.Product
import Refinement.Algorithm
import Refinement.ImpossibleFutures
import Refinement.Proofs.ImpossibleFutures_Proofs

open Refinement

-- Contract pin: fails to compile if `impossibleFuturesRefines_iff_not_reachable_ifWitness`'s
-- signature drifts (Theorem 2).
example [Cslib.HasTau Label]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1)
    (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsIFWitness lts1 lts2 U s :=
  impossibleFuturesRefines_iff_not_reachable_ifWitness lts1 s1 lts2 s2

-- Contract pin: `impossibleFuturesRefines_iff_not_foundWitness` (Algorithms 2 and 4).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1) (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 (IsIFWitness lts1 lts2) (NormInit lts1 s1, s2) :=
  impossibleFuturesRefines_iff_not_foundWitness lts1 s1 lts2 s2

-- Contract pin: `impossibleFuturesRefines_iff_not_foundStableWitness` (Section 4.2, Lemma 10).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1) (lts2 : Cslib.LTS State2 Label) (s2 : State2)
    (hconv : ∀ s, ¬ lts2.Divergent s) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 (IsStableIFWitness lts1 lts2) (NormInit lts1 s1, s2) :=
  impossibleFuturesRefines_iff_not_foundStableWitness lts1 s1 lts2 s2 hconv

-- Contract pin: `impossibleFuturesRefines_iff_of_tauCycle` (Lemma 11).
example [Cslib.HasTau Label]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1) (lts2 : Cslib.LTS State2 Label) {s2 s2' : State2}
    (h1 : WeakTr lts2 s2 [] s2') (h2 : WeakTr lts2 s2' [] s2) :
    (s1 ⊑if[lts1,lts2] s2) ↔ (s1 ⊑if[lts1,lts2] s2') :=
  impossibleFuturesRefines_iff_of_tauCycle lts1 s1 lts2 h1 h2
