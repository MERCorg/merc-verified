import Refinement.Semantics
import Refinement.Product
import Refinement.Algorithm
import Refinement.ImpossibleFutures
import Refinement.AlgorithmOpt
import Refinement.Proofs.AlgorithmOpt_Proofs

open Refinement

-- Contract pin: `weakTraceOpt_correct` (Proposition 3, Algorithm 5).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    (lts1 : Cslib.LTS State1 Label) (lts2 : Cslib.LTS State2 Label)
    (pos neg : Set (Set State2 × State1)) (hpos : PosSound lts1 lts2 pos)
    (hneg : NegSound lts1 lts2 neg) (t : State1) (impl : State2) :
    (∃ b pos' neg', WeakTraceOpt lts1 lts2 pos neg t impl b pos' neg') ∧
    ∀ b pos' neg', WeakTraceOpt lts1 lts2 pos neg t impl b pos' neg' →
      (b = true ↔ (impl ⊑tr[lts2,lts1] t)) ∧ PosSound lts1 lts2 pos' ∧ NegSound lts1 lts2 neg' :=
  weakTraceOpt_correct lts1 lts2 pos neg hpos hneg t impl

-- Contract pin: `optImpossibleFutures_correct` (Theorem 3, Algorithm 6).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1) (lts2 : Cslib.LTS State2 Label) (s2 : State2)
    (hconv : ∀ s, ¬ lts2.Divergent s) :
    (s1 ⊑if[lts1,lts2] s2) ↔ ¬ OptFoundFailure lts1 lts2 (NormInit lts1 s1, s2) :=
  optImpossibleFutures_correct lts1 s1 lts2 s2 hconv
