import Refinement.Semantics
import Refinement.Product
import Refinement.Antichain
import Refinement.Algorithm
import Refinement.Proofs.Algorithm_Proofs

open Refinement

-- Contract pin: fails to compile if `foundWitness_iff_exists_witness`'s signature drifts
-- (Theorem 5.2/5.14, conditional on termination - see that file's module docstring).
example [Cslib.HasTau Label]
    {L1 : Cslib.LTS (Set State1) Label} (hmono : IsMonotoneNormalForm L1)
    {lts2 : Cslib.LTS State2 Label} {IsWitness : Set State1 → State2 → Prop}
    (hantitone : ∀ {U V : Set State1} {s t : State2}, ProductLE (U, s) (V, t) →
      IsWitness V t → IsWitness U s)
    {p0 : Set State1 × State2}
    (hterminates : ∃ c, AlgRun L1 lts2 (AlgState.initial p0) c ∧ c.Terminal) :
    FoundWitness L1 lts2 IsWitness p0 ↔
      ∃ q, (product L1 lts2).CanReach p0 q ∧ IsWitness q.1 q.2 :=
  foundWitness_iff_exists_witness hmono hantitone hterminates

-- Contract pin: fails to compile if `AlgRun.terminates`'s signature drifts (Theorem 5.6).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    {L1 : Cslib.LTS (Set State1) Label} {lts2 : Cslib.LTS State2 Label}
    {p0 : Set State1 × State2} {c : AlgState State1 State2}
    (h : AlgRun L1 lts2 (AlgState.initial p0) c) :
    ∃ c', AlgRun L1 lts2 c c' ∧ c'.Terminal :=
  AlgRun.terminates h

-- Contract pin: fails to compile if `foundWitness_iff_exists_witness_finite`'s signature drifts
-- (Theorem 5.2/5.14, unconditional).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    {L1 : Cslib.LTS (Set State1) Label} (hmono : IsMonotoneNormalForm L1)
    {lts2 : Cslib.LTS State2 Label} {IsWitness : Set State1 → State2 → Prop}
    (hantitone : ∀ {U V : Set State1} {s t : State2}, ProductLE (U, s) (V, t) →
      IsWitness V t → IsWitness U s)
    (p0 : Set State1 × State2) :
    FoundWitness L1 lts2 IsWitness p0 ↔
      ∃ q, (product L1 lts2).CanReach p0 q ∧ IsWitness q.1 q.2 :=
  foundWitness_iff_exists_witness_finite hmono hantitone p0

-- Contract pin: fails to compile if `traceRefines_iff_not_foundWitness`'s signature drifts
-- (Algorithm 4, correctness).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1) (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑tr[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 IsTRWitness (NormInit lts1 s1, s2) :=
  traceRefines_iff_not_foundWitness lts1 s1 lts2 s2

-- Contract pin: fails to compile if `stableFailuresRefines_iff_not_foundWitness`'s signature
-- drifts (Algorithm 5, correctness).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1) (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑sfr[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 (IsSFWitness lts1 lts2) (NormInit lts1 s1, s2) :=
  stableFailuresRefines_iff_not_foundWitness lts1 s1 lts2 s2

-- Contract pin: fails to compile if `failuresDivergencesRefines_iff_not_foundWitness`'s
-- signature drifts (Algorithm 6, correctness).
example [Cslib.HasTau Label] [Finite State1] [Finite State2]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1) (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑fdr[lts1,lts2] s2) ↔
      ¬ FoundWitness (FdrNormTr lts1) lts2 (IsFDWitness lts1 lts2) (NormInit lts1 s1, s2) :=
  failuresDivergencesRefines_iff_not_foundWitness lts1 s1 lts2 s2
