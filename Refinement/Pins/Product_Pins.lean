import Refinement.Semantics
import Refinement.Product
import Refinement.Proofs.Product_Proofs

open Refinement

-- Contract pin: fails to compile if `traceRefines_iff_not_reachable_trWitness`'s signature
-- drifts (Theorem 3.11).
example [Cslib.HasTau Label]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1)
    (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑tr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsTRWitness U s :=
  traceRefines_iff_not_reachable_trWitness lts1 s1 lts2 s2

-- Contract pin: fails to compile if `stableFailuresRefines_iff_not_reachable_sfWitness`'s
-- signature drifts (Theorem 3.14).
example [Cslib.HasTau Label]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1)
    (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑sfr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsSFWitness lts1 lts2 U s :=
  stableFailuresRefines_iff_not_reachable_sfWitness lts1 s1 lts2 s2

-- Contract pin: fails to compile if `failuresDivergencesRefines_iff_not_reachable_fdWitness`'s
-- signature drifts (Theorem 3.24).
example [Cslib.HasTau Label]
    (lts1 : Cslib.LTS State1 Label) (s1 : State1)
    (lts2 : Cslib.LTS State2 Label) (s2 : State2) :
    (s1 ⊑fdr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (FdrNormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsFDWitness lts1 lts2 U s :=
  failuresDivergencesRefines_iff_not_reachable_fdWitness lts1 s1 lts2 s2
