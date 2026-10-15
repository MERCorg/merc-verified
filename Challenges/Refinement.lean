import MercLib.Refinement.Semantics
import MercLib.Refinement.Product
import MercLib.Refinement.Antichain
import MercLib.Refinement.Algorithm
import MercLib.Refinement.ImpossibleFutures
import MercLib.Refinement.AlgorithmImpossibleFutures

/-!
# Comparator challenge: refinement checking (human-vetted)

The headline theorems of `MercLib/Refinement/`, stated with `sorry` against the human-vetted spec
files only. `lake comparator` (configured by `comparator.json`) checks that
the solution module (`MercLib`) proves each of them with the same statement, using only the
axioms listed there, and replays the proofs through the kernel.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

open Cslib (LTS HasTau)

namespace MercLib.Refinement

/-! ## Witnesses (Theorems 3.11, 3.14, 3.24 of [Laveaux2021]) -/

theorem traceRefines_iff_not_reachable_trWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑tr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsTRWitness U s := sorry

theorem stableFailuresRefines_iff_not_reachable_sfWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑sfr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsSFWitness lts1 lts2 U s := sorry

theorem failuresDivergencesRefines_iff_not_reachable_fdWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑fdr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (FdrNormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsFDWitness lts1 lts2 U s := sorry

/-! ## Algorithm 2 (Theorem 2 of [Laveaux2019]) -/

/-- Theorem 2: `refines_new` decides stable failures refinement when `CheckDiv` is `false` and
    failures-divergences refinement when it is `true`. -/
theorem refinesNewCorrect {State1 State2 Label : Type*} [HasTau Label] [Finite Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (refinesNew lts1 s1 lts2 s2 false = true ↔ s1 ⊑sfr[lts1, lts2] s2) ∧
      (refinesNew lts1 s1 lts2 s2 true = true ↔ s1 ⊑fdr[lts1, lts2] s2) := sorry

/-! ## Impossible futures (Theorem 2 and Lemma 11 of [Laveaux2026]) -/

theorem impossibleFuturesRefines_iff_not_reachable_ifWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsIFWitness lts1 lts2 U s := sorry

theorem impossibleFuturesRefines_iff_of_tauCycle [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) {s2 s2' : State2}
    (h1 : WeakTr lts2 s2 [] s2') (h2 : WeakTr lts2 s2' [] s2) :
    (s1 ⊑if[lts1,lts2] s2) ↔ (s1 ⊑if[lts1,lts2] s2') := sorry

/-! ## Algorithms 5 and 6 (Proposition 3 and Theorem 3 of [Laveaux2026]) -/

/-- Proposition 3: from sound antichains, Algorithm 5 returns `true` iff `t ⊑wt impl`
    (`weaktraces lts1 t ⊆ weaktraces lts2 impl`), and the returned antichain (the extended
    `antichain⁺` on `true`, the extended `antichain⁻` on `false`) is again sound. -/
theorem weakTraceOptCorrect {State1 State2 Label : Type*} [HasTau Label] [Finite Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Antichain (Set State2 × State1)) (hpos : PosSound lts1 lts2 pos)
    (hneg : NegSound lts1 lts2 neg) (t : State1) (impl : State2) :
    ((weakTraceOpt lts1 lts2 t impl pos neg).1 = true ↔ impl ⊑tr[lts2,lts1] t) ∧
      (if (weakTraceOpt lts1 lts2 t impl pos neg).1 then
        PosSound lts1 lts2 (weakTraceOpt lts1 lts2 t impl pos neg).2
      else NegSound lts1 lts2 (weakTraceOpt lts1 lts2 t impl pos neg).2) := sorry

/-- Theorem 3: for finite LTSs with a convergent implementation, Algorithm 6 returns `true` iff
    weak impossible futures refinement holds. -/
theorem weakImpossibleFuturesOptCorrect {State1 State2 Label : Type*} [HasTau Label]
    [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hconv : Convergent lts2) :
    weakImpossibleFuturesOpt lts1 s1 lts2 s2 = true ↔ s1 ⊑if[lts1,lts2] s2 := sorry

end MercLib.Refinement
