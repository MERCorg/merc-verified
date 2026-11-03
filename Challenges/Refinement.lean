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

/-- **Trace refinement is the absence of a reachable TR-witness.** For two LTSs with a silent
action, a specification state `s1` and an implementation state `s2`, `s1 ⊑tr s2` holds iff no
pair `(U, s)` with `U = ∅` (`IsTRWitness`: a weak trace of the implementation the specification
cannot follow) is reachable from `(NormInit lts1 s1, s2)` in the product of the specification's
normal form `NormTr lts1` with the implementation `lts2`. -/
theorem traceRefines_iff_not_reachable_trWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑tr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsTRWitness U s := sorry

/-- **Stable failures refinement is the absence of a reachable SF-witness.** For two LTSs with a
silent action, `s1 ⊑sfr s2` holds iff no SF-witness `(U, s)` is reachable from
`(NormInit lts1 s1, s2)` in the product of the specification's normal form `NormTr lts1` with the
implementation `lts2` (`IsSFWitness`: a TR-witness, or `s` stable and refusing something that the
specification states in `U` cannot all refuse). -/
theorem stableFailuresRefines_iff_not_reachable_sfWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑sfr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsSFWitness lts1 lts2 U s := sorry

/-- **Failures-divergences refinement is the absence of a reachable FD-witness.** For two LTSs
with a silent action, `s1 ⊑fdr s2` holds iff no FD-witness `(U, s)` is reachable from
`(NormInit lts1 s1, s2)` in the product of the divergence-pruned normal form `FdrNormTr lts1` with
`lts2` (`IsFDWitness`: `U` not divergent, and `U = ∅`, a stable failure not allowed by `U`, or `s`
divergent). -/
theorem failuresDivergencesRefines_iff_not_reachable_fdWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑fdr[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (FdrNormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsFDWitness lts1 lts2 U s := sorry

/-! ## Algorithm 2 (Theorem 2 of [Laveaux2019]) -/

/-- **`refines_new` decides stable failures and failures-divergences refinement (Theorem 2).**
For two finite LTSs with a silent action over a finite alphabet,
`refinesNew lts1 s1 lts2 s2 false = true` iff `s1 ⊑sfr s2`, and
`refinesNew lts1 s1 lts2 s2 true = true` iff `s1 ⊑fdr s2`. -/
theorem refinesNewCorrect {State1 State2 Label : Type*} [HasTau Label] [Finite Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (refinesNew lts1 s1 lts2 s2 false = true ↔ s1 ⊑sfr[lts1, lts2] s2) ∧
      (refinesNew lts1 s1 lts2 s2 true = true ↔ s1 ⊑fdr[lts1, lts2] s2) := sorry

/-! ## Impossible futures (Theorem 2 and Lemma 11 of [Laveaux2026]) -/

/-- **Impossible futures refinement is the absence of a reachable IF-witness.** For two LTSs with
a silent action, `s1 ⊑if s2` holds iff no IF-witness `(U, s)` is reachable from
`(NormInit lts1 s1, s2)` in the product of the specification's normal form `NormTr lts1` with the
implementation `lts2` (`IsIFWitness`: `U` empty, or no state of `U` has all its weak traces among
those of `s`). -/
theorem impossibleFuturesRefines_iff_not_reachable_ifWitness [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑if[lts1,lts2] s2) ↔
      ¬ ∃ U s, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) (U, s) ∧
        IsIFWitness lts1 lts2 U s := sorry

/-- **Impossible futures refinement is invariant on τ-cycles of the implementation.** If the
implementation states `s2` and `s2'` reach each other by silent steps only, then `s1 ⊑if s2` iff
`s1 ⊑if s2'`, for every specification state `s1`. -/
theorem impossibleFuturesRefines_iff_of_tauCycle [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) {s2 s2' : State2}
    (h1 : WeakTr lts2 s2 [] s2') (h2 : WeakTr lts2 s2' [] s2) :
    (s1 ⊑if[lts1,lts2] s2) ↔ (s1 ⊑if[lts1,lts2] s2') := sorry

/-! ## Algorithms 5 and 6 (Proposition 3 and Theorem 3 of [Laveaux2026]) -/

/-- **The antichain weak-trace check is correct (Proposition 3).** Let `lts1` and `lts2` be finite
LTSs over a finite alphabet, and `pos`, `neg` sound antichains (`PosSound`: no TR-witness is
reachable from a pair in `pos`; `NegSound`: one is reachable from every pair in `neg`). Then for
all states `t` and `impl`, `weakTraceOpt` returns `true` iff `impl ⊑tr t` (all weak traces of `t`
are weak traces of `impl`). The returned antichain is a sound positive one on `true` and a sound
negative one on `false`, so it can be reused for later checks. -/
theorem weakTraceOptCorrect {State1 State2 Label : Type*} [HasTau Label] [Finite Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Antichain (Set State2 × State1)) (hpos : PosSound lts1 lts2 pos)
    (hneg : NegSound lts1 lts2 neg) (t : State1) (impl : State2) :
    ((weakTraceOpt lts1 lts2 t impl pos neg).1 = true ↔ impl ⊑tr[lts2,lts1] t) ∧
      (if (weakTraceOpt lts1 lts2 t impl pos neg).1 then
        PosSound lts1 lts2 (weakTraceOpt lts1 lts2 t impl pos neg).2
      else NegSound lts1 lts2 (weakTraceOpt lts1 lts2 t impl pos neg).2) := sorry

/-- **The optimised impossible futures check is correct (Theorem 3).** For two finite LTSs over a
finite alphabet with a convergent implementation `lts2` (no infinite silent path),
`weakImpossibleFuturesOpt lts1 s1 lts2 s2 = true` iff `s1 ⊑if s2`. -/
theorem weakImpossibleFuturesOptCorrect {State1 State2 Label : Type*} [HasTau Label]
    [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hconv : Convergent lts2) :
    weakImpossibleFuturesOpt lts1 s1 lts2 s2 = true ↔ s1 ⊑if[lts1,lts2] s2 := sorry

end MercLib.Refinement
