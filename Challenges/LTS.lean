import MercLib.LTS.BranchingBisimilarity

/-!
# Comparator challenge: labelled transition systems (human-vetted)

The headline theorems of `MercLib/LTS/`, stated with `sorry` against the human-vetted spec files
only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

open Cslib (LTS HasTau)

namespace MercLib.LTS

/-! ## Branching bisimilarity is an equivalence -/

/-- **Branching bisimilarity is reflexive.** In an LTS `lts` with a silent action (`HasTau`),
every state `s` satisfies `s ≈br[lts] s`. -/
theorem BranchingBisimilarity.refl [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈br[lts] s := sorry

/-- **Branching bisimilarity is symmetric.** In an LTS with a silent action, if `s ≈br[lts] s'`
then `s' ≈br[lts] s`. -/
theorem BranchingBisimilarity.symm [HasTau Label] {lts : LTS State Label}
    {s s' : State} (h : s ≈br[lts] s') : s' ≈br[lts] s := sorry

/-- **Branching bisimilarity is transitive.** In an LTS with a silent action, if
`s1 ≈br[lts] s2` and `s2 ≈br[lts] s3` then `s1 ≈br[lts] s3`. The proof goes through semi-branching
bisimilarity. -/
theorem BranchingBisimilarity.trans [HasTau Label] {lts : LTS State Label}
    {s1 s2 s3 : State} (h12 : s1 ≈br[lts] s2) (h23 : s2 ≈br[lts] s3) :
    s1 ≈br[lts] s3 := sorry

end MercLib.LTS
