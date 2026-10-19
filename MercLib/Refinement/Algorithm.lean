module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import MercLib.Refinement.Semantics
public import MercLib.Refinement.Product
public import MercLib.Refinement.Antichain
public import Mathlib.Data.Set.Card

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.Refinement

/-!
# The corrected antichain-based refinement checking algorithm (Algorithm 2)

Algorithm 2 (`refines_new`) of [M. Laveaux, J. F. Groote, T. A. C. Willemse, *Correct and
Efficient Antichain Algorithms for Refinement Checking*][Laveaux2019], FORTE 2019, transcribed line
by line as `refinesNew` (the paper's line numbers are in the comments), including the early
`return false` on lines 8, 12 and 19.

`CheckDiv = false` decides stable failures refinement, `CheckDiv = true` failures-divergences
refinement (Theorem 2).

**Modeling choices**
* All set operations go through classical choice (`noncomputable`). The stack `working` is a
  `List` (push and pop at the head); `antichain` is an `Antichain` ordered by `ProductLE`, with
  membership `⊑` (`⋐`) and `insert` (`⊎`).
* The `for` loop (lines 13-22) visits the outgoing transitions of `impl` in an arbitrary but fixed
  order (`outgoing`); the paper leaves this order unspecified.
* The `while` loop has no termination proof in the definition; its correctness proof also shows
  that it terminates.
* The loop state lives in the universe of `State1` and `State2`, so the result is a
  `ULift Bool`.
-/

/-- The outgoing transitions `impl -a-> impl'` of `s`, in an arbitrary fixed order (line 13). -/
noncomputable def outgoing [Finite Label] [Finite State2] (lts2 : LTS State2 Label) (s : State2) :
    List (Label × State2) :=
  (Set.toFinite { p : Label × State2 | lts2.Tr s p.1 p.2 }).toFinset.toList

open scoped Classical in
/-- Algorithm 2: `refines_new(L1, L2, CheckDiv)` for the specification `lts1` started in `s1` and
    the implementation `lts2` started in `s2`. -/
noncomputable def refinesNew [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (checkDiv : Bool) : Bool := ULift.down <| Id.run do
  let mut working := [(NormInit lts1 s1, s2)]                                      --  2
  let mut antichain := insert (NormInit lts1 s1, s2) (Antichain.empty ProductLE)  --  3
  while h : working ≠ [] do                                                        --  4
    let (spec, impl) := working.head h                                             --  5
    working := working.tail
    if ¬ SetDivergent lts1 spec ∨ checkDiv = false then                            --  6
      if checkDiv = true ∧ lts2.Divergent impl then                                --  7
        return .up false                                                           --  8
      else                                                                         --  9
        if Stable lts2 impl then                                                   -- 10
          if ¬ refusalsOf lts2 impl ⊆ refusals lts1 spec then                      -- 11
            return .up false                                                       -- 12
        for (a, impl') in outgoing lts2 impl do                                    -- 13
          let spec' := if a = HasTau.τ then spec                                   -- 14-15
            else { s' | ∃ s ∈ spec, WeakTr lts1 s [a] s' }                         -- 16-17
          if spec' = ∅ then                                                        -- 18
            return .up false                                                       -- 19
          if ¬ (spec', impl') ⊑ antichain then                                     -- 20
            antichain := insert (spec', impl') antichain                           -- 21
            working := (spec', impl') :: working                                   -- 22
  return .up true                                                                  -- 23

end MercLib.Refinement
