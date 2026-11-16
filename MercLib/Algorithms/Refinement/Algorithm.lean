module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import MercLib.Theory.Refinement.Semantics
public import MercLib.Theory.Refinement.Product
public import MercLib.Algorithms.Refinement.Antichain
public import Mathlib.Data.Set.Card

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.Refinement

/-!
# The corrected antichain-based refinement checking algorithms (Algorithms 5 and 6)

Algorithms 5 (`refines-stable-failures_new`) and 6 (`refines-failures-divergences_new`) of
[M. Laveaux, J. F. Groote, T. A. C. Willemse, *Correct and Efficient Antichain Algorithms for
Refinement Checking*][Laveaux2021], LMCS 2021, as one function `refinesNew` with a flag
`CheckDiv`: `CheckDiv = false` is Algorithm 5 and decides stable failures refinement,
`CheckDiv = true` is Algorithm 6 and decides failures-divergences refinement (Theorem 5.2).
It is transcribed line by line from Algorithm 6 (its line numbers are in the comments), including
the early `return false` on lines 9, 12 and 19; with `CheckDiv = false` the divergence tests of
lines 7-8 are skipped, which leaves exactly Algorithm 5.

**Modeling choices**
* All set operations go through classical choice (`noncomputable`). The stack `working` is a
  `List` (push and pop at the head); `antichain` is an `Antichain` ordered by `ProductLE`, with
  membership `⊑` (`⋐`) and `insert` (`⊎`).
* The `for` loop (lines 13-22) visits the outgoing transitions of `impl` in an arbitrary but fixed
  order (`outgoing`); the paper leaves this order unspecified.
* The ghost variable `done` of Algorithm 6 (lines 4 and 23), used only in the paper's proof, is
  left out.
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
/-- Algorithm 5 (`checkDiv = false`) and Algorithm 6 (`checkDiv = true`) for the specification
    `lts1` started in `s1` and the implementation `lts2` started in `s2`. -/
noncomputable def refinesNew [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (checkDiv : Bool) : Bool := ULift.down <| Id.run do
  let mut working := [(NormInit lts1 s1, s2)]                                      --  2
  let mut antichain := insert (NormInit lts1 s1, s2) (Antichain.empty ProductLE)  --  3
  while h : working ≠ [] do                                                        --  5
    let (spec, impl) := working.head h                                             --  6
    working := working.tail
    if ¬ SetDivergent lts1 spec ∨ checkDiv = false then                            --  7
      if checkDiv = true ∧ lts2.Divergent impl then                                --  8
        return .up false                                                           --  9
      else                                                                         -- 10
        if Stable lts2 impl then                                                   -- 11
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
  return .up true                                                                  -- 24

end MercLib.Refinement
