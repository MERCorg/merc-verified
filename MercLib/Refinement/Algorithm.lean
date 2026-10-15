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
by line, including the early `return false` on lines 8, 12 and 19:

```
 1: procedure refines_new(L1, L2, CheckDiv)
 2:   let working be a stack containing a pair ({s | ι1 =ε=> s}, ι2)
 3:   let antichain := ∅ ⊎ ({s | ι1 =ε=> s}, ι2)
 4:   while working ≠ ∅ do
 5:     pop (spec, impl) from working
 6:     if not div(spec) or not CheckDiv then
 7:       if CheckDiv and div(impl) then
 8:         return false
 9:       else
10:         if stable(impl) then
11:           if refusals(impl) ⊈ refusals(spec) then
12:             return false
13:         for impl -a-> impl' do
14:           if a = τ then
15:             spec' := spec
16:           else
17:             spec' := {s' | ∃ s ∈ spec : s =a=> s'}
18:           if spec' = ∅ then
19:             return false
20:           if (spec', impl') ⋐ antichain is not true then
21:             antichain := antichain ⊎ (spec', impl')
22:             push (spec', impl') into working
23:   return true
```

`CheckDiv = false` decides stable failures refinement, `CheckDiv = true` failures-divergences
refinement (Theorem 2).

**Modeling choices**
* All set operations go through classical choice (`noncomputable`). The stack `working` is a
  `List` (push and pop at the head); `antichain` is an `Antichain` ordered by `ProductLE`, with
  membership `⊑` (`⋐`) and `insert` (`⊎`).
* The inner `for` loop (lines 13-22) is `forSuccessors`. It returns `none` when line 19 fires and
  the updated `(working, antichain)` otherwise. It visits the outgoing transitions of `impl` in an
  arbitrary but fixed order (`outgoing`); the paper leaves this order unspecified.
* The `while` loop is `refinesLoop`. It carries the paper's ghost variable `done` (Lemma 2) as an
  argument, and terminates on the size of the complement of `done`. Each popped pair is checked
  against the guard `(spec, impl) ∉ done`; Lemma 2 (`done ∩ working = ∅`) says the guard always
  holds, which is part of the correctness proof. The `else` branch, which skips the pair, only
  exists to make the definition total.
-/

/-- The outgoing transitions `impl -a-> impl'` of `s`, in an arbitrary fixed order (line 13). -/
noncomputable def outgoing [Finite Label] [Finite State2] (lts2 : LTS State2 Label) (s : State2) :
    List (Label × State2) :=
  (Set.toFinite { p : Label × State2 | lts2.Tr s p.1 p.2 }).toFinset.toList

open scoped Classical in
/-- Lines 13-22: the inner `for` loop over the outgoing transitions of `impl`, extending
    `working` and `antichain`. Returns `none` if line 19 (`return false`) fires. -/
noncomputable def forSuccessors [HasTau Label] (lts1 : LTS State1 Label) (spec : Set State1) :
    List (Label × State2) → List (Set State1 × State2) → Antichain (Set State1 × State2) →
      Option (List (Set State1 × State2) × Antichain (Set State1 × State2))
  | [], working, antichain => some (working, antichain)
  | (a, impl') :: rest, working, antichain =>
    let spec' := if a = HasTau.τ then spec else { s' | ∃ s ∈ spec, WeakTr lts1 s [a] s' }
    if spec' = ∅ then none
    else if ¬ (spec', impl') ⊑ antichain then
      forSuccessors lts1 spec rest ((spec', impl') :: working)
        (insert (spec', impl') antichain)
    else forSuccessors lts1 spec rest working antichain

open scoped Classical in
/-- Lines 4-23: the `while` loop, with the ghost variable `done` of Lemma 2. -/
noncomputable def refinesLoop [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (checkDiv : Bool)
    (done : Set (Set State1 × State2)) (working : List (Set State1 × State2))
    (antichain : Antichain (Set State1 × State2)) : Bool :=
  match working with
  | [] => true
  | (spec, impl) :: working =>
    if _hdone : (spec, impl) ∉ done then
      if ¬ SetDivergent lts1 spec ∨ checkDiv = false then
        if checkDiv = true ∧ lts2.Divergent impl then false
        else if Stable lts2 impl ∧ ¬ refusalsOf lts2 impl ⊆ refusals lts1 spec then false
        else
          match forSuccessors lts1 spec (outgoing lts2 impl) working antichain with
          | none => false
          | some (working', antichain') =>
            refinesLoop lts1 lts2 checkDiv (insert (spec, impl) done) working' antichain'
      else refinesLoop lts1 lts2 checkDiv (insert (spec, impl) done) working antichain
    else refinesLoop lts1 lts2 checkDiv done working antichain
termination_by ((Set.univ \ done).ncard, working.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp)
    | (apply Prod.Lex.left
       refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
       refine ⟨Set.sdiff_subset_sdiff_right (Set.subset_insert _ _), fun hsub => ?_⟩
       exact (hsub ⟨Set.mem_univ _, _hdone⟩).2 (Set.mem_insert _ _))

/-- Algorithm 2: `refines_new(L1, L2, CheckDiv)` for the specification `lts1` started in `s1` and
    the implementation `lts2` started in `s2`. -/
noncomputable def refinesNew [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (checkDiv : Bool) : Bool :=
  refinesLoop lts1 lts2 checkDiv ∅ [(NormInit lts1 s1, s2)] 
    (insert (NormInit lts1 s1, s2) (Antichain.empty ProductLE))

end MercLib.Refinement
