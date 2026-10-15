module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import MercLib.Refinement.Semantics
public import MercLib.Refinement.Product
public import MercLib.Refinement.Antichain
public import MercLib.Refinement.Algorithm
public import MercLib.Refinement.ImpossibleFutures
public import Mathlib.Data.Set.Card

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.Refinement

/-!
# The optimised impossible futures algorithms (Algorithms 5 and 6)

Section 4.2 of [M. Laveaux and T. A. C. Willemse, *Deciding Impossible Futures*][Laveaux2026],
LNCS 16365, 2026, transcribed line by line, including the early `return`s.

**Orientation.** As in `ImpossibleFutures.lean`, `lts1` is the specification (the paper's `L2`)
and `lts2` the implementation (the paper's `L1`); pairs are written `(spec, impl)`. Algorithm 5 is
called as `Weak-Trace_{ac-opt}(t, impl, …)` with `t` a specification state, i.e. it checks
`t ⊑wt impl`; so inside it `t`'s side (`lts1`) is explored and `impl`'s side (`lts2`) is
normalised, and its pairs live in `Set State2 × State1`.

**Algorithm 5**, `weakTraceOpt t impl pos neg`:
```
 1: procedure Weak-Trace_{ac-opt}(s1, s2, antichain⁺, antichain⁻)
 2:   if (s1, {s ∈ S2 | s2 =ε=> s}) ⋐ antichain⁺ then
 3:     return (true, antichain⁺)
 4:   else if (s1, {s ∈ S2 | s2 =ε=> s}) ⋐≥ antichain⁻ then
 5:     return (false, antichain⁻)
 6:   let working be a stack containing the pair (s1, {s ∈ S2 | s2 =ε=> s})
 7:   let antichain := ∅ ⊎ (s1, {s ∈ S2 | s2 =ε=> s})
 8:   while working ≠ ∅ do
 9:     pop (impl, spec) from working
10:     for impl -a->1 impl' do
11:       if a = τ then
12:         spec' := spec
13:       else
14:         spec' := {s' ∈ S2 | ∃ s ∈ spec : s =a=>2 s'}
15:       if (impl', spec') ⋐≥ antichain⁻ ∨ spec' = ∅ then
16:         return (false, antichain⁻ ⊎≥ (s1, {s ∈ S2 | s2 =ε=> s}))
17:       if (impl', spec') ∉ antichain ∧ (impl', spec') ∉ antichain⁺ then
18:         antichain := antichain ⊎ (impl', spec')
19:         push (impl', spec') into working
20:   return (true, antichain⁺ ∪ antichain)
```
(The paper's line 15 reads `(impl, spec')`; we test the successor `(impl', spec')`, as the
surrounding text and line 17 intend.)

**Algorithm 6**, `weakImpossibleFuturesOpt s1 lts1 s2 lts2`:
```
 1: procedure Weak-Impossible-Futures_{ac-opt}(s1, s2)
 2:   let working be a stack containing the pair (s1, {s ∈ S2 | s2 =ε=> s})
 3:   let antichain := ∅ ⊎ (s1, {s ∈ S2 | s2 =ε=> s})
 4:   let (antichain⁻, antichain⁺) := (∅, ∅)
 5:   while working ≠ ∅ do
 6:     pop (impl, spec) from working
 7:     (b, spec') := (true, spec)
 8:     while impl ↛τ1 ∧ spec' ≠ ∅ ∧ b do
 9:       pop t from spec'
10:       (b', antichain') := Weak-Trace_{ac-opt}(t, impl, antichain⁺, antichain⁻)
11:       if b' then
12:         (b, antichain⁺) := (false, antichain')
13:       else
14:         antichain⁻ := antichain'
15:     if b = true ∧ impl ↛τ1 then
16:       return false
17:     for impl -a->1 impl' do
18:       if a = τ then
19:         spec' := spec
20:       else
21:         spec' := {s' ∈ S2 | ∃ s ∈ spec : s =a=>2 s'}
22:       if spec' = ∅ then
23:         return false
24:       if (impl', spec') ∉ antichain then
25:         antichain := antichain ⊎ (impl', spec')
26:         push (impl', spec') into working
27:   return true
```
Lines 17-26 are exactly lines 13-22 of Algorithm 2, so they reuse `forSuccessors`.

**Modeling choices**
* As in `Algorithm.lean`: classical choice throughout (`noncomputable`), stacks are `List`s, `for`
  loops over the outgoing transitions use the fixed order of `outgoing`, and each `while` loop
  carries the ghost variable `done`, terminating on the size of its complement. The guard
  `(spec, impl) ∉ done` always holds and the `else` branch only exists to make the definition
  total.
* The positive antichain is ordered by `ProductLE`; the negative antichain by its converse, so
  that `x ⊑ antichain⁻` is the paper's `⋐≥` and `insert` is its `⊎≥`.
* `antichain⁺ ∪ antichain` (line 20) is the union of the stored sets, keeping `antichain⁺`'s order.
* Line 9 pops the states of `spec'` in an arbitrary fixed order (`toList`).
-/

/-- The states of a finite set, in an arbitrary fixed order (line 9 of Algorithm 6). -/
noncomputable def toList [Finite State] (U : Set State) : List State :=
  (Set.toFinite U).toFinset.toList

/-! ## Algorithm 5 -/

open scoped Classical in
/-- Lines 10-19 of Algorithm 5: the `for` loop over the outgoing transitions of `impl` (a state
    of `lts1`), extending `working` and `antichain`. Returns `none` if line 16 fires. -/
noncomputable def forSuccessorsOpt [HasTau Label] (lts2 : LTS State2 Label)
    (pos neg : Antichain (Set State2 × State1)) (spec : Set State2) :
    List (Label × State1) → List (Set State2 × State1) → Antichain (Set State2 × State1) →
      Option (List (Set State2 × State1) × Antichain (Set State2 × State1))
  | [], working, antichain => some (working, antichain)
  | (a, impl') :: rest, working, antichain =>
    let spec' := if a = HasTau.τ then spec else { s' | ∃ s ∈ spec, WeakTr lts2 s [a] s' }
    if (spec', impl') ⊑ neg ∨ spec' = ∅ then none
    else if ¬ (spec', impl') ⊑ antichain ∧ ¬ (spec', impl') ⊑ pos then
      forSuccessorsOpt lts2 pos neg spec rest ((spec', impl') :: working)
        (insert (spec', impl') antichain)
    else forSuccessorsOpt lts2 pos neg spec rest working antichain

open scoped Classical in
/-- Lines 8-20 of Algorithm 5: the `while` loop, with the ghost variable `done`. `init` is the
    initial pair, recorded in `antichain⁻` on a `false` verdict. -/
noncomputable def weakTraceLoop [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (init : Set State2 × State1)
    (pos neg : Antichain (Set State2 × State1)) (done : Set (Set State2 × State1))
    (working : List (Set State2 × State1)) (antichain : Antichain (Set State2 × State1)) :
    Bool × Antichain (Set State2 × State1) :=
  match working with
  | [] => (true, ⟨pos.le, pos.set ∪ antichain.set⟩)
  | (spec, impl) :: working =>
    if _hdone : (spec, impl) ∉ done then
      match forSuccessorsOpt lts2 pos neg spec (outgoing lts1 impl) working antichain with
      | none => (false, insert init neg)
      | some (working', antichain') =>
        weakTraceLoop lts1 lts2 init pos neg (insert (spec, impl) done) working' antichain'
    else weakTraceLoop lts1 lts2 init pos neg done working antichain
termination_by ((Set.univ \ done).ncard, working.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp)
    | (apply Prod.Lex.left
       refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
       refine ⟨Set.sdiff_subset_sdiff_right (Set.subset_insert _ _), fun hsub => ?_⟩
       exact (hsub ⟨Set.mem_univ _, _hdone⟩).2 (Set.mem_insert _ _))

open scoped Classical in
/-- Algorithm 5: `Weak-Trace_{ac-opt}(t, impl, antichain⁺, antichain⁻)`, checking `t ⊑wt impl`
    for a specification state `t` and an implementation state `impl`. Returns the verdict and the
    extended `antichain⁺` (on `true`) or `antichain⁻` (on `false`). -/
noncomputable def weakTraceOpt [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (t : State1) (impl : State2)
    (pos neg : Antichain (Set State2 × State1)) : Bool × Antichain (Set State2 × State1) :=
  if (NormInit lts2 impl, t) ⊑ pos then (true, pos)
  else if (NormInit lts2 impl, t) ⊑ neg then (false, neg)
  else
    weakTraceLoop lts1 lts2 (NormInit lts2 impl, t) pos neg ∅ [(NormInit lts2 impl, t)]
      (insert (NormInit lts2 impl, t) (Antichain.empty ProductLE))

/-! ## Algorithm 6 -/

open scoped Classical in
/-- Lines 8-14 of Algorithm 6: the inner `while` loop, popping the states `t` of `spec'` and
    calling Algorithm 5 against `impl`. Returns the final `(b, antichain⁺, antichain⁻)`. -/
noncomputable def checkLoop [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (impl : State2) :
    List State1 → Bool → Antichain (Set State2 × State1) → Antichain (Set State2 × State1) →
      Bool × Antichain (Set State2 × State1) × Antichain (Set State2 × State1)
  | [], b, pos, neg => (b, pos, neg)
  | t :: spec', b, pos, neg =>
    if Stable lts2 impl ∧ b = true then
      match weakTraceOpt lts1 lts2 t impl pos neg with
      | (true, antichain') => checkLoop lts1 lts2 impl spec' false antichain' neg
      | (false, antichain') => checkLoop lts1 lts2 impl spec' b pos antichain'
    else (b, pos, neg)

open scoped Classical in
/-- Lines 5-27 of Algorithm 6: the outer `while` loop, with the ghost variable `done`. -/
noncomputable def impossibleFuturesLoop [HasTau Label] [Finite Label] [Finite State1]
    [Finite State2] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (done : Set (Set State1 × State2)) (working : List (Set State1 × State2))
    (antichain : Antichain (Set State1 × State2)) (pos neg : Antichain (Set State2 × State1)) :
    Bool :=
  match working with
  | [] => true
  | (spec, impl) :: working =>
    if _hdone : (spec, impl) ∉ done then
      match checkLoop lts1 lts2 impl (toList spec) true pos neg with
      | (b, pos', neg') =>
        if b = true ∧ Stable lts2 impl then false
        else
          match forSuccessors lts1 spec (outgoing lts2 impl) working antichain with
          | none => false
          | some (working', antichain') =>
            impossibleFuturesLoop lts1 lts2 (insert (spec, impl) done) working' antichain'
              pos' neg'
    else impossibleFuturesLoop lts1 lts2 done working antichain pos neg
termination_by ((Set.univ \ done).ncard, working.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp)
    | (apply Prod.Lex.left
       refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
       refine ⟨Set.sdiff_subset_sdiff_right (Set.subset_insert _ _), fun hsub => ?_⟩
       exact (hsub ⟨Set.mem_univ _, _hdone⟩).2 (Set.mem_insert _ _))

/-- Algorithm 6: `Weak-Impossible-Futures_{ac-opt}` for the specification `lts1` started in `s1`
    and the implementation `lts2` started in `s2`. -/
noncomputable def weakImpossibleFuturesOpt [HasTau Label] [Finite Label] [Finite State1]
    [Finite State2] (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label)
    (s2 : State2) : Bool :=
  impossibleFuturesLoop lts1 lts2 ∅ [(NormInit lts1 s1, s2)]
    (insert (NormInit lts1 s1, s2) (Antichain.empty ProductLE))
    (Antichain.empty ProductLE) (Antichain.empty fun y x => ProductLE x y)

/-! ## Antichain soundness (hypotheses of Proposition 3) -/

/-- A positive antichain is sound (Proposition 3, second hypothesis): it is ordered by
    `ProductLE`, and no TR-witness is reachable in the inner product `NormTr lts2 ⋉ lts1` from any
    pair it contains. -/
def PosSound [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos : Antichain (Set State2 × State1)) : Prop :=
  pos.le = ProductLE ∧ ∀ x, x ⊑ pos →
    ¬ ∃ q, (product (NormTr lts2) lts1).CanReach x q ∧ IsTRWitness q.1 q.2

/-- A negative antichain is sound (Proposition 3, first hypothesis): it is ordered by the converse
    of `ProductLE`, and a TR-witness is reachable from every pair it contains. -/
def NegSound [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (neg : Antichain (Set State2 × State1)) : Prop :=
  neg.le = (fun y x => ProductLE x y) ∧ ∀ x, x ⊑ neg →
    ∃ q, (product (NormTr lts2) lts1).CanReach x q ∧ IsTRWitness q.1 q.2

end MercLib.Refinement
