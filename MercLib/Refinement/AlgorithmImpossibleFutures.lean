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
LNCS 16365, 2026, transcribed line by line as `weakTraceOpt` (Algorithm 5) and
`weakImpossibleFuturesOpt` (Algorithm 6), with the paper's line numbers in the comments, including
the early `return`s.

**Orientation.** As in `ImpossibleFutures.lean`, `lts1` is the specification (the paper's `L2`)
and `lts2` the implementation (the paper's `L1`); pairs are written `(spec, impl)`. Algorithm 5 is
called as `Weak-Trace_{ac-opt}(t, impl, …)` with `t` a specification state, i.e. it checks
`t ⊑wt impl`; so inside it `t`'s side (`lts1`) is explored and `impl`'s side (`lts2`) is
normalised, and its pairs live in `Set State2 × State1`.

The paper's line 15 of Algorithm 5 reads `(impl, spec')`; we test the successor `(impl', spec')`,
as the surrounding text and line 17 intend.

**Modeling choices**
* As in `Algorithm.lean`: classical choice throughout (`noncomputable`), stacks are `List`s, `for`
  loops over the outgoing transitions use the fixed order of `outgoing`, the `while` loops have no
  termination proof in the definition, and the loop state of Algorithm 6 forces its result to be a
  `ULift Bool`.
* The positive antichain is ordered by `ProductLE`; the negative antichain by its converse, so
  that `x ⊑ antichain⁻` is the paper's `⋐≥` and `insert` is its `⊎≥`.
* `antichain⁺ ∪ antichain` (line 20 of Algorithm 5) is the union of the stored sets, keeping
  `antichain⁺`'s order.
* Lines 8-9 of Algorithm 6 pop the states of `spec'` in an arbitrary fixed order (`toList`).
-/

/-- The states of a finite set, in an arbitrary fixed order (line 9 of Algorithm 6). -/
noncomputable def toList [Finite State] (U : Set State) : List State :=
  (Set.toFinite U).toFinset.toList

open scoped Classical in
/-- Algorithm 5: `Weak-Trace_{ac-opt}(t, impl, antichain⁺, antichain⁻)`, checking `t ⊑wt impl`
    for a specification state `t` and an implementation state `impl`. Returns the verdict and the
    extended `antichain⁺` (on `true`) or `antichain⁻` (on `false`). -/
noncomputable def weakTraceOpt [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (t : State1) (impl : State2)
    (pos neg : Antichain (Set State2 × State1)) : Bool × Antichain (Set State2 × State1) :=
  Id.run do
  let init := (NormInit lts2 impl, t)
  if init ⊑ pos then                                                         --  2
    return (true, pos)                                                       --  3
  else if init ⊑ neg then                                                    --  4
    return (false, neg)                                                      --  5
  let mut working := [init]                                                  --  6
  let mut antichain := insert init (Antichain.empty ProductLE)               --  7
  while h : working ≠ [] do                                                  --  8
    let (spec, impl) := working.head h                                       --  9
    working := working.tail
    for (a, impl') in outgoing lts1 impl do                                  -- 10
      let spec' := if a = HasTau.τ then spec                                 -- 11-12
        else { s' | ∃ s ∈ spec, WeakTr lts2 s [a] s' }                       -- 13-14
      if (spec', impl') ⊑ neg ∨ spec' = ∅ then                               -- 15
        return (false, insert init neg)                                      -- 16
      if ¬ (spec', impl') ⊑ antichain ∧ ¬ (spec', impl') ⊑ pos then          -- 17
        antichain := insert (spec', impl') antichain                         -- 18
        working := (spec', impl') :: working                                 -- 19
  return (true, ⟨pos.le, pos.set ∪ antichain.set⟩)                           -- 20

open scoped Classical in
/-- Algorithm 6: `Weak-Impossible-Futures_{ac-opt}` for the specification `lts1` started in `s1`
    and the implementation `lts2` started in `s2`. -/
noncomputable def weakImpossibleFuturesOpt {State1 : Type u} {State2 : Type v} [HasTau Label]
    [Finite Label] [Finite State1] [Finite State2] (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label)
    (s2 : State2) : Bool := ULift.down <| Id.run do
  let mut working := [(NormInit lts1 s1, s2)]                                      --  2
  let mut antichain := insert (NormInit lts1 s1, s2) (Antichain.empty ProductLE)  --  3
  let mut neg : Antichain (Set State2 × State1) := Antichain.empty fun y x => ProductLE x y  -- 4
  let mut pos : Antichain (Set State2 × State1) := Antichain.empty ProductLE
  while h : working ≠ [] do                                                        --  5
    let (spec, impl) := working.head h                                             --  6
    working := working.tail
    let mut b := true                                                              --  7
    for t in toList spec do                                                        --  8-9
      if ¬ (Stable lts2 impl ∧ b = true) then break
      let (b', antichain') := weakTraceOpt lts1 lts2 t impl pos neg                -- 10
      if b' then                                                                   -- 11
        b := false                                                                 -- 12
        pos := antichain'
      else                                                                         -- 13
        neg := antichain'                                                          -- 14
    if b = true ∧ Stable lts2 impl then                                            -- 15
      return .up false                                                             -- 16
    for (a, impl') in outgoing lts2 impl do                                        -- 17
      let spec' := if a = HasTau.τ then spec                                       -- 18-19
        else { s' | ∃ s ∈ spec, WeakTr lts1 s [a] s' }                             -- 20-21
      if spec' = ∅ then                                                            -- 22
        return .up false                                                           -- 23
      if ¬ (spec', impl') ⊑ antichain then                                         -- 24
        antichain := insert (spec', impl') antichain                               -- 25
        working := (spec', impl') :: working                                       -- 26
  return .up true                                                                  -- 27

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
