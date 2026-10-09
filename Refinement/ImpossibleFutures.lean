module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Cslib.Foundations.Semantics.LTS.Divergence
public import Refinement.Semantics
public import Refinement.Product

open Cslib (LTS HasTau)

@[expose] public section ImpossibleFutures

namespace Refinement

/-!
# Weak impossible futures

Sections 2-3 of M. Laveaux and T. A. C. Willemse, *Deciding Impossible Futures*, LNCS 16365,
2026 (the preorder is due to Voorhoeve and Mauw, *Impossible futures and determinism*, 2001).

**Orientation.** As everywhere in this package, `lts1`/`State1` is the *specification* and
`lts2`/`State2` the *implementation*. The paper writes `L1 ⊑if L2` with `L1` the implementation,
so its `L1`/`L2` correspond to our `lts2`/`lts1`: we write `s1 ⊑if[lts1,lts2] s2` for
"`IF(s2) ⊆ IF(s1)`", exactly as `⊑tr`, `⊑sfr`, `⊑fdr` are written. Likewise the paper's
witnesses `(s, U) ∈ L1 ⋉ norm(L2)` are our `(U, s)` in `product (NormTr lts1) lts2`.
-/

/-- The weak impossible futures `IF(s)` of a state (Definition 2.2): pairs `(ρ, X)` of a weak trace
    `ρ` and a set `X` of traces such that after `ρ` the system can reach a state `t` none of whose
    weak traces lies in `X`. -/
def impossibleFutures [HasTau Label] (lts : LTS State Label) (s : State) :
    Set (List Label × Set (List Label)) :=
  { p | ∃ t, WeakTr lts s p.1 t ∧ p.2 ∩ weaktraces lts t = ∅ }

/-- Weak impossible futures refinement (Definition 3): every impossible future of the
    implementation `s2` is one of the specification `s1`. -/
def ImpossibleFuturesRefines [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) : Prop :=
  impossibleFutures lts2 s2 ⊆ impossibleFutures lts1 s1

/-- Notation for weak impossible futures refinement, mirroring the paper's `L1 ⊑if L2`
    (with the roles of the two systems as explained in the module docstring). -/
notation s1:max " ⊑if[" lts1 "," lts2 "] " s2:max => ImpossibleFuturesRefines lts1 s1 lts2 s2

/-- A `(U, s)` pair is an IF-witness (Definition 6): `U` is empty, or no state of `U` has all its
    weak traces among those of the implementation state `s` (`t ⊑wt s` fails for every `t ∈ U`). -/
def IsIFWitness [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (U : Set State1) (s : State2) : Prop :=
  U = ∅ ∨ ∀ t ∈ U, ¬ weaktraces lts1 t ⊆ weaktraces lts2 s

/-- The IF-witness test of Algorithm 6 (Section 4.2): as `IsIFWitness`, but the (expensive) weak
    trace comparison is only performed at *stable* implementation states. -/
def IsStableIFWitness [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (U : Set State1) (s : State2) : Prop :=
  U = ∅ ∨ (Stable lts2 s ∧ ∀ t ∈ U, ¬ weaktraces lts1 t ⊆ weaktraces lts2 s)

/-- An LTS is convergent when it has no divergent state, i.e. no infinite `τ`-path (Section 4.2). -/
def Convergent [HasTau Label] (lts : LTS State Label) : Prop :=
  ∀ s, ¬ lts.Divergent s

end Refinement

end ImpossibleFutures
