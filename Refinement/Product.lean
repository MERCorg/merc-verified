module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Cslib.Foundations.Semantics.LTS.Divergence
public import Refinement.Semantics

open Cslib (LTS HasTau)

@[expose] public section Product

/-!
# Product, normal form and witnesses

Section 3 of M. Laveaux, J. F. Groote, T. A. C. Willemse, *Correct and Efficient Antichain
Algorithms for Refinement Checking*, LMCS 17(1:8), 2021.

Throughout, `State1`/`lts1` plays the role of the specification, `State2`/`lts2` the
implementation.
-/

/-- The product of two LTSs over the same label type (Definition 3.1): a `τ`-step on the right
    leaves the left component unchanged; a shared visible step advances both components
    together. -/
def product [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    LTS (State1 × State2) Label where
  Tr p μ q :=
    (μ = HasTau.τ ∧ q.1 = p.1 ∧ lts2.Tr p.2 HasTau.τ q.2) ∨
    (IsVisible μ ∧ lts1.Tr p.1 μ q.1 ∧ lts2.Tr p.2 μ q.2)

/-- A set of states is divergent iff one of its members is. Used to guard `FdrNormTr`'s
    transitions and in the definition of an FD-witness (Definition 3.21), where the paper writes
    `[[U]]⇑`. -/
def SetDivergent [HasTau Label] (lts : LTS State Label) (U : Set State) : Prop :=
  ∃ s ∈ U, lts.Divergent s

/-- The normal form transition relation (Definition 3.3): `U -a-> V` iff `V` is the set of
    `a`-derivatives (via `WeakTr`) of the states in `U`, for visible `a`. There is never a
    `τ`-transition in the normal form, since `IsVisible a` excludes it. -/
def NormTr [HasTau Label] (lts : LTS State Label) : LTS (Set State) Label where
  Tr U a V := IsVisible a ∧ V = { t | ∃ s ∈ U, WeakTr lts s [a] t }

/-- The failures-divergences normal form transition relation (Definition 3.16): as `NormTr`, but
    additionally guarded by `U` not being divergent, so `normfdr` is a subgraph of `norm`
    (states beyond a divergence are pruned rather than explored). -/
def FdrNormTr [HasTau Label] (lts : LTS State Label) : LTS (Set State) Label where
  Tr U a V := IsVisible a ∧ ¬ SetDivergent lts U ∧ V = { t | ∃ s ∈ U, WeakTr lts s [a] t }

/-- The initial state of the normal form, shared by `NormTr` and `FdrNormTr`
    (Definitions 3.3 and 3.16): the set of states reachable from `s` by zero or more
    `τ`-steps. -/
def NormInit [HasTau Label] (lts : LTS State Label) (s : State) : Set State :=
  { t | WeakTr lts s [] t }

/-! ## Witnesses (Definitions 3.7, 3.21)

A witness is a state of a product whose reachability certifies a refinement violation
(Theorems 3.11, 3.14, 3.24). `U : Set State1` is a normal-form state of the specification;
`s : State2` is an implementation state. -/

/-- A `(U, s)` pair is a TR-witness (Definition 3.7) iff `U` is empty: the specification's normal
    form has no derivative along the weak trace that reached `s`, i.e. that trace is not a weak
    trace of the specification. -/
def IsTRWitness (U : Set State1) (_s : State2) : Prop := U = ∅

/-- A `(U, s)` pair is an SF-witness (Definition 3.7): either a TR-witness, or `s` is stable and
    stably refuses something the specification states comprising `U` cannot all refuse. -/
def IsSFWitness [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (U : Set State1) (s : State2) : Prop :=
  U = ∅ ∨ (Stable lts2 s ∧ ¬ refusalsOf lts2 s ⊆ refusals lts1 U)

/-- A `(U, s)` pair is an FD-witness (Definition 3.21): `U` itself not divergent, and either an
    SF-witness-style condition, or `s` is divergent. -/
def IsFDWitness [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (U : Set State1) (s : State2) : Prop :=
  ¬ SetDivergent lts1 U ∧
    (U = ∅ ∨ (Stable lts2 s ∧ ¬ refusalsOf lts2 s ⊆ refusals lts1 U) ∨ lts2.Divergent s)

end Product
