module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.CoupledSim

/-!
# Coupled similarity

This module formalises the theory of coupled similarity, a notion of equivalence for systems
with internal actions that refines weak similarity with a weak form of symmetry ("coupling").
It follows [B. Bisping and U. Nestmann, *Computing Coupled Similarity*][Bisping2019]
(TACAS 2019); the definitions and theorem statements mirror the paper's Sections 2–4 and the
authors' Isabelle/HOL formalization.

## Main definitions

- `DTr`: the *delay steps* `q =μ⟼ q'`, the "shortened" weak steps of delay simulation
  (identity for `μ = τ`; no trailing `τ`-steps for visible `μ`).
- `IsWeakSimulation`, `Coupling`, `IsCoupledSimulation`: Definitions 3 and 4 of the paper.
- `IsCoupledDelaySimulation`: Definition 5 of the paper.
- `CoupledSimulationPreorder` (`≼cs`), `CoupledSimilarity` (`≡cs`): the preorder and
  equivalence induced by coupled simulations.
- `WeakSimulationPreorder` (`≼ws`): needed to state the reduction of weak similarity to
  coupled similarity (Theorem 1).
- `extendSink`: the LTS extended by a `τ`-reachable sink `none` (Theorem 1).

## Main statements

See the `Proofs/` files next to this module; the headline theorems are restated in
`Challenges/CoupledSim.lean`.

## References

- [B. Bisping and U. Nestmann, *Computing Coupled Similarity*][Bisping2019]
-/

/-! ## Delay steps

Delay simulations are defined in terms of *shortened* weak steps: a visible step may not be
followed by `τ`-steps, and a `τ`-step may not move at all ([Bisping2019], Sect. 2.2). -/

/-- A delay step `s =μ⟼ s'`: for the internal action `τ` it is the identity, and for a visible
action `μ` it is a `τ`-prefix, the strong `μ`-step, and *nothing* after it. -/
inductive DTr [HasTau Label] (lts : LTS State Label) : State → Label → State → Prop where
  | tau {s : State} : DTr lts s HasTau.τ s
  | vis {s t s' : State} {μ : Label} (hμ : μ ≠ HasTau.τ) (hτ : lts.τSTr s t)
      (htr : lts.Tr t μ s') : DTr lts s μ s'

/-! ## Simulations -/

/-- **Weak simulation** (Definition 3 of [Bisping2019]): every strong step of the left state can
be matched by a weak step of the right state with the same label, staying inside the relation. -/
def IsWeakSimulation [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ ⦃p q⦄, r p q → ∀ μ p', lts.Tr p μ p' → ∃ q', r p' q' ∧ lts.STr q μ q'

/-- **Coupling** (Definition 4 of [Bisping2019]): a weak form of symmetry — from a related pair,
the right state can catch up to the left one by internal steps. -/
def Coupling [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  ∀ ⦃p q⦄, r p q → ∃ q', lts.τSTr q q' ∧ r q' p

/-- **Coupled simulation** (Definition 4 of [Bisping2019]): a weak simulation with coupling. -/
def IsCoupledSimulation [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) : Prop :=
  IsWeakSimulation lts r ∧ Coupling lts r

/-- **Coupled delay simulation** (Definition 5 of [Bisping2019]): like `IsCoupledSimulation`, but
strong steps are matched by delay steps `DTr` instead of weak steps `STr`. -/
def IsCoupledDelaySimulation [HasTau Label] (lts : LTS State Label)
    (r : State → State → Prop) : Prop :=
  (∀ ⦃p q⦄, r p q → ∀ μ p', lts.Tr p μ p' → ∃ q', r p' q' ∧ DTr lts q μ q') ∧ Coupling lts r

/-! ## The coupled simulation preorder and coupled similarity -/

/-- **The coupled simulation preorder** `≼cs` (Definition 4 of [Bisping2019]): `p ≼cs q` iff some
coupled simulation relates `p` and `q`. -/
def CoupledSimulationPreorder [HasTau Label] (lts : LTS State Label) :
    State → State → Prop :=
  fun p q => ∃ r, IsCoupledSimulation lts r ∧ r p q

/-- **The weak simulation preorder** `≼ws` (Definition 3 of [Bisping2019]). -/
def WeakSimulationPreorder [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun p q => ∃ r, IsWeakSimulation lts r ∧ r p q

/-- `p ≼cs[lts] q`: `p` is coupled-simulated by `q` in `lts`. -/
scoped notation s:max " ≼cs[" lts "] " s':max => CoupledSimulationPreorder lts s s'

/-- `p ≼ws[lts] q`: `p` is weakly simulated by `q` in `lts`. -/
scoped notation s:max " ≼ws[" lts "] " s':max => WeakSimulationPreorder lts s s'

/-- **Coupled similarity** `≡cs` (Definition 4 of [Bisping2019]): the symmetric closure of the
coupled simulation preorder. -/
def CoupledSimilarity [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun p q => p ≼cs[lts] q ∧ q ≼cs[lts] p

/-- `p ≡cs[lts] q`: `p` and `q` are coupled similar in `lts`. -/
scoped notation s:max " ≡cs[" lts "] " s':max => CoupledSimilarity lts s s'

/-! ## Reduction of weak similarity to coupled similarity (Theorem 1)

Extending an LTS by a sink state `none` that is `τ`-reachable from everywhere turns weak
simulation into coupled simulation. -/

/-- The LTS `lts` extended by a sink state `none` reachable by a `τ`-step from every state,
including `none` itself (Theorem 1 of [Bisping2019]). -/
def extendSink [HasTau Label] (lts : LTS State Label) : LTS (Option State) Label where
  Tr p μ p' :=
    match p, p' with
    | some s, some s' => lts.Tr s μ s'
    | some _, none => μ = HasTau.τ
    | none, none => μ = HasTau.τ
    | none, some _ => False

end MercLib.CoupledSim
