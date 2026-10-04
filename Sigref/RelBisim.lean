import Signatures.BranchingBisimilarity
import Mathlib.Logic.Relation

/-!
# `E π`: branching bisimilarity relative to a partition

For a partition `π`, `E π s t` is the coarsest relation that is a *branching bisimulation in which
only the τ-steps inside a block of `π` are inert, and the targets of every other transition are
compared up to `π`* (instead of up to the relation itself). This is exactly the equivalence induced
by the paper's inductive signature `Sig_π` (checked by brute force, see
`scripts/sigref_bruteforce.py`), but stated without hashes or absorption.

It is defined as ordinary branching bisimilarity of an auxiliary LTS `relLTS lts π` in which the
non-inert transition `s -a→ x` is replaced by `s -(a, [x]_π)→ ⊥`. This gives reflexivity,
symmetry and transitivity from `Signatures`, and `E_step` / `E_coind` below are the unfolded
matching condition and the coinduction principle.
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label]

/-- A τ-step inside one block of `π`. -/
def InertTr (lts : LTS State Label) (π : Setoid State) (s t : State) : Prop :=
  lts.Tr s HasTau.τ t ∧ π.r s t

/-- A path of inert τ-steps. -/
abbrev InertReach (lts : LTS State Label) (π : Setoid State) : State → State → Prop :=
  Relation.ReflTransGen (InertTr lts π)

instance relHasTau (π : Setoid State) : HasTau (Label × Option (Quotient π)) := ⟨(HasTau.τ, none)⟩

/-- The auxiliary LTS: inert steps stay, every other transition `s -a→ x` becomes
`s -(a, [x]_π)→ ⊥`. -/
def relLTS (lts : LTS State Label) (π : Setoid State) :
    LTS (State ⊕ Unit) (Label × Option (Quotient π)) where
  Tr
    | .inl s, l, .inl x => l = (HasTau.τ, none) ∧ InertTr lts π s x
    | .inl s, l, .inr _ => ∃ a x, l = (a, some (Quotient.mk π x)) ∧ lts.Tr s a x ∧
        ¬ (a = HasTau.τ ∧ π.r s x)
    | .inr _, _, _ => False

/-- `E π`: branching bisimilarity relative to `π`. -/
def E (lts : LTS State Label) (π : Setoid State) (s t : State) : Prop :=
  π.r s t ∧ BranchingBisimilarity (relLTS lts π) (.inl s) (.inl t)

end Sigref
