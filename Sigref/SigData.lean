import Signatures.InductiveSignatures

/-!
# Inductive signature data

`SigData lts π` packages a fixed point `sigFn` of the paper's inductive signature `Sig` for the
partition `π`, together with a *coherent* hash `sigHash` (equal hash ⇔ equal signature), as an
implementation's hash map provides. `sigData_exists` shows that it exists on a finite τ-loop-free LTS.
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label]

structure SigData (lts : LTS State Label) (π : Setoid State) where
  Tag : Type
  sigHash : State → Tag
  sigFn : State → Set (Label × (Quotient π ⊕ Tag))
  hFix : ∀ s, sigFn s = Sig lts (Quotient.mk π) sigHash sigFn s
  hCoh : ∀ s t, sigHash s = sigHash t ↔ sigFn s = sigFn t

/-- Existence of hash-coherent signature data on a finite τ-loop-free LTS. -/
def SigDataExists [Finite State] (lts : LTS State Label) (π : Setoid State) : Prop :=
  TauLoopFree lts → Nonempty (SigData lts π)

end Sigref
