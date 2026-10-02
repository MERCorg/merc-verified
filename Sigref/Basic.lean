import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# Abstract signature refinement: shared definitions

The `Sigref` package formalises the *pseudocode* of the dirty-set signature-refinement algorithms
(Martens & Laveaux, TACAS 2026, Algorithms 1 and 2) in a deliberately non-isomorphic way:

* a partition is a `Setoid` (an equivalence relation), not an array of block ids;
* the algorithm is a **non-deterministic step relation**: pick *any* class containing a dirty
  state, split it, and keep *any* resulting part under the old identity. This covers every worklist
  order and block-numbering convention of an implementation;
* correctness is an **invariant plus a fixpoint**: the invariant is preserved by every step, and a
  configuration with no dirty states is the coarsest bisimulation.

Nothing here mentions vectors, hash maps, indices or worklists. The Rust implementation is related
to this model by a simulation proof (see `docs/branching-correctness-plan.md`).
-/

namespace Sigref

/-- A configuration of the algorithm: the current partition `π` and the set `X` of dirty states
(those whose signature may differ from the one last computed). -/
structure Config (State : Type) where
  π : Setoid State
  X : Set State

/-- A set of states that is a union of `π`-classes. -/
def Saturated {State : Type} (π : Setoid State) (B : Set State) : Prop :=
  ∀ s t, π.r s t → (s ∈ B ↔ t ∈ B)

/-- The relation obtained by splitting the (saturated) set `B` of `π`: the *dirty* part `D ⊆ B` is
regrouped by the signature `σ`, while the clean part `B \ D` stays together. States outside `B` keep
their old relation. -/
def splitRel {State Sg : Type} (π : Setoid State) (B D : Set State) (σ : State → Sg) :
    State → State → Prop :=
  fun s t => π.r s t ∧ (s ∈ B → ((s ∈ D ↔ t ∈ D) ∧ (s ∈ D → σ s = σ t)))

/-- `splitRel` is an equivalence when `B` is saturated. -/
def splitSetoid {State Sg : Type} (π : Setoid State) (B D : Set State) (σ : State → Sg)
    (hB : Saturated π B) : Setoid State where
  r := splitRel π B D σ
  iseqv := by
    refine ⟨fun s => ⟨π.refl s, fun _ => ⟨Iff.rfl, fun _ => rfl⟩⟩, ?_, ?_⟩
    · intro s t ⟨hst, h⟩
      refine ⟨π.symm hst, fun ht => ?_⟩
      have hs : s ∈ B := (hB s t hst).2 ht
      obtain ⟨h1, h2⟩ := h hs
      exact ⟨h1.symm, fun htD => (h2 (h1.2 htD)).symm⟩
    · intro s t u ⟨hst, h1⟩ ⟨htu, h2⟩
      refine ⟨π.trans hst htu, fun hs => ?_⟩
      obtain ⟨a1, a2⟩ := h1 hs
      obtain ⟨b1, b2⟩ := h2 ((hB s t hst).1 hs)
      exact ⟨a1.trans b1, fun hsD => (a2 hsD).trans (b2 (a1.1 hsD))⟩

/-- The signature-agnostic fact `splitSetoid` refines `π`. -/
theorem splitSetoid_le {State Sg : Type} (π : Setoid State) (B D : Set State) (σ : State → Sg)
    (hB : Saturated π B) {s t : State} (h : (splitSetoid π B D σ hB).r s t) : π.r s t :=
  h.1

end Sigref
