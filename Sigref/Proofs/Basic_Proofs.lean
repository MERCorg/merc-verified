import Sigref.Basic

/-!
# Proofs: Basic

Basic facts about splitting a partition.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/Basic_Pins.lean` (human-vetted).
-/

namespace Sigref

/-- The signature-agnostic fact `splitSetoid` refines `π`. -/
theorem splitSetoid_le {State Sg : Type} (π : Setoid State) (B D : Set State) (σ : State → Sg)
    (hB : Saturated π B) {s t : State} (h : (splitSetoid π B D σ hB).r s t) : π.r s t :=
  h.1

end Sigref
