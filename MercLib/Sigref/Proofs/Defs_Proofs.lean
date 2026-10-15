module

public import MercLib.Sigref.Defs

@[expose] public section

/-!
# Proofs: Defs

Basic facts about splitting a partition.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). -/

namespace MercLib.Sigref

/-- The signature-agnostic fact `splitSetoid` refines `π`. -/
theorem splitSetoid_le {State Sg : Type} (π : Setoid State) (B D : Set State) (σ : State → Sg)
    (hB : Saturated π B) {s t : State} (h : (splitSetoid π B D σ hB).r s t) : π.r s t :=
  h.1

end MercLib.Sigref
