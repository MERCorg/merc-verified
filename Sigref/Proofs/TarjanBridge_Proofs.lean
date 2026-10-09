import Sigref.Proofs.TarjanMain_Proofs
import Sigref.Scc

/-!
# Proofs: the SCC partition of the Tarjan model is a τ-SCC partition of the LTS

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

namespace Sigref.Tarjan

open Cslib Relation

variable {n : ℕ} {Label : Type} [HasTau Label]

/-- If the hidden edges of the graph are the τ-steps of the LTS, an SCC numbering of the graph is a
τ-SCC numbering of the LTS. -/
theorem isTauSccPartition_of_scc (lts : LTS (Fin n) Label) (g : Graph n)
    (hE : ∀ u v, Edge g u v ↔ lts.Tr u HasTau.τ v) {blk : Fin n → ℕ} {k : ℕ}
    (h : IsSccPartition g blk k) : Sigref.IsTauSccPartition lts blk k := by
  have hR : ∀ u v, ReflTransGen (Edge g) u v ↔ lts.τSTr u v := by
    intro u v
    constructor
    · intro hh
      induction hh with
      | refl => exact ReflTransGen.refl
      | tail _ he ih => exact ih.tail ((hE _ _).1 he)
    · intro hh
      induction hh with
      | refl => exact ReflTransGen.refl
      | tail _ he ih => exact ih.tail ((hE _ _).2 he)
  refine ⟨h.1, h.2.1, fun s t => ?_⟩
  rw [h.2.2 s t]
  unfold Sigref.TauScc
  rw [hR, hR]

end Sigref.Tarjan
