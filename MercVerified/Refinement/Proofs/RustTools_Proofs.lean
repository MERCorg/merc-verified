import MercVerified.Refinement.Proofs.BranchingProcess_Proofs
import MercVerified.Refinement.Proofs.BranchingDirty_Proofs
import Aeneas.Std.WP

/-!
# Small tools for the proofs about the preprocessing

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open MercVerified.Lts.Proofs MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

theorem loop_cont' {α β : Type} (body : α → Result (ControlFlow α β)) (x x' : α)
    (h : body x = ok (cont x')) : loop body x = loop body x' := by
  rw [loop, h]; simp

theorem loop_done' {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) (y : β)
    (h : body x = ok (done y)) : loop body x = ok y := by
  rw [loop, h]; simp

theorem tag_ne_ok {Tag : Type} (a b : TagIndex Std.Usize Tag) :
    core.cmp.PartialEq.ne.trait_default
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex Tag
        core.cmp.PartialEqUsize) a b = ok (decide (a.index.val ≠ b.index.val)) := by
  rw [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  simp [tag_partial_eq_inst]
  by_cases h : a.index = b.index
  · simp [h]
  · have : a.index.val ≠ b.index.val := fun e => h (UScalar.eq_of_val_eq e)
    simp [h, this]

theorem vec_deref_val {U : Type} (v : alloc.vec.Vec U) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

end MercVerified.Refinement.Proofs
