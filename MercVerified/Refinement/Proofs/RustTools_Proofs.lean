module

public import MercVerified.Refinement.Proofs.BranchingProcess_Proofs
public import MercVerified.Refinement.Proofs.BranchingDirty_Proofs
public import Aeneas.Std.WP
import all MercLib.LTS.Proofs.BranchingBisimilarity_Transitivity_Proofs
import all MercLib.Signatures.Proofs.InductiveSignatures_Proofs
import all MercLib.Sigref.Proofs.Absorb_Proofs
import all MercLib.Sigref.Proofs.CountingSort_Proofs
import all MercLib.Sigref.Proofs.KeyComp_Proofs
import all MercLib.Sigref.Proofs.RelBisim_Proofs
import all MercLib.Sigref.Proofs.SigData_Proofs
import all MercLib.Sigref.Proofs.SigE_Proofs
import all MercVerified.Lts.Proofs.Foundation_Proofs
import all MercVerified.Refinement.Proofs.BranchingDirty_Proofs
import all MercVerified.Refinement.Proofs.BranchingProcess_Proofs
import all MercVerified.Refinement.Proofs.BranchingRenumber_Proofs
import all MercVerified.Refinement.Proofs.BranchingSignature_Proofs
import all MercVerified.Refinement.Proofs.BranchingSubset_Proofs
import all MercVerified.Refinement.Proofs.FinishBlocks_Proofs
import all MercVerified.Refinement.Proofs.FinishPartition_Proofs
import all MercVerified.Refinement.Proofs.Intern_Proofs
import all MercVerified.Refinement.Proofs.LoopTools_Proofs
import all MercVerified.Refinement.Proofs.MarkDirty_Proofs
import all MercVerified.Refinement.Proofs.MarkedSorted_Proofs
import all MercVerified.Refinement.Proofs.PartitionInv_Proofs
import all MercVerified.Refinement.Proofs.Partition_Proofs
import all MercVerified.Refinement.Proofs.ScatterLoop_Proofs
import all MercVerified.Refinement.Proofs.SigKey_Proofs
import all MercVerified.Refinement.Proofs.SplitPartInv_Proofs
import all MercVerified.Refinement.Proofs.Split_Proofs
import all MercVerified.Refinement.Proofs.Spme_Proofs
import all MercVerified.Refinement.Proofs.StrongSignature_Proofs
import all MercVerified.Refinement.Proofs.SwapBlocks_Proofs
import all MercVerified.Refinement.Proofs.WorklistLoop_Proofs
import all Aeneas.Std.Scalar.Ops.Add
import all Aeneas.Std.Core.Core
import all Aeneas.Std.Core.Cmp
import all Aeneas.Data.List.List
import all Init.Data.List.Control

@[expose] public section

/-!
# Small tools for the proofs about the preprocessing

Machine-generated; may be freely edited or regenerated (see AGENTS.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open MercVerified.Lts.Proofs MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

private theorem loop_cont' {α β : Type} (body : α → Result (ControlFlow α β)) (x x' : α)
    (h : body x = ok (cont x')) : loop body x = loop body x' := by
  rw [loop, h]; simp

private theorem loop_done' {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) (y : β)
    (h : body x = ok (done y)) : loop body x = ok y := by
  rw [loop, h]; simp

private theorem tag_ne_ok {Tag : Type} (a b : TagIndex Std.Usize Tag) :
    core.cmp.PartialEq.ne.trait_default
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex Tag
        core.cmp.PartialEqUsize) a b = ok (decide (a.index.val ≠ b.index.val)) := by
  rw [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  simp [tag_partial_eq_inst]
  by_cases h : a.index = b.index
  · simp [h]
  · have : a.index.val ≠ b.index.val := fun e => h (UScalar.eq_of_val_eq e)
    simp [h, this]

private theorem vec_deref_val {U : Type} (v : alloc.vec.Vec U) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

end MercVerified.Refinement.Proofs
