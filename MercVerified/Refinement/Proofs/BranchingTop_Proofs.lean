import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Refinement_Proofs
import MercVerified.Refinement.Proofs.BranchingRun_Proofs
import MercVerified.Refinement.Proofs.BranchingIncoming_Proofs
import MercVerified.Refinement.Proofs.BranchingBridge_Proofs
import Aeneas.Std.WP

/-!
# Proofs for the `branching_bisim_sigref_impl` correctness contract

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

`branching_bisim_sigref_impl_correct` proves `BranchingBisimSigrefImplCorrectSpec`
(`MercVerified/Refinement/Refinement.lean`); its pin lives in `Pins/Refinement_Pins.lean`.
The proof unfolds `branching_signature_refinement` down to `branching_run_worklist_loop`, whose
contract (`branching_run_worklist_loop_spec`) gives the partition on the `Fin n` view; the bridge
`bb_embed` moves branching bisimilarity to the `toLTS` view.
-/

open Aeneas Aeneas.Std WP Result
open verified.merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open verified.merc_reduction.signature_refinement (WorklistContextBranching)
open MercVerified.Lts (toLTS)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The `resize_with` closure of `branching_signature_refinement` never fails. -/
theorem branching_resize_closure_total {L Label : Type} (LTSInst : LTS L Label) :
    core.ops.function.FnMut.IsTotal
      (verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag
        LTSInst) := by
  intro c
  obtain ⟨ti, hti⟩ := merc_utilities.tagged_index.TagIndex.new_spec (T := Std.Usize) BlockTag 0#usize
  refine ⟨(ti, c), ?_⟩
  show verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag.call_mut LTSInst c () = _
  unfold verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag.call_mut
  rw [hti, bind_ok]

private theorem FromVecArray_from_ok' {T : Type} {N : Std.Usize} (a : Array T N) :
    ∃ v : alloc.vec.Vec T, alloc.vec.FromVecArray.from a = ok v := by
  have hbnd : a.val.length ≤ Usize.max := by scalar_tac
  rw [alloc.vec.FromVecArray.from]
  exact ⟨alloc.vec.Vec.from a.val hbnd, rfl⟩

private theorem BlockPartitionBuilder_default_ok' :
    ∃ bpb : verified.merc_reduction.block_partition.BlockPartitionBuilder,
      verified.merc_reduction.block_partition.BlockPartitionBuilder.Insts.CoreDefaultDefault.default = ok bpb := by
  rw [verified.merc_reduction.block_partition.BlockPartitionBuilder.Insts.CoreDefaultDefault.default]
  rcases (alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec (TagIndex Std.Usize BlockTag)) with ⟨b0, hb0, -⟩
  rcases (alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec Std.Usize) with ⟨b1, hb1, -⟩
  rw [hb0, hb1]
  exact ⟨({ index_to_block := b0, block_sizes := b1, old_elements := b0 } :
    verified.merc_reduction.block_partition.BlockPartitionBuilder), by simp⟩

/-- The `Fin n` view of a branching-bisimulation-quotient: the sub-LTS of real states embeds into
`toLTS`. -/
theorem branching_bb_toLTS {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n) (hnmax : n.val ≤ Usize.max) (a b : Fin n.val) :
    BranchingBisimilarity (aLTS LTSInst sys n.val) a b ↔
      BranchingBisimilarity (toLTS LTSInst sys) (stOf a) (stOf b) := by
  refine bb_embed (aLTS LTSInst sys n.val) (toLTS LTSInst sys) stOf (fun _ _ _ => Iff.rfl) ?_ a b
  intro a μ t htr
  obtain ⟨ts, hts, hmem⟩ := htr
  obtain ⟨ts', hts', htg⟩ := hwf.2.1 n hns (stOf a) (by rw [stOf_index _ hnmax]; exact a.2)
  have : ts' = ts := by have := hts'.symm.trans hts; simpa using this
  subst this
  have hlt : t.index.val < n.val := htg _ hmem
  refine ⟨⟨t.index.val, hlt⟩, ?_⟩
  apply merc_utilities.tagged_index.TagIndex.ext
  apply UScalar.eq_of_val_eq
  rw [stOf_index _ hnmax]

/-- `branching_signature_refinement` succeeds and its partition is the branching-bisimilarity
partition of the `Fin n` view. -/
theorem branching_signature_refinement_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (hasm : BranchingLtsAssumptions LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hincoming : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n) (hnpos : 0 < n.val) :
    ∃ partition : BlockPartition,
      verified.merc_reduction.signature_refinement.branching_signature_refinement LTSInst sys
        incoming = ok partition ∧ PartInv n.val partition ∧
      ∀ s t : Fin n.val, e2bAt partition s.val = e2bAt partition t.val ↔
        BranchingBisimilarity (aLTS LTSInst sys n.val) s t := by
  obtain ⟨⟨nl, hnl, hhid, hlab⟩, htopo⟩ := hasm
  have hE : CEnv LTSInst sys nl := ⟨hnl, hhid, hlab⟩
  rcases (alloc.vec.Vec.resize_with_spec Global
      (verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag
        LTSInst) (branching_resize_closure_total LTSInst)
      (alloc.vec.Vec.new (TagIndex Std.Usize BlockTag)) n ()) with ⟨state_to_key, hstate_to_key, hstklen⟩
  rcases (block_partition_new_spec n hnpos) with ⟨bp, hbp, -⟩
  rcases (merc_utilities.tagged_index.TagIndex.new_spec (T := Std.Usize) BlockTag 0#usize) with ⟨ti, hti⟩
  have hti' := hti
  simp at hti'
  subst hti'
  rcases (FromVecArray_from_ok' (Array.make 1#usize [({ index := 0#usize, marker := () } : TagIndex Std.Usize BlockTag)])) with ⟨v, hv⟩
  rcases (alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec
      ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag))) with ⟨v1, hv1, -⟩
  rcases (BlockPartitionBuilder_default_ok') with ⟨bpb, hbpb⟩
  let ctx0 : WorklistContextBranching :=
    { partition := bp, worklist := v,
      states := alloc.vec.Vec.new (TagIndex Std.Usize StateTag),
      builder := v1, split_builder := bpb, state_to_key := state_to_key }
  have hinit : BranchingInitial n ctx0 := ⟨_, hti, hv, hbp, hstklen⟩
  have hIC := MercVerified.Lts.Proofs.incoming_transitions_correct LTSInst sys hwf hfit incoming
    hincoming
  have hsil := incoming_silent_correct LTSInst sys hwf hfit incoming hincoming n hns
  obtain ⟨ctx, hloop, hPI, hiff⟩ := branching_run_worklist_loop_spec LTSInst sys hwf hfit incoming
    hIC n hns hE htopo hsil ctx0 hinit
  refine ⟨ctx.partition, ?_, hPI, hiff⟩
  unfold verified.merc_reduction.signature_refinement.branching_signature_refinement
  rw [hns]
  simp
  rw [hstate_to_key]
  simp
  rw [hbp]
  simp
  rw [hv]
  simp
  rw [hv1]
  simp
  rw [hbpb]
  simp
  rw [hloop]
  simp

/-- **Contract**: `branching_bisim_sigref_impl` returns a partition whose blocks are exactly the
branching bisimilarity classes of the real states. -/
theorem branching_bisim_sigref_impl_correct
    {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (hasm : BranchingLtsAssumptions LTSInst sys) (timing : Timing) :
    BranchingBisimSigrefImplCorrectSpec LTSInst sys hwf hfit hasm timing := by
  unfold BranchingBisimSigrefImplCorrectSpec
  obtain ⟨n, hns, hnpos⟩ := hwf.1
  have hn2 := hfit n hns
  have hnmax : n.val ≤ Usize.max := by scalar_tac
  rcases (MercVerified.Lts.Proofs.incoming_new_ok LTSInst sys hwf hfit)
    with ⟨incoming, hincoming⟩
  obtain ⟨partition', hsr, hPI, hiff⟩ := branching_signature_refinement_spec LTSInst sys hwf hfit
    hasm incoming hincoming n hns hnpos
  have hcall0 :
      (verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition
        LTSInst).call_once (sys, incoming) () = ok partition' := by
    show verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition.call_once LTSInst (sys, incoming) () = _
    rw [verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition.call_once]
    simpa using hsr
  have hmeasure := merc_utilities.timing.Timing.measure_spec
    (verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition
      LTSInst) timing (toStr "reduction") (sys, incoming)
  rw [hcall0] at hmeasure
  obtain ⟨partition, hmeasure', hcall⟩ : ∃ partition, merc_utilities.timing.Timing.measure
      (verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition
        LTSInst) timing (toStr "reduction") (sys, incoming) = ok partition ∧
      (verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition
        LTSInst).call_once (sys, incoming) () = ok partition :=
    ⟨partition', hmeasure, hcall0⟩
  have hp' : partition' = partition := Result.ok_injective (hcall0.symm.trans hcall)
  subst hp'
  let blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag :=
    fun s => partition'.element_to_block.val.getD s.index.val zBT
  refine ⟨partition', blockOf, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl
    rw [hincoming]
    simp
    rw [hmeasure']
  · intro s b _ hz
    show partition'.element_to_block.val.getD s.index.val zBT = b
    rw [List.getD_eq_getElem?_getD, hz]; rfl
  · intro n' hn' s hs
    have hnn' : n' = n := by have := hn'.symm.trans hns; simpa using this
    subst hnn'
    have hown := hPI.own s.index.val hs
    have hblk := hPI.blk (e2bAt partition' s.index.val) hown.1
    have hoff_lt : offAt partition' s.index.val < n'.val := by omega
    have hmem : eAt partition' (offAt partition' s.index.val) ∈ partition'.elements.val := by
      unfold eAt
      rw [List.getD_eq_getElem _ _ (by rw [hPI.len_e]; exact hoff_lt)]
      exact List.getElem_mem _
    have heq : eAt partition' (offAt partition' s.index.val) = s :=
      merc_utilities.tagged_index.TagIndex.ext
        (UScalar.eq_of_val_eq (hPI.inv s.index.val hs))
    rwa [heq] at hmem
  · intro n' hn' s hs
    have hnn' : n' = n := by have := hn'.symm.trans hns; simpa using this
    subst hnn'
    refine ⟨partition'.element_to_block.val.getD s.index.val zBT, ?_⟩
    have h : s.index.val < partition'.element_to_block.val.length := by
      rw [hPI.len_e2b]; exact hs
    simp [List.getElem?_eq_getElem h]
  · intro n' hn' s s' hs hs'
    have hnn' : n' = n := by have := hn'.symm.trans hns; simpa using this
    subst hnn'
    have hfin : ∀ y : TagIndex Std.Usize StateTag, ∀ hy : y.index.val < n'.val,
        stOf (⟨y.index.val, hy⟩ : Fin n'.val) = y := by
      intro y hy
      apply merc_utilities.tagged_index.TagIndex.ext
      apply UScalar.eq_of_val_eq
      rw [stOf_index _ hnmax]
    have hb : ∀ y : TagIndex Std.Usize StateTag, y.index.val < n'.val →
        (blockOf y).index.val = e2bAt partition' y.index.val := fun y hy =>
      e2bAt_eq hPI y.index.val hy
    have hbeq : blockOf s = blockOf s' ↔ e2bAt partition' s.index.val = e2bAt partition' s'.index.val := by
      constructor
      · intro h; rw [← hb s hs, ← hb s' hs', h]
      · intro h
        apply merc_utilities.tagged_index.TagIndex.ext
        apply UScalar.eq_of_val_eq
        rw [hb s hs, hb s' hs', h]
    rw [hbeq]
    have h1 := hiff ⟨s.index.val, hs⟩ ⟨s'.index.val, hs'⟩
    rw [branching_bb_toLTS LTSInst sys hwf n' hns hnmax, hfin s hs, hfin s' hs'] at h1
    exact h1

end MercVerified.Refinement.Proofs
