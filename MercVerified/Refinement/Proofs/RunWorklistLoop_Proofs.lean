import MercVerified.Refinement.Proofs.WorklistStep_Proofs
import MercVerified.Lts.Proofs.IncomingTransitionsCorrect_Proofs
import Aeneas.Std.WP

/-!
# Termination of `strong_run_worklist_loop`

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)
open verified.merc_reduction.signature_refinement (WorklistContextStrong)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The initial context of `strong_signature_refinement` satisfies the loop invariant, and its
    measure is at most `n * (n + 2)`. -/
theorem initial_loopInv {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (n : Sz)
    (hn : 0 < n.val) (ctx0 : WorklistContextStrong)
    (hinit : InitialWorklistContext LTSInst n ctx0) :
    LoopInv n.val ctx0 ∧ worklistMeasure n.val ctx0 ≤ n.val * (n.val + 2) := by
  obtain ⟨ti, hti, hwl, hpart, hres, -⟩ := hinit
  have hti' : ti = ({ index := 0#usize, marker := () } : BT) := by
    simp at hti; exact hti.symm
  subst hti'
  obtain ⟨p, hnew, hPI, hN⟩ := init_partInv n hn
  have hp : ctx0.partition = p := by
    have := hnew.symm.trans hpart; simp at this; exact this.symm
  obtain ⟨p', hnew', hbl, -⟩ := block_partition_new_spec n hn
  have hpp : p' = p := by
    have := hnew'.symm.trans hnew; simpa using this
  rw [hpp] at hbl
  obtain ⟨w, hw, hwlen⟩ := alloc.vec.Vec.resize_with_spec Global
    (verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag
      LTSInst)
    (alloc.vec.Vec.new (TagIndex Std.Usize BlockTag)) n ()
  have hw' : w = ctx0.state_to_key := by
    have := hw.symm.trans hres; simpa using this
  subst hw'
  have hwv : ctx0.worklist.val = [({ index := 0#usize, marker := () } : BT)] := by
    simp [alloc.vec.FromVecArray.from, Array.make] at hwl
    rw [← hwl]; simp [alloc.vec.Vec.from_val]
  have hblk : blkAt p 0 = { begin := 0#usize, marked_split := 0#usize, «end» := n } := by
    simp [blkAt, hbl]
  refine ⟨⟨⟨by rw [hp]; exact hPI, ?_, ?_⟩, hwlen⟩, ?_⟩
  · rw [hwv]; simp
  · intro x hx
    rw [hwv] at hx
    simp at hx; subst hx
    rw [hp]
    refine ⟨by rw [hN]; show 0 < 1; omega, ?_⟩
    show (blkAt p 0).marked_split.val < (blkAt p 0).«end».val
    rw [hblk]; simpa using hn
  · unfold worklistMeasure numBlocks
    rw [hp, hN, hwv]
    simp only [List.length_singleton]
    have h1 : (n.val - 1) * (n.val + 1) ≤ n.val * (n.val + 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    nlinarith


/-- The loop state of `strong_run_worklist_loop_loop`. -/
abbrev RunState := WorklistContextStrong × Std.Usize

/-- Termination of `strong_run_worklist_loop` from the initial context of a well-formed LTS. -/
theorem strong_run_worklist_loop_terminates
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0) :
    ∃ ctx, verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx := by
  obtain ⟨n0, hn0, hnpos⟩ := hwf.1
  have hnn : n0 = n := by
    have := hn0.symm.trans hns; simpa using this
  subst hnn
  have hIC := MercVerified.Lts.Proofs.incoming_transitions_correct LTSInst sys hwf incoming hinc
  have hincS : ∀ s : ST, s.index.val < n0.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n0.val := fun s hs => by
    obtain ⟨res, h1, h2, -⟩ := hIC n0 hns s hs
    exact ⟨res, h1, h2⟩
  obtain ⟨hI0, hM0⟩ := initial_loopInv LTSInst n0 hnpos ctx0 hinit
  have hn2 := hwf.2.2.1 n0 hns
  have hnmax : n0.val ≤ Usize.max := by scalar_tac
  unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop
  obtain ⟨progress, hprog⟩ := merc_reduction.signature_refinement.new_worklist_progress_spec
  rw [hprog]
  simp only [bind_tc_ok]
  suffices h : ∃ y, verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop false
      LTSInst sys incoming ctx0 0#usize progress = ok y by
    obtain ⟨y, hy⟩ := h
    rw [hy]
    obtain ⟨a, b, c, d, e, f⟩ := y
    exact ⟨{ partition := a, worklist := b, states := c, builder := d, split_builder := e, state_to_key := f }, by simp⟩
  rw [verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop]
  have hspec : loop (fun x : RunState =>
      verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
        false LTSInst sys incoming progress x.1 x.2) (ctx0, 0#usize) ⦃ _ => True ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : RunState => worklistMeasure n0.val x.1)
      (inv := fun x : RunState => LoopInv n0.val x.1 ∧
        x.2.val + worklistMeasure n0.val x.1 ≤ worklistMeasure n0.val ctx0)
      (post := fun _ => True)
      (body := fun x : RunState =>
        verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
          false LTSInst sys incoming progress x.1 x.2)
      (x := (ctx0, 0#usize))
    · intro x hx
      obtain ⟨hI, hit⟩ := hx
      by_cases hwl : x.1.worklist.val = []
      · have hb : verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
            false LTSInst sys incoming progress x.1 x.2 =
            ok (done (x.1.partition, x.1.worklist, x.1.states, x.1.builder, x.1.split_builder,
              x.1.state_to_key)) := by
          unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
          simp [alloc.vec.Vec.pop_nil_spec Global x.1.worklist hwl]
        exact Std.WP.exists_imp_spec ⟨_, hb, trivial⟩
      · have hne : x.1.worklist.val ≠ [] := hwl
        have hsplit : x.1.worklist.val = x.1.worklist.val.dropLast ++ [x.1.worklist.val.getLast hne] :=
          (List.dropLast_append_getLast hne).symm
        obtain ⟨v', hpop, hv'⟩ := worklist_pop_some x.1.worklist (x.1.worklist.val.getLast hne)
          x.1.worklist.val.dropLast hsplit
        obtain ⟨ctx', hproc, hI', hmeas⟩ := strong_process_worklist_block_step LTSInst sys hwf n0 hns
          incoming hincS x.1 (x.1.worklist.val.getLast hne) v' (by rw [hv']; exact hsplit) hI
        have hlenpos : 1 ≤ x.1.worklist.val.length := List.length_pos_iff.mpr hne
        have hmpos : 1 ≤ worklistMeasure n0.val x.1 := by
          unfold worklistMeasure; omega
        obtain ⟨it1, hadd⟩ := add1_ok_of_lt_max x.2 (by
          have := hM0
          omega)
        have hit1 : it1.val = x.2.val + 1 := usize_add_one_val x.2 it1 hadd
        have hb := strong_run_worklist_loop_body_pop_ext false LTSInst sys incoming progress x.1 ctx'
          (x.1.worklist.val.getLast hne) ⟨v', hpop, hproc⟩ x.2 it1 hadd
        exact Std.WP.exists_imp_spec ⟨cont (ctx', it1), hb, ⟨hI', by simp only []; omega⟩, by simp only []; omega⟩
    · exact ⟨hI0, by simp⟩
  obtain ⟨y, hy, -⟩ := spec_imp_exists hspec
  exact ⟨y, hy⟩

/-- Partial correctness of `strong_run_worklist_loop`: whenever it returns, the result is correct. -/
theorem strong_run_worklist_loop_partial_correct
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0)
    (ctx : WorklistContextStrong)
    (hrun : verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx) :
    ∃ blockOf, WorklistLoopCorrect LTSInst sys ctx blockOf := by
  sorry


/-- Contract of `strong_run_worklist_loop` from the initial context of a well-formed LTS: it
    returns a context whose partition is correct (see `WorklistLoopCorrect`). -/
theorem run_worklist_loop_spec
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0) :
    ∃ ctx blockOf,
      verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
        LTSInst sys incoming ctx0 = ok ctx ∧ WorklistLoopCorrect LTSInst sys ctx blockOf := by
  obtain ⟨ctx, hctx⟩ := strong_run_worklist_loop_terminates LTSInst sys hwf incoming hinc n hns ctx0 hinit
  obtain ⟨blockOf, hb⟩ := strong_run_worklist_loop_partial_correct LTSInst sys hwf incoming hinc n hns ctx0 hinit ctx hctx
  exact ⟨ctx, blockOf, hctx, hb⟩


end MercVerified.Refinement.Proofs
