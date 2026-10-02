import MercVerified.Refinement.Proofs.WorklistStep_Proofs
import MercVerified.Refinement.Proofs.WorklistLoopCorrect_Proofs
import MercVerified.Lts.Proofs.IncomingTransitionsCorrect_Proofs
import Signatures.Proofs.Signature_Proofs
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

/-- The `resize_with` closure of `strong_signature_refinement` never fails: it just builds the
    block index `0`. -/
theorem resize_closure_total {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) :
    core.ops.function.FnMut.IsTotal
      (verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag
        LTSInst) := by
  intro c
  obtain ⟨ti, hti⟩ := merc_utilities.tagged_index.TagIndex.new_spec (T := Std.Usize) BlockTag 0#usize
  refine ⟨(ti, c), ?_⟩
  show verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag.call_mut LTSInst c () = _
  unfold verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag.call_mut
  rw [hti, bind_ok]

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
      LTSInst) (resize_closure_total LTSInst)
    (alloc.vec.Vec.new (TagIndex Std.Usize BlockTag)) n ()
  have hw' : w = ctx0.state_to_key := by
    have := hw.symm.trans hres; simpa using this
  subst hw'
  have hwv : ctx0.worklist.val = [({ index := 0#usize, marker := () } : BT)] := by
    simp [alloc.vec.FromVecArray.from, Array.make] at hwl
    rw [← hwl]; simp [alloc.vec.Vec.from_val]
  have hblk : blkAt p 0 = { begin := 0#usize, marked_split := 0#usize, «end» := n } := by
    simp [blkAt, hbl]
  refine ⟨⟨⟨by rw [hp]; exact hPI, ?_, ?_⟩, hwlen, ?_⟩, ?_⟩
  · rw [hwv]; simp
  · intro x hx
    rw [hwv] at hx
    simp at hx; subst hx
    rw [hp]
    refine ⟨by rw [hN]; show 0 < 1; omega, ?_⟩
    show (blkAt p 0).marked_split.val < (blkAt p 0).«end».val
    rw [hblk]; simpa using hn
  · intro t ht _
    refine ⟨({ index := 0#usize, marker := () } : BT), by rw [hwv]; simp, ?_⟩
    rw [hp]
    have hlt := (hPI.own t.index.val ht).1
    rw [hN] at hlt
    show (0 : Nat) = e2bAt p t.index.val
    omega
  · unfold worklistMeasure numBlocks
    rw [hp, hN, hwv]
    simp only [List.length_singleton]
    have h1 : (n.val - 1) * (n.val + 1) ≤ n.val * (n.val + 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    nlinarith


/-- The loop state of `strong_run_worklist_loop_loop`. -/
abbrev RunState := WorklistContextStrong × Std.Usize

/-- Termination of `strong_run_worklist_loop` from the initial context of a well-formed LTS,
    carrying the loop invariant (hence `PartInv`) through to the returned context: the loop only
    exits once the worklist is empty, so the exit case of `loop.spec_decr_nat`'s postcondition can
    keep `LoopInv` instead of discarding it as `True`. -/
theorem strong_run_worklist_loop_terminates'
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0) :
    ∃ ctx, verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx ∧ LoopInv n.val ctx ∧ ctx.worklist.val = [] := by
  obtain ⟨n0, hn0, hnpos⟩ := hwf.1
  have hnn : n0 = n := by
    have := hn0.symm.trans hns; simpa using this
  subst hnn
  have hIC := MercVerified.Lts.Proofs.incoming_transitions_correct LTSInst sys hwf hfit incoming hinc
  have hincS : ∀ s : ST, s.index.val < n0.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n0.val := fun s hs => by
    obtain ⟨res, h1, h2, -⟩ := hIC n0 hns s hs
    exact ⟨res, h1, h2⟩
  obtain ⟨hI0, hM0⟩ := initial_loopInv LTSInst n0 hnpos ctx0 hinit
  have hn2 := hfit n0 hns
  have hnmax : n0.val ≤ Usize.max := by scalar_tac
  unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop
  obtain ⟨progress, hprog⟩ := merc_reduction.signature_refinement.new_worklist_progress_spec
  rw [hprog]
  simp only [bind_ok]
  suffices h : ∃ y, verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop false
      LTSInst sys incoming ctx0 0#usize progress = ok y ∧
      ∃ ctx' : WorklistContextStrong,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ LoopInv n0.val ctx' ∧ ctx'.worklist.val = [] by
    obtain ⟨y, hy, ctx', hyeq, hI', hwl'⟩ := h
    refine ⟨ctx', ?_, hI', hwl'⟩
    rw [hy, hyeq]
    simp
  rw [verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop]
  have hspec : loop (fun x : RunState =>
      verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
        false LTSInst sys incoming progress x.1 x.2) (ctx0, 0#usize)
      ⦃ fun y => ∃ ctx' : WorklistContextStrong,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ LoopInv n0.val ctx' ∧ ctx'.worklist.val = [] ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : RunState => worklistMeasure n0.val x.1)
      (inv := fun x : RunState => LoopInv n0.val x.1 ∧
        x.2.val + worklistMeasure n0.val x.1 ≤ worklistMeasure n0.val ctx0)
      (post := fun y => ∃ ctx' : WorklistContextStrong,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ LoopInv n0.val ctx' ∧ ctx'.worklist.val = [])
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
        exact Std.WP.exists_imp_spec ⟨_, hb, ⟨x.1, rfl, hI, hwl⟩⟩
      · have hne : x.1.worklist.val ≠ [] := hwl
        have hsplit : x.1.worklist.val = x.1.worklist.val.dropLast ++ [x.1.worklist.val.getLast hne] :=
          (List.dropLast_append_getLast hne).symm
        obtain ⟨v', hpop, hv'⟩ := worklist_pop_some x.1.worklist (x.1.worklist.val.getLast hne)
          x.1.worklist.val.dropLast hsplit
        obtain ⟨ctx', hproc, hI', hmeas⟩ := strong_process_worklist_block_step LTSInst sys hwf hfit n0 hns
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
  obtain ⟨y, hy, hpost⟩ := spec_imp_exists hspec
  exact ⟨y, hy, hpost⟩

/-- Termination of `strong_run_worklist_loop` from the initial context of a well-formed LTS. -/
theorem strong_run_worklist_loop_terminates
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0) :
    ∃ ctx, verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx := by
  obtain ⟨ctx, hctx, -, -⟩ := strong_run_worklist_loop_terminates' LTSInst sys hwf hfit incoming hinc n hns
    ctx0 hinit
  exact ⟨ctx, hctx⟩

/-- Termination of `strong_run_worklist_loop`, additionally carrying `RefinesQ Q` (for an arbitrary
    `Q`-stable partition) through to the returned context: a copy of
    `strong_run_worklist_loop_terminates'`'s own proof, using `strong_process_worklist_block_step_RQ`
    (`WorklistLoopCorrect_Proofs.lean`) instead of the plain `strong_process_worklist_block_step` at
    each iteration. -/
theorem strong_run_worklist_loop_RefinesQ
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0)
    {Block : Type} (Q : ST → Block)
    (hQstable : IsStable (fun s => StrongSignature (MercVerified.Lts.toLTS LTSInst sys) s Q) Q) :
    ∃ ctx, verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx ∧ LoopInv n.val ctx ∧ ctx.worklist.val = [] ∧
      RefinesQ Q n.val ctx.partition ∧ SettledStable LTSInst sys n.val ctx.partition := by
  obtain ⟨n0, hn0, hnpos⟩ := hwf.1
  have hnn : n0 = n := by
    have := hn0.symm.trans hns; simpa using this
  subst hnn
  have hIC := MercVerified.Lts.Proofs.incoming_transitions_correct LTSInst sys hwf hfit incoming hinc
  have hincS : ∀ s : ST, s.index.val < n0.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n0.val := fun s hs => by
    obtain ⟨res, h1, h2, -⟩ := hIC n0 hns s hs
    exact ⟨res, h1, h2⟩
  obtain ⟨hI0, hM0⟩ := initial_loopInv LTSInst n0 hnpos ctx0 hinit
  have hRQ0 : RefinesQ Q n0.val ctx0.partition := RefinesQ.initial LTSInst n0 hnpos ctx0 hinit Q
  have hSS0 : SettledStable LTSInst sys n0.val ctx0.partition :=
    SettledStable.initial LTSInst sys n0 hnpos ctx0 hinit
  have hn2 := hfit n0 hns
  have hnmax : n0.val ≤ Usize.max := by scalar_tac
  unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop
  obtain ⟨progress, hprog⟩ := merc_reduction.signature_refinement.new_worklist_progress_spec
  rw [hprog]
  simp only [bind_ok]
  suffices h : ∃ y, verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop false
      LTSInst sys incoming ctx0 0#usize progress = ok y ∧
      ∃ ctx' : WorklistContextStrong,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ LoopInv n0.val ctx' ∧ ctx'.worklist.val = [] ∧
          RefinesQ Q n0.val ctx'.partition ∧ SettledStable LTSInst sys n0.val ctx'.partition by
    obtain ⟨y, hy, ctx', hyeq, hI', hwl', hRQ', hSS'⟩ := h
    refine ⟨ctx', ?_, hI', hwl', hRQ', hSS'⟩
    rw [hy, hyeq]
    simp
  rw [verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop]
  have hspec : loop (fun x : RunState =>
      verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
        false LTSInst sys incoming progress x.1 x.2) (ctx0, 0#usize)
      ⦃ fun y => ∃ ctx' : WorklistContextStrong,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ LoopInv n0.val ctx' ∧ ctx'.worklist.val = [] ∧
          RefinesQ Q n0.val ctx'.partition ∧ SettledStable LTSInst sys n0.val ctx'.partition ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : RunState => worklistMeasure n0.val x.1)
      (inv := fun x : RunState => LoopInv n0.val x.1 ∧ RefinesQ Q n0.val x.1.partition ∧
        SettledStable LTSInst sys n0.val x.1.partition ∧
        x.2.val + worklistMeasure n0.val x.1 ≤ worklistMeasure n0.val ctx0)
      (post := fun y => ∃ ctx' : WorklistContextStrong,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ LoopInv n0.val ctx' ∧ ctx'.worklist.val = [] ∧
          RefinesQ Q n0.val ctx'.partition ∧ SettledStable LTSInst sys n0.val ctx'.partition)
      (body := fun x : RunState =>
        verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
          false LTSInst sys incoming progress x.1 x.2)
      (x := (ctx0, 0#usize))
    · intro x hx
      obtain ⟨hI, hRQx, hSSx, hit⟩ := hx
      by_cases hwl : x.1.worklist.val = []
      · have hb : verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
            false LTSInst sys incoming progress x.1 x.2 =
            ok (done (x.1.partition, x.1.worklist, x.1.states, x.1.builder, x.1.split_builder,
              x.1.state_to_key)) := by
          unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
          simp [alloc.vec.Vec.pop_nil_spec Global x.1.worklist hwl]
        exact Std.WP.exists_imp_spec ⟨_, hb, ⟨x.1, rfl, hI, hwl, hRQx, hSSx⟩⟩
      · have hne : x.1.worklist.val ≠ [] := hwl
        have hsplit : x.1.worklist.val = x.1.worklist.val.dropLast ++ [x.1.worklist.val.getLast hne] :=
          (List.dropLast_append_getLast hne).symm
        obtain ⟨v', hpop, hv'⟩ := worklist_pop_some x.1.worklist (x.1.worklist.val.getLast hne)
          x.1.worklist.val.dropLast hsplit
        obtain ⟨ctx', hproc, hI', hmeas, hRQ', hSS'⟩ := strong_process_worklist_block_step_RQ LTSInst sys
          hwf hfit n0 hns incoming hIC hincS x.1 (x.1.worklist.val.getLast hne) v'
          (by rw [hv']; exact hsplit) hI Q hQstable hRQx hSSx
        have hlenpos : 1 ≤ x.1.worklist.val.length := List.length_pos_iff.mpr hne
        have hmpos : 1 ≤ worklistMeasure n0.val x.1 := by
          unfold worklistMeasure; omega
        obtain ⟨it1, hadd⟩ := add1_ok_of_lt_max x.2 (by
          have := hM0
          omega)
        have hit1 : it1.val = x.2.val + 1 := usize_add_one_val x.2 it1 hadd
        have hb := strong_run_worklist_loop_body_pop_ext false LTSInst sys incoming progress x.1 ctx'
          (x.1.worklist.val.getLast hne) ⟨v', hpop, hproc⟩ x.2 it1 hadd
        exact Std.WP.exists_imp_spec
          ⟨cont (ctx', it1), hb, ⟨hI', hRQ', hSS', by simp only []; omega⟩, by simp only []; omega⟩
    · exact ⟨hI0, hRQ0, hSS0, by simp⟩
  obtain ⟨y, hy, hpost⟩ := spec_imp_exists hspec
  exact ⟨y, hy, hpost⟩

/-- Partial correctness of `strong_run_worklist_loop`: whenever it returns, the result is correct. -/
theorem strong_run_worklist_loop_partial_correct
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0)
    (ctx : WorklistContextStrong)
    (hrun : verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx) :
    ∃ blockOf, WorklistLoopCorrect LTSInst sys ctx blockOf := by
  obtain ⟨ctx', hctx', hI, hwlnil⟩ :=
    strong_run_worklist_loop_terminates' LTSInst sys hwf hfit incoming hinc n hns ctx0 hinit
  have hctxeq : ctx = ctx' := by have := hrun.symm.trans hctx'; simpa using this
  subst hctxeq
  obtain ⟨⟨hp, -, -⟩, -, hmark⟩ := hI
  refine ⟨blockFn ctx.partition, ?_, ?_, ?_, ?_⟩
  · -- coherence: `blockFn` reads `element_to_block` directly.
    intro s b _ hb
    simp [blockFn, List.getD_eq_getElem?_getD, hb]
  · -- coverage: every in-range state is `elements`'s inverse image under its own offset.
    intro n' hn' s hs
    have hnn' : n' = n := by have := hn'.symm.trans hns; simpa using this
    subst hnn'
    have hown := hp.own s.index.val hs
    have hblk := hp.blk (e2bAt ctx.partition s.index.val) hown.1
    have hoff_lt : offAt ctx.partition s.index.val < n'.val := by omega
    have hmem : eAt ctx.partition (offAt ctx.partition s.index.val) ∈ ctx.partition.elements.val := by
      unfold eAt
      rw [List.getD_eq_getElem _ _ (by rw [hp.len_e]; exact hoff_lt)]
      exact List.getElem_mem _
    have heq : eAt ctx.partition (offAt ctx.partition s.index.val) = s :=
      merc_utilities.tagged_index.TagIndex.ext
        (UScalar.eq_of_val_eq (hp.inv s.index.val hs))
    rwa [heq] at hmem
  · -- stability/soundness: `SettledStable` never mentions `Q`, so any `Q` (e.g. the identity, which
    -- trivially satisfies `IsStable` for any signature) suffices to pull it out of
    -- `strong_run_worklist_loop_RefinesQ`. At loop exit the worklist is empty, so `LoopInv`'s marking
    -- conjunct forces both `s` and `s'` unmarked, and `SettledStable` gives exactly this conjunct.
    intro n' hn' s s' hs hs' hbeq
    have hnn' : n' = n := by have := hn'.symm.trans hns; simpa using this
    rw [hnn'] at hs hs'
    obtain ⟨ctx2, hctx2, -, -, -, hSS2⟩ :=
      strong_run_worklist_loop_RefinesQ LTSInst sys hwf hfit incoming hinc n hns ctx0 hinit
        (fun s : ST => s) (fun s s' (h : s = s') => by subst h; rfl)
    have hctx2eq : ctx2 = ctx := by have := hctx2.symm.trans hrun; simpa using this
    rw [hctx2eq] at hSS2
    have hm : ¬ IsMarked ctx.partition s.index.val := fun hmarked => by
      obtain ⟨x, hx, -⟩ := hmark s hs hmarked
      rw [hwlnil] at hx; simp at hx
    have hm' : ¬ IsMarked ctx.partition s'.index.val := fun hmarked => by
      obtain ⟨x, hx, -⟩ := hmark s' hs' hmarked
      rw [hwlnil] at hx; simp at hx
    exact hSS2 s s' hs hs' hbeq hm hm'
  · -- completeness w.r.t. `StrongFixPoint`: unpack the stable partition `Q` witnessing the
    -- hypothesis, carry `RefinesQ Q` to loop exit via `strong_run_worklist_loop_RefinesQ`, and
    -- identify its context with `ctx` by determinism (both come from running the same
    -- `strong_run_worklist_loop` on the same `ctx0`).
    intro n' hn' s s' hs hs' hSFP
    have hnn' : n' = n := by have := hn'.symm.trans hns; simpa using this
    rw [hnn'] at hs hs'
    obtain ⟨Block, Q, hQstable, hQeq⟩ := hSFP
    obtain ⟨ctx2, hctx2, -, -, hRQ2, -⟩ :=
      strong_run_worklist_loop_RefinesQ LTSInst sys hwf hfit incoming hinc n hns ctx0 hinit Q hQstable
    have hctx2eq : ctx2 = ctx := by have := hctx2.symm.trans hrun; simpa using this
    rw [← hctx2eq]
    exact (hRQ2 s s' hs hs' hQeq).1


/-- Contract of `strong_run_worklist_loop` from the initial context of a well-formed LTS: it
    returns a context whose partition is correct (see `WorklistLoopCorrect`). -/
theorem run_worklist_loop_spec
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0) :
    ∃ ctx blockOf,
      verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
        LTSInst sys incoming ctx0 = ok ctx ∧ WorklistLoopCorrect LTSInst sys ctx blockOf := by
  obtain ⟨ctx, hctx⟩ := strong_run_worklist_loop_terminates LTSInst sys hwf hfit incoming hinc n hns ctx0 hinit
  obtain ⟨blockOf, hb⟩ := strong_run_worklist_loop_partial_correct LTSInst sys hwf hfit incoming hinc n hns ctx0 hinit ctx hctx
  exact ⟨ctx, blockOf, hctx, hb⟩


end MercVerified.Refinement.Proofs
