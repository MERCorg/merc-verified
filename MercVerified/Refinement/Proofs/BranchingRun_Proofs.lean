import MercVerified.Refinement.Proofs.BranchingStep_Proofs
import MercVerified.Refinement.Proofs.RunWorklistLoop_Proofs
import MercVerified.Lts.Proofs.IncomingTransitionsCorrect_Proofs
import Aeneas.Std.WP

/-!
# The outer loop `branching_run_worklist_loop`

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

The loop pops blocks from the worklist and runs `branching_process_worklist_block`, which is a step
of the abstract algorithm (`BranchingStep_Proofs`). It terminates (`bworklistMeasure`), and at exit
the worklist is empty, hence no state is marked, hence the partition is branching bisimilarity
(`Sigref.branchingInv_final`).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)
open verified.merc_reduction.signature_refinement (WorklistContextBranching)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The initial context of `branching_signature_refinement` for a system with `n` states. -/
def BranchingInitial (n : Sz) (ctx0 : WorklistContextBranching) : Prop :=
  ∃ ti : TagIndex Std.Usize BlockTag,
    verified.merc_utilities.tagged_index.TagIndex.new BlockTag 0#usize = ok ti ∧
    alloc.vec.FromVecArray.from (Array.make 1#usize [ti]) = ok ctx0.worklist ∧
    BlockPartition.new n = ok ctx0.partition ∧
    ctx0.state_to_key.val.length = n.val

open verified.merc_reduction.signature_refinement in
/-- With an empty worklist the loop body stops. -/
theorem branching_run_worklist_loop_body_done {L Label : Type}
    (LTSInst : LTS L Label) (sys : L) (incoming : IncomingTransitions)
    (progress : merc_io.progress.TimeProgress (Std.Usize × Std.Usize))
    (ctx : WorklistContextBranching) (it : Std.Usize) (hwl : ctx.worklist.val = []) :
    branching_run_worklist_loop_loop.body LTSInst sys incoming progress ctx it =
      ok (done (ctx.partition, ctx.worklist, ctx.states, ctx.builder, ctx.split_builder,
        ctx.state_to_key)) := by
  unfold branching_run_worklist_loop_loop.body
  simp [alloc.vec.Vec.pop_nil_spec Global ctx.worklist hwl]

open verified.merc_reduction.signature_refinement in
/-- One iteration of the loop body on a non-empty worklist. -/
theorem branching_run_worklist_loop_body_pop {L Label : Type}
    (LTSInst : LTS L Label) (sys : L) (incoming : IncomingTransitions)
    (progress : merc_io.progress.TimeProgress (Std.Usize × Std.Usize))
    (ctx ctx' : WorklistContextBranching) (b : TagIndex Std.Usize BlockTag)
    (w : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (it iteration1 : Std.Usize)
    (hpop : alloc.vec.Vec.pop Global ctx.worklist = ok (some b, w))
    (hproc : branching_process_worklist_block LTSInst sys incoming { ctx with worklist := w } b =
      ok ctx')
    (hadd : it + 1#usize = ok iteration1) :
    branching_run_worklist_loop_loop.body LTSInst sys incoming progress ctx it =
      ok (cont (ctx', iteration1)) := by
  unfold branching_run_worklist_loop_loop.body
  simp [hpop]
  rw [hproc, hadd]
  simp [verified.merc_reduction.block_partition.BlockPartition.num_of_blocks,
    merc_io.progress.TimeProgress.print_spec]

/-- The initial context satisfies the loop invariant, with a measure of at most `n * (n + 2)`. -/
theorem branching_initial_inv {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Sz)
    (hn : 0 < n.val) (ctx0 : WorklistContextBranching) (hinit : BranchingInitial n ctx0) :
    BrLoopInv LTSInst sys n.val ctx0 ∧ bworklistMeasure n.val ctx0 ≤ n.val * (n.val + 2) := by
  obtain ⟨ti, hti, hwl, hpart, hlen⟩ := hinit
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
  have hwv : ctx0.worklist.val = [({ index := 0#usize, marker := () } : BT)] := by
    simp [alloc.vec.FromVecArray.from, Array.make] at hwl
    rw [← hwl]; simp [alloc.vec.Vec.from_val]
  have hblk : blkAt p 0 = { begin := 0#usize, marked_split := 0#usize, «end» := n } := by
    simp [blkAt, hbl]
  have hzero : ∀ t : ST, t.index.val < n.val → e2bAt p t.index.val = 0 := by
    intro t ht
    have hlt := (hPI.own t.index.val ht).1
    rw [hN] at hlt
    omega
  have hqueued : ∀ t : ST, t.index.val < n.val → IsMarked ctx0.partition t.index.val →
      ∃ x ∈ ctx0.worklist.val, x.index.val = e2bAt ctx0.partition t.index.val := by
    intro t ht _
    refine ⟨({ index := 0#usize, marker := () } : BT), by rw [hwv]; simp, ?_⟩
    rw [hp, hzero t ht]; rfl
  refine ⟨⟨⟨by rw [hp]; exact hPI, ?_, ?_⟩, hlen, hqueued, ?_⟩, ?_⟩
  · rw [hwv]; simp
  · intro x hx
    rw [hwv] at hx
    simp at hx; subst hx
    rw [hp]
    refine ⟨by rw [hN]; show 0 < 1; omega, ?_⟩
    show (blkAt p 0).marked_split.val < (blkAt p 0).«end».val
    rw [hblk]; simpa using hn
  · have hnm : n.val ≤ Usize.max := by scalar_tac
    have hzeroF : ∀ x : Fin n.val, e2bAt p x.val = 0 := fun x => by
      have := hzero (stOf x) (by rw [stOf_index _ hnm]; exact x.2)
      rwa [stOf_index _ hnm] at this
    have hcfg : cfgOf ctx0.partition n.val = Sigref.initConfig (Fin n.val) := by
      rw [hp]
      have h1 : (bdOf p n.val).setoid = Sigref.topSetoid (Fin n.val) :=
        Setoid.ext fun x y => by
          show e2bAt p x.val = e2bAt p y.val ↔ True
          rw [hzeroF x, hzeroF y]
          exact iff_of_true rfl trivial
      have h2 : {x : Fin n.val | IsMarked p x.val} = Set.univ :=
        Set.eq_univ_of_forall fun x => by
          show IsMarked p x.val
          unfold IsMarked
          rw [hzeroF x, hblk]
          exact Nat.zero_le _
      show (⟨(bdOf p n.val).setoid, {x | IsMarked p x.val}⟩ : Sigref.Config (Fin n.val)) =
        ⟨Sigref.topSetoid (Fin n.val), Set.univ⟩
      rw [h1, h2]
    rw [hcfg]
    exact Sigref.branchingInv_init _
  · unfold bworklistMeasure
    rw [hp, hN, hwv]
    simp only [List.length_singleton]
    have h1 : (n.val - 1) * (n.val + 1) ≤ n.val * (n.val + 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    nlinarith

abbrev BRunState := WorklistContextBranching × Std.Usize

open verified.merc_reduction.signature_refinement in
/-- Termination of `branching_run_worklist_loop` from the initial context, carrying the loop
invariant to the returned context, whose worklist is empty. -/
theorem branching_run_worklist_loop_terminates {L Label : Type}
    (LTSInst : LTS L Label) (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : IncomingTransitions) (hIC : MercVerified.Lts.IncomingTransitionsCorrect LTSInst sys incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    {nl : Std.Usize} (hE : CEnv LTSInst sys nl) (htopo : ConcTopo LTSInst sys)
    (hsil : IncSilent LTSInst sys n.val incoming)
    (ctx0 : WorklistContextBranching) (hinit : BranchingInitial n ctx0) :
    ∃ ctx, branching_run_worklist_loop LTSInst sys incoming ctx0 = ok ctx ∧
      BrLoopInv LTSInst sys n.val ctx ∧ ctx.worklist.val = [] := by
  obtain ⟨n0, hn0, hnpos⟩ := hwf.1
  have hnn : n0 = n := by
    have := hn0.symm.trans hns; simpa using this
  subst hnn
  have hincS : ∀ s : ST, s.index.val < n0.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n0.val := fun s hs => by
    obtain ⟨res, h1, h2, -⟩ := hIC n0 hns s hs
    exact ⟨res, h1, h2⟩
  have hmemc : ∀ s : ST, s.index.val < n0.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
      ∀ i : FromTransition, i ∈ res.val ↔ ∃ (μ : TagIndex Std.Usize LabelTag) (s' : ST),
        s'.index.val < n0.val ∧ MercVerified.Lts.tr LTSInst sys s' μ s ∧
          (i.label, i.«from») = (μ, s') := fun s hs => by
    obtain ⟨res, h1, -, h3⟩ := hIC n0 hns s hs
    exact ⟨res, h1, h3⟩
  obtain ⟨hI0, hM0⟩ := branching_initial_inv LTSInst sys n0 hnpos ctx0 hinit
  have hn2 := hfit n0 hns
  have hnmax : n0.val ≤ Usize.max := by scalar_tac
  unfold branching_run_worklist_loop
  obtain ⟨progress, hprog⟩ := merc_reduction.signature_refinement.new_worklist_progress_spec
  rw [hprog]
  simp only [bind_ok]
  suffices h : ∃ y, branching_run_worklist_loop_loop LTSInst sys incoming ctx0 0#usize progress =
      ok y ∧ ∃ ctx' : WorklistContextBranching,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ BrLoopInv LTSInst sys n0.val ctx' ∧ ctx'.worklist.val = [] by
    obtain ⟨y, hy, ctx', hyeq, hI', hwl'⟩ := h
    refine ⟨ctx', ?_, hI', hwl'⟩
    rw [hy, hyeq]
    simp
  rw [branching_run_worklist_loop_loop]
  have hspec : loop (fun x : BRunState =>
      branching_run_worklist_loop_loop.body LTSInst sys incoming progress x.1 x.2) (ctx0, 0#usize)
      ⦃ fun y => ∃ ctx' : WorklistContextBranching,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ BrLoopInv LTSInst sys n0.val ctx' ∧ ctx'.worklist.val = [] ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : BRunState => bworklistMeasure n0.val x.1)
      (inv := fun x : BRunState => BrLoopInv LTSInst sys n0.val x.1 ∧
        x.2.val + bworklistMeasure n0.val x.1 ≤ bworklistMeasure n0.val ctx0)
      (post := fun y => ∃ ctx' : WorklistContextBranching,
        y = (ctx'.partition, ctx'.worklist, ctx'.states, ctx'.builder, ctx'.split_builder,
          ctx'.state_to_key) ∧ BrLoopInv LTSInst sys n0.val ctx' ∧ ctx'.worklist.val = [])
      (body := fun x : BRunState =>
        branching_run_worklist_loop_loop.body LTSInst sys incoming progress x.1 x.2)
      (x := (ctx0, 0#usize))
    · intro x hx
      obtain ⟨hI, hit⟩ := hx
      by_cases hwl : x.1.worklist.val = []
      · have hb := branching_run_worklist_loop_body_done LTSInst sys incoming progress x.1 x.2 hwl
        exact Std.WP.exists_imp_spec ⟨_, hb, ⟨x.1, rfl, hI, hwl⟩⟩
      · have hne : x.1.worklist.val ≠ [] := hwl
        have hsplit : x.1.worklist.val =
            x.1.worklist.val.dropLast ++ [x.1.worklist.val.getLast hne] :=
          (List.dropLast_append_getLast hne).symm
        obtain ⟨v', hpop, hv'⟩ := worklist_pop_some x.1.worklist (x.1.worklist.val.getLast hne)
          x.1.worklist.val.dropLast hsplit
        obtain ⟨ctx', hproc, hI', -, hmeas⟩ := branching_worklist_step_struct LTSInst sys hwf hfit n0
          hns hnpos hE htopo incoming hincS hsil hmemc x.1 (x.1.worklist.val.getLast hne) v'
          (by rw [hv']; exact hsplit) hI
        have hlenpos : 1 ≤ x.1.worklist.val.length := List.length_pos_iff.mpr hne
        have hmpos : 1 ≤ bworklistMeasure n0.val x.1 := by
          unfold bworklistMeasure; omega
        obtain ⟨it1, hadd⟩ := add1_ok_of_lt_max x.2 (by
          have := hM0
          omega)
        have hit1 : it1.val = x.2.val + 1 := usize_add_one_val x.2 it1 hadd
        have hb := branching_run_worklist_loop_body_pop LTSInst sys incoming progress x.1 ctx'
          (x.1.worklist.val.getLast hne) v' x.2 it1 hpop hproc hadd
        exact Std.WP.exists_imp_spec ⟨cont (ctx', it1), hb, ⟨hI', by simp only []; omega⟩,
          by simp only []; omega⟩
    · exact ⟨hI0, by simp⟩
  obtain ⟨y, hy, hpost⟩ := spec_imp_exists hspec
  exact ⟨y, hy, hpost⟩

/-- **Partial and total correctness of `branching_run_worklist_loop`** from the initial context:
it terminates, and two states of `Fin n` are in the same block of the resulting partition exactly
when they are branching bisimilar. -/
theorem branching_run_worklist_loop_spec {L Label : Type}
    (LTSInst : LTS L Label) (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : IncomingTransitions) (hIC : MercVerified.Lts.IncomingTransitionsCorrect LTSInst sys incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    {nl : Std.Usize} (hE : CEnv LTSInst sys nl) (htopo : ConcTopo LTSInst sys)
    (hsil : IncSilent LTSInst sys n.val incoming)
    (ctx0 : WorklistContextBranching) (hinit : BranchingInitial n ctx0) :
    ∃ ctx, verified.merc_reduction.signature_refinement.branching_run_worklist_loop LTSInst sys
        incoming ctx0 = ok ctx ∧ PartInv n.val ctx.partition ∧
      ∀ s t : Fin n.val, e2bAt ctx.partition s.val = e2bAt ctx.partition t.val ↔
        BranchingBisimilarity (aLTS LTSInst sys n.val) s t := by
  obtain ⟨ctx, hrun, hI, hwl⟩ := branching_run_worklist_loop_terminates LTSInst sys hwf hfit incoming
    hIC n hns hE htopo hsil ctx0 hinit
  refine ⟨ctx, hrun, hI.dirty.1, fun s t => ?_⟩
  have hn2 := hfit n hns
  have hnmax : n.val ≤ Usize.max := by scalar_tac
  have hX : ∀ x, x ∉ (cfgOf ctx.partition n.val).X := by
    intro x hx
    obtain ⟨y, hy, -⟩ := hI.queued (stOf x) (by rw [stOf_index _ hnmax]; exact x.2)
      (by rw [stOf_index _ hnmax]; exact hx)
    rw [hwl] at hy; simp at hy
  exact Sigref.branchingInv_final _ hI.sem hX s t

end MercVerified.Refinement.Proofs
