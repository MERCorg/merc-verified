import MercVerified.Signatures.Refinement
import MercVerified.Signatures.Proofs.StrongSignature_Proofs
import MercVerified.Signatures.Proofs.Partition_Proofs
import Aeneas.Std.WP

/-!
# Proofs about the `strong_run_worklist_loop` worklist loop

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

These lemmas reason about the *translated body* of
`strong_run_worklist_loop_loop` (in `MercVerified/Code/Funs.lean`) rather than
about the `run_worklist_loop_spec` contract axiom in `MercVerified/Basic.lean`.
The goal is to replace that axiom with a proof.

- `strong_run_worklist_loop_loop_base`: if the worklist is empty, the loop
  terminates immediately (`Vec::pop` returns `None`) and leaves the context
  untouched.
- `strong_run_worklist_loop_base`: the wrapper sees the same behaviour.
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition)
open verified.merc_lts.incoming_transitions (IncomingTransitions)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)
open verified.merc_reduction.signature_refinement (WorklistContextStrong)

namespace MercVerified.Signatures.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option allowUnsafeReducibility true
attribute [local reducible] Aeneas.Std.WP.Post
attribute [local reducible] alloc.vec.into_iter.IntoIter

/-- The loop state: the worklist context paired with the iteration counter. -/
private abbrev WLS := WorklistContextStrong × Std.Usize

/-- The result of one completed `loop` run: a 6-tuple holding the fields of the
    final worklist context (the `done` value of the `ControlFlow`). -/
private abbrev Bounds :=
  BlockPartition ×
  (alloc.vec.Vec (TagIndex Std.Usize BlockTag)) ×
  (alloc.vec.Vec (TagIndex Std.Usize StateTag)) ×
  (alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag))) ×
  BlockPartitionBuilder ×
  (alloc.vec.Vec (TagIndex Std.Usize BlockTag))

/-- If the worklist is empty, the `strong_run_worklist_loop` loop terminates
    immediately (`Vec::pop` returns `None`), leaving the context untouched - for
    any progress ticker, iteration counter and `BRANCHING` flag. -/
theorem strong_run_worklist_loop_loop_base
    (BRANCHING : Bool)
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (progress : merc_io.progress.TimeProgress (Std.Usize × Std.Usize))
    (ctx : WorklistContextStrong)
    (hwl : ctx.worklist.val = [])
    (it : Std.Usize) :
    verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop
      BRANCHING LTSInst sys incoming ctx it progress = ok
      (ctx.partition, ctx.worklist, ctx.states, ctx.builder, ctx.split_builder, ctx.state_to_key) := by
  rw [verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop]
  let post : Bounds → Prop :=
    fun b => b = (ctx.partition, ctx.worklist, ctx.states, ctx.builder, ctx.split_builder, ctx.state_to_key)
  have hspec :
      loop (fun x : WLS =>
        verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
          BRANCHING LTSInst sys incoming progress x.1 x.2)
        (ctx, it) ⦃ b => post b ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun _ : WLS => 0)
      (inv := fun x : WLS => x.1 = ctx)
      (post := post)
      (body := fun x : WLS =>
        verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
          BRANCHING LTSInst sys incoming progress x.1 x.2)
      (x := (ctx, it))
    · intro x hx
      have hc : x.1 = ctx := hx
      rw [hc]
      unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
      have hnext : alloc.vec.Vec.pop Global ctx.worklist
          ⦃ o v => o = none ∧ v = ctx.worklist ⦄ := by
        rw [alloc.vec.Vec.pop_nil_spec Global ctx.worklist hwl]
        simp [spec_ok]
      apply spec_bind hnext
      intro y hy
      rcases y with ⟨o, v⟩
      simp at hy
      rcases hy with ⟨ho, hv⟩
      subst o
      subst v
      simp [spec_ok, post]
    · rfl
  rcases (spec_imp_exists hspec) with ⟨y, hy, hpost⟩
  rw [hy]
  rw [hpost]

/-- With an empty initial worklist, `strong_run_worklist_loop` returns the
    context unchanged. -/
theorem strong_run_worklist_loop_base
    (BRANCHING : Bool)
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (ctx : WorklistContextStrong)
    (hwl : ctx.worklist.val = []) :
    verified.merc_reduction.signature_refinement.strong_run_worklist_loop
      BRANCHING LTSInst sys incoming ctx = ok ctx := by
  unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop
  rcases (merc_reduction.signature_refinement.new_worklist_progress_spec)
    with ⟨progress, hprog⟩
  rw [hprog]
  simp
  rw [show verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop
        BRANCHING LTSInst sys incoming ctx (0#usize) progress = ok
        (ctx.partition, ctx.worklist, ctx.states, ctx.builder, ctx.split_builder, ctx.state_to_key)
    from strong_run_worklist_loop_loop_base BRANCHING LTSInst sys incoming progress ctx hwl (0#usize)]
  simp

/-- One iteration of the worklist loop on a *non-empty* worklist: if
    `Vec::pop` returns the last block `b` (leaving `w`), and processing that
    block via `strong_process_worklist_block` succeeds with context `ctx'`,
    then the loop body returns `cont (ctx', iteration + 1)` - exactly the
    continuation the loop induction will walk. This holds for any progress
    ticker: the `TimeProgress.print` call never fails. -/
theorem strong_run_worklist_loop_body_pop
    (BRANCHING : Bool)
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (progress : merc_io.progress.TimeProgress (Std.Usize × Std.Usize))
    (ctx : WorklistContextStrong)
    (b : TagIndex Std.Usize BlockTag)
    (w : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (ctx' : WorklistContextStrong)
    (it iteration1 : Std.Usize)
    (hpop : alloc.vec.Vec.pop Global ctx.worklist = ok (some b, w))
    (hproc :
      verified.merc_reduction.signature_refinement.strong_process_worklist_block
        BRANCHING LTSInst sys incoming { ctx with worklist := w } b = ok ctx')
    (hadd : it + 1#usize = ok iteration1) :
    verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
      BRANCHING LTSInst sys incoming progress ctx it =
      ok (cont (ctx', iteration1)) := by
  unfold verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
  simp [hpop]
  rw [hproc, hadd]
  simp [verified.merc_reduction.block_partition.BlockPartition.num_of_blocks,
    merc_io.progress.TimeProgress.print_spec]

/-- `Vec::pop` on a vector of the form `rest ++ [x]` returns exactly `x` and a
    vector with contents `rest` (witness packaging of
    `alloc.vec.Vec.pop_cons_spec`). -/
theorem worklist_pop_some {T : Type} (v : alloc.vec.Vec T) (x : T) (rest : List T)
    (h : v.val = rest ++ [x]) :
    ∃ v' : alloc.vec.Vec T,
      alloc.vec.Vec.pop Global v = ok (some x, v') ∧ v'.val = rest :=
  alloc.vec.Vec.pop_cons_spec Global v x rest h

/-- Same as `strong_run_worklist_loop_body_pop`, but with the pop/process
    results bundled into a single existential witness `w` (the shape that will
    arise in the loop induction from `worklist_pop_some`). -/
theorem strong_run_worklist_loop_body_pop_ext
    (BRANCHING : Bool)
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (progress : merc_io.progress.TimeProgress (Std.Usize × Std.Usize))
    (ctx ctx' : WorklistContextStrong)
    (b : TagIndex Std.Usize BlockTag)
    (hpop : ∃ w : alloc.vec.Vec (TagIndex Std.Usize BlockTag),
        alloc.vec.Vec.pop Global ctx.worklist = ok (some b, w) ∧
        (verified.merc_reduction.signature_refinement.strong_process_worklist_block
          BRANCHING LTSInst sys incoming { ctx with worklist := w } b = ok ctx'))
    (it iteration1 : Std.Usize) (hadd : it + 1#usize = ok iteration1) :
    verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body
      BRANCHING LTSInst sys incoming progress ctx it =
      ok (cont (ctx', iteration1)) := by
  rcases hpop with ⟨w, hp, hproc⟩
  exact strong_run_worklist_loop_body_pop
    BRANCHING LTSInst sys incoming progress ctx b w ctx' it iteration1 hp hproc hadd

/-!
# Termination of the worklist loop

Derived from the Rust source (`signature_refinement.rs:842-903`,
`block_partition.rs:144-283`). One loop iteration pops block `b`, then:

1. `strong_process_marked_elements` recomputes the strong signature of each
   marked state of `b` (the `[marked_split, end)` tail) and, through
   `finish_partition_marked`, moves these states into fresh blocks above
   `end_of_blocks` (or back into `b` when it has no unmarked part and the
   states form a single signature class). Unmarked states stay in `b`.
2. `mark_dirty_new_blocks`/`mark_dirty_states` then re-marks *every* state
   with an incoming edge into each newly-created block, pushing the affected
   blocks onto the worklist (each at most once while they stay marked).

So naive measures on counts of marked states or on `rocklist` length do not
work: re-marking can grow both. The decreasing quantity we intend to use is
the **refinement rank**: a block is pushed at level `k` only after a block
created at level `k-1` received it as an *incoming* target, and blocks created
(and the state-to-block map) refine with each split; the rank of every block
strictly increases the moment it is marked, and each state's rank is bounded
by the number of states. Concretely:

- `Inv` : each worklist block has at least one marked state and the worklist
  contains each block at most once; every state's current block is the one
  `state_to_key`/`element_to_block` assign.
- `measure (ctx, it) := Σ (unmarked) blocks are "settled at level bound"`.

Proving `strong_run_worklist_loop_loop.spec` requires (a) the two inner
loops (`strong_process_marked_elements`, `mark_dirty_new_blocks`) framed via
the list-length measures (done body-level lemmas pending), and (b) the rank
argument above linking iterations, which is the crux of replacing
`run_worklist_loop_spec`.
-/

attribute [local reducible] alloc.vec.into_iter.IntoIter


abbrev Sz := Std.Usize
abbrev BT := TagIndex Sz BlockTag
abbrev ST := TagIndex Sz StateTag
abbrev InIter := alloc.vec.into_iter.IntoIter BT
abbrev VecTy := alloc.vec.Vec
abbrev PWS := BlockPartition × VecTy BT × VecTy ST

noncomputable abbrev tagEqInst : core.cmp.PartialEq BT BT :=
  verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex
    BlockTag core.cmp.PartialEqUsize

lemma tagEq_spec (a b : BT) :
    tagEqInst.eq a b = ok (decide (a = b)) := by
  unfold tagEqInst
  have hinst : (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex
      BlockTag core.cmp.PartialEqUsize).eq a b
      = verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq
        core.cmp.PartialEqUsize a b := rfl
  rw [hinst, tag_partial_eq_inst]
  by_cases h : a = b
  · subst h; simp
  · have : a.index ≠ b.index := fun e => h (merc_utilities.tagged_index.TagIndex.ext e)
    simp [h, this]

lemma neq_tag (a b : BT) :
    core.cmp.PartialEq.ne.trait_default tagEqInst a b = ok (!decide (a = b)) := by
  rw [core.cmp.PartialEq.ne.trait_default]
  rw [core.cmp.PartialEq.ne.default]
  rw [tagEq_spec]
  simp

theorem neq_bind {β : Type} (a b : BT) (k : Bool → Result β) :
    (do
      let x ← core.cmp.PartialEq.ne.trait_default tagEqInst a b
      k x) = k (!decide (a = b)) := by
  rw [neq_tag]
  simp

lemma into_iter_next_some (it : InIter) (v : BT) (tl : List BT) (h : it.val = v :: tl) :
    ∃ it1 : InIter,
      alloc.vec.into_iter.IteratorIntoIter.next it = ok (some v, it1) ∧ it1.val = tl := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rename_i heq'
    have : v :: tl = [] := h.symm.trans heq'
    cases this
  · rename_i hd' tl' heq'
    have hvc : v :: tl = hd' :: tl' := h.symm.trans heq'
    cases hvc
    refine ⟨alloc.vec.Vec.from tl (by grind), ?_⟩
    constructor
    · congr
    · simp [alloc.vec.Vec.from, alloc.vec.Vec.val]

lemma into_iter_next_none (it : InIter) (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rfl
  · rename_i hd' tl' heq'
    have : hd' :: tl' = [] := heq'.symm.trans h
    cases this

noncomputable def markDirtyStep (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz)
    (nb : BT) (p : BlockPartition) (w : VecTy BT) (s : VecTy ST) : Result PWS := do
  let b ← core.cmp.PartialEq.ne.trait_default tagEqInst block_index nb
  if b then
    let r ←
      verified.merc_reduction.signature_refinement.mark_dirty_states BRANCHING ltsInst lts p
        incoming w s nb num_blocks
    ok (r.1, r.2.1, r.2.2)
  else ok (p, w, s)

noncomputable def markDirtyAcc (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz)
    (p : BlockPartition) (w : VecTy BT) (s : VecTy ST) : List BT → Result PWS
  | [] => ok (p, w, s)
  | nb :: tl => do
      let b ← core.cmp.PartialEq.ne.trait_default tagEqInst block_index nb
      if b then
        let r ←
          verified.merc_reduction.signature_refinement.mark_dirty_states BRANCHING ltsInst lts p
            incoming w s nb num_blocks
        markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks r.1 r.2.1 r.2.2 tl
      else markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p w s tl

theorem markDirtyAcc_cons (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz)
    (p : BlockPartition) (w : VecTy BT) (s : VecTy ST)
    (nb : BT) (tl : List BT) :
    markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p w s (nb :: tl)
      = (do
          let r ← markDirtyStep BRANCHING ltsInst lts incoming block_index num_blocks nb p w s
          markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks r.1 r.2.1 r.2.2 tl) := by
  simp only [markDirtyAcc, markDirtyStep, neq_bind]
  by_cases hab : block_index = nb
  · have hx : (!decide (block_index = nb)) = false := by
      have hx_true : decide (block_index = nb) = true := by
        rw [decide_eq_true_eq]
        exact hab
      simp [hx_true]
    rw [hx]
    simp
  · have hx : (!decide (block_index = nb)) = true := by
      have hd : decide (block_index = nb) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        exact hab (of_decide_eq_true htrue)
      simp [hd]
    rw [hx]
    simp

theorem markDirtyAcc_append (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz)
    (p : BlockPartition) (w : VecTy BT) (s : VecTy ST) (l1 l2 : List BT) :
    markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p w s (l1 ++ l2)
      = (do
          let r ← markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p w s l1
          markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks r.1 r.2.1 r.2.2 l2) := by
  induction l1 generalizing p w s with
  | nil => simp [markDirtyAcc]
  | cons nb tl ih =>
      rw [List.cons_append]
      rw [markDirtyAcc_cons BRANCHING ltsInst lts incoming block_index num_blocks p w s nb (tl ++ l2)]
      rw [markDirtyAcc_cons BRANCHING ltsInst lts incoming block_index num_blocks p w s nb tl]
      simp only [bind_assoc_eq]
      congr 1
      funext r
      exact ih r.1 r.2.1 r.2.2

lemma markDirtyStep_pos (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz) (v : BT)
    (p : BlockPartition) (w : VecTy BT) (s : VecTy ST) (h : block_index = v) :
    markDirtyStep BRANCHING ltsInst lts incoming block_index num_blocks v p w s = ok (p, w, s) := by
  rw [markDirtyStep]
  rw [neq_bind block_index v]
  have hc : (!decide (block_index = v)) = false := by
    have ht : decide (block_index = v) = true := by
      rw [decide_eq_true_eq]
      exact h
    simp [ht]
  rw [hc]
  simp

lemma markDirtyStep_neg (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz) (v : BT)
    (p : BlockPartition) (w : VecTy BT) (s : VecTy ST) (h : ¬ block_index = v) :
    markDirtyStep BRANCHING ltsInst lts incoming block_index num_blocks v p w s
      = (do
          let r ← verified.merc_reduction.signature_refinement.mark_dirty_states BRANCHING ltsInst lts p
              incoming w s v num_blocks
          ok (r.1, r.2.1, r.2.2)) := by
  rw [markDirtyStep]
  rw [neq_bind block_index v]
  have hc : (!decide (block_index = v)) = true := by
    have hd : decide (block_index = v) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact h (of_decide_eq_true htrue)
    simp [hd]
  rw [hc]
  simp



lemma mark_dirty_new_blocks_loop.body_some_step (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz)
    (iter : InIter) (partition : BlockPartition) (worklist : VecTy BT) (states : VecTy ST)
    (v : BT) (it1 : InIter)
    (hnext : alloc.vec.into_iter.IteratorIntoIter.next iter = ok (some v, it1)) :
    verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body
        BRANCHING ltsInst lts incoming block_index num_blocks iter partition worklist states
      = (do
          let b ← core.cmp.PartialEq.ne.trait_default
            (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag
              core.cmp.PartialEqUsize)
            block_index v
          if b = true then do
            let (partition1, worklist1, states1) ←
              verified.merc_reduction.signature_refinement.mark_dirty_states
                BRANCHING ltsInst lts partition incoming worklist states v num_blocks
            ok (cont (it1, partition1, worklist1, states1))
          else ok (cont (it1, partition, worklist, states))) := by
  rw [verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body]
  rw [hnext]
  simp


lemma loop_eq_bind {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) :
    Aeneas.Std.loop body x
      = (do
          let r ← body x
          match r with
          | ControlFlow.cont c => Aeneas.Std.loop body c
          | ControlFlow.done d => ok d) := by
  rw [Aeneas.Std.loop]
  rfl

theorem mark_dirty_new_blocks_loop_spec (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz)
    (iter : InIter) (partition : BlockPartition) (worklist : VecTy BT) (states : VecTy ST) :
    verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop BRANCHING ltsInst iter lts
      partition incoming worklist states block_index num_blocks
      = markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks partition worklist states iter.val := by
  let loopF := fun (iter : InIter) (p : BlockPartition) (w : VecTy BT) (s : VecTy ST) =>
    verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop BRANCHING ltsInst iter lts p incoming w s block_index num_blocks
  let ul : (InIter × BlockPartition × VecTy BT × VecTy ST) → Result (ControlFlow (InIter × BlockPartition × VecTy BT × VecTy ST) PWS) :=
    fun (i, pa, wl, st) =>
      verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body BRANCHING ltsInst lts incoming block_index num_blocks i pa wl st
  have hloop_unfold :
    ∀ (it : InIter) (p : BlockPartition) (w : VecTy BT) (s : VecTy ST),
      Aeneas.Std.loop ul (it, p, w, s)
        = verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop BRANCHING ltsInst it lts p incoming w s block_index num_blocks := by
    intro it p w s
    rw [verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop]
  have hw : ∀ n iter p w s, iter.val.length = n → loopF iter p w s = markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p w s iter.val := by
    intro n
    induction n with
    | zero =>
      intro iter p w s hzero
      have hnil : iter.val = [] := List.eq_nil_of_length_eq_zero hzero
      have hbodyv : verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body BRANCHING ltsInst lts incoming block_index num_blocks iter p w s
          = ok (done (p, w, s)) := by
        rw [verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body]
        rw [into_iter_next_none iter hnil]
        simp
      rw [show loopF iter p w s = Aeneas.Std.loop ul (iter, p, w, s) from by
        simp [loopF, ul, (hloop_unfold iter p w s)]]
      rw [loop_eq_bind ul (iter, p, w, s)]
      rw [show ul (iter, p, w, s) = verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body BRANCHING ltsInst lts incoming block_index num_blocks iter p w s from by rfl]
      rw [hbodyv]
      rw [hnil]
      rw [markDirtyAcc]
      simp
    | succ n ih =>
      intro iter p w s hlen
      cases h : iter.val with
      | nil =>
        exfalso
        rw [h] at hlen
        simp at hlen
      | cons v tl =>
        rcases into_iter_next_some iter v tl h with ⟨it1, hnext, hval⟩
        have hbstep := mark_dirty_new_blocks_loop.body_some_step BRANCHING ltsInst lts incoming block_index num_blocks iter p w s v it1 hnext
        have hlenvc : (v :: tl).length = n + 1 := by
          rw [← h]
          exact hlen
        have hlen1 : it1.val.length = n := by
          calc
            it1.val.length = tl.length := by rw [hval]
            _ = n := by
              have ht : tl.length + 1 = n + 1 := by
                rw [← hlenvc]
                simp
              omega
        by_cases hb : block_index = v
        · have hc : (!decide (block_index = v)) = false := by
            have ht : decide (block_index = v) = true := by
              rw [decide_eq_true_eq]
              exact hb
            simp [ht]
          rw [show loopF iter p w s = Aeneas.Std.loop ul (iter, p, w, s) from by
            simp [loopF, ul, (hloop_unfold iter p w s)]]
          rw [loop_eq_bind ul (iter, p, w, s)]
          rw [show ul (iter, p, w, s) = verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body BRANCHING ltsInst lts incoming block_index num_blocks iter p w s from by rfl]
          rw [hbstep]
          rw [neq_bind block_index v]
          rw [hc]
          simp
          rw [hloop_unfold it1 p w s]
          rw [markDirtyAcc]
          rw [neq_bind block_index v]
          rw [hc]
          simp
          rw [show markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p w s tl
              = markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p w s it1.val from by rw [hval]]
          exact ih it1 p w s hlen1
        · have hc : (!decide (block_index = v)) = true := by
            have hd : decide (block_index = v) = false := by
              apply Bool.eq_false_of_not_eq_true
              intro htrue
              exact hb (of_decide_eq_true htrue)
            simp [hd]
          rw [show loopF iter p w s = Aeneas.Std.loop ul (iter, p, w, s) from by
            simp [loopF, ul, (hloop_unfold iter p w s)]]
          rw [loop_eq_bind ul (iter, p, w, s)]
          rw [show ul (iter, p, w, s) = verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body BRANCHING ltsInst lts incoming block_index num_blocks iter p w s from by rfl]
          rw [hbstep]
          rw [neq_bind block_index v]
          rw [hc]
          simp
          rw [markDirtyAcc]
          rw [neq_bind block_index v]
          rw [hc]
          simp
          congr 1
          funext x
          rcases x with ⟨p1, w1, s1⟩
          simp
          rw [hloop_unfold it1 p1 w1 s1]
          rw [show markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p1 w1 s1 tl
              = markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks p1 w1 s1 it1.val from by rw [hval]]
          exact ih it1 p1 w1 s1 hlen1
  rw [show verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop BRANCHING ltsInst iter lts partition incoming worklist states block_index num_blocks = loopF iter partition worklist states from by rfl]
  exact hw (iter.val.length) iter partition worklist states rfl

/-- `mark_dirty_new_blocks` iterates `new_block_indices` end-to-end; its
    wrapper frame is exactly the `markDirtyAcc` accumulator. -/
theorem mark_dirty_new_blocks_contract (BRANCHING : Bool) {L : Type} {Label : Type}
    (ltsInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (block_index : BT) (num_blocks : Sz)
    (partition : BlockPartition) (worklist : VecTy BT) (states : VecTy ST)
    (nbi : VecTy BT) :
    verified.merc_reduction.signature_refinement.mark_dirty_new_blocks BRANCHING ltsInst lts
      partition incoming worklist states block_index nbi num_blocks =
      markDirtyAcc BRANCHING ltsInst lts incoming block_index num_blocks partition worklist states nbi.val := by
  rw [verified.merc_reduction.signature_refinement.mark_dirty_new_blocks]
  rw [alloc.vec.IntoIteratorVec.into_iter]
  simp
  rw [mark_dirty_new_blocks_loop_spec BRANCHING ltsInst lts incoming block_index
    num_blocks nbi partition worklist states]

/-- `strong_process_worklist_block` passes a fresh `id` map, reads block
    `b = blocks[b.val]`, asserts its marked suffix is non-empty (the loop
    invariant), closes the backward closure, then runs
    `strong_partition_marked` and `mark_dirty_new_blocks`. The do-mirror
    records every step with the leaf contracts already rewritten in. -/
theorem strong_process_worklist_block_contract {L : Type} {Label : Type}
    (BRANCHING : Bool) (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (ctx : WorklistContextStrong) (b : BT)
    (hIdx : b.index.val < ctx.partition.blocks.val.length)
    (b0 : verified.merc_reduction.block_partition.Block)
    (hb0 : ctx.partition.blocks.slice.val[b.index.val] = b0)
    (hMark : (b0.marked_split : Nat) < (b0.«end» : Nat)) :
    verified.merc_reduction.signature_refinement.strong_process_worklist_block
      BRANCHING LTSInst sys incoming ctx b =
      (do
        let id ←
          std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault.default
            (VecTy ((TagIndex Std.Usize LabelTag) × BT)) (TagIndex Std.Usize BlockTag)
            verified.rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault
        let _bk ← ok b0
        let b1 ← ok (decide ((b0.marked_split : Nat) < (b0.«end» : Nat)))
        massert b1
        let bp ←
          verified.merc_reduction.signature_refinement.maybe_mark_backward_closure
            BRANCHING ctx.partition b incoming
        let num_blocks ← ok (alloc.vec.Vec.len bp.blocks)
        let (nbi, bp1, _, _, v, bpb, v1) ←
          verified.merc_reduction.signature_refinement.strong_partition_marked
            LTSInst sys bp b id (alloc.vec.Vec.new (VecTy ((TagIndex Std.Usize LabelTag) × BT)))
            ctx.builder ctx.split_builder ctx.state_to_key
        let (bp2, v2, v3) ←
          verified.merc_reduction.signature_refinement.mark_dirty_new_blocks
            BRANCHING LTSInst sys bp1 incoming ctx.worklist ctx.states b nbi
            num_blocks
        ok { partition := bp2, worklist := v2, states := v3, builder := v,
             split_builder := bpb, state_to_key := v1 }) := by
  unfold verified.merc_reduction.signature_refinement.strong_process_worklist_block
  rw [block_partition_block_val ctx.partition b hIdx]
  rw [hb0]
  simp [block_has_marked_contract, num_of_blocks_contract, hMark, bind_tc_ok]

/-!
# `strong_process_marked_elements` internals

Value-level specs for the helpers of
`strong_process_marked_elements`: `count_block_occurrence` (increment the
counter for a block, resizing the `block_sizes` vector on demand) and
`strong_intern_signature` (intern a signature in the `id` map). -/

theorem count_block_occurrence_spec_lt (block_sizes : alloc.vec.Vec Sz)
    (index : BT)
    (h : index.index.val < block_sizes.val.length)
    (hsucc_elem : ∃ newelem : Sz,
      (block_sizes.val.get ⟨index.index.val, h⟩) + 1#usize = ok newelem) :
    ∃ v : alloc.vec.Vec Sz,
      verified.merc_reduction.signature_refinement.count_block_occurrence block_sizes index = ok v ∧
      ∃ newelem : Sz,
        (block_sizes.val.get ⟨index.index.val, h⟩) + 1#usize = ok newelem ∧
        v.val = block_sizes.val.set index.index.val newelem := by
  unfold verified.merc_reduction.signature_refinement.count_block_occurrence
  simp only []
  have hb : index.index.val + 1 < 2 ^ System.Platform.numBits := by
    have hlen : block_sizes.val.length ≤ Usize.max := by simp
    have hsucc_le : index.index.val + 1 ≤ Usize.max := by omega
    have hmax_lt : Usize.max < 2 ^ System.Platform.numBits := by
      simp [Usize.max, Usize.numBits]
    omega
  have hindex1 : index.index + 1#usize = ok (Usize.ofNatCore (index.index.val + 1) hb) := by
    rw [show index.index + 1#usize = UScalar.add index.index 1#usize by rfl]
    simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
    split_ifs with hif
    · rfl
    · exfalso
      apply hif
      simp [UScalar.check_bounds]
      exact hb
  have him :
      ∃ x0 : Sz, ∃ back : Sz → alloc.vec.Vec Sz,
        verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
          (T := Std.Usize) (U := Std.Usize) (Tag := BlockTag) core.marker.CopyUsize
          (core.slice.index.SliceIndexUsizeSlice Std.Usize) block_sizes index = ok (x0, back) ∧
        x0 = block_sizes.val.get ⟨index.index.val, h⟩ ∧
        back = fun u : Sz => ({ slice := Slice.set block_sizes.slice index.index u } : alloc.vec.Vec Sz) := by
    rcases spec_imp_exists (Slice.index_mut_usize_spec block_sizes.slice index.index h) with ⟨w, hw, hpost⟩
    rcases w with ⟨x, f⟩
    rcases hpost with ⟨hx, hf⟩
    refine ⟨x, fun u : Sz => ({ slice := f u } : alloc.vec.Vec Sz), ?_, ?_, ?_⟩
    · rw [vec_tagged_index_mut_eq]
      rw [hw]
      simp
    · rw [hx]
      change (↑block_sizes.slice)[↑index.index] = (↑block_sizes.slice)[↑index.index]
      rfl
    · simp [hf]
  rcases him with ⟨x0, back, himok, hx0, hback⟩
  simp only [tag_value_id, bind_tc_ok]
  rw [hindex1]
  have hge : ¬ (block_sizes.val.length ≤ index.index.val) := by omega
  simp [hge]
  obtain ⟨newelem, hnew⟩ := hsucc_elem
  have hnew' : x0 + 1#usize = ok newelem := by
    rw [hx0]
    exact hnew
  have hmain :
      (do
        let (i3, index_mut_back) ←
          verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
            (T := Std.Usize) (U := Std.Usize) (Tag := BlockTag) core.marker.CopyUsize
              (core.slice.index.SliceIndexUsizeSlice Std.Usize) block_sizes index
        let i4 ← i3 + 1#usize
        ok (index_mut_back i4)) = ok (back newelem) := by
    conv_lhs =>
      pattern verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
        (T := Std.Usize) (U := Std.Usize) (Tag := BlockTag) core.marker.CopyUsize
        (core.slice.index.SliceIndexUsizeSlice Std.Usize) block_sizes index
      rw [himok]
    simp
    rw [hnew']
    simp
  refine ⟨back newelem, hmain, newelem, hnew, ?_⟩
  · rw [hback]
    change Slice.val (Slice.set block_sizes.slice index.index newelem) =
        List.set (Slice.val block_sizes.slice) index.index.val newelem
    rw [Slice.set_val_eq]

/-! ## `count_block_occurrence` (resize branch): `count_block_occurrence_spec_ge`

When the block size cell for `index` is beyond the current length of
`block_sizes`, the count grows the vector (padding with zeros) and marks the
fresh cell with `1`. This pins the resulting value completely:

`v.val = List.set index.index.val 1#usize (List.resize (index.index.val + 1) 0#usize block_sizes.val)`

The success hypothesis `hsucc_elem` guards the `index + 1` increments against
overflow. -/
theorem count_block_occurrence_spec_ge (block_sizes : alloc.vec.Vec Sz)
    (index : BT)
    (h : block_sizes.val.length ≤ index.index.val)
    (hsucc_elem : ∃ i3 : Sz, index.index + 1#usize = ok i3) :
    ∃ v : alloc.vec.Vec Sz,
verified.merc_reduction.signature_refinement.count_block_occurrence block_sizes index = ok v ∧
      v.val = List.set (List.resize block_sizes.val (index.index.val + 1) 0#usize) index.index.val 1#usize := by
  unfold verified.merc_reduction.signature_refinement.count_block_occurrence
  simp only []
  have hbig : 1 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]
      norm_num
    · rw [h64]
      norm_num
  have hb : index.index.val + 1 < 2 ^ System.Platform.numBits := by
    rcases hsucc_elem with ⟨i3, hi3⟩
    by_contra hnot
    have hfail : index.index + 1#usize = (Result.fail Error.integerOverflow : Result Sz) := by
      rw [show index.index + 1#usize = UScalar.add index.index 1#usize by rfl]
      simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
      split_ifs with hif
      · exfalso
        apply hnot
        simpa [UScalar.check_bounds] using hif
      · rfl
    have hbad : (Result.fail Error.integerOverflow : Result Sz) = ok i3 := by
      rw [← hfail]
      exact hi3
    exact (fail_not_ok hbad)
  have hindex1 : index.index + 1#usize = ok (Usize.ofNatCore (index.index.val + 1) hb) := by
    rw [show index.index + 1#usize = UScalar.add index.index 1#usize by rfl]
    simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
    split_ifs with hif
    · rfl
    · exfalso
      apply hif
      simp [UScalar.check_bounds]
      exact hb
  have hzeroAdd : (0#usize : Sz) + 1#usize = ok 1#usize := by
    rw [show (0#usize : Sz) + 1#usize = UScalar.add 0#usize 1#usize by rfl]
    simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
    split_ifs with hif
    · rfl
    · exfalso
      apply hif
      simp [UScalar.check_bounds]
      rcases System.Platform.numBits_eq with h32 | h64
      · rw [h32]
        decide
      · rw [h64]
        decide
  have hcl0 : core.clone.CloneUsize.clone 0#usize = ok (0#usize : Sz) := by
    simp [core.clone.impls.CloneUsize.clone]
  simp only [tag_value_id, bind_tc_ok]
  rw [hindex1]
  have hlenle : block_sizes.val.length ≤ index.index.val := h
  simp [hlenle]
  have hval : (Usize.ofNatCore (index.index.val + 1) hb).val = index.index.val + 1 := by
    simp [Usize.ofNatCore]
  rcases spec_imp_exists
      (alloc.vec.Vec.resize_spec core.clone.CloneUsize block_sizes
        (Usize.ofNatCore (index.index.val + 1) hb) 0#usize hcl0) with ⟨bs1, hresok, hresval⟩
  have hresval' : bs1.val = List.resize block_sizes.val (index.index.val + 1) 0#usize := by
    simpa [hval] using hresval
  have hbound : index.index.val < bs1.val.length := by
    rw [hresval']
    rw [List.resize_length]
    omega
  have hbound2 : index.index.val <
      (block_sizes.val ++
        List.replicate (index.index.val + 1 - block_sizes.val.length) 0#usize).length := by
    rw [List.length_append, List.replicate_length]
    omega
  have hzz2 :
      (block_sizes.val ++
          List.replicate (index.index.val + 1 - block_sizes.val.length) 0#usize)[index.index.val]'hbound2 =
      (0#usize : Sz) := by
    rw [List.getElem_append_right]
    · rw [List.getElem_replicate]
    · exact h
  have h1 : List.resize block_sizes.val (index.index.val + 1) 0#usize =
      block_sizes.val ++
        List.replicate (index.index.val + 1 - block_sizes.val.length) 0#usize := by
    unfold List.resize
    rw [if_pos (Nat.zero_le (index.index.val + 1))]
    rw [List.take_of_length_le]
    omega
  have hzz : (List.resize block_sizes.val (index.index.val + 1) 0#usize)[index.index.val] =
      (0#usize : Sz) := by
    simpa [h1] using hzz2
  have hzeroElem : bs1.val[index.index.val] = (0#usize : Sz) := by
    simp [hresval', hzz]
  rcases spec_imp_exists (Slice.index_mut_usize_spec bs1.slice index.index hbound) with ⟨w, hw, hpost⟩
  rcases w with ⟨x, f⟩
  rcases hpost with ⟨hx2, hf2⟩
  let back : Sz → alloc.vec.Vec Sz :=
    fun u => ({ slice := f u } : alloc.vec.Vec Sz)
  have hback' : back = fun u : Sz => ({ slice := f u } : alloc.vec.Vec Sz) := rfl
  have hzero : x = (0#usize : Sz) := by
    rw [hx2]
    exact hzeroElem
  have haddzero : x + 1#usize = ok 1#usize := by
    rw [hzero]
    exact hzeroAdd
  have him1 :
      verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
        (T := Std.Usize) (U := Std.Usize) (Tag := BlockTag) core.marker.CopyUsize
        (core.slice.index.SliceIndexUsizeSlice Std.Usize) bs1 index = ok (x, back) := by
    rw [vec_tagged_index_mut_eq]
    rw [hw]
    simp [back]
  have hfull :
      (do
        let block_sizes1 ←
          alloc.vec.Vec.resize core.clone.CloneUsize block_sizes
            (Usize.ofNatCore (index.index.val + 1) hb) 0#usize
        let (i3, index_mut_back) ←
          verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
            (T := Std.Usize) (U := Std.Usize) (Tag := BlockTag) core.marker.CopyUsize
              (core.slice.index.SliceIndexUsizeSlice Std.Usize) block_sizes1 index
        let i4 ← i3 + 1#usize
        ok (index_mut_back i4)) = ok (back 1#usize) := by
    conv_lhs =>
      pattern alloc.vec.Vec.resize core.clone.CloneUsize block_sizes
        (Usize.ofNatCore (index.index.val + 1) hb) 0#usize
      rw [hresok]
    simp
    conv_lhs =>
      pattern verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
        (T := Std.Usize) (U := Std.Usize) (Tag := BlockTag) core.marker.CopyUsize
        (core.slice.index.SliceIndexUsizeSlice Std.Usize) bs1 index
      rw [him1]
    simp
    rw [haddzero]
    simp [hback']
  refine ⟨back 1#usize, hfull, ?_⟩
  · rw [hback', hf2]
    change Slice.val (Slice.set bs1.slice index.index 1#usize) =
        List.set (List.resize block_sizes.val (index.index.val + 1) 0#usize) index.index.val 1#usize
    rw [Slice.set_val_eq]
    change (bs1.val).set index.index.val (1#usize : Sz) =
        List.set (List.resize block_sizes.val (index.index.val + 1) 0#usize) index.index.val 1#usize
    rw [hresval']

/-- `count_block_occurrence` always succeeds: whether `index` is in range
    (increment the existing count) or out of range (resize and set to `1`),
    an updated `block_sizes` is returned. -/
theorem count_block_occurrence_spec_ok (block_sizes : alloc.vec.Vec Sz) (index : BT)
    (hsucc_index : ∃ i3 : Sz, index.index + 1#usize = ok i3)
    (hsucc_elem : ∀ (h : index.index.val < block_sizes.val.length),
      ∃ newelem : Sz, block_sizes.val.get ⟨index.index.val, h⟩ + 1#usize = ok newelem) :
    ∃ v : alloc.vec.Vec Sz,
      verified.merc_reduction.signature_refinement.count_block_occurrence block_sizes index = ok v := by
  by_cases h : index.index.val < block_sizes.val.length
  · rcases count_block_occurrence_spec_lt block_sizes index h (hsucc_elem h) with ⟨v, hvok, _⟩
    exact ⟨v, hvok⟩
  · have hge : block_sizes.val.length ≤ index.index.val := by omega
    rcases count_block_occurrence_spec_ge block_sizes index hge hsucc_index with ⟨v, hvok, _⟩
    exact ⟨v, hvok⟩

/-! ## `strong_intern_signature`

The signature→block-index `id` map is an opaque `HashMap` (see the `HashMap`
boundary axioms in `MercVerified/Basic.lean`). These lemmas pin the two
observable behaviours of the strong interning used by
`strong_process_marked_elements`: a cache hit returns the stored index and
touches nothing; a cache miss interns the signature under
`key_to_signature.length`, inserts it into the map and pushes it, returning the
fresh index. -/

abbrev SigPair := (TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)
abbrev SigKey := alloc.vec.Vec SigPair
abbrev InternMap := std.collections.hash.map.HashMap SigKey BT verified.rustc_hash.FxBuildHasher Global

private noncomputable abbrev internEqInst : core.cmp.Eq SigKey :=
  verified.alloc.vec.Vec.Insts.CoreCmpEq Global (verified.Pair.Insts.CoreCmpEq
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpEq LabelTag core.cmp.EqUsize)
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpEq BlockTag core.cmp.EqUsize))

private noncomputable abbrev internHashInst : core.hash.Hash SigKey :=
  verified.alloc.vec.Vec.Insts.CoreHashHash Global (verified.Pair.Insts.CoreHashHash
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreHashHash LabelTag verified.Usize.Insts.CoreHashHash)
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreHashHash BlockTag verified.Usize.Insts.CoreHashHash))

private noncomputable abbrev internBuildHasher : verified.core.hash.BuildHasher verified.rustc_hash.FxBuildHasher rustc_hash.FxHasher :=
  verified.rustc_hash.FxBuildHasher.Insts.CoreHashBuildHasherFxHasher

/-- Strong interning, cache hit: the signature is already in `id`, its stored
    block index is returned and nothing is mutated. -/
lemma strong_intern_signature_found (id : InternMap) (kts : alloc.vec.Vec SigKey)
    (sb : SigKey) (idx : BT)
    (hget : std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
      internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst
      internEqInst id sb = ok (some (sb, idx))) :
    verified.merc_reduction.signature_refinement.strong_intern_signature id kts sb
      = ok (idx, id, kts) := by
  unfold verified.merc_reduction.signature_refinement.strong_intern_signature
  rw [hget]
  simp

/-- Strong interning, cache miss: the signature is cloned, interned at position
    `key_to_signature.length`, inserted in `id` (so a later lookup of `sb`
    returns exactly it), pushed, and the fresh index is returned. -/
lemma strong_intern_signature_absent (id : InternMap) (kts : alloc.vec.Vec SigKey)
    (sb : SigKey)
    (hget : std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
      internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst
      internEqInst id sb = ok none)
    (hlen : kts.val.length < Usize.max) :
    ∃ id' : InternMap, ∃ kts' : alloc.vec.Vec SigKey,
      verified.merc_reduction.signature_refinement.strong_intern_signature id kts sb =
        ok (({ index := alloc.vec.Vec.len kts, marker := () } : BT), id', kts') ∧
      kts'.val = kts.val ++ [sb] ∧
      std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
        internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst
        internEqInst id' sb = ok (some (sb, ({ index := alloc.vec.Vec.len kts, marker := () } : BT))) := by
  unfold verified.merc_reduction.signature_refinement.strong_intern_signature
  rw [hget]
  have hclone : ∀ x : SigKey, alloc.vec.CloneVec.clone (BuiltinClone SigPair) x = ok x := by
    intro x
    unfold alloc.vec.CloneVec.clone
    rcases x with ⟨sx⟩
    have hm : Slice.clone (BuiltinClone SigPair).clone sx ⦃ s' => sx = s' ⦄ :=
      Slice.clone_spec (clone := (BuiltinClone SigPair).clone) (s := sx) (by
        intro y hy; unfold BuiltinClone; rfl)
    rcases Std.WP.spec_imp_exists hm with ⟨s', hs', heq'⟩
    subst heq'
    rw [hs']
    simp
  rcases (std.collections.hash.map.HashMap.insert_spec (K := SigKey) (V := BT)
      internEqInst internHashInst internBuildHasher id sb (({ index := alloc.vec.Vec.len kts, marker := () } : BT)))
      with ⟨_, id1, hins, hlookup⟩
  rcases Std.WP.spec_imp_exists (alloc.vec.Vec.push_spec kts sb hlen) with ⟨kts1, hpush, hval⟩
  rw [hclone sb]
  simp
  rw [hclone sb]
  simp
  rw [hins]
  simp
  rw [hpush]
  simp
  constructor
  · exact hval
  · exact hlookup

/-- Strong interning always returns a fresh-or-existing index: whatever the map
    contents, an interned index exists (`found` returns the stored one, a miss
    interns `sb` at position `kts.length`). -/
lemma strong_intern_signature_total (id : InternMap) (kts : alloc.vec.Vec SigKey)
    (sb : SigKey) :
    (∃ idx : BT,
      std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
        internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst
        internEqInst id sb = ok (some (sb, idx))) ∨
      (std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
        internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst
        internEqInst id sb = ok none ∧ kts.val.length < Usize.max) →
      ∃ index : BT, ∃ id1 : InternMap, ∃ kts1 : alloc.vec.Vec SigKey,
        verified.merc_reduction.signature_refinement.strong_intern_signature id kts sb =
          ok (index, id1, kts1) := by
  intro h
  rcases h with ⟨idx, hget⟩ | ⟨hget, hlen⟩
  · exact ⟨idx, id, kts, strong_intern_signature_found id kts sb idx hget⟩
  · rcases strong_intern_signature_absent id kts sb hget hlen with ⟨id1, kts1, h⟩
    exact ⟨({ index := alloc.vec.Vec.len kts, marker := () } : BT), id1, kts1, h.1⟩

/-!
# `strong_process_marked_elements` value-level loop spec

The loop walks `split_builder.old_elements` from `element_index` upward. Each
iteration (while `element_index < old_elements.len`):

1. reads the marked state `state_index := old_elements[element_index]`,
2. recomputes its strong (bisimulation) signature into `signature_builder`
   (`strong_bisim_signature`),
3. interns it (`strong_intern_signature`), obtaining/reusing block `index`,
4. reassigns the element's block slot `index_to_block[element_index] := index`
   and the state's block slot `state_to_key[state_index] := index`,
5. increments the occurrence counter `block_sizes[index]`
   (`count_block_occurrence`), and
6. advances `element_index`.

When `element_index ≥ old_elements.len` the loop terminates, returning the
(possibly mutated) map/vector triple together with the final
`split_builder.index_to_block`/`block_sizes`/`old_elements` and
`state_to_key`. -/

/-- One iteration of `strong_process_marked_elements_loop` with the index
    past the end of `old_elements`: the loop body returns `done` with every
    accumulator unchanged. -/
theorem strong_process_marked_elements_loop.body_done_step
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (partition : BlockPartition)
    (id : InternMap) (key_to_signature : VecTy SigKey)
    (signature_builder : SigKey)
    (split_builder : BlockPartitionBuilder)
    (state_to_key : VecTy BT)
    (element_index : Sz)
    (hge : split_builder.old_elements.val.length ≤ element_index.val) :
    verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
      LTSInst sys partition id key_to_signature signature_builder split_builder
      state_to_key element_index
      = ok (done (id, key_to_signature, signature_builder,
          split_builder.index_to_block, split_builder.block_sizes,
          split_builder.old_elements, state_to_key)) := by
  unfold verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
  simp [hge]

/-- If, upon entry, the loop index already sits at/past the end of
    `old_elements`, `strong_process_marked_elements_loop` terminates
    immediately and returns every accumulator unchanged. -/
theorem strong_process_marked_elements_loop_base
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (partition : BlockPartition)
    (id : InternMap) (key_to_signature : VecTy SigKey)
    (signature_builder : SigKey)
    (split_builder : BlockPartitionBuilder)
    (state_to_key : VecTy BT)
    (element_index : Sz)
    (hge : split_builder.old_elements.val.length ≤ element_index.val) :
    verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop
      LTSInst sys partition id key_to_signature signature_builder split_builder
      state_to_key element_index
      = ok (id, key_to_signature, signature_builder,
          split_builder.index_to_block, split_builder.block_sizes,
          split_builder.old_elements, state_to_key) := by
  rw [verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop]
  let post : (InternMap × VecTy SigKey × SigKey × VecTy BT × VecTy Sz ×
      VecTy ST × VecTy BT) → Prop :=
    fun b => b = (id, key_to_signature, signature_builder,
      split_builder.index_to_block, split_builder.block_sizes,
      split_builder.old_elements, state_to_key)
  have hspec :
      loop (fun x : (InternMap × VecTy SigKey × SigKey × BlockPartitionBuilder ×
          VecTy BT × Sz) =>
        verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
          LTSInst sys partition x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
        (id, key_to_signature, signature_builder, split_builder, state_to_key,
          element_index) ⦃ b => post b ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun _ : (InternMap × VecTy SigKey × SigKey × BlockPartitionBuilder ×
          VecTy BT × Sz) => 0)
      (inv := fun x : (InternMap × VecTy SigKey × SigKey × BlockPartitionBuilder ×
          VecTy BT × Sz) => x = (id, key_to_signature, signature_builder,
            split_builder, state_to_key, element_index))
      (post := post)
      (body := fun x : (InternMap × VecTy SigKey × SigKey × BlockPartitionBuilder ×
          VecTy BT × Sz) =>
        verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
          LTSInst sys partition x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
      (x := (id, key_to_signature, signature_builder, split_builder, state_to_key,
          element_index))
    · intro x hx
      subst x
      have hdone := strong_process_marked_elements_loop.body_done_step LTSInst sys partition
        id key_to_signature signature_builder split_builder state_to_key element_index hge
      rw [hdone]
      simp [post]
    · rfl
  rcases (spec_imp_exists hspec) with ⟨y, hy, hpost⟩
  rw [hy]
  rw [hpost]

/-- One iteration of `strong_process_marked_elements_loop` on a live element:
    the marked state is read, its strong signature recomputed and interned
    (block `index`), the element's `index_to_block` slot and the state's
    `state_to_key` slot are reassigned to `index`, the `block_sizes` counter
    is incremented, and the iteration counter advances. -/
theorem strong_process_marked_elements_loop.body_some_step
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (partition : BlockPartition)
    (id : InternMap) (key_to_signature : VecTy SigKey)
    (signature_builder : SigKey)
    (split_builder : BlockPartitionBuilder)
    (state_to_key : VecTy BT)
    (element_index : Sz)
    (hlt : element_index.val < split_builder.old_elements.val.length)
    (state_index : ST)
    (hsid : split_builder.old_elements.index_usize element_index = ok state_index)
    (signature_builder1 : SigKey)
    (hsig : verified.merc_reduction.signatures.strong_bisim_signature LTSInst
      (verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition)
      state_index sys partition signature_builder = ok signature_builder1)
    (index : BT) (id1 : InternMap) (key_to_signature1 : VecTy SigKey)
    (hintern : verified.merc_reduction.signature_refinement.strong_intern_signature
      id key_to_signature signature_builder1 = ok (index, id1, key_to_signature1))
    (hmut1 : BT → VecTy BT)
    (hmut1ok : ∃ x : BT, split_builder.index_to_block.index_mut_usize element_index
      = ok (x, hmut1))
    (v : VecTy Sz)
    (hcount : verified.merc_reduction.signature_refinement.count_block_occurrence
      split_builder.block_sizes index = ok v)
    (hmut2 : BT → VecTy BT)
    (hmut2ok : ∃ x : BT, verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
      core.marker.CopyUsize (core.slice.index.SliceIndexUsizeSlice BT)
      state_to_key state_index = ok (x, hmut2))
    (element_index1 : Sz)
    (hadd : element_index + 1#usize = ok element_index1) :
    verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
      LTSInst sys partition id key_to_signature signature_builder split_builder
      state_to_key element_index
      = ok (cont (id1, key_to_signature1, signature_builder1,
          { split_builder with index_to_block := hmut1 index, block_sizes := v },
          hmut2 index, element_index1)) := by
  rw [verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body]
  simp [hlt]
  rw [hsid]
  simp
  rw [hsig]
  simp
  rw [hintern]
  simp
  rcases hmut1ok with ⟨_, hmut1ok'⟩
  rw [hmut1ok']
  simp
  rw [hcount]
  simp
  rcases hmut2ok with ⟨_, hmut2ok'⟩
  rw [hmut2ok']
  simp
  rw [hadd]
  simp

/-- The final result type of `strong_process_marked_elements_loop`:
    `(id, key_to_signature, signature_builder, index_to_block, block_sizes,
    old_elements, state_to_key)`. -/
abbrev SpmeFinal :=
  InternMap × VecTy SigKey × SigKey × VecTy BT × VecTy Sz × VecTy ST × VecTy BT

/-- The loop state type of `strong_process_marked_elements_loop`. -/
abbrev SpmeState :=
  InternMap × VecTy SigKey × SigKey × BlockPartitionBuilder × VecTy BT × Sz

/-- One element of `old_elements` is processable: the loop body's calls succeed
    from state `(id, kts, sigb, spb, stk)` at position `ei`.  This packages
    exactly the hypotheses of `strong_process_marked_elements_loop.body_some_step`
    so the invariant of the loop spec can ask "every remaining element is
    processable" without naming the intermediate values. -/
def LoopElementOk {L : Type} {Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (partition : BlockPartition) (id : InternMap) (kts : VecTy SigKey)
    (sigb : SigKey) (spb : BlockPartitionBuilder) (stk : VecTy BT) (ei : Sz) : Prop :=
  ei.val < spb.old_elements.val.length ∧
  ∃ state_index : ST, ∃ ts : alloc.vec.Vec Transition,
    spb.old_elements.index_usize ei = ok state_index ∧
    LTSInst.outgoing_transitions sys state_index = ok ts ∧
    ∃ signature_builder1 : SigKey, ∃ index : BT, ∃ id1 : InternMap, ∃ kts1 : VecTy SigKey,
      verified.merc_reduction.signatures.strong_bisim_signature LTSInst
        (verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition)
        state_index sys partition sigb = ok signature_builder1 ∧
      verified.merc_reduction.signature_refinement.strong_intern_signature id kts signature_builder1 =
        ok (index, id1, kts1) ∧
      ∃ hmut1 : BT → VecTy BT,
        (∃ x : BT, spb.index_to_block.index_mut_usize ei = ok (x, hmut1)) ∧
      ∃ v : VecTy Sz,
        verified.merc_reduction.signature_refinement.count_block_occurrence spb.block_sizes index = ok v ∧
      ∃ hmut2 : BT → VecTy BT,
        (∃ x : BT,
          verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
            (core.slice.index.SliceIndexUsizeSlice BT) stk state_index = ok (x, hmut2)) ∧
      ∃ ei1 : Sz, ei + 1#usize = ok ei1

/-- Accumulator matching `strong_process_marked_elements_loop` step for step,
    whose recursion is structural on the list `rest` of remaining elements
    (`rest` is intended to be `old_elements.val.drop element_index.val`).  Each
    step just runs the machine-generated loop body and recurses on the
    continuation state; this gives an induction-friendly view of the loop. -/
noncomputable def spmeAcc {L : Type} {Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (partition : BlockPartition) (id : InternMap) (kts : VecTy SigKey)
    (sigb : SigKey) (spb : BlockPartitionBuilder) (stk : VecTy BT) (ei : Sz) :
    List ST → Result SpmeFinal
  | [] =>
      ok (id, kts, sigb, spb.index_to_block, spb.block_sizes, spb.old_elements, stk)
  | _ :: rest =>
      do
        let r ←
          verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
            LTSInst sys partition id kts sigb spb stk ei
        match r with
        | ControlFlow.cont c =>
            spmeAcc LTSInst sys partition c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1
              c.2.2.2.2.2 rest
        | ControlFlow.done d => ok d

/-- A call to `spmeAcc` on the full remaining list is the same as one step of
    the fold. -/
theorem spmeAcc_step (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (partition : BlockPartition) (id : InternMap) (kts : VecTy SigKey)
    (sigb : SigKey) (spb : BlockPartitionBuilder) (stk : VecTy BT) (ei : Sz)
    (head : ST) (rest : List ST) :
    spmeAcc LTSInst sys partition id kts sigb spb stk ei (head :: rest)
      = (do
          let r ←
            verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
              LTSInst sys partition id kts sigb spb stk ei
          match r with
          | ControlFlow.cont c =>
              spmeAcc LTSInst sys partition c.1 c.2.1 c.2.2.1 c.2.2.2.1
                c.2.2.2.2.1 c.2.2.2.2.2 rest
          | ControlFlow.done d => ok d) := by
  rw [spmeAcc]

/-- The base case of `spmeAcc`: with no remaining elements it returns the
    unchanged accumulator, matching the loop's `done` branch. -/
theorem spmeAcc_nil (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (partition : BlockPartition) (id : InternMap) (kts : VecTy SigKey)
    (sigb : SigKey) (spb : BlockPartitionBuilder) (stk : VecTy BT) (ei : Sz) :
    spmeAcc LTSInst sys partition id kts sigb spb stk ei []
      = ok (id, kts, sigb, spb.index_to_block, spb.block_sizes, spb.old_elements, stk) := by
  rw [spmeAcc]

/-- If the current element is processable, the loop body takes a `cont` step
    whose next state is the interned/updated accumulator. -/
theorem spme_body_success {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (id : InternMap) (kts : VecTy SigKey) (sigb : SigKey) (spb : BlockPartitionBuilder)
    (stk : VecTy BT) (ei : Sz) (hok : LoopElementOk LTSInst sys partition id kts sigb spb stk ei) :
    ∃ y : SpmeState,
      verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
        LTSInst sys partition id kts sigb spb stk ei = ok (cont y) := by
  rcases hok with ⟨hlt, state_index, ts, hsid, hout, sigb1, index, id1, kts1, hsig,
    hintern, hmut1, hmut1ok, v, hcount, hmut2, hmut2ok, ei1, hadd⟩
  have hstep : verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
        LTSInst sys partition id kts sigb spb stk ei =
      ok (cont (id1, kts1, sigb1, { spb with index_to_block := hmut1 index, block_sizes := v },
        hmut2 index, ei1)) :=
    strong_process_marked_elements_loop.body_some_step LTSInst sys partition id kts sigb spb stk ei
      hlt state_index hsid sigb1 hsig index id1 kts1 hintern hmut1 hmut1ok v hcount hmut2 hmut2ok
      ei1 hadd
  refine ⟨(id1, kts1, sigb1, { spb with index_to_block := hmut1 index, block_sizes := v },
    hmut2 index, ei1), hstep⟩

/-!
# `strong_process_marked_elements_loop` totality: loop ≡ fold

We show that `strong_process_marked_elements_loop` (a `Aeneas.Std.loop` over
`strong_process_marked_elements_loop.body`) agrees *value for value* with the
structural accumulator `spmeAcc`, provided every element it visits is
processable.  Reachability is recorded by `spmeTable` (no intermediate state
data is nameable, since each successor is the *existential* output of the
opaque helper calls), and `LoopStepEq` bundles exactly the success data of one
`cont` step plus the successor-state equalities.
-/

/-- `ei + 1#usize` succeeds exactly when it produces a `Usize` of value
    `ei.val + 1` (`UScalar.add` magic, cf. `count_block_occurrence_spec_lt`). -/
lemma usize_add_one_val (ei ei1 : Sz) (hadd : ei + 1#usize = ok ei1) : ei1.val = ei.val + 1 := by
  have hb : ei.val + 1 < 2 ^ System.Platform.numBits := by
    by_contra hnot
    have hfail : ei + 1#usize = (Result.fail Error.integerOverflow : Result Sz) := by
      rw [show ei + 1#usize = UScalar.add ei 1#usize by rfl]
      simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
      split_ifs with hif
      · exfalso
        apply hnot
        simpa [UScalar.check_bounds] using hif
      · rfl
    have hbad : (Result.fail Error.integerOverflow : Result Sz) = ok ei1 := by
      rw [← hfail]
      exact hadd
    exact (fail_not_ok hbad)
  have hindex1 : ei + 1#usize = ok (Usize.ofNatCore (ei.val + 1) hb) := by
    rw [show ei + 1#usize = UScalar.add ei 1#usize by rfl]
    simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
    split_ifs with hif
    · rfl
    · exfalso
      apply hif
      simp [UScalar.check_bounds]
      exact hb
  have hcon : ok (Usize.ofNatCore (ei.val + 1) hb) = ok ei1 := by
    rw [← hindex1]
    exact hadd
  have heq : Usize.ofNatCore (ei.val + 1) hb = ei1 := by
    exact (Result.ok.injEq).mp hcon
  have hvalc : (Usize.ofNatCore (ei.val + 1) hb).val = ei.val + 1 := by
    rfl
  calc
    ei1.val = (Usize.ofNatCore (ei.val + 1) hb).val := by rw [heq]
    _ = ei.val + 1 := hvalc

/-- `drop (n+1) xs = (drop n xs).tail`. -/
lemma list_drop_succ {α : Type} (xs : List α) (n : Nat) :
    xs.drop (n + 1) = (xs.drop n).tail := by
  induction xs generalizing n with
  | nil => simp
  | cons y ys ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [show (y :: ys).drop (n + 1 + 1) = ys.drop (n + 1) by rfl]
          rw [show ((y :: ys).drop (n + 1)).tail = (ys.drop n).tail by rfl]
          exact ih n

/-- `drop n l = []` iff `l.length ≤ n`. -/
lemma list_drop_eq_nil_iff {α : Type} (l : List α) (n : Nat) :
    l.drop n = [] ↔ l.length ≤ n := by
  constructor
  · intro h
    have hlen : (l.drop n).length = 0 := by rw [h]; rfl
    rw [List.length_drop] at hlen
    omega
  · intro hle
    induction n generalizing l with
    | zero =>
        have hnil : l = [] := by
          cases l with
          | nil => rfl
          | cons a b => simp at hle
        simp [hnil]
    | succ n ih =>
        cases l with
        | nil => rfl
        | cons a b =>
            have hle' : b.length ≤ n := by
              rw [List.length_cons] at hle
              omega
            rw [show (a :: b).drop (n + 1) = b.drop n by rfl]
            exact ih b hle'

/-- One `cont` step of `strong_process_marked_elements_loop.body`: exactly the
    success data of `LoopElementOk` together with the successor-state
    equations  `c = (id1, kts1, signature_builder1, …)` so that the body is
    pinned to the concrete continuation `c`. -/
def LoopStepEq {L : Type} {Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (partition : BlockPartition) (st c : SpmeState) : Prop :=
  ∃ (state_index : ST) (ts : alloc.vec.Vec Transition)
    (signature_builder1 : SigKey) (index : BT) (id1 : InternMap) (kts1 : VecTy SigKey)
    (hmut1 : BT → VecTy BT) (v : VecTy Sz) (hmut2 : BT → VecTy BT) (ei1 : Sz),
    st.2.2.2.2.2.val < st.2.2.2.1.old_elements.val.length ∧
    st.2.2.2.1.old_elements.index_usize st.2.2.2.2.2 = ok state_index ∧
    LTSInst.outgoing_transitions sys state_index = ok ts ∧
    verified.merc_reduction.signatures.strong_bisim_signature LTSInst
      (verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition)
      state_index sys partition st.2.2.1 = ok signature_builder1 ∧
    verified.merc_reduction.signature_refinement.strong_intern_signature st.1 st.2.1 signature_builder1 =
      ok (index, id1, kts1) ∧
    (∃ x : BT, st.2.2.2.1.index_to_block.index_mut_usize st.2.2.2.2.2 = ok (x, hmut1)) ∧
    verified.merc_reduction.signature_refinement.count_block_occurrence st.2.2.2.1.block_sizes index = ok v ∧
    (∃ x : BT, verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice BT) st.2.2.2.2.1 state_index = ok (x, hmut2)) ∧
    st.2.2.2.2.2 + 1#usize = ok ei1 ∧
    c.1 = id1 ∧ c.2.1 = kts1 ∧ c.2.2.1 = signature_builder1 ∧
    c.2.2.2.1 = { st.2.2.2.1 with index_to_block := hmut1 index, block_sizes := v } ∧
    c.2.2.2.2.1 = hmut2 index ∧ c.2.2.2.2.2 = ei1

/-- From `LoopStepEq`, the body literally takes the recorded `cont c` step. -/
theorem spme_step_next {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (st c : SpmeState) (h : LoopStepEq LTSInst sys partition st c) :
    verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
      LTSInst sys partition st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2
      = ok (cont c) := by
  rcases h with ⟨state_index, ts, sigb1, index, id1, kts1, hmut1, v, hmut2, ei1, hlt, hsid, hout,
    hsig, hintern, hmut1ok, hcount, hmut2ok, hadd, h1, h2, h3, h4, h5, h6⟩
  have hstep := strong_process_marked_elements_loop.body_some_step LTSInst sys partition
    st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2 hlt state_index hsid sigb1 hsig index
    id1 kts1 hintern hmut1 hmut1ok v hcount hmut2 hmut2ok ei1 hadd
  have hc :
      (id1, kts1, sigb1, { st.2.2.2.1 with index_to_block := hmut1 index, block_sizes := v },
        hmut2 index, ei1) = c := by
    calc
      (id1, kts1, sigb1, { st.2.2.2.1 with index_to_block := hmut1 index, block_sizes := v },
        hmut2 index, ei1)
          = (c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2) := by
            simp [h1, h2, h3, h4, h5, h6]
      _ = c := by
            cases c; rfl
  rw [hc] at hstep
  exact hstep

/-- `LoopElementOk` at a state yields a fully-pinned `LoopStepEq` to the
    concrete successor state produced by the body.  This is the bridge from the
    element-level invariant to the reachability table `spmeTable`. -/
theorem loopStepEq_of_elementOk {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (st : SpmeState)
    (hok : LoopElementOk LTSInst sys partition st.1 st.2.1 st.2.2.1 st.2.2.2.1
      st.2.2.2.2.1 st.2.2.2.2.2) :
    ∃ c : SpmeState, LoopStepEq LTSInst sys partition st c := by
  rcases hok with ⟨hlt, state_index, ts, hsid, hout, sigb1, index, id1, kts1, hsig, hintern,
    hmut1, hmut1ok, v, hcount, hmut2, hmut2ok, ei1, hadd⟩
  refine ⟨(id1, kts1, sigb1, { st.2.2.2.1 with index_to_block := hmut1 index, block_sizes := v },
    hmut2 index, ei1), ?_⟩
  refine ⟨state_index, ts, sigb1, index, id1, kts1, hmut1, v, hmut2, ei1, hlt, hsid, hout, hsig,
    hintern, hmut1ok, hcount, hmut2ok, hadd, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- A `LoopStepEq` step advances the drop-remainder exactly one element: the
    successor's remaining list is the tail of the current one. -/
theorem LoopStepEq.successor_drop {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    {st c : SpmeState} (h : LoopStepEq LTSInst sys partition st c) :
    (st.2.2.2.1.old_elements.val.drop st.2.2.2.2.2.val).tail
      = c.2.2.2.1.old_elements.val.drop c.2.2.2.2.2.val := by
  rcases h with ⟨state_index, ts, sigb1, index, id1, kts1, hmut1, v, hmut2, ei1, hlt, hsid, hout,
    hsig, hintern, hmut1ok, hcount, hmut2ok, hadd, h1, h2, h3, h4, h5, h6⟩
  have hold : c.2.2.2.1.old_elements.val = st.2.2.2.1.old_elements.val := by rw [h4]
  have hc5 : c.2.2.2.2.2.val = st.2.2.2.2.2.val + 1 := by
    rw [h6]
    exact usize_add_one_val st.2.2.2.2.2 ei1 hadd
  rw [hold, hc5, list_drop_succ]

/-- `x + 1` (as an overflowing-capable `usize` addition) always succeeds provided
    `x.val < max`: the failing case is exactly `max + 1`. -/
theorem add1_ok_of_lt_max (a : Sz) (h : a.val < Usize.max) : ∃ b : Sz, a + 1#usize = ok b := by
  have hb : a.val + 1 < 2 ^ System.Platform.numBits := by
    have hmax_lt : Usize.max < 2 ^ System.Platform.numBits := by
      simp [Usize.max, Usize.numBits]
    omega
  refine ⟨Usize.ofNatCore (a.val + 1) hb, ?_⟩
  rw [show a + 1#usize = UScalar.add a 1#usize by rfl]
  simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
  split_ifs with hif
  · rfl
  · exfalso
    apply hif
    simp [UScalar.check_bounds]
    exact hb

/-- Equal-length vectors produce equal `get` values at the same index, for
    possibly-different length proofs. -/
theorem vec_val_getElem_congr {α : Type} (v w : VecTy α) (h : v = w) (i : Nat)
    (hv : i < v.val.length) (hw : i < w.val.length) :
    v.val.get ⟨i, hv⟩ = w.val.get ⟨i, hw⟩ := by
  have hg : (v.val[i]? = w.val[i]? : Prop) := by rw [h]
  have hq1 : v.val[i]? = some (v.val.get ⟨i, hv⟩) := by
    simp
  have hq2 : w.val[i]? = some (w.val.get ⟨i, hw⟩) := by
    simp
  exact Option.some_inj.mp (hq1.symm.trans hg ▸ hq2)

/-- The `state_to_key` mutation produced by `index_mut` in the loop body does not
    change the length of the vector. -/
theorem vec_index_mut_preserves_length (v : VecTy BT) (i : Sz) (y x : BT)
    (back : BT → VecTy BT) (h : i.val < v.val.length)
    (hw : v.index_mut_usize i = ok (x, back)) :
    (back y).val.length = v.val.length := by
  rcases spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec v i h) with ⟨w, hw2, hpost⟩
  have hpair : w = (x, back) := Result.ok.injEq.mp (hw2.symm.trans hw)
  have hb : back = v.set i := by
    simpa [hpair] using hpost.2
  rw [hb]
  simp

/-- The `Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut` mutation of
    `state_to_key` (the Slice-level bridge used by the loop body) preserves
    the length of the vector. -/
theorem stk_back_preserves_length (stk : VecTy BT) (state_index : ST) (u x : BT)
    (hmut2 : BT → VecTy BT)
    (hw : verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
        (core.slice.index.SliceIndexUsizeSlice BT) stk state_index = ok (x, hmut2)) :
    (hmut2 u).val.length = stk.val.length := by
  by_cases hb : state_index.index.val < stk.slice.length
  · rcases spec_imp_exists (Slice.index_mut_usize_spec stk.slice state_index.index hb) with ⟨w, hw2, hpost⟩
    rcases w with ⟨x0, f⟩
    rcases hpost with ⟨hx0, hf⟩
    have hnice :
        verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
          (core.slice.index.SliceIndexUsizeSlice BT) stk state_index
          = ok (x0, fun u : BT => ({ slice := f u } : VecTy BT)) := by
      rw [vec_tagged_index_mut_eq]
      rw [hw2]
      simp
    have hpair : (x0, (fun u : BT => ({ slice := f u } : VecTy BT))) = (x, hmut2) :=
      Result.ok.injEq.mp (hnice.symm.trans hw)
    have hhmut : hmut2 = fun u : BT => ({ slice := f u } : VecTy BT) := by
      have hhmut' : (fun u : BT => ({ slice := f u } : VecTy BT)) = hmut2 :=
        congrArg Prod.snd hpair
      exact hhmut'.symm
    rw [hhmut, hf]
    change (stk.slice.set state_index.index u).val.length = stk.slice.val.length
    rw [Slice.set]
    exact Slice.setAtNat_length stk.slice state_index.index.val u
  · have hn : stk.slice.val[state_index.index.val]? = none := by
      rw [List.getElem?_eq_none_iff]
      exact Nat.not_lt.mp hb
    have hfail : Slice.index_mut_usize stk.slice state_index.index = .fail .arrayOutOfBounds := by
      simp [Slice.index_mut_usize, Slice.index_usize, Slice.getElem?_Usize_eq, hn]
    have hfull :
        verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
          (core.slice.index.SliceIndexUsizeSlice BT) stk state_index = .fail .arrayOutOfBounds := by
      rw [vec_tagged_index_mut_eq]
      rw [hfail]
      simp
    exfalso
    have hfailok : (Result.fail (Error.arrayOutOfBounds : Error) : Result (BT × (BT → VecTy BT))) = ok (x, hmut2) := by
      rw [← hfull]
      exact hw
    exact fail_not_ok hfailok

/-- The element-level invariant of `strong_process_marked_elements_loop` at its
    entry: with `olds`/`stk0` the entry's `old_elements`/`state_to_key`, every
    reachable state pinning those is `LoopElementOk`, and (for the discharge)
    each visiting state's `index_to_block` has the same length as its
    `old_elements`. -/
abbrev SpmeInvariant {L : Type} {Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (partition : BlockPartition) (olds : VecTy ST) (stk0 : VecTy BT) : Prop :=
  ∀ (st' : SpmeState) (r : List ST),
    st'.2.2.2.1.old_elements = olds →
    st'.2.2.2.2.1.val.length = stk0.val.length →
    st'.2.2.2.1.index_to_block.val.length = st'.2.2.2.1.old_elements.val.length →
    r = st'.2.2.2.1.old_elements.val.drop st'.2.2.2.2.2.val →
    r ≠ [] →
    LoopElementOk LTSInst sys partition st'.1 st'.2.1 st'.2.2.1 st'.2.2.2.1 st'.2.2.2.2.1
      st'.2.2.2.2.2

/-- The invariant is discharged once the global facts hold: the LTS's
    `outgoing_transitions` is total (`hout`), the partition's `block_number` is
    total (`hblock`), the intern `id` map answers every query (with
    `key_to_signature` below capacity on a miss), every `usize` index/counter
    stays below `max` (`hbt`/`hcnt`/`hlen`/`hstklen`), and each reached state's
    `index_to_block` keeps the length of `old_elements`. -/
theorem loopElementOk_of_reach {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (olds : VecTy ST) (stk0 : VecTy BT)
    (blockNumber : ST → BT)
    (hblock : ∀ t : ST,
        verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number
          partition t = ok (blockNumber t))
    (hout : ∀ s : ST, ∃ ts : alloc.vec.Vec Transition, LTSInst.outgoing_transitions sys s = ok ts)
    (hintern : ∀ (id : InternMap) (kts : VecTy SigKey) (sb : SigKey),
        (∃ idx : BT,
          std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
            internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst
            internEqInst id sb = ok (some (sb, idx))) ∨
        (std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
          internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst
          internEqInst id sb = ok none ∧ kts.val.length < Usize.max))
    (hbt : ∀ b : BT, b.index.val < Usize.max)
    (hcnt : ∀ (bs : VecTy Sz) (i : Nat) (hi : i < bs.val.length),
        (bs.val.get ⟨i, hi⟩).val < Usize.max)
    (hlen : olds.val.length < Usize.max)
    (hstklen : ∀ i (hi : i < olds.val.length), (olds.val[i]).index.val < stk0.val.length) :
    SpmeInvariant LTSInst sys partition olds stk0 := by
  intro st' r hold hstk hIdx hdrop hne
  have hdropne : st'.2.2.2.1.old_elements.val.drop st'.2.2.2.2.2.val ≠ [] := by
    intro hn
    apply hne
    rw [hdrop]
    exact hn
  have hlt : st'.2.2.2.2.2.val < st'.2.2.2.1.old_elements.val.length := by
    have hnotle : ¬ st'.2.2.2.1.old_elements.val.length ≤ st'.2.2.2.2.2.val := by
      intro hle
      exact hdropne ((list_drop_eq_nil_iff st'.2.2.2.1.old_elements.val st'.2.2.2.2.2.val).mpr hle)
    omega
  refine ⟨hlt, ?_⟩
  rcases spec_imp_exists (alloc.vec.Vec.index_usize_spec st'.2.2.2.1.old_elements
      st'.2.2.2.2.2 hlt) with ⟨state_index, hsid, hsval⟩
  refine ⟨state_index, ?_⟩
  rcases hout state_index with ⟨ts, houtq⟩
  refine ⟨ts, hsid, houtq, ?_⟩
  have hspec := strong_bisim_signature_spec_general LTSInst
    (verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition)
    sys partition state_index st'.2.2.1 blockNumber hblock ts houtq
  unfold StrongBisimSignatureSpec at hspec
  rcases hspec with ⟨signature_builder1, hsig, _⟩
  refine ⟨signature_builder1, ?_⟩
  rcases strong_intern_signature_total st'.1 st'.2.1 signature_builder1
    (hintern st'.1 st'.2.1 signature_builder1) with ⟨index, id1, kts1, hinternok⟩
  refine ⟨index, id1, kts1, hsig, hinternok, ?_⟩
  have hbound_idx : st'.2.2.2.2.2.val < st'.2.2.2.1.index_to_block.val.length := by
    rw [hIdx]
    exact hlt
  rcases spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec st'.2.2.2.1.index_to_block
      st'.2.2.2.2.2 hbound_idx) with ⟨w, hmut1ok, _⟩
  refine ⟨w.2, ⟨w.1, hmut1ok⟩, ?_⟩
  rcases count_block_occurrence_spec_ok st'.2.2.2.1.block_sizes index
    (add1_ok_of_lt_max index.index (hbt index))
    (by
      intro hb
      exact add1_ok_of_lt_max (st'.2.2.2.1.block_sizes.val.get ⟨index.index.val, hb⟩)
        (hcnt st'.2.2.2.1.block_sizes index.index.val hb)) with ⟨v, hcount⟩
  refine ⟨v, hcount, ?_⟩
  have hbound_stk : state_index.index.val < st'.2.2.2.2.1.val.length := by
    rw [hstk]
    have hsval' : state_index.index.val = (st'.2.2.2.1.old_elements.val.get ⟨st'.2.2.2.2.2.val, hlt⟩).index.val := by
      exact congrArg (fun z : ST => z.index.val) hsval
    rw [hsval']
    have hlt_olds : st'.2.2.2.2.2.val < olds.val.length := by
      rw [← hold]
      exact hlt
    have hbridge : st'.2.2.2.1.old_elements.val.get ⟨st'.2.2.2.2.2.val, hlt⟩ =
        olds.val.get ⟨st'.2.2.2.2.2.val, hlt_olds⟩ := by
      exact vec_val_getElem_congr st'.2.2.2.1.old_elements olds hold
        (st'.2.2.2.2.2.val) hlt hlt_olds
    rw [hbridge]
    exact hstklen st'.2.2.2.2.2.val hlt_olds
  rcases spec_imp_exists (Slice.index_mut_usize_spec st'.2.2.2.2.1.slice state_index.index hbound_stk)
    with ⟨w, hwslice, hpost⟩
  rcases w with ⟨x0, f⟩
  rcases hpost with ⟨hx0, hf⟩
  have hok :
      verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
        (core.slice.index.SliceIndexUsizeSlice BT) st'.2.2.2.2.1 state_index
        = ok (x0, fun u : BT => ({ slice := f u } : VecTy BT)) := by
    rw [vec_tagged_index_mut_eq]
    rw [hwslice]
    simp
  refine ⟨fun u : BT => ({ slice := f u } : VecTy BT), ⟨x0, hok⟩, ?_⟩
  have heimax : st'.2.2.2.2.2.val < Usize.max := by
    have hlen' : st'.2.2.2.1.old_elements.val.length < Usize.max := by
      rw [hold]
      exact hlen
    omega
  rcases add1_ok_of_lt_max st'.2.2.2.2.2 heimax with ⟨ei1, haddok⟩
  refine ⟨ei1, haddok⟩

/-- Reachability table of `strong_process_marked_elements_loop`: a sequence of
    visitable states whose successive moves exhaust exactly the remaining list
    `rest` (intended to be `old_elements.val.drop element_index.val`).  `base`
    records "no more work"; `step` records one fully-pinned `cont` move. -/
inductive spmeTable {L : Type} {Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (partition : BlockPartition) : SpmeState → List ST → Prop where
  | base : ∀ st : SpmeState, spmeTable LTSInst sys partition st []
  | step : ∀ (st c : SpmeState) (head : ST) (rest : List ST),
      LoopStepEq LTSInst sys partition st c →
      spmeTable LTSInst sys partition c rest →
      spmeTable LTSInst sys partition st (head :: rest)

/-- Build the reachability table by induction on the remaining list, assuming
    every state whose remainder is that list is `LoopElementOk`.  This isolates
    the per-element processability (the caller-side invariant) from the
    table/loop machinery. -/
theorem spmeTable_of_all_ok {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (olds : VecTy ST) (stk0 : VecTy BT)
    (h : SpmeInvariant LTSInst sys partition olds stk0)
    (st : SpmeState) (rest : List ST)
    (hold : st.2.2.2.1.old_elements = olds)
    (hstk : st.2.2.2.2.1.val.length = stk0.val.length)
    (hIdx : st.2.2.2.1.index_to_block.val.length = st.2.2.2.1.old_elements.val.length)
    (hdrop : rest = st.2.2.2.1.old_elements.val.drop st.2.2.2.2.2.val) :
    spmeTable LTSInst sys partition st rest := by
  induction rest generalizing st with
  | nil => exact spmeTable.base st
  | cons head tail ih =>
      have hne : head :: tail ≠ [] := by simp
      rcases loopStepEq_of_elementOk LTSInst sys partition st
        (h st (head :: tail) hold hstk hIdx hdrop hne) with ⟨c, hstepEq⟩
      have hd : (st.2.2.2.1.old_elements.val.drop st.2.2.2.2.2.val).tail
          = c.2.2.2.1.old_elements.val.drop c.2.2.2.2.2.val :=
        LoopStepEq.successor_drop LTSInst sys partition hstepEq
      have hd2 : (st.2.2.2.1.old_elements.val.drop st.2.2.2.2.2.val).tail = tail :=
        congrArg List.tail hdrop.symm
      rw [hd2] at hd
      have hstepEq' := hstepEq
      rcases hstepEq with ⟨state_index, ts, sigb1, index, id1, kts1, hmut1, v, hmut2, ei1, hlt,
        hsid, hout, hsig, hintern, hmut1ok, hcount, hmut2ok, hadd, h1, h2, h3, h4, h5, h6⟩
      have hold' : c.2.2.2.1.old_elements = olds := by
        rw [h4]
        change st.2.2.2.1.old_elements = olds
        exact hold
      have hstk' : c.2.2.2.2.1.val.length = stk0.val.length := by
        rw [h5]
        rcases hmut2ok with ⟨x0, hmmut2ok⟩
        rw [stk_back_preserves_length st.2.2.2.2.1 state_index index x0 hmut2 hmmut2ok]
        exact hstk
      have hIdx' : c.2.2.2.1.index_to_block.val.length = c.2.2.2.1.old_elements.val.length := by
        rw [h4]
        change (hmut1 index).val.length = st.2.2.2.1.old_elements.val.length
        rcases hmut1ok with ⟨xw, hmmut1ok⟩
        have hei_idx : st.2.2.2.2.2.val < st.2.2.2.1.index_to_block.val.length := by
          rw [hIdx]
          exact hlt
        have hlen1 : (hmut1 index).val.length = st.2.2.2.1.index_to_block.val.length :=
          vec_index_mut_preserves_length st.2.2.2.1.index_to_block st.2.2.2.2.2 index xw hmut1
            hei_idx hmmut1ok
        rw [hlen1]
        exact hIdx
      exact spmeTable.step st c head tail hstepEq' (ih c hold' hstk' hIdx' hd)

/-- If the reachability table for the remaining elements is provided, the loop
    and the structural fold agree on the result value. -/
theorem strong_process_marked_elements_loop_trace
    {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (partition : BlockPartition) (st : SpmeState) {rest : List ST}
    (hdrop : rest = st.2.2.2.1.old_elements.val.drop st.2.2.2.2.2.val)
    (htable : spmeTable LTSInst sys partition st rest) :
    verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop
      LTSInst sys partition st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2
      = spmeAcc LTSInst sys partition st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1
        st.2.2.2.2.2 rest := by
  let ul : SpmeState → Result (ControlFlow SpmeState SpmeFinal) :=
    fun (i1, k1, s1, b1, k2, e1) =>
      verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
        LTSInst sys partition i1 k1 s1 b1 k2 e1
  have hloop_unfold : ∀ x : SpmeState,
      Aeneas.Std.loop ul (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2) =
        verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop
          LTSInst sys partition x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 := by
    intro x
    rw [verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop]
  induction htable with
  | base st' =>
      have hge : st'.2.2.2.1.old_elements.val.length ≤ st'.2.2.2.2.2.val := by
        exact (list_drop_eq_nil_iff (st'.2.2.2.1.old_elements.val) st'.2.2.2.2.2.val).mp hdrop.symm
      have hdone := strong_process_marked_elements_loop.body_done_step LTSInst sys partition
        st'.1 st'.2.1 st'.2.2.1 st'.2.2.2.1 st'.2.2.2.2.1 st'.2.2.2.2.2 hge
      have hbodyapp :
          ul (st'.1, st'.2.1, st'.2.2.1, st'.2.2.2.1, st'.2.2.2.2.1, st'.2.2.2.2.2) =
            verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
              LTSInst sys partition st'.1 st'.2.1 st'.2.2.1 st'.2.2.2.1 st'.2.2.2.2.1
              st'.2.2.2.2.2 := by
        rfl
      rw [← hloop_unfold st']
      rw [loop_eq_bind ul (st'.1, st'.2.1, st'.2.2.1, st'.2.2.2.1, st'.2.2.2.2.1, st'.2.2.2.2.2)]
      rw [hbodyapp]
      rw [hdone]
      simp
      rw [spmeAcc_nil]
  | step st' c head rest hstep ht ih =>
      have hb := spme_step_next LTSInst sys partition st' c hstep
      rcases hstep with ⟨state_index, ts, sigb1, index, id1, kts1, hmut1, v, hmut2, ei1, hlt, hsid,
        hout, hsig, hintern, hmut1ok, hcount, hmut2ok, hadd, h1, h2, h3, h4, h5, h6⟩
      have hold : c.2.2.2.1.old_elements.val = st'.2.2.2.1.old_elements.val := by
        rw [h4]
      have hc5 : c.2.2.2.2.2.val = st'.2.2.2.2.2.val + 1 := by
        rw [h6]
        exact usize_add_one_val st'.2.2.2.2.2 ei1 hadd
      have hdrop' : rest = c.2.2.2.1.old_elements.val.drop c.2.2.2.2.2.val := by
        have hc : c.2.2.2.1.old_elements.val.drop c.2.2.2.2.2.val = rest := by
          calc
            c.2.2.2.1.old_elements.val.drop c.2.2.2.2.2.val
                = st'.2.2.2.1.old_elements.val.drop (st'.2.2.2.2.2.val + 1) := by rw [hold, hc5]
            _ = (st'.2.2.2.1.old_elements.val.drop st'.2.2.2.2.2.val).tail := by rw [list_drop_succ]
            _ = (head :: rest).tail := by
                  rw [hdrop]
            _ = rest := by simp
        exact hc.symm
      have hbodyapp :
          ul (st'.1, st'.2.1, st'.2.2.1, st'.2.2.2.1, st'.2.2.2.2.1, st'.2.2.2.2.2) =
            verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
              LTSInst sys partition st'.1 st'.2.1 st'.2.2.1 st'.2.2.2.1 st'.2.2.2.2.1
              st'.2.2.2.2.2 := by
        rfl
      rw [← hloop_unfold st']
      rw [loop_eq_bind ul (st'.1, st'.2.1, st'.2.2.1, st'.2.2.2.1, st'.2.2.2.2.1, st'.2.2.2.2.2)]
      rw [hbodyapp, hb]
      simp
      rw [spmeAcc_step LTSInst sys partition st'.1 st'.2.1 st'.2.2.1 st'.2.2.2.1
            st'.2.2.2.2.1 st'.2.2.2.2.2 head rest]
      rw [hb]
      simp
      have hctuple :
          (c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2) = c := by
        cases c
        rfl
      rw [← hctuple]
      rw [hloop_unfold c]
      exact ih hdrop'

/-- Loop spec in terms of the element-level invariant: if every state whose
    remainder is `rest` is `LoopElementOk`, the loop agrees with the fold. -/
theorem strong_process_marked_elements_loop_spec {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (olds : VecTy ST) (stk0 : VecTy BT)
    (st : SpmeState) {rest : List ST}
    (hold : st.2.2.2.1.old_elements = olds)
    (hstk : st.2.2.2.2.1.val.length = stk0.val.length)
    (hIdx : st.2.2.2.1.index_to_block.val.length = st.2.2.2.1.old_elements.val.length)
    (hdrop : rest = st.2.2.2.1.old_elements.val.drop st.2.2.2.2.2.val)
    (h : SpmeInvariant LTSInst sys partition olds stk0) :
    verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop
      LTSInst sys partition st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2
      = spmeAcc LTSInst sys partition st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1
        st.2.2.2.2.2 rest :=
  strong_process_marked_elements_loop_trace LTSInst sys partition st hdrop
    (spmeTable_of_all_ok LTSInst sys partition olds stk0 h st rest hold hstk hIdx hdrop)

/-- Loop spec at the initial `element_index = 0`: the remaining list is the
    whole `old_elements`, exactly as called by `strong_process_marked_elements`. -/
theorem strong_process_marked_elements_loop_spec_zero {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (id : InternMap) (kts : VecTy SigKey) (sigb : SigKey) (spb : BlockPartitionBuilder)
    (stk : VecTy BT)
    (hIdx0 : spb.index_to_block.val.length = spb.old_elements.val.length)
    (h : SpmeInvariant LTSInst sys partition spb.old_elements stk) :
    verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop
      LTSInst sys partition id kts sigb spb stk 0#usize
      = spmeAcc LTSInst sys partition id kts sigb spb stk 0#usize spb.old_elements.val := by
  have hdrop : spb.old_elements.val = spb.old_elements.val.drop (0#usize).val := by
    simp
  exact strong_process_marked_elements_loop_spec LTSInst sys partition spb.old_elements stk
    (id, kts, sigb, spb, stk, 0#usize) rfl rfl hIdx0 hdrop h

/-- The wrapper `strong_process_marked_elements` repacks the final loop state:
    with `SpmeInvariant` satisfied for the whole `old_elements`, running the
    loop from `element_index = 0` and repacking into a fresh
    `BlockPartitionBuilder` gives exactly the `spmeAcc` fold value. -/
theorem strong_process_marked_elements_contract {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (partition : BlockPartition)
    (id : InternMap) (kts : VecTy SigKey) (sigb : SigKey)
    (spb : BlockPartitionBuilder) (stk : VecTy BT)
    (hIdx0 : spb.index_to_block.val.length = spb.old_elements.val.length)
    (h : SpmeInvariant LTSInst sys partition spb.old_elements stk) :
    (do
      let (id1, kts1, sigb1, v, v1, v2, stk1) ← spmeAcc LTSInst sys partition id kts sigb spb stk 0#usize spb.old_elements.val
      Result.ok (id1, kts1, sigb1,
        ({ index_to_block := v, block_sizes := v1, old_elements := v2 } : BlockPartitionBuilder),
        stk1))
    = verified.merc_reduction.signature_refinement.strong_process_marked_elements
        LTSInst sys partition id kts sigb spb stk := by
  rw [verified.merc_reduction.signature_refinement.strong_process_marked_elements]
  rw [strong_process_marked_elements_loop_spec_zero LTSInst sys partition id kts sigb spb stk hIdx0 h]

/-!
## Contract of `strong_run_worklist_loop`

The loop is only correct when started from the context that `strong_signature_refinement` builds
(all elements in block `0`, which alone is on the worklist; empty `states`/`builder`; a
`state_to_key` of the right length) over a well-formed LTS and its own `IncomingTransitions`.
`InitialWorklistContext` captures exactly that context. The contract is split into

- `strong_run_worklist_loop_partial_correct`: *if* the loop returns, the result is correct
  (proved by induction on the loop with an invariant; no termination argument needed), and
- `strong_run_worklist_loop_terminates`: under well-formedness the loop does return
  (the refinement-rank argument described above),

and `run_worklist_loop_spec` is their conjunction. The two component theorems are still `sorry`:
they are the open proof obligations that replaced the former `run_worklist_loop_spec` axiom.
-/

/-- `ctx0` is the initial worklist context that `strong_signature_refinement` builds for a system
    with `n` states. -/
def InitialWorklistContext {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (n : Std.Usize) (ctx0 : WorklistContextStrong) : Prop :=
  ∃ ti : TagIndex Std.Usize BlockTag,
    verified.merc_utilities.tagged_index.TagIndex.new BlockTag 0#usize = ok ti ∧
    alloc.vec.FromVecArray.from (Array.make 1#usize [ti]) = ok ctx0.worklist ∧
    BlockPartition.new n = ok ctx0.partition ∧
    alloc.vec.Vec.resize_with Global
      (verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag
        LTSInst)
      (alloc.vec.Vec.new (TagIndex Std.Usize BlockTag)) n () = ok ctx0.state_to_key ∧
    alloc.vec.Vec.Insts.CoreDefaultDefault.default
      ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)) = ok ctx0.builder ∧
    BlockPartitionBuilder.Insts.CoreDefaultDefault.default = ok ctx0.split_builder ∧
    ctx0.states = alloc.vec.Vec.new (TagIndex Std.Usize StateTag)

/-- The postcondition of the loop: the returned context's partition, read through `blockOf`, is
    coherent, covers all states, is stable for the strong signature and is complete w.r.t.
    `StrongFixPoint`. -/
def WorklistLoopCorrect {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (ctx : WorklistContextStrong)
    (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag) : Prop :=
  (∀ s b, (s, b) ∈ List.zip ctx.partition.elements.val ctx.partition.element_to_block.val →
      blockOf s = b) ∧
  (∀ n, LTSInst.num_of_states sys = ok n →
    ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val → s ∈ ctx.partition.elements.val) ∧
  IsStable (fun s => StrongSignature (verified.merc_lts.lts.LTS.toLTS LTSInst sys) s blockOf)
    blockOf ∧
  ∀ s s', StrongFixPoint (verified.merc_lts.lts.LTS.toLTS LTSInst sys) s s' → blockOf s = blockOf s'

/-- Partial correctness of `strong_run_worklist_loop`: whenever it returns, the result is correct. -/
theorem strong_run_worklist_loop_partial_correct
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : LTSInst.WellFormed sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0)
    (ctx : WorklistContextStrong)
    (hrun : verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx) :
    ∃ blockOf, WorklistLoopCorrect LTSInst sys ctx blockOf := by
  sorry

/-- Termination of `strong_run_worklist_loop` from the initial context of a well-formed LTS. -/
theorem strong_run_worklist_loop_terminates
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : LTSInst.WellFormed sys)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (hinc : verified.merc_lts.incoming_transitions.IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n)
    (ctx0 : WorklistContextStrong) (hinit : InitialWorklistContext LTSInst n ctx0) :
    ∃ ctx, verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
      LTSInst sys incoming ctx0 = ok ctx := by
  sorry

/-- Contract of `strong_run_worklist_loop` from the initial context of a well-formed LTS: it
    returns a context whose partition is correct (see `WorklistLoopCorrect`). -/
theorem run_worklist_loop_spec
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : LTSInst.WellFormed sys)
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

end MercVerified.Signatures.Proofs
