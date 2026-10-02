import MercVerified.Refinement.Proofs.WorklistStep_Proofs
import MercVerified.Lts.Proofs.IncomingTransitionsCorrect_Proofs
import Signatures.Proofs.Signature_Proofs
import Aeneas.Std.WP

/-!
# The completeness/soundness invariant for `strong_run_worklist_loop`

`LoopInv` (`WorklistStep_Proofs.lean`) is purely a *termination* invariant: it never mentions
`StrongSignature`/`StrongFixPoint` at all. This file adds the missing *correctness* invariant
needed for `strong_run_worklist_loop_partial_correct`'s remaining two conjuncts (stability and
`StrongFixPoint`-completeness), carried alongside `LoopInv` through the same outer loop.

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

/-- The algorithm's own partition (read through `blockFn`) is always at least as coarse as an
    arbitrary given partition `Q` — it never separates two states `Q` keeps together — and marking
    status is coherent with `Q` (so the backward-closure marking machinery, which only ever looks
    at the algorithm's own partition, treats `Q`-equivalent states identically). Maintained as a
    loop invariant for an arbitrary `Q`, this specializes at the very end to the `StrongFixPoint`
    witness, giving `WorklistLoopCorrect`'s completeness conjunct. -/
def RefinesQ {Block : Type} (Q : ST → Block) (n : Nat) (p : BlockPartition) : Prop :=
  ∀ s s', s.index.val < n → s'.index.val < n → Q s = Q s' →
    blockFn p s = blockFn p s' ∧ (IsMarked p s.index.val ↔ IsMarked p s'.index.val)

/-- `RefinesQ` holds trivially for the initial partition: one block covers every state, and every
    state starts out uniformly marked (`marked_split = begin = 0`, see `initial_loopInv`). -/
theorem RefinesQ.initial {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (n : Sz)
    (hn : 0 < n.val) (ctx0 : WorklistContextStrong)
    (hinit : InitialWorklistContext LTSInst n ctx0)
    {Block : Type} (Q : ST → Block) :
    RefinesQ Q n.val ctx0.partition := by
  obtain ⟨ti, hti, hwl, hpart, hres, -⟩ := hinit
  have hti' : ti = ({ index := 0#usize, marker := () } : BT) := by
    simp at hti; exact hti.symm
  subst hti'
  obtain ⟨p, hnew, hPI, hN⟩ := init_partInv n hn
  have hp : ctx0.partition = p := by
    have := hnew.symm.trans hpart; simp at this; exact this.symm
  have hblk : blkAt p 0 = { begin := 0#usize, marked_split := 0#usize, «end» := n } := by
    have hlt : ∀ i, i < n.val → i < 2 ^ UScalarTy.Usize.numBits :=
      fun i hi => lt_trans hi (sz_val_lt_two_pow n)
    obtain ⟨p', hnew', hbl, -⟩ := block_partition_new_spec n hn
    have hpp : p' = p := by have := hnew'.symm.trans hnew; simpa using this
    rw [hpp] at hbl
    simp [blkAt, hbl]
  intro s s' hs hs' _
  rw [hp]
  have he2bs : (0 : Nat) = e2bAt p s.index.val := by
    have hlt := (hPI.own s.index.val hs).1
    rw [hN] at hlt
    omega
  have he2bs' : (0 : Nat) = e2bAt p s'.index.val := by
    have hlt := (hPI.own s'.index.val hs').1
    rw [hN] at hlt
    omega
  refine ⟨?_, by unfold IsMarked; rw [← he2bs, ← he2bs']; simp [hblk],
    by unfold IsMarked; rw [← he2bs, ← he2bs']; simp [hblk]⟩
  unfold blockFn
  exact merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (he2bs.symm.trans he2bs'))

/-- `RefinesQ` survives one call to `strong_partition_marked`, characterized abstractly by its
    `SplitPost` contract (so this is applicable to any concrete split call, with no
    determinism-reconciliation needed): states of `b` or of a freshly-created block are unmarked
    right afterwards (`hmk.1`, as in `WorklistStep_Proofs.lean`'s `hbase`), so `Q`-equivalence
    trivially still matches marking status there; states of an untouched block keep their old block
    record and offset (`hother`/`hmk.2`), so the fact carries over from the hypothesis `hRQ` about
    the pre-split partition. -/
theorem RefinesQ.split_preserved {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (_hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU)
    {p : BlockPartition} (hp : PartInv nU.val p) (b : BT) (nbi : VecTy BT) {p1 : BlockPartition}
    (hsplit : SplitPost LTSInst sys nU.val p b nbi p1)
    {Block : Type} (Q : ST → Block)
    (hQstable : IsStable (fun s => StrongSignature (MercVerified.Lts.toLTS LTSInst sys) s Q) Q)
    (hRQ : RefinesQ Q nU.val p) :
    RefinesQ Q nU.val p1 := by
  obtain ⟨hp1, k, hN1, hnbi, hother, hmk⟩ := hsplit
  -- a transition's target is always an in-range state (`WellFormed`'s second conjunct).
  have hsucc : ∀ s : ST, s.index.val < nU.val → ∀ μ s', MercVerified.Lts.tr LTSInst sys s μ s' →
      s'.index.val < nU.val := by
    intro s hs μ s' htr
    obtain ⟨ts, houtgoing, hmem⟩ := htr
    obtain ⟨ts', houtgoing', hbound⟩ := hwf.2.1 nU hns s hs
    have hts : ts = ts' := by have h := houtgoing.symm.trans houtgoing'; simpa using h
    exact hbound _ (hts ▸ hmem)
  -- `e2bAt p s.index.val` and `(blockFn p s).index.val` are the same `getD` lookup.
  have he2b : ∀ (p : BlockPartition) (s : ST), e2bAt p s.index.val = (blockFn p s).index.val :=
    fun _ _ => rfl
  intro t t' ht ht' hQtt'
  by_cases hold : e2bAt p t.index.val = b.index.val
  · -- `t` was in `b` before the split; by `hRQ`, so was `t'`.
    have hold' : e2bAt p t'.index.val = b.index.val := by
      have hbe := (hRQ t t' ht ht' hQtt').1
      rw [he2b, ← hbe, ← he2b, hold]
    have hlocT := hmk.2.2.1 t ht hold
    have hlocT' := hmk.2.2.1 t' ht' hold'
    have hnm : ¬ IsMarked p1 t.index.val := by
      have hme := hmk.1 (e2bAt p1 t.index.val) hlocT
      have hlt := (hp1.own t.index.val ht).2.2
      unfold IsMarked; omega
    have hnm' : ¬ IsMarked p1 t'.index.val := by
      have hme := hmk.1 (e2bAt p1 t'.index.val) hlocT'
      have hlt := (hp1.own t'.index.val ht').2.2
      unfold IsMarked; omega
    refine ⟨?_, by simp [hnm, hnm']⟩
    have hdisj :
        (¬ IsMarked p t.index.val ∧ ¬ IsMarked p t'.index.val) ∨
        (IsMarked p t.index.val ∧ IsMarked p t'.index.val ∧
          SigOf LTSInst sys p t = SigOf LTSInst sys p t') := by
      by_cases hm : IsMarked p t.index.val
      · have hm' : IsMarked p t'.index.val := (hRQ t t' ht ht' hQtt').2.mp hm
        refine Or.inr ⟨hm, hm', ?_⟩
        unfold SigOf
        apply Set.ext
        rintro ⟨μ, α⟩
        constructor
        · rintro ⟨s', htr, hblkeq⟩
          have hsr : s'.index.val < nU.val := hsucc t ht μ s' htr
          have hsig : (μ, Q s') ∈ StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t Q :=
            ⟨s', htr, rfl⟩
          have hQsig : StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t Q =
              StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t' Q := hQstable t t' hQtt'
          rw [hQsig] at hsig
          obtain ⟨s'', htr', hQeq⟩ := hsig
          have hsr' : s''.index.val < nU.val := hsucc t' ht' μ s'' htr'
          have hblkeq2 : blockFn p s' = blockFn p s'' :=
            (hRQ s' s'' hsr hsr' hQeq.symm).1
          exact ⟨s'', htr', by rw [← hblkeq2]; exact hblkeq⟩
        · rintro ⟨s', htr, hblkeq⟩
          have hsr : s'.index.val < nU.val := hsucc t' ht' μ s' htr
          have hsig : (μ, Q s') ∈ StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t' Q :=
            ⟨s', htr, rfl⟩
          have hQsig : StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t Q =
              StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t' Q := hQstable t t' hQtt'
          rw [← hQsig] at hsig
          obtain ⟨s'', htr', hQeq⟩ := hsig
          have hsr' : s''.index.val < nU.val := hsucc t ht μ s'' htr'
          have hblkeq2 : blockFn p s' = blockFn p s'' :=
            (hRQ s' s'' hsr hsr' hQeq.symm).1
          exact ⟨s'', htr', by rw [← hblkeq2]; exact hblkeq⟩
      · exact Or.inl ⟨hm, fun hm' => hm ((hRQ t t' ht ht' hQtt').2.mpr hm')⟩
    have he2beq := (hmk.2.2.2 t t' ht ht' hold hold').mpr hdisj
    unfold blockFn
    exact merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq he2beq)
  · -- `t` was untouched by the split; by `hRQ`, so was `t'`. Both keep their old block record.
    have hne' : e2bAt p t'.index.val ≠ b.index.val := by
      intro heq
      apply hold
      have hbe := (hRQ t t' ht ht' hQtt').1
      rw [he2b, hbe, ← he2b, heq]
    have hpres := hmk.2.1 t ht hold
    have hpres' := hmk.2.1 t' ht' hne'
    have hjlt : e2bAt p1 t.index.val < p.blocks.val.length := by
      rw [hpres.1]; exact (hp.own t.index.val ht).1
    have hjlt' : e2bAt p1 t'.index.val < p.blocks.val.length := by
      rw [hpres'.1]; exact (hp.own t'.index.val ht').1
    have hjne : e2bAt p1 t.index.val ≠ b.index.val := by rw [hpres.1]; exact hold
    have hjne' : e2bAt p1 t'.index.val ≠ b.index.val := by rw [hpres'.1]; exact hne'
    have hblk : blkAt p1 (e2bAt p1 t.index.val) = blkAt p (e2bAt p t.index.val) := by
      rw [hother _ hjlt hjne, hpres.1]
    have hblk' : blkAt p1 (e2bAt p1 t'.index.val) = blkAt p (e2bAt p t'.index.val) := by
      rw [hother _ hjlt' hjne', hpres'.1]
    refine ⟨?_, ?_, ?_⟩
    · have hbe := (hRQ t t' ht ht' hQtt').1
      have h3 : e2bAt p t.index.val = e2bAt p t'.index.val := by
        rw [he2b, hbe, ← he2b]
      unfold blockFn
      exact merc_utilities.tagged_index.TagIndex.ext
        (UScalar.eq_of_val_eq (hpres.1.trans (h3.trans hpres'.1.symm)))
    · intro hm
      have hm0 : IsMarked p t.index.val := by
        unfold IsMarked at hm ⊢; rw [← hblk, ← hpres.2]; exact hm
      have hm0' : IsMarked p t'.index.val := (hRQ t t' ht ht' hQtt').2.mp hm0
      unfold IsMarked; rw [hblk', hpres'.2]; exact hm0'
    · intro hm
      have hm0' : IsMarked p t'.index.val := by
        unfold IsMarked at hm ⊢; rw [← hblk', ← hpres'.2]; exact hm
      have hm0 : IsMarked p t.index.val := (hRQ t t' ht ht' hQtt').2.mpr hm0'
      unfold IsMarked; rw [hblk, hpres.2]; exact hm0

/-- `RefinesQ` survives the whole `markDirtyAcc` fold (the backward-closure re-marking of
    predecessors of the freshly split blocks): the fold never moves states between blocks
    (`DirtySem`'s first conjunct, `element_to_block` unchanged), so the block-coarseness half is
    untouched; and a state gets newly marked exactly when it has a transition into one of the new
    blocks (`PredBlk`, read off `incoming` via `IncomingTransitionsCorrect`), which `Q`-equivalent
    states do or don't share together, because `hQstable` gives them matching transitions (same
    label, `Q`-equal target) and `hRQ` (on the *targets*) then puts those matching targets in the
    same new block too. -/
theorem RefinesQ.fold_preserved {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (_hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (incoming : IncomingTransitions)
    (hIC : MercVerified.Lts.IncomingTransitionsCorrect LTSInst sys incoming)
    (nU : Sz) (hns : LTSInst.num_of_states sys = ok nU) (hnmax : nU.val ≤ Usize.max)
    (hinc : ∀ s : ST, s.index.val < nU.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < nU.val)
    (block_index : BT) (num_blocks : Sz) (l : List BT) (p1 : BlockPartition) (w : VecTy BT)
    (states : VecTy ST) (hl : ∀ nb ∈ l, nb.index.val < p1.blocks.val.length)
    (hDirty : DirtyInv nU.val p1 w)
    (hmq1 : ∀ t : ST, t.index.val < nU.val → IsMarked p1 t.index.val →
      ∃ x ∈ w.val, x.index.val = e2bAt p1 t.index.val)
    {Block : Type} (Q : ST → Block)
    (hQstable : IsStable (fun s => StrongSignature (MercVerified.Lts.toLTS LTSInst sys) s Q) Q)
    (hRQ : RefinesQ Q nU.val p1) :
    -- exposes the same `DirtyInv`/length/`DirtySem` facts `markDirtyAcc_spec` itself would, so this
    -- theorem is a drop-in replacement for that spec call wherever `RefinesQ` also needs threading
    -- through (no separate call, hence no determinism-reconciliation, needed).
    ∃ p2 w2 s2, markDirtyAcc false LTSInst sys incoming block_index num_blocks p1 w states l
        = ok (p2, w2, s2) ∧ DirtyInv nU.val p2 w2 ∧ p2.blocks.val.length = p1.blocks.val.length ∧
      DirtySem nU.val p1 p2 w2 (fun t => False ∨ ∃ nb ∈ l, nb ≠ block_index ∧
        PredBlk incoming nU.val p1 nb.index.val t) ∧
      RefinesQ Q nU.val p2 := by
  obtain ⟨p2, w2, s2, hrun, hI2, hlen2, hsem2⟩ :=
    markDirtyAcc_spec LTSInst sys incoming block_index num_blocks hnmax hinc l states hl hDirty
      (⟨rfl, fun _ _ => by simp, hmq1⟩ : DirtySem nU.val p1 p1 w (fun _ => False))
  refine ⟨p2, w2, s2, hrun, hI2, hlen2, hsem2, ?_⟩
  -- a transition's target is always an in-range state.
  have hsucc : ∀ s : ST, s.index.val < nU.val → ∀ μ s', MercVerified.Lts.tr LTSInst sys s μ s' →
      s'.index.val < nU.val := by
    intro s hs μ s' htr
    obtain ⟨ts, houtgoing, hmem⟩ := htr
    obtain ⟨ts', houtgoing', hbound⟩ := hwf.2.1 nU hns s hs
    have hts : ts = ts' := by have h := houtgoing.symm.trans houtgoing'; simpa using h
    exact hbound _ (hts ▸ hmem)
  -- `t0` has a transition into some state of block `nb` iff `t0` is recorded as a predecessor of
  -- (some state of) block `nb` in `incoming`.
  have htr_of_pred : ∀ (nb : Nat) (t0 : ST), PredBlk incoming nU.val p1 nb t0 →
      ∃ s μ, s.index.val < nU.val ∧ e2bAt p1 s.index.val = nb ∧
        MercVerified.Lts.tr LTSInst sys t0 μ s := by
    rintro nb t0 ⟨s, hsr, hsblk, res, hres, i, hires, hifrom⟩
    obtain ⟨resIC, hresIC, -, hiff⟩ := hIC nU hns s hsr
    have hreseq : res = resIC := by have h := hres.symm.trans hresIC; simpa using h
    rw [hreseq] at hires
    obtain ⟨μ, s', hs'r, htr, hlf⟩ := (hiff i).mp hires
    have hif : i.«from» = s' := congrArg Prod.snd hlf
    have hseq : s' = t0 :=
      merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (by rw [← hif]; exact hifrom))
    exact ⟨s, μ, hsr, hsblk, hseq ▸ htr⟩
  have hpred_of_tr : ∀ (s t0 : ST), s.index.val < nU.val → t0.index.val < nU.val →
      ∀ μ, MercVerified.Lts.tr LTSInst sys t0 μ s → PredBlk incoming nU.val p1 (e2bAt p1 s.index.val) t0 := by
    intro s t0 hsr ht0r μ htr
    obtain ⟨resIC, hresIC, -, hiff⟩ := hIC nU hns s hsr
    exact ⟨s, hsr, rfl, resIC, hresIC, ⟨μ, t0⟩, (hiff _).mpr ⟨μ, t0, ht0r, htr, rfl⟩, rfl⟩
  intro t t' ht ht' hQtt'
  have hblk_eq : blockFn p2 t = blockFn p2 t' := by
    have h1 : blockFn p2 t = blockFn p1 t := by unfold blockFn; rw [hsem2.1]
    have h2 : blockFn p2 t' = blockFn p1 t' := by unfold blockFn; rw [hsem2.1]
    rw [h1, h2]; exact (hRQ t t' ht ht' hQtt').1
  refine ⟨hblk_eq, ?_⟩
  have hDiff : (∃ nb ∈ l, nb ≠ block_index ∧ PredBlk incoming nU.val p1 nb.index.val t) ↔
      (∃ nb ∈ l, nb ≠ block_index ∧ PredBlk incoming nU.val p1 nb.index.val t') := by
    constructor
    · rintro ⟨nb, hnbl, hnbne, hpred⟩
      obtain ⟨s, μ, hsr, hsblk, htr⟩ := htr_of_pred nb.index.val t hpred
      have hsig : (μ, Q s) ∈ StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t Q := ⟨s, htr, rfl⟩
      have hQsig : StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t Q =
          StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t' Q := hQstable t t' hQtt'
      rw [hQsig] at hsig
      obtain ⟨s'', htr', hQeq⟩ := hsig
      have hs''r : s''.index.val < nU.val := hsucc t' ht' μ s'' htr'
      have hblkeq : blockFn p1 s = blockFn p1 s'' := (hRQ s s'' hsr hs''r hQeq.symm).1
      have hsblk'' : e2bAt p1 s''.index.val = nb.index.val := by
        unfold blockFn at hblkeq
        have : e2bAt p1 s.index.val = e2bAt p1 s''.index.val := congrArg (·.index.val) hblkeq
        rw [← this]; exact hsblk
      exact ⟨nb, hnbl, hnbne, hsblk'' ▸ hpred_of_tr s'' t' hs''r ht' μ htr'⟩
    · rintro ⟨nb, hnbl, hnbne, hpred⟩
      obtain ⟨s, μ, hsr, hsblk, htr⟩ := htr_of_pred nb.index.val t' hpred
      have hsig : (μ, Q s) ∈ StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t' Q := ⟨s, htr, rfl⟩
      have hQsig : StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t Q =
          StrongSignature (MercVerified.Lts.toLTS LTSInst sys) t' Q := hQstable t t' hQtt'
      rw [← hQsig] at hsig
      obtain ⟨s'', htr', hQeq⟩ := hsig
      have hs''r : s''.index.val < nU.val := hsucc t ht μ s'' htr'
      have hblkeq : blockFn p1 s = blockFn p1 s'' := (hRQ s s'' hsr hs''r hQeq.symm).1
      have hsblk'' : e2bAt p1 s''.index.val = nb.index.val := by
        unfold blockFn at hblkeq
        have : e2bAt p1 s.index.val = e2bAt p1 s''.index.val := congrArg (·.index.val) hblkeq
        rw [← this]; exact hsblk
      exact ⟨nb, hnbl, hnbne, hsblk'' ▸ hpred_of_tr s'' t hs''r ht μ htr'⟩
  have hm2 := hsem2.2.1 t ht
  have hm2' := hsem2.2.1 t' ht'
  simp only [false_or] at hm2 hm2'
  rw [hm2, hm2']
  have hmiff : IsMarked p1 t.index.val ↔ IsMarked p1 t'.index.val := (hRQ t t' ht ht' hQtt').2
  constructor
  · rintro (h | hD)
    · exact Or.inl (hmiff.mp h)
    · exact Or.inr (hDiff.mp hD)
  · rintro (h | hD)
    · exact Or.inl (hmiff.mpr h)
    · exact Or.inr (hDiff.mpr hD)

/-- Two same-block, doubly-unmarked states always have equal local signature relative to the
    current partition. This is the missing invariant for conjunct 3 (stability/soundness) of
    `WorklistLoopCorrect`: at loop exit every state is unmarked (`LoopInv`'s marking conjunct with an
    empty worklist), so `SettledStable` specializes there to exactly that conjunct. -/
def SettledStable {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (n : Nat) (p : BlockPartition) : Prop :=
  ∀ s s' : ST, s.index.val < n → s'.index.val < n → blockFn p s = blockFn p s' →
    ¬ IsMarked p s.index.val → ¬ IsMarked p s'.index.val →
    SigOf LTSInst sys p s = SigOf LTSInst sys p s'

/-- `SettledStable` holds vacuously for the initial partition: every state starts out uniformly
    marked (`marked_split = begin = 0`, see `initial_loopInv`), so there is no unmarked pair to
    satisfy the conclusion for. -/
theorem SettledStable.initial {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (n : Sz) (hn : 0 < n.val) (ctx0 : WorklistContextStrong)
    (hinit : InitialWorklistContext LTSInst n ctx0) :
    SettledStable LTSInst sys n.val ctx0.partition := by
  obtain ⟨ti, hti, hwl, hpart, hres, -⟩ := hinit
  have hti' : ti = ({ index := 0#usize, marker := () } : BT) := by
    simp at hti; exact hti.symm
  subst hti'
  obtain ⟨p, hnew, hPI, hN⟩ := init_partInv n hn
  have hp : ctx0.partition = p := by
    have := hnew.symm.trans hpart; simp at this; exact this.symm
  have hblk : blkAt p 0 = { begin := 0#usize, marked_split := 0#usize, «end» := n } := by
    obtain ⟨p', hnew', hbl, -⟩ := block_partition_new_spec n hn
    have hpp : p' = p := by have := hnew'.symm.trans hnew; simpa using this
    rw [hpp] at hbl
    simp [blkAt, hbl]
  intro s s' hs hs' _ hm _
  exfalso; apply hm
  rw [hp]
  have he2bs : (0 : Nat) = e2bAt p s.index.val := by
    have hlt := (hPI.own s.index.val hs).1
    rw [hN] at hlt; omega
  unfold IsMarked
  rw [← he2bs]
  simp [hblk]

/-- `SettledStable` survives one full worklist step (`strong_partition_marked` followed by the
    `markDirtyAcc` backward-closure fold): a pair that stays unmarked throughout the step either (a)
    was untouched by the split (so its own block, its successors' blocks, and its marking status are
    all literally unchanged, and the conclusion follows directly from the IH), or (b) was one of `b`'s
    original members and landed in the same post-split block as its partner (`SplitSem`'s pairwise
    conjunct handles the "both unmarked, or both marked with equal old `SigOf`" case uniformly, and a
    mixed untouched/from-`b` pairing is impossible, since their post-split block indices then live in
    disjoint ranges). In both surviving cases, staying unmarked after the fold (`¬ D`) means every
    transition target of the state kept its old block identity — even a target that was itself in `b`
    stays in `b` (post-split), since a target that moved to a genuinely new block would make the
    *source* state a `D`-predecessor of that new block (`hpred_of_tr`, mirroring
    `RefinesQ.fold_preserved`'s own use of it) — so `SigOf` relative to the post-split partition
    literally equals `SigOf` relative to the pre-split one. -/
theorem SettledStable.step_preserved {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU)
    {p : BlockPartition} (hp : PartInv nU.val p) (b : BT) (nbi : VecTy BT) {p1 : BlockPartition}
    (hsplit : SplitPost LTSInst sys nU.val p b nbi p1)
    (incoming : IncomingTransitions)
    (hIC : MercVerified.Lts.IncomingTransitionsCorrect LTSInst sys incoming)
    {p2 : BlockPartition} {D : ST → Prop}
    (hblk2 : ∀ t : ST, blockFn p2 t = blockFn p1 t)
    (hmarkIff : ∀ t : ST, t.index.val < nU.val → (IsMarked p2 t.index.val ↔ IsMarked p1 t.index.val ∨ D t))
    (hDiff : ∀ t : ST, D t ↔ ∃ nb ∈ nbi.val, nb ≠ b ∧ PredBlk incoming nU.val p1 nb.index.val t)
    (hSS : SettledStable LTSInst sys nU.val p) :
    SettledStable LTSInst sys nU.val p2 := by
  obtain ⟨hp1, k, hN1, hnbi, hother, hmk⟩ := hsplit
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hn2 := hfit nU hns
  have hlt2 : nU.val < 2 ^ UScalarTy.Usize.numBits := by have := usize_max_succ; omega
  have hN1n : p1.blocks.val.length ≤ nU.val := hp1.blocks_le_n
  have hsucc : ∀ s : ST, s.index.val < nU.val → ∀ μ s', MercVerified.Lts.tr LTSInst sys s μ s' →
      s'.index.val < nU.val := by
    intro s hs μ s' htr
    obtain ⟨ts, houtgoing, hmem⟩ := htr
    obtain ⟨ts', houtgoing', hbound⟩ := hwf.2.1 nU hns s hs
    have hts : ts = ts' := by have h := houtgoing.symm.trans houtgoing'; simpa using h
    exact hbound _ (hts ▸ hmem)
  have he2b : ∀ (q : BlockPartition) (x : ST), e2bAt q x.index.val = (blockFn q x).index.val :=
    fun _ _ => rfl
  have hpred_of_tr : ∀ (s t0 : ST), s.index.val < nU.val → t0.index.val < nU.val →
      ∀ μ, MercVerified.Lts.tr LTSInst sys t0 μ s → PredBlk incoming nU.val p1 (e2bAt p1 s.index.val) t0 := by
    intro s t0 hsr ht0r μ htr
    obtain ⟨resIC, hresIC, -, hiff⟩ := hIC nU hns s hsr
    exact ⟨s, hsr, rfl, resIC, hresIC, ⟨μ, t0⟩, (hiff _).mpr ⟨μ, t0, ht0r, htr, rfl⟩, rfl⟩
  -- a non-`D` state's transitions all keep their pre-split block identity: a target in `b` stays in
  -- `b`, and a target outside `b` is untouched, so in both cases `blockFn p1` agrees with `blockFn p`.
  have hstay : ∀ t : ST, t.index.val < nU.val → ¬ D t → ∀ μ t', MercVerified.Lts.tr LTSInst sys t μ t' →
      blockFn p1 t' = blockFn p t' := by
    intro t ht hnD μ t' htr
    have ht'r : t'.index.val < nU.val := hsucc t ht μ t' htr
    by_cases hb' : e2bAt p t'.index.val = b.index.val
    · rcases hmk.2.2.1 t' ht'r hb' with hstays | hnew
      · exact merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (by
          show e2bAt p1 t'.index.val = e2bAt p t'.index.val
          rw [hstays, hb']))
      · exfalso
        obtain ⟨hge, hlt⟩ := hnew
        have hbval : b.index.val < p.blocks.val.length := by
          have := (hp.own t'.index.val ht'r).1; rw [hb'] at this; omega
        have hxval : (uTag (e2bAt p1 t'.index.val) : BT).index.val = e2bAt p1 t'.index.val :=
          uTotal_val_of_lt (by omega)
        have hmem : (uTag (e2bAt p1 t'.index.val) : BT) ∈ nbi.val := by
          rw [hnbi]; right
          exact List.mem_map_of_mem (List.mem_range'_1.mpr ⟨hge, by omega⟩)
        have hne : (uTag (e2bAt p1 t'.index.val) : BT) ≠ b := by
          intro heq
          have hbb : (uTag (e2bAt p1 t'.index.val) : BT).index.val = b.index.val := by rw [heq]
          omega
        have hpred : PredBlk incoming nU.val p1 (uTag (e2bAt p1 t'.index.val) : BT).index.val t := by
          rw [hxval]; exact hpred_of_tr t' t ht'r ht μ htr
        exact hnD ((hDiff t).mpr ⟨uTag (e2bAt p1 t'.index.val), hmem, hne, hpred⟩)
    · have hpres := hmk.2.1 t' ht'r hb'
      exact merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq hpres.1)
  -- hence `SigOf` relative to `p1` literally equals `SigOf` relative to `p` for a non-`D` state.
  have hsig_eq : ∀ t : ST, t.index.val < nU.val → ¬ D t →
      SigOf LTSInst sys p1 t = SigOf LTSInst sys p t := by
    intro t ht hnD
    unfold SigOf
    apply Set.ext
    rintro ⟨μ, α⟩
    constructor
    · rintro ⟨t', htr, hα⟩
      exact ⟨t', htr, by rw [← hα, hstay t ht hnD μ t' htr]⟩
    · rintro ⟨t', htr, hα⟩
      exact ⟨t', htr, by rw [← hα, ← hstay t ht hnD μ t' htr]⟩
  -- `blockFn p2` agrees pointwise with `blockFn p1`, hence so do the two partitions' `SigOf`.
  have hSigOf_p2_p1 : ∀ x : ST, SigOf LTSInst sys p2 x = SigOf LTSInst sys p1 x := by
    intro x
    unfold SigOf
    apply Set.ext
    rintro ⟨μ, α⟩
    constructor
    · rintro ⟨t', htr, hα⟩; exact ⟨t', htr, by rw [← hα, hblk2]⟩
    · rintro ⟨t', htr, hα⟩; exact ⟨t', htr, by rw [← hα, ← hblk2]⟩
  -- untouched states (by the split) keep their old marking status as well as their old block record.
  have huntouched_mark : ∀ t : ST, t.index.val < nU.val → e2bAt p t.index.val ≠ b.index.val →
      (IsMarked p1 t.index.val ↔ IsMarked p t.index.val) := by
    intro t ht hbt
    have hpres := hmk.2.1 t ht hbt
    have hjlt : e2bAt p t.index.val < p.blocks.val.length := (hp.own t.index.val ht).1
    have hblkrec : blkAt p1 (e2bAt p t.index.val) = blkAt p (e2bAt p t.index.val) :=
      hother _ hjlt hbt
    unfold IsMarked
    rw [hpres.1, hpres.2, hblkrec]
  intro s s' hs hs' hbeq hm hm'
  have hnD : ¬ D s := fun hD => hm ((hmarkIff s hs).mpr (Or.inr hD))
  have hnD' : ¬ D s' := fun hD => hm' ((hmarkIff s' hs').mpr (Or.inr hD))
  have hm1 : ¬ IsMarked p1 s.index.val := fun h => hm ((hmarkIff s hs).mpr (Or.inl h))
  have hm1' : ¬ IsMarked p1 s'.index.val := fun h => hm' ((hmarkIff s' hs').mpr (Or.inl h))
  have hbeq1 : blockFn p1 s = blockFn p1 s' := by rw [← hblk2, ← hblk2]; exact hbeq
  have hidxeq : e2bAt p1 s.index.val = e2bAt p1 s'.index.val := by rw [he2b, he2b, hbeq1]
  rw [hSigOf_p2_p1, hSigOf_p2_p1]
  by_cases hbold : e2bAt p s.index.val = b.index.val
  · by_cases hbold' : e2bAt p s'.index.val = b.index.val
    · have hpairIff := (hmk.2.2.2 s s' hs hs' hbold hbold').mp hidxeq
      rw [hsig_eq s hs hnD, hsig_eq s' hs' hnD']
      rcases hpairIff with ⟨hmA, hmA'⟩ | ⟨-, -, hsigA⟩
      · exact hSS s s' hs hs'
          (merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (hbold.trans hbold'.symm)))
          hmA hmA'
      · exact hsigA
    · exfalso
      have hpres1' : e2bAt p1 s'.index.val = e2bAt p s'.index.val := (hmk.2.1 s' hs' hbold').1
      have hbval : b.index.val < p.blocks.val.length := by
        have := (hp.own s.index.val hs).1; rw [hbold] at this; exact this
      have hjlt : e2bAt p s'.index.val < p.blocks.val.length := (hp.own s'.index.val hs').1
      rcases hmk.2.2.1 s hs hbold with h | ⟨hge, -⟩ <;> omega
  · by_cases hbold' : e2bAt p s'.index.val = b.index.val
    · exfalso
      have hpres1 : e2bAt p1 s.index.val = e2bAt p s.index.val := (hmk.2.1 s hs hbold).1
      have hbval : b.index.val < p.blocks.val.length := by
        have := (hp.own s'.index.val hs').1; rw [hbold'] at this; exact this
      have hjlt : e2bAt p s.index.val < p.blocks.val.length := (hp.own s.index.val hs).1
      rcases hmk.2.2.1 s' hs' hbold' with h | ⟨hge, -⟩ <;> omega
    · have hiff : IsMarked p1 s.index.val ↔ IsMarked p s.index.val := huntouched_mark s hs hbold
      have hiff' : IsMarked p1 s'.index.val ↔ IsMarked p s'.index.val := huntouched_mark s' hs' hbold'
      have hm0 : ¬ IsMarked p s.index.val := fun h => hm1 (hiff.mpr h)
      have hm0' : ¬ IsMarked p s'.index.val := fun h => hm1' (hiff'.mpr h)
      have hpres1 : e2bAt p1 s.index.val = e2bAt p s.index.val := (hmk.2.1 s hs hbold).1
      have hpres1' : e2bAt p1 s'.index.val = e2bAt p s'.index.val := (hmk.2.1 s' hs' hbold').1
      have hbeqOld : blockFn p s = blockFn p s' :=
        merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (by
          rw [← he2b, ← he2b]; omega))
      rw [hsig_eq s hs hnD, hsig_eq s' hs' hnD']
      exact hSS s s' hs hs' hbeqOld hm0 hm0'

/-- One worklist step preserves `RefinesQ` alongside `LoopInv`: a copy of
    `strong_process_worklist_block_step`'s own proof (`WorklistStep_Proofs.lean`), applying
    `RefinesQ.split_preserved`/`RefinesQ.fold_preserved` to the very same `strong_partition_marked`/
    `markDirtyAcc` calls that proof already makes, so there is no separate derivation of `p1`/`p2` to
    reconcile against the executable computation. -/
theorem strong_process_worklist_block_step_RQ {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU) (incoming : IncomingTransitions)
    (hIC : MercVerified.Lts.IncomingTransitionsCorrect LTSInst sys incoming)
    (hinc : ∀ s : ST, s.index.val < nU.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < nU.val)
    (ctx : WorklistContextStrong) (b : BT) (w : VecTy BT) (hw : ctx.worklist.val = w.val ++ [b])
    (hI : LoopInv nU.val ctx)
    {Block : Type} (Q : ST → Block)
    (hQstable : IsStable (fun s => StrongSignature (MercVerified.Lts.toLTS LTSInst sys) s Q) Q)
    (hRQ : RefinesQ Q nU.val ctx.partition)
    (hSS : SettledStable LTSInst sys nU.val ctx.partition) :
    ∃ ctx', verified.merc_reduction.signature_refinement.strong_process_worklist_block false LTSInst
        sys incoming { ctx with worklist := w } b = ok ctx' ∧
      LoopInv nU.val ctx' ∧ worklistMeasure nU.val ctx' < worklistMeasure nU.val ctx ∧
      RefinesQ Q nU.val ctx'.partition ∧ SettledStable LTSInst sys nU.val ctx'.partition := by
  obtain ⟨⟨hp, hnd, hwl⟩, hstk, hmq⟩ := hI
  rw [hw] at hnd hwl
  have hbmem : b ∈ w.val ++ [b] := by simp
  obtain ⟨hbN, hbmark⟩ := hwl b hbmem
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hn2 := hfit nU hns
  have hnbw : b ∉ w.val := by
    intro hbw
    have := (List.nodup_append.mp hnd).2.2 b hbw b (by simp)
    exact this rfl
  have hDw : DirtyInv nU.val ctx.partition w := by
    refine ⟨hp, (List.nodup_append.mp hnd).1, ?_⟩
    intro x hx
    exact hwl x (List.mem_append_left _ hx)
  have hb0 : ctx.partition.blocks.slice.val[b.index.val]'hbN = blkAt ctx.partition b.index.val :=
    (blkAt_eq_getElem hbN).symm
  have hcon := strong_process_worklist_block_contract false LTSInst sys incoming
    { ctx with worklist := w } b hbN _ hb0 (partInv_blockWF hp hbN) hbmark
  obtain ⟨idm, hidm, hid⟩ := std.collections.hash.map.HashMapKVSGlobal.default_spec
    (alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × BT)) BT
    verified.rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault
  have hkts : (alloc.vec.Vec.new (VecTy ((TagIndex Std.Usize LabelTag) × BT))).val = [] := rfl
  obtain ⟨nbi, p1, id1, kts1, sigb1, sb1, stk1, hspm, hstk1, hsplit⟩ :=
    strong_partition_marked_spec LTSInst sys hwf hfit nU hns hp b hbN hbmark idm
      (fun q => hid _ _ _ internHash_total internBuildHasher_total q) (alloc.vec.Vec.new _) hkts ctx.builder ctx.split_builder
      ctx.state_to_key hstk
  have hRQ1 : RefinesQ Q nU.val p1 :=
    RefinesQ.split_preserved LTSInst sys hwf hfit nU hns hp b nbi hsplit Q hQstable hRQ
  have hsplit' := hsplit
  obtain ⟨hp1, k, hN1, hnbi, hother, hmk⟩ := hsplit
  have hND : DirtyInv nU.val p1 w := by
    refine ⟨hp1, hDw.2.1, fun x hx => ?_⟩
    obtain ⟨hx1, hx2⟩ := hwl x (List.mem_append_left _ hx)
    have hxb : x.index.val ≠ b.index.val := fun h =>
      hnbw (by
        have : x = b := merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq h)
        rw [← this]; exact hx)
    refine ⟨by omega, ?_⟩
    rw [hother _ hx1 hxb]; exact hx2
  have hbase : DirtySem nU.val p1 p1 w (fun _ => False) := by
    refine ⟨rfl, fun t _ => by simp, fun t ht hm => ?_⟩
    by_cases hjb : e2bAt p1 t.index.val = b.index.val
    · exfalso
      have hme := hmk.1 (e2bAt p1 t.index.val) (Or.inl hjb)
      have hlt := (hp1.own t.index.val ht).2.2
      unfold IsMarked at hm
      omega
    · by_cases hjnew : ctx.partition.blocks.val.length ≤ e2bAt p1 t.index.val ∧
          e2bAt p1 t.index.val < ctx.partition.blocks.val.length + k
      · exfalso
        have hme := hmk.1 (e2bAt p1 t.index.val) (Or.inr hjnew)
        have hlt := (hp1.own t.index.val ht).2.2
        unfold IsMarked at hm
        omega
      · have hjlt : e2bAt p1 t.index.val < ctx.partition.blocks.val.length := by
          have hown := (hp1.own t.index.val ht).1
          rw [hN1] at hown
          omega
        have hne : e2bAt ctx.partition t.index.val ≠ b.index.val := by
          intro heq
          rcases hmk.2.2.1 t ht heq with h | h
          · exact hjb h
          · exact hjnew h
        have hpres := hmk.2.1 t ht hne
        have hblk : blkAt p1 (e2bAt p1 t.index.val) = blkAt ctx.partition (e2bAt ctx.partition t.index.val) := by
          rw [hother _ hjlt hjb, hpres.1]
        have hm' : IsMarked ctx.partition t.index.val := by
          unfold IsMarked at hm ⊢
          rw [hblk, hpres.2] at hm
          exact hm
        obtain ⟨x, hx, hxe⟩ := hmq t ht hm'
        rw [hw] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, hx, by rw [hpres.1]; exact hxe⟩
        · simp at hx
          subst hx
          exact absurd hxe.symm hne
  rw [hcon]
  simp only [hidm, massert, hbmark, decide_true, verified.merc_reduction.signature_refinement.maybe_mark_backward_closure]
  simp only [Bool.false_eq_true, if_false, if_true, bind_ok]
  rw [hspm]
  simp only [bind_ok, mark_dirty_new_blocks_contract]
  show ∃ ctx', (do
      let r ← markDirtyAcc false LTSInst sys incoming b ctx.partition.blocks.len p1 w ctx.states nbi.val
      ok ({ partition := r.1, worklist := r.2.1, states := r.2.2, builder := sigb1,
            split_builder := sb1, state_to_key := stk1 } : WorklistContextStrong)) = ok ctx' ∧
    LoopInv nU.val ctx' ∧ worklistMeasure nU.val ctx' < worklistMeasure nU.val ctx ∧
    RefinesQ Q nU.val ctx'.partition ∧ SettledStable LTSInst sys nU.val ctx'.partition
  have hNn : (ctx.partition.blocks.val.length) ≤ nU.val := hp.blocks_le_n
  have hN1n : p1.blocks.val.length ≤ nU.val := hp1.blocks_le_n
  have hlenw : w.val.length + 1 = ctx.worklist.val.length := by rw [hw]; simp
  have hlt2 : nU.val < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; omega
  by_cases hk : k = 0
  · subst hk
    have hnbi' : nbi.val = [b] := by rw [hnbi]; simp
    have hSS1 : SettledStable LTSInst sys nU.val p1 := by
      have hblk2 : ∀ t : ST, blockFn p1 t = blockFn p1 t := fun _ => rfl
      have hmarkIff : ∀ t : ST, t.index.val < nU.val →
          (IsMarked p1 t.index.val ↔ IsMarked p1 t.index.val ∨ False) := fun _ _ => by simp
      have hDiff : ∀ t : ST, (False : Prop) ↔
          ∃ nb ∈ nbi.val, nb ≠ b ∧ PredBlk incoming nU.val p1 nb.index.val t := by
        intro t
        constructor
        · exact False.elim
        · rintro ⟨nb, hnb, hne, -⟩
          apply hne
          rw [hnbi'] at hnb
          simpa using hnb
      exact SettledStable.step_preserved LTSInst sys hwf hfit nU hns hp b nbi hsplit' incoming hIC
        hblk2 hmarkIff hDiff hSS
    rw [hnbi', markDirtyAcc_cons, markDirtyStep_pos false LTSInst sys incoming b _ b p1 w ctx.states rfl]
    simp only [bind_ok, markDirtyAcc]
    refine ⟨_, rfl, ⟨hND, hstk1, hbase.2.2⟩, ?_, hRQ1, hSS1⟩
    unfold worklistMeasure numBlocks
    simp only []
    rw [hN1, Nat.add_zero]
    omega
  · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    obtain ⟨p2, w2, s2, hrun, hI2, hlen2, hsem2, hRQ2⟩ := RefinesQ.fold_preserved LTSInst sys hwf hfit
      incoming hIC nU hns hnmax hinc b (alloc.vec.Vec.len ctx.partition.blocks) nbi.val p1 w ctx.states
      (by
        intro x hx
        rw [hnbi] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
          have hj' := List.mem_range'_1.mp hj
          show (uTag j : BT).index.val < _
          simp only [uTag]
          rw [uTotal_val_of_lt (by omega)]
          omega) hND hbase.2.2 Q hQstable hRQ1
    have hSS2 : SettledStable LTSInst sys nU.val p2 := by
      have hblk2 : ∀ t : ST, blockFn p2 t = blockFn p1 t := by
        intro t; unfold blockFn; rw [hsem2.1]
      have hmarkIff : ∀ t : ST, t.index.val < nU.val →
          (IsMarked p2 t.index.val ↔ IsMarked p1 t.index.val ∨
            (∃ nb ∈ nbi.val, nb ≠ b ∧ PredBlk incoming nU.val p1 nb.index.val t)) := by
        intro t ht
        have := hsem2.2.1 t ht
        simpa using this
      have hDiff : ∀ t : ST, (∃ nb ∈ nbi.val, nb ≠ b ∧ PredBlk incoming nU.val p1 nb.index.val t) ↔
          ∃ nb ∈ nbi.val, nb ≠ b ∧ PredBlk incoming nU.val p1 nb.index.val t := fun _ => Iff.rfl
      exact SettledStable.step_preserved LTSInst sys hwf hfit nU hns hp b nbi hsplit' incoming hIC
        hblk2 hmarkIff hDiff hSS
    rw [hrun]
    simp only [bind_ok]
    refine ⟨_, rfl, ⟨hI2, hstk1, hsem2.2.2⟩, ?_, hRQ2, hSS2⟩
    have hN2n : p2.blocks.val.length ≤ nU.val := hI2.1.blocks_le_n
    have hw2 : w2.val.length ≤ p2.blocks.val.length :=
      nodup_bounded_length_le _ _ hI2.2.1 (fun x hx => (hI2.2.2 x hx).1)
    unfold worklistMeasure numBlocks
    simp only []
    rw [hlen2, hN1]
    rw [hlen2] at hw2 hN2n
    rw [hN1] at hw2 hN2n hN1n
    obtain ⟨a, ha⟩ : ∃ a, a = nU.val - (ctx.partition.blocks.val.length + k) := ⟨_, rfl⟩
    have hsub : nU.val - ctx.partition.blocks.val.length = a + k := by omega
    rw [← ha, hsub]
    have : (a + k) * (nU.val + 1) = a * (nU.val + 1) + k * (nU.val + 1) := by ring
    have hk1 : nU.val + 1 ≤ k * (nU.val + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

end MercVerified.Refinement.Proofs
