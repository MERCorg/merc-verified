import MercVerified.Refinement.Proofs.MarkDirty_Proofs
import Aeneas.Std.WP

/-!
# One iteration of `strong_run_worklist_loop` (non-branching)

`strong_process_worklist_block` keeps `LoopInv` and strictly decreases `worklistMeasure`.

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

/-- The loop invariant of the termination proof: the worklist bookkeeping (`DirtyInv`), the key
    table's length, and every currently marked state's block is on the worklist. -/
def LoopInv (n : Nat) (ctx : WorklistContextStrong) : Prop :=
  DirtyInv n ctx.partition ctx.worklist ∧ ctx.state_to_key.val.length = n ∧
  ∀ t : ST, t.index.val < n → IsMarked ctx.partition t.index.val →
    ∃ x ∈ ctx.worklist.val, x.index.val = e2bAt ctx.partition t.index.val

theorem strong_process_worklist_block_step {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU) (incoming : IncomingTransitions)
    (hinc : ∀ s : ST, s.index.val < nU.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < nU.val)
    (ctx : WorklistContextStrong) (b : BT) (w : VecTy BT) (hw : ctx.worklist.val = w.val ++ [b])
    (hI : LoopInv nU.val ctx) :
    ∃ ctx', verified.merc_reduction.signature_refinement.strong_process_worklist_block false LTSInst
        sys incoming { ctx with worklist := w } b = ok ctx' ∧
      LoopInv nU.val ctx' ∧ worklistMeasure nU.val ctx' < worklistMeasure nU.val ctx := by
  obtain ⟨⟨hp, hnd, hwl⟩, hstk, hmq⟩ := hI
  rw [hw] at hnd hwl
  have hbmem : b ∈ w.val ++ [b] := by simp
  obtain ⟨hbN, hbmark⟩ := hwl b hbmem
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hn2 := hwf.2.2.1 nU hns
  -- the worklist without `b`
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
    { ctx with worklist := w } b hbN _ hb0 hbmark
  obtain ⟨idm, hidm, hid⟩ := std.collections.hash.map.HashMapKVSGlobal.default_spec
    (alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × BT)) BT
    verified.rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault
  have hkts : (alloc.vec.Vec.new (VecTy ((TagIndex Std.Usize LabelTag) × BT))).val = [] := rfl
  obtain ⟨nbi, p1, id1, kts1, sigb1, sb1, stk1, hspm, hstk1, hsplit⟩ :=
    strong_partition_marked_spec LTSInst sys hwf nU hns hp b hbN hbmark idm
      (fun q => hid _ _ _ q) (alloc.vec.Vec.new _) hkts ctx.builder ctx.split_builder
      ctx.state_to_key hstk
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
  -- every state marked in the freshly split `p1` is already queued in `w`: states of `b` or of a
  -- new block are unmarked right after the split (`hmk.1`), and states of an untouched block keep
  -- their old block record and offset (`hmk.2`/`hother`), so the fact carries over from `hmq`.
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
  simp only [hidm, bind_tc_ok, massert, hbmark, decide_true, verified.merc_reduction.signature_refinement.maybe_mark_backward_closure]
  simp only [Bool.false_eq_true, if_false, if_true, bind_tc_ok]
  rw [hspm]
  simp only [bind_tc_ok, mark_dirty_new_blocks_contract]
  show ∃ ctx', (do
      let r ← markDirtyAcc false LTSInst sys incoming b ctx.partition.blocks.len p1 w ctx.states nbi.val
      ok ({ partition := r.1, worklist := r.2.1, states := r.2.2, builder := sigb1,
            split_builder := sb1, state_to_key := stk1 } : WorklistContextStrong)) = ok ctx' ∧
    LoopInv nU.val ctx' ∧ worklistMeasure nU.val ctx' < worklistMeasure nU.val ctx
  have hNn : (ctx.partition.blocks.val.length) ≤ nU.val := hp.blocks_le_n
  have hN1n : p1.blocks.val.length ≤ nU.val := hp1.blocks_le_n
  have hlenw : w.val.length + 1 = ctx.worklist.val.length := by rw [hw]; simp
  have hlt2 : nU.val < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; omega
  by_cases hk : k = 0
  · subst hk
    have hnbi' : nbi.val = [b] := by rw [hnbi]; simp
    rw [hnbi', markDirtyAcc_cons, markDirtyStep_pos false LTSInst sys incoming b _ b p1 w ctx.states rfl]
    simp only [bind_tc_ok, markDirtyAcc]
    refine ⟨_, rfl, ⟨hND, hstk1, hbase.2.2⟩, ?_⟩
    unfold worklistMeasure numBlocks
    simp only []
    rw [hN1, Nat.add_zero]
    omega
  · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    obtain ⟨p2, w2, s2, hrun, hI2, hlen2, hsem2⟩ := markDirtyAcc_spec LTSInst sys incoming b
      (alloc.vec.Vec.len ctx.partition.blocks) hnmax hinc nbi.val ctx.states (p := p1) (w := w) (by
        intro x hx
        rw [hnbi] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
          have hj' := List.mem_range'_1.mp hj
          show (uTag j : BT).index.val < _
          simp only [uTag]
          rw [uTotal_val_of_lt (by omega)]
          omega) hND hbase
    rw [hrun]
    simp only [bind_tc_ok]
    refine ⟨_, rfl, ⟨hI2, hstk1, hsem2.2.2⟩, ?_⟩
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
