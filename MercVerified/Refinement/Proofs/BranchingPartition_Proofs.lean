import MercVerified.Refinement.Proofs.BranchingProcess_Proofs
import MercVerified.Refinement.Proofs.Split_Proofs
import Aeneas.Std.WP

/-!
# `branching_partition_marked`

The branching analogue of `strong_partition_marked_spec`: the split key is the abstract key
computation `Sigref.RP.keysOf`.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The effect of a split on the partition, with the split key `sg`. -/
def SplitPostG {X : Type} (sg : ST → X) (n : Nat)
    (p : BlockPartition) (b : BT) (nbi : VecTy BT) (p' : BlockPartition) : Prop :=
  PartInv n p' ∧ ∃ k, p'.blocks.val.length = p.blocks.val.length + k ∧
    nbi.val = b :: (List.range' p.blocks.val.length k).map uTag ∧
    (∀ j, j < p.blocks.val.length → j ≠ b.index.val → blkAt p' j = blkAt p j) ∧
    (∀ j, (j = b.index.val ∨ (p.blocks.val.length ≤ j ∧ j < p.blocks.val.length + k)) →
      (blkAt p' j).marked_split.val = (blkAt p' j).«end».val) ∧
    SplitSemG sg n p b k p'

open verified.merc_reduction.signature_refinement in
theorem branching_partition_marked_nontrivial_contract {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (partition : BlockPartition) (block_index : BT) (id : InternMap) (kts : VecTy SigKey)
    (sigb : SigKey) (spb : BlockPartitionBuilder) (stk : VecTy BT)
    (hAll : verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned partition block_index = ok false) :
    branching_partition_marked LTSInst sys partition block_index id kts sigb spb stk =
      (do
        let spb1 ←
          verified.merc_reduction.block_partition.BlockPartition.marked_elements_sorted
            partition block_index spb
        let (id1, kts1, sigb1, spb2, stk1) ←
          branching_process_marked_elements LTSInst sys partition id kts sigb spb1 stk
        let (v, partition1, spb3) ←
          verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked
            partition block_index spb2
        ok (v, partition1, id1, kts1, sigb1, spb3, stk1)) := by
  unfold branching_partition_marked
  rw [hAll]
  simp

/-- The processed states `olds` as `Fin n` are the dirty states of the block, in order. -/
theorem oldsF_eq {n : Nat} (hn0 : 0 < n) (p : BlockPartition) (b : Nat) (olds : List ST)
    (hold : ∀ x ∈ olds, x.index.val < n)
    (hsorted : List.Pairwise (fun a c : ST => a.index.val < c.index.val) olds)
    (hmem : ∀ x : ST, x.index.val < n →
      ((e2bAt p x.index.val = b ∧ IsMarked p x.index.val) ↔ x ∈ olds)) (hn : n ≤ Usize.max) :
    olds.map (toFin hn0) = Sigref.RP.sortedDirty (bdOf p n) b := by
  obtain ⟨hpw, hmemD⟩ := Sigref.RP.sortedDirty_facts (bdOf p n) b
  have htf : ∀ s ∈ olds, (toFin hn0 s).val = s.index.val := fun s hs =>
    Nat.mod_eq_of_lt (hold s hs)
  have hpw' : List.Pairwise (· < ·) (olds.map (toFin hn0)) := by
    rw [List.pairwise_map]
    refine hsorted.imp_of_mem (fun {a c} ha hc h => ?_)
    show (toFin hn0 a).val < (toFin hn0 c).val
    rw [htf a ha, htf c hc]; exact h
  refine List.Pairwise.eq_of_mem_iff hpw' hpw (fun x => ?_)
  rw [hmemD x]
  constructor
  · intro hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    have := (hmem s (hold s hs)).2 hs
    rw [← htf s hs] at this
    exact this
  · intro hx
    have hxs : (stOf x).index.val = x.val := stOf_index x hn
    have hin := (hmem (stOf x) (by rw [hxs]; exact x.2)).1 (by rw [hxs]; exact hx)
    refine List.mem_map.2 ⟨stOf x, hin, ?_⟩
    apply Fin.ext
    show (stOf x).index.val % n = x.val
    rw [hxs]; exact Nat.mod_eq_of_lt x.2

open verified.merc_reduction.signature_refinement in
/-- Contract of `branching_partition_marked` on a block that has marked elements: the split key is
the abstract key computation `keysOf`. -/
theorem branching_partition_marked_spec {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU) (hn0 : 0 < nU.val)
    {nl : Std.Usize} (hE : CEnv LTSInst sys nl) (htopo : ConcTopo LTSInst sys)
    {p : BlockPartition} (hp : PartInv nU.val p) (b : BT) (hb : b.index.val < p.blocks.val.length)
    (hmark : (blkAt p b.index.val).marked_split.val < (blkAt p b.index.val).«end».val)
    (id : InternMap)
    (hid : ∀ q, std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
      internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst internEqInst id q = ok none)
    (kts : VecTy SigKey) (hkts : kts.val = []) (sigb : SigKey) (sb : BlockPartitionBuilder)
    (stk : VecTy BT) (hstk : stk.val.length = nU.val) :
    ∃ nbi p' id1 kts1 sigb1 sb1 stk1,
      branching_partition_marked LTSInst sys p b id kts sigb sb stk
        = ok (nbi, p', id1, kts1, sigb1, sb1, stk1) ∧
      stk1.val.length = nU.val ∧
      SplitPostG (fun s : ST => Sigref.RP.keysOf (aLTS LTSInst sys nU.val) (bdOf p nU.val)
        b.index.val (keyOf stk) (toFin hn0 s)) nU.val p b nbi p' := by
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hn2 := hfit nU hns
  have hn : nU.val < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; omega
  have h2n : 2 * nU.val ≤ Usize.max := by nlinarith
  obtain ⟨tb, htb, htbl⟩ := is_trivially_partitioned_ok hp b hb
  cases tb with
  | true =>
    obtain ⟨v0, p0, heq, hv, hpb, hpeq⟩ := trivial_partition_marked_contract p b hb
    refine ⟨v0, p0, id, kts, sigb, sb, stk, ?_, hstk, ?_⟩
    · unfold branching_partition_marked
      rw [htb]
      simp only [bind_ok, if_true]
      rw [heq]
      simp
    · have hbk := hp.blk b.index.val hb
      have hP := hp.set_marked_split b.index hb (blkAt p b.index.val).«end» (by omega) (by omega)
      have hEq : p0 = { p with blocks := ({ slice := p.blocks.slice.set b.index { blkAt p b.index.val with marked_split := (blkAt p b.index.val).«end» } } : alloc.vec.Vec verified.merc_reduction.block_partition.Block) } := by
        rw [hpeq, blkAt_eq_getElem hb]
      subst hEq
      have hsingle := htbl rfl
      refine ⟨hP, 0, ?_, ?_, ?_, ?_, ?_⟩
      · show (p.blocks.slice.set _ _).val.length = _
        rw [Slice.set_val_eq, List.length_set]; rfl
      · rw [hv]; simp
      · intro j hj hne
        rw [blkAt_set b.index hb, if_neg (by omega)]
      · intro j hj
        rw [blkAt_set b.index hb]
        have : j = b.index.val := by omega
        rw [if_pos this.symm]
      · -- the semantics: nothing moves, the block has a single state
        have he2b : ∀ s : Nat, e2bAt ({ p with blocks := ({ slice := p.blocks.slice.set b.index { blkAt p b.index.val with marked_split := (blkAt p b.index.val).«end» } } : alloc.vec.Vec verified.merc_reduction.block_partition.Block) } : BlockPartition) s = e2bAt p s := fun s => rfl
        have hoff : ∀ s : Nat, offAt ({ p with blocks := ({ slice := p.blocks.slice.set b.index { blkAt p b.index.val with marked_split := (blkAt p b.index.val).«end» } } : alloc.vec.Vec verified.merc_reduction.block_partition.Block) } : BlockPartition) s = offAt p s := fun s => rfl
        refine ⟨fun s hs hne => ⟨he2b _, hoff _⟩, fun s hs hX => Or.inl (by rw [he2b]; exact hX), ?_⟩
        intro s s' hs hs' hX hX'
        rw [he2b, he2b]
        have hXs := (by
          obtain ⟨h1, h2, h3⟩ := hp.own s.index.val hs
          rw [hX] at h2 h3; exact ⟨h2, h3⟩ : (blkAt p b.index.val).begin.val ≤ offAt p s.index.val ∧
            offAt p s.index.val < (blkAt p b.index.val).«end».val)
        have hXs' := (by
          obtain ⟨h1, h2, h3⟩ := hp.own s'.index.val hs'
          rw [hX'] at h2 h3; exact ⟨h2, h3⟩ : (blkAt p b.index.val).begin.val ≤ offAt p s'.index.val ∧
            offAt p s'.index.val < (blkAt p b.index.val).«end».val)
        have hoeq : offAt p s.index.val = offAt p s'.index.val := by omega
        have hss : s = s' := by
          have e1 := hp.inv s.index.val hs
          have e2 := hp.inv s'.index.val hs'
          rw [hoeq] at e1
          exact tag_eq_of_val (e1.symm.trans e2)
        subst hss
        by_cases hm : IsMarked p s.index.val
        · exact ⟨fun _ => Or.inr ⟨hm, hm, rfl⟩, fun _ => rfl⟩
        · exact ⟨fun _ => Or.inl ⟨hm, hm⟩, fun _ => rfl⟩
  | false =>
    obtain ⟨sb1, hsb1, hbs1, hi2b1, hperm1, hsort1⟩ := marked_elements_sorted_spec hp b hb sb
    have hbk := hp.blk b.index.val hb
    set bk := blkAt p b.index.val with hbkdef
    have hreg_len : (regionElems p bk.marked_split.val (bk.«end».val - bk.marked_split.val)).length
        = bk.«end».val - bk.marked_split.val := by simp [regionElems]
    have holdlen : sb1.old_elements.val.length = bk.«end».val - bk.marked_split.val := by
      rw [hperm1.length_eq, hreg_len]
    have hold : ∀ x ∈ sb1.old_elements.val, x.index.val < nU.val := fun x hx =>
      regionElems_lt hp _ _ (by omega) x (hperm1.subset hx)
    have hmemO : ∀ x : ST, x.index.val < nU.val →
        ((e2bAt p x.index.val = b.index.val ∧ IsMarked p x.index.val) ↔ x ∈ sb1.old_elements.val) := by
      intro x hx
      have hXiff : e2bAt p x.index.val = b.index.val ↔
          (bk.begin.val ≤ offAt p x.index.val ∧ offAt p x.index.val < bk.«end».val) := by
        obtain ⟨h1, h2, h3⟩ := hp.own x.index.val hx
        constructor
        · intro h; rw [h] at h2 h3; exact ⟨h2, h3⟩
        · rintro ⟨h4, h5⟩; exact hp.pos_block_unique h1 hb ⟨h2, h3⟩ ⟨h4, h5⟩
      have hmsend : bk.marked_split.val + (bk.«end».val - bk.marked_split.val) = bk.«end».val := by
        omega
      have hbeg : bk.begin.val ≤ bk.marked_split.val := by omega
      have hin := idx_in_old_iff hp sb1.old_elements.val _ _ hperm1 (by omega) hx
      have hxold : x ∈ sb1.old_elements.val ↔ (∃ y ∈ sb1.old_elements.val, y.index.val = x.index.val) := by
        constructor
        · intro h; exact ⟨x, h, rfl⟩
        · rintro ⟨y, hy, hyx⟩
          have : y = x := merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq hyx)
          rwa [this] at hy
      rw [hxold, hin]
      constructor
      · rintro ⟨hbx, hmk⟩
        have hmk' : bk.marked_split.val ≤ offAt p x.index.val := by
          unfold IsMarked at hmk; rw [hbx] at hmk; exact hmk
        have h5 := (hXiff.1 hbx).2
        exact ⟨hmk', by rw [hmsend]; exact h5⟩
      · rintro ⟨h1, h2⟩
        rw [hmsend] at h2
        have hbx : e2bAt p x.index.val = b.index.val :=
          hXiff.2 ⟨le_trans hbeg h1, h2⟩
        refine ⟨hbx, ?_⟩
        unfold IsMarked; rw [hbx]; exact h1
    obtain ⟨id1, kts1, sigb1, sb2, stk1, hspme, hold2, hlen2, hstk2, htk, hcnt, hpos, hsem⟩ :=
      branching_process_marked_elements_dense LTSInst sys hwf nU hns hn0 hE htopo hp b.index.val hold
        (by omega) hsort1 hmemO id hid kts hkts sigb sb1 stk hstk rfl
        (by rw [hi2b1]; intro x hx; simp at hx; rw [hx.2]; rfl)
        (by rw [hi2b1]; simp [holdlen]) hbs1
    have hd : BuilderDense p b sb2 (sb2.block_sizes.val.map (fun z => z.val))
        (sb2.index_to_block.val.map (fun x => x.index.val)) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, htk, hcnt, hpos⟩
      · simp [hold2, hlen2, holdlen]
      · simp only [List.length_map, hlen2, holdlen]
        rw [hold2]; exact hperm1
      · simp [hlen2, holdlen, hbkdef]
    obtain ⟨nbi, p3, bo1, hfin, hpost⟩ := finish_partition_marked_spec hp b hb hmark sb2 _ _ hd hn hnmax h2n
    refine ⟨nbi, p3, id1, kts1, sigb1, { sb2 with block_sizes := bo1 }, stk1, ?_, hstk2, ?_⟩
    · rw [branching_partition_marked_nontrivial_contract LTSInst sys p b id kts sigb sb stk htb, hsb1]
      simp only [bind_ok]
      rw [hspme]
      simp only [bind_ok]
      show (do
        let (v, partition1, split_builder3) ←
          verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked p b sb2
        ok (v, partition1, id1, kts1, sigb1, split_builder3, stk1)) = _
      rw [hfin]
      simp
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
      refine ⟨h1, _, h2, h3, h4, h5, ?_⟩
      have hcl_len : (sb2.index_to_block.val.map (fun x => x.index.val)).length =
          bk.«end».val - bk.marked_split.val := by
        simp [hlen2, holdlen]
      have hoLen : sb2.old_elements.val.length = (sb2.index_to_block.val.map (fun x => x.index.val)).length := by
        simp [hold2, hlen2, holdlen]
      have hperm2 : sb2.old_elements.val.Perm (regionElems p bk.marked_split.val
          (sb2.index_to_block.val.map (fun x => x.index.val)).length) := by
        rw [hcl_len, hold2]; simpa [hbkdef] using hperm1
      have hlt2 : ∀ x ∈ sb2.index_to_block.val.map (fun x => x.index.val),
          x < (sb2.block_sizes.val.map (fun z => z.val)).length := htk
      -- the classes are the abstract keys
      have hfe := oldsF_eq hn0 p b.index.val sb1.old_elements.val hold hsort1 hmemO hnmax
      have hrunkeys : ∀ a : Fin nU.val, keyOf (n := nU.val) stk1 a =
          Sigref.RP.keysOf (aLTS LTSInst sys nU.val) (bdOf p nU.val) b.index.val (keyOf stk) a := by
        intro a
        have h := congrArg Sigref.KC.key hsem.abs
        rw [List.take_length, hfe] at h
        exact congrFun h a
      have hkeyEq : ∀ t, t < sb1.old_elements.val.length →
          clsAt sb2 t = Sigref.RP.keysOf (aLTS LTSInst sys nU.val) (bdOf p nU.val) b.index.val
            (keyOf stk) (toFin hn0 (sb1.old_elements.val.getD t zST)) := by
        intro t ht
        rw [← hrunkeys, hsem.cls t ht]
        have hmem' : sb1.old_elements.val.getD t zST ∈ sb1.old_elements.val := by
          rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _
        show _ = (stk1.val.getD (toFin hn0 (sb1.old_elements.val.getD t zST)).val zBT).index.val
        rw [show (toFin hn0 (sb1.old_elements.val.getD t zST)).val =
          (sb1.old_elements.val.getD t zST).index.val from Nat.mod_eq_of_lt (hold _ hmem')]
      refine split_sem_nontrivialG _ hp b hb _ _ rfl _ _ p3 (by rw [hcl_len]) hoLen hperm2 hlt2
        (by simpa [List.length_map] using h6) ?_
      intro t t' ht ht'
      have hcl_old : (sb2.index_to_block.val.map (fun x => x.index.val)).length = sb1.old_elements.val.length := by
        simp [hlen2]
      have e1 : ∀ t, (sb2.index_to_block.val.map (fun x => x.index.val)).getD t 0 = clsAt sb2 t := by
        intro t
        unfold clsAt
        by_cases ht : t < sb2.index_to_block.val.length
        · rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getD_eq_getElem _ _ ht]; simp
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]; rfl
      rw [e1, e1]
      have e2 : sb2.old_elements.val = sb1.old_elements.val := by rw [hold2]
      rw [e2]
      rw [hkeyEq t (by rw [← hcl_old]; exact ht), hkeyEq t' (by rw [← hcl_old]; exact ht')]

end MercVerified.Refinement.Proofs
