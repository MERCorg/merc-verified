import MercVerified.Refinement.Proofs.Spme_Proofs
import Aeneas.Std.WP

/-!
# `strong_partition_marked`: structure and semantics of the split

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The block map read off the partition: `t ↦ element_to_block[t]`. -/
def blockFn (p : BlockPartition) : ST → BT := fun t => p.element_to_block.val.getD t.index.val zBT

/-- The strong signature of a state under the partition's block map. -/
def SigOf {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (p : BlockPartition) (s : ST) : Set ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)) :=
  StrongSignature (MercVerified.Lts.toLTS LTSInst sys) s (blockFn p)

/-- The semantic effect of splitting block `b` of `p` into `p1` (with `k` new blocks): states
    outside `b` keep block and offset; states of `b` end up in `b` or one of the new blocks; and two
    states of `b` share a block afterwards iff both were unmarked, or both were marked with equal
    strong signature. -/
def SplitSem {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (n : Nat)
    (p : BlockPartition) (b : BT) (k : Nat) (p1 : BlockPartition) : Prop :=
  (∀ s : ST, s.index.val < n → e2bAt p s.index.val ≠ b.index.val →
      e2bAt p1 s.index.val = e2bAt p s.index.val ∧ offAt p1 s.index.val = offAt p s.index.val) ∧
  (∀ s : ST, s.index.val < n → e2bAt p s.index.val = b.index.val →
      e2bAt p1 s.index.val = b.index.val ∨
        (p.blocks.val.length ≤ e2bAt p1 s.index.val ∧ e2bAt p1 s.index.val < p.blocks.val.length + k)) ∧
  (∀ s s' : ST, s.index.val < n → s'.index.val < n → e2bAt p s.index.val = b.index.val →
      e2bAt p s'.index.val = b.index.val →
      (e2bAt p1 s.index.val = e2bAt p1 s'.index.val ↔
        ((¬ IsMarked p s.index.val ∧ ¬ IsMarked p s'.index.val) ∨
          (IsMarked p s.index.val ∧ IsMarked p s'.index.val ∧
            SigOf LTSInst sys p s = SigOf LTSInst sys p s'))))

theorem swapIdx_inj {l r a a' : Nat} (h : swapIdx l r a = swapIdx l r a') : a = a' := by
  have := congrArg (swapIdx l r) h
  rwa [swapIdx_invol, swapIdx_invol] at this

/-- Two states get the same class iff their signature sets are equal. -/
theorem cls_eq_iff_sig {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (bn : ST → BT) {olds : List ST} {kts : VecTy SigKey} {cl : Nat → Nat} {len : Nat}
    (hnd : kts.val.Nodup)
    (hcls : ∀ t, t < len → cl t < kts.val.length ∧
      IsSigKey LTSInst sys bn (olds.getD t zST) (kts.val.getD (cl t) emptyKey))
    {t t' : Nat} (ht : t < len) (ht' : t' < len) :
    cl t = cl t' ↔
      StrongSignature (MercVerified.Lts.toLTS LTSInst sys) (olds.getD t zST) bn =
        StrongSignature (MercVerified.Lts.toLTS LTSInst sys) (olds.getD t' zST) bn := by
  obtain ⟨hc1, hk1, hs1⟩ := hcls t ht
  obtain ⟨hc2, hk2, hs2⟩ := hcls t' ht'
  constructor
  · intro h
    rw [h] at hk1
    ext ⟨μ, β⟩
    rw [← hk1, ← hk2]
  · intro h
    have hmem : ∀ x, x ∈ (kts.val.getD (cl t) emptyKey).val ↔ x ∈ (kts.val.getD (cl t') emptyKey).val := by
      rintro ⟨μ, β⟩
      rw [hk1, hk2, h]
    have hk : kts.val.getD (cl t) emptyKey = kts.val.getD (cl t') emptyKey :=
      alloc.vec.Vec.ext _ _ (sigKey_unique hs1 hs2 hmem)
    rw [List.getD_eq_getElem _ _ hc1, List.getD_eq_getElem _ _ hc2] at hk
    exact (List.Nodup.getElem_inj_iff hnd).mp hk

theorem labelIdx_inj {bi N K : Nat} {u : Bool} (hb : bi < N) {c c' : Nat} (_hc : c < K) (_hc' : c' < K)
    (h : labelIdx bi u N c = labelIdx bi u N c') : c = c' := by
  cases u
  · simp only [labelIdx, firstNew, Bool.false_eq_true, if_false, and_true] at h
    split_ifs at h <;> omega
  · simp only [labelIdx, firstNew, if_true, Bool.true_eq_false, and_false, if_false] at h
    omega

theorem labelIdx_range {bi N K : Nat} {u : Bool} {c : Nat} (hc : c < K) :
    labelIdx bi u N c = bi ∨ (N ≤ labelIdx bi u N c ∧ labelIdx bi u N c < N + (K - firstNew u)) := by
  unfold labelIdx firstNew
  by_cases h : c = 0 ∧ u = false
  · left; simp [h]
  · right; simp only [h, if_false]; split_ifs <;> simp_all; omega

theorem labelIdx_ne {bi N : Nat} {u : Bool} (hb : bi < N) (hu : u = true) {c : Nat} :
    labelIdx bi u N c ≠ bi := by
  unfold labelIdx firstNew
  simp [hu]; omega

/-- What the caller of `strong_partition_marked` learns about the new partition and the new-block
    list: `b` and the `k` fresh blocks `N, …, N+k-1` are exactly the blocks that may have changed,
    all of them unmarked afterwards, and `SplitSem` says which states moved where. -/
def SplitPost {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L) (n : Nat)
    (p : BlockPartition) (b : BT) (nbi : VecTy BT) (p' : BlockPartition) : Prop :=
  PartInv n p' ∧ ∃ k, p'.blocks.val.length = p.blocks.val.length + k ∧
    nbi.val = b :: (List.range' p.blocks.val.length k).map uTag ∧
    (∀ j, j < p.blocks.val.length → j ≠ b.index.val → blkAt p' j = blkAt p j) ∧
    (∀ j, (j = b.index.val ∨ (p.blocks.val.length ≤ j ∧ j < p.blocks.val.length + k)) →
      (blkAt p' j).marked_split.val = (blkAt p' j).«end».val) ∧
    SplitSem LTSInst sys n p b k p'

theorem is_trivially_partitioned_ok {n : Nat} {p : BlockPartition} (hp : PartInv n p) (b : BT)
    (hb : b.index.val < p.blocks.val.length) :
    ∃ tb, verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned p b = ok tb ∧
      (tb = true → (blkAt p b.index.val).«end».val = (blkAt p b.index.val).begin.val + 1) := by
  rw [is_trivially_partitioned_after_ok p b hb, ← blkAt_eq_getElem hb]
  have hbk := hp.blk b.index.val hb
  obtain ⟨i, hi, hiv, -⟩ := spec_imp_exists
    (Usize.sub_spec (x := (blkAt p b.index.val).«end») (y := (blkAt p b.index.val).begin) (by omega))
  refine ⟨decide (i = 1#usize), ?_, ?_⟩
  · rw [show (ok (blkAt p b.index.val) : Result _) = pure _ from rfl]
    simp only [pure_bind]
    rw [block_len_contract, hi]
    simp
  · intro h
    have h' : i = 1#usize := by simpa using h
    have : i.val = 1 := by rw [h']; rfl
    omega

theorem regionElems_lt {n : Nat} {p : BlockPartition} (hp : PartInv n p) (ms len : Nat)
    (hle : ms + len ≤ n) : ∀ x ∈ regionElems p ms len, x.index.val < n := by
  intro x hx
  unfold regionElems at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have := (hp.perm (ms + i) (by have := List.mem_range.mp hi; omega)).1
  exact this


theorem swapIdx_mem {b mx N k j : Nat}
    (hmx : mx = b ∨ (N ≤ mx ∧ mx < N + k)) (hj : j = b ∨ (N ≤ j ∧ j < N + k)) :
    swapIdx b mx j = b ∨ (N ≤ swapIdx b mx j ∧ swapIdx b mx j < N + k) := by
  unfold swapIdx
  split_ifs <;> omega

theorem tag_eq_of_val {Tag : Type} {a b : TagIndex Std.Usize Tag} (h : a.index.val = b.index.val) :
    a = b := merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq h)

/-- The semantic effect of `finish_partition_marked` (`FinishSem`) together with the class/signature
    correspondence gives `SplitSem`. -/
theorem split_sem_nontrivial {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    {n : Nat} {p : BlockPartition} (hp : PartInv n p) (b : BT) (hb : b.index.val < p.blocks.val.length)
    (K : Nat) (u : Bool)
    (hu : u = decide ((blkAt p b.index.val).begin.val < (blkAt p b.index.val).marked_split.val))
    (cls : List Nat) (old : List ST) (p3 : BlockPartition)
    (hlen : cls.length = (blkAt p b.index.val).«end».val - (blkAt p b.index.val).marked_split.val)
    (holdlen : old.length = cls.length)
    (hperm : old.Perm (regionElems p (blkAt p b.index.val).marked_split.val cls.length))
    (hlt : ∀ x ∈ cls, x < K)
    (hsem : FinishSem n p b K u cls old p3)
    (hsig : ∀ t t', t < cls.length → t' < cls.length →
      (cls.getD t 0 = cls.getD t' 0 ↔
        SigOf LTSInst sys p (old.getD t zST) = SigOf LTSInst sys p (old.getD t' zST))) :
    SplitSem LTSInst sys n p b (K - firstNew u) p3 := by
  obtain ⟨mx, hmx, hA, hB⟩ := hsem
  have hbkr := hp.blk b.index.val hb
  have hle : (blkAt p b.index.val).marked_split.val + cls.length ≤ n := by omega
  have hinold : ∀ s : Nat, s < n → ((∃ t, t < cls.length ∧ (old.getD t zST).index.val = s) ↔
      ((blkAt p b.index.val).marked_split.val ≤ offAt p s ∧
        offAt p s < (blkAt p b.index.val).marked_split.val + cls.length)) := by
    intro s hs
    rw [← idx_in_old_iff hp old _ cls.length hperm hle hs]
    constructor
    · rintro ⟨t, ht, e⟩
      exact ⟨old.getD t zST, by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _, e⟩
    · rintro ⟨x, hx, e⟩
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
      exact ⟨t, by omega, by rw [List.getD_eq_getElem _ _ ht]; exact e⟩
  have hXiff : ∀ s : Nat, s < n → (e2bAt p s = b.index.val ↔
      ((blkAt p b.index.val).begin.val ≤ offAt p s ∧ offAt p s < (blkAt p b.index.val).«end».val)) := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hp.own s hs
    constructor
    · intro h; rw [h] at h2 h3; exact ⟨h2, h3⟩
    · rintro ⟨h4, h5⟩; exact hp.pos_block_unique h1 hb ⟨h2, h3⟩ ⟨h4, h5⟩
  have hcK : ∀ t, t < cls.length → cls.getD t 0 < K := fun t ht => hlt _ (by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _)
  have hmk : ∀ s : ST, s.index.val < n → e2bAt p s.index.val = b.index.val →
      (IsMarked p s.index.val ↔ ∃ t, t < cls.length ∧ (old.getD t zST).index.val = s.index.val) := by
    intro s hs hX
    rw [hinold _ hs]
    have := (hXiff _ hs).mp hX
    unfold IsMarked
    rw [hX]
    omega
  have hgetD : ∀ t, t < cls.length → old.getD t zST ∈ old := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  refine ⟨?_, ?_, ?_⟩
  · -- outside the block
    intro s hs hne
    have hnot : ∀ t, t < cls.length → (old.getD t zST).index.val ≠ s.index.val := by
      intro t ht e
      have := (hinold _ hs).mp ⟨t, ht, e⟩
      exact hne ((hXiff _ hs).mpr ⟨by omega, by omega⟩)
    obtain ⟨he, ho⟩ := hB s.index.val hs hnot
    refine ⟨?_, ho⟩
    rw [he]
    obtain ⟨h1, -, -⟩ := hp.own s.index.val hs
    unfold swapIdx
    rcases hmx with h | h
    · rw [if_neg (by omega), if_neg hne]
    · rw [if_neg (by omega), if_neg hne]
  · -- inside the block
    intro s hs hX
    by_cases hin : ∃ t, t < cls.length ∧ (old.getD t zST).index.val = s.index.val
    · obtain ⟨t, ht, e⟩ := hin
      have := hA t ht
      rw [e] at this
      rw [this]
      exact swapIdx_mem hmx (labelIdx_range (hcK t ht))
    · have hnot : ∀ t, t < cls.length → (old.getD t zST).index.val ≠ s.index.val :=
        fun t ht e => hin ⟨t, ht, e⟩
      obtain ⟨he, -⟩ := hB s.index.val hs hnot
      rw [he, hX]
      exact swapIdx_mem hmx (Or.inl rfl)
  · -- pairs in the block
    intro s s' hs hs' hX hX'
    have hb0 : ∀ s : ST, s.index.val < n → e2bAt p s.index.val = b.index.val →
        ¬ (∃ t, t < cls.length ∧ (old.getD t zST).index.val = s.index.val) →
        e2bAt p3 s.index.val = swapIdx b.index.val mx b.index.val := by
      intro s hs hX hin
      have hnot : ∀ t, t < cls.length → (old.getD t zST).index.val ≠ s.index.val :=
        fun t ht e => hin ⟨t, ht, e⟩
      obtain ⟨he, -⟩ := hB s.index.val hs hnot
      rw [he, hX]
    have hbeq : ∀ s : ST, ∀ t, (old.getD t zST).index.val = s.index.val → old.getD t zST = s :=
      fun s t e => tag_eq_of_val e
    have huT : ∀ s : ST, s.index.val < n → e2bAt p s.index.val = b.index.val →
        ¬ (∃ t, t < cls.length ∧ (old.getD t zST).index.val = s.index.val) → u = true := by
      intro s hs hX hin
      have h1 := (hXiff _ hs).mp hX
      have h2 := (hinold _ hs)
      have : ¬ ((blkAt p b.index.val).marked_split.val ≤ offAt p s.index.val ∧
          offAt p s.index.val < (blkAt p b.index.val).marked_split.val + cls.length) :=
        fun h => hin (h2.mpr h)
      rw [hu]
      simp only [decide_eq_true_eq]
      omega
    by_cases h1 : ∃ t, t < cls.length ∧ (old.getD t zST).index.val = s.index.val
    · obtain ⟨t, ht, e⟩ := h1
      have hAs : e2bAt p3 s.index.val = swapIdx b.index.val mx
          (labelIdx b.index.val u p.blocks.val.length (cls.getD t 0)) := by
        have := hA t ht; rw [e] at this; exact this
      by_cases h2 : ∃ t', t' < cls.length ∧ (old.getD t' zST).index.val = s'.index.val
      · obtain ⟨t', ht', e'⟩ := h2
        have hAs' : e2bAt p3 s'.index.val = swapIdx b.index.val mx
            (labelIdx b.index.val u p.blocks.val.length (cls.getD t' 0)) := by
          have := hA t' ht'; rw [e'] at this; exact this
        have hm1 : IsMarked p s.index.val := (hmk s hs hX).mpr ⟨t, ht, e⟩
        have hm2 : IsMarked p s'.index.val := (hmk s' hs' hX').mpr ⟨t', ht', e'⟩
        rw [hAs, hAs']
        have hsg := hsig t t' ht ht'
        rw [hbeq s t e, hbeq s' t' e'] at hsg
        constructor
        · intro h
          have := labelIdx_inj hb (hcK t ht) (hcK t' ht') (swapIdx_inj h)
          exact Or.inr ⟨hm1, hm2, hsg.mp this⟩
        · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
          · exact absurd hm1 h
          · exact congrArg _ (congrArg _ (hsg.mpr h))
      · have hm1 : IsMarked p s.index.val := (hmk s hs hX).mpr ⟨t, ht, e⟩
        have hm2 : ¬ IsMarked p s'.index.val := fun h => h2 ((hmk s' hs' hX').mp h)
        have hue := huT s' hs' hX' h2
        rw [hAs, hb0 s' hs' hX' h2]
        constructor
        · intro h
          exact absurd (swapIdx_inj h) (labelIdx_ne hb hue)
        · rintro (⟨h, -⟩ | ⟨-, h, -⟩)
          · exact absurd hm1 h
          · exact absurd h hm2
    · by_cases h2 : ∃ t', t' < cls.length ∧ (old.getD t' zST).index.val = s'.index.val
      · obtain ⟨t', ht', e'⟩ := h2
        have hAs' : e2bAt p3 s'.index.val = swapIdx b.index.val mx
            (labelIdx b.index.val u p.blocks.val.length (cls.getD t' 0)) := by
          have := hA t' ht'; rw [e'] at this; exact this
        have hm1 : ¬ IsMarked p s.index.val := fun h => h1 ((hmk s hs hX).mp h)
        have hm2 : IsMarked p s'.index.val := (hmk s' hs' hX').mpr ⟨t', ht', e'⟩
        have hue := huT s hs hX h1
        rw [hAs', hb0 s hs hX h1]
        constructor
        · intro h
          exact absurd (swapIdx_inj h.symm) (labelIdx_ne hb hue)
        · rintro (⟨-, h⟩ | ⟨h, -, -⟩)
          · exact absurd hm2 h
          · exact absurd h hm1
      · have hm1 : ¬ IsMarked p s.index.val := fun h => h1 ((hmk s hs hX).mp h)
        have hm2 : ¬ IsMarked p s'.index.val := fun h => h2 ((hmk s' hs' hX').mp h)
        rw [hb0 s hs hX h1, hb0 s' hs' hX' h2]
        exact ⟨fun _ => Or.inl ⟨hm1, hm2⟩, fun _ => rfl⟩

/-- Contract of `strong_partition_marked` on a block that has marked elements. -/
theorem strong_partition_marked_spec {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU)
    {p : BlockPartition} (hp : PartInv nU.val p) (b : BT) (hb : b.index.val < p.blocks.val.length)
    (hmark : (blkAt p b.index.val).marked_split.val < (blkAt p b.index.val).«end».val)
    (id : InternMap)
    (hid : ∀ q, std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
      internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst internEqInst id q = ok none)
    (kts : VecTy SigKey) (hkts : kts.val = []) (sigb : SigKey) (sb : BlockPartitionBuilder)
    (stk : VecTy BT) (hstk : stk.val.length = nU.val) :
    ∃ nbi p' id1 kts1 sigb1 sb1 stk1,
      verified.merc_reduction.signature_refinement.strong_partition_marked LTSInst sys p b id kts sigb sb
        stk = ok (nbi, p', id1, kts1, sigb1, sb1, stk1) ∧
      stk1.val.length = nU.val ∧ SplitPost LTSInst sys nU.val p b nbi p' := by
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hn2 := hwf.2.2.1 nU hns
  have hn : nU.val < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; omega
  have h2n : 2 * nU.val ≤ Usize.max := by nlinarith
  obtain ⟨tb, htb, htbl⟩ := is_trivially_partitioned_ok hp b hb
  cases tb with
  | true =>
    obtain ⟨v0, p0, heq, hv, hpb, hpeq⟩ := trivial_partition_marked_contract p b hb
    refine ⟨v0, p0, id, kts, sigb, sb, stk, ?_, hstk, ?_⟩
    · unfold verified.merc_reduction.signature_refinement.strong_partition_marked
      rw [htb]
      simp only [bind_tc_ok, if_true]
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
    obtain ⟨sb1, hsb1, hbs1, hi2b1, hperm1⟩ := marked_elements_sorted_spec hp b hb sb
    have hbk := hp.blk b.index.val hb
    set bk := blkAt p b.index.val with hbkdef
    have hreg_len : (regionElems p bk.marked_split.val (bk.«end».val - bk.marked_split.val)).length
        = bk.«end».val - bk.marked_split.val := by simp [regionElems]
    have holdlen : sb1.old_elements.val.length = bk.«end».val - bk.marked_split.val := by
      rw [hperm1.length_eq, hreg_len]
    have hold : ∀ x ∈ sb1.old_elements.val, x.index.val < nU.val := fun x hx =>
      regionElems_lt hp _ _ (by omega) x (hperm1.subset hx)
    obtain ⟨id1, kts1, sigb1, sb2, stk1, hspme, hold2, hlen2, hstk2, htk, hcnt, hpos, hidinv, hsemcls⟩ :=
      strong_process_marked_elements_dense LTSInst sys hwf nU hns hp hold (by omega) id hid kts hkts sigb
        sb1 stk hstk rfl
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
    · rw [strong_partition_marked_nontrivial_contract LTSInst sys p b id kts sigb sb stk htb, hsb1]
      simp only [bind_tc_ok]
      rw [hspme]
      simp only [bind_tc_ok]
      show (do
        let (v, partition1, split_builder3) ←
          verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked p b sb2
        ok (v, partition1, id1, kts1, sigb1, split_builder3, stk1)) = _
      rw [hfin]
      simp
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
      refine ⟨h1, _, h2, h3, h4, h5, ?_⟩
      have hlenK : (List.map (fun z => z.val) sb2.block_sizes.val).length = sb2.block_sizes.val.length := by simp
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
      refine split_sem_nontrivial LTSInst sys hp b hb _ _ rfl _ _ p3 (by rw [hcl_len]) hoLen hperm2 hlt2
        (by simpa [List.length_map] using h6) ?_
      intro t t' ht ht'
      have hnd := hidinv.nodup kts1.property
      have hcls' := hsemcls
      have hcl_old : (sb2.index_to_block.val.map (fun x => x.index.val)).length = sb1.old_elements.val.length := by
        simp [hlen2]
      have key := cls_eq_iff_sig LTSInst sys (blockFn p) hnd (cl := fun t => clsAt sb2 t) (len := sb1.old_elements.val.length) hcls'
        (t := t) (t' := t') (by rw [← hcl_old]; exact ht) (by rw [← hcl_old]; exact ht')
      have e1 : ∀ t, (sb2.index_to_block.val.map (fun x => x.index.val)).getD t 0 = clsAt sb2 t := by
        intro t
        unfold clsAt
        by_cases ht : t < sb2.index_to_block.val.length
        · rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getD_eq_getElem _ _ ht]; simp
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]; rfl
      rw [e1, e1]
      have e2 : sb2.old_elements.val = sb1.old_elements.val := by rw [hold2]
      rw [e2]
      exact key


end MercVerified.Refinement.Proofs
