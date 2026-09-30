import MercVerified.Refinement.Proofs.WorklistLoop_Proofs
import MercVerified.Refinement.Proofs.Intern_Proofs
import MercVerified.Refinement.Proofs.PartitionInv_Proofs
import MercVerified.Refinement.Proofs.LoopTools_Proofs
import MercVerified.Refinement.Proofs.MarkedSorted_Proofs
import MercVerified.Refinement.Proofs.FinishBlocks_Proofs
import Aeneas.Std.WP

/-!
# `strong_process_marked_elements`: totality and density of the classes

Starting from the builder that `marked_elements_sorted` leaves (zeroed `index_to_block`, empty
`block_sizes`) and a fresh `id` map / empty `key_to_signature`, the loop always succeeds and leaves
classes `0 .. K-1` (`K = key_to_signature.length`) that are all non-empty, with `block_sizes`
counting exactly the class occurrences in `index_to_block`.

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

/-- The loop invariant of `strong_process_marked_elements_loop` after `m` processed elements. -/
structure SpmeInv (n : Nat) (olds : VecTy ST) (m : Nat) (id : InternMap) (kts : VecTy SigKey)
    (spb : BlockPartitionBuilder) (stk : VecTy BT) (ei : Sz) : Prop where
  ei_eq : ei.val = m
  m_le : m ≤ olds.val.length
  olds_le : olds.val.length ≤ n
  old : spb.old_elements = olds
  len_i2b : spb.index_to_block.val.length = olds.val.length
  len_stk : stk.val.length = n
  kts_le : kts.val.length ≤ m
  len_bs : spb.block_sizes.val.length = kts.val.length
  taken : ∀ x ∈ (spb.index_to_block.val.map (fun x => x.index.val)).take m, x < kts.val.length
  dropped : ∀ x ∈ (spb.index_to_block.val.map (fun x => x.index.val)).drop m, x = 0
  sizes : ∀ j, j < kts.val.length →
    (spb.block_sizes.val.map (fun z => z.val)).getD j 0
      = ((spb.index_to_block.val.map (fun x => x.index.val)).take m).count j
  pos : ∀ j, j < kts.val.length → 0 < (spb.block_sizes.val.map (fun z => z.val)).getD j 0
  ids : std.collections.hash.map.HashMap.AllValues internEqInst internHashInst internBuildHasher id
    (fun v => v.index.val < kts.val.length)


/-- `k` is the canonical key of the signature of `s` under the block map `bn`: its members are
    exactly the `StrongSignature`, and it is strictly sorted. -/
def IsSigKey {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (bn : ST → BT) (s : ST) (k : SigKey) : Prop :=
  (∀ μ β, (μ, β) ∈ k.val ↔ (μ, β) ∈ StrongSignature (MercVerified.Lts.toLTS LTSInst sys) s bn) ∧
  List.Pairwise entLt k.val

noncomputable abbrev emptyKey : SigKey := alloc.vec.Vec.new SigPair

/-- The class index `index_to_block[t]` of the `t`-th processed element. -/
def clsAt (spb : BlockPartitionBuilder) (t : Nat) : Nat := (spb.index_to_block.val.getD t zBT).index.val

/-- The signature-key semantics of the loop after `m` processed elements: the interning map and key
    table agree, and the class of each processed element names the key table entry holding the
    canonical key of its signature (w.r.t. the block map `bn`). -/
structure SpmeSem {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (bn : ST → BT) (olds : VecTy ST) (m : Nat) (id : InternMap) (kts : VecTy SigKey)
    (spb : BlockPartitionBuilder) : Prop where
  idinv : IdInv id kts
  cls : ∀ t, t < m → clsAt spb t < kts.val.length ∧
    IsSigKey LTSInst sys bn (olds.val.getD t zST) (kts.val.getD (clsAt spb t) emptyKey)

theorem list_take_succ_set {α : Type} (l : List α) (m : Nat) (c : α) (hm : m < l.length) :
    (l.set m c).take (m + 1) = l.take m ++ [c] := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_set, List.getElem_append]
    by_cases hi : i < m
    · have hne : m ≠ i := by omega
      have hil : i < l.length := by omega
      simp [hi, hne, hil]
    · have : i = m := by simp at h1 h2; omega
      subst this; simp

theorem list_drop_succ_set {α : Type} (l : List α) (m : Nat) (c : α) :
    (l.set m c).drop (m + 1) = l.drop (m + 1) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, List.getElem_set]
    rw [if_neg (by omega)]

theorem list_take_set_lt {α : Type} (l : List α) (m : Nat) (c : α) :
    (l.set m c).take m = l.take m := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_set]
    have : i < m := by simp at h1; omega
    rw [if_neg (by omega)]


/-- Commit step, the signature was already interned (class `idx < K`). -/
theorem spme_commit_old {n : Nat} {olds : VecTy ST} {m : Nat} {id : InternMap} {kts : VecTy SigKey}
    {spb : BlockPartitionBuilder} {stk stk1 : VecTy BT} {ei ei1 : Sz}
    (hinv : SpmeInv n olds m id kts spb stk ei) (hm : m < olds.val.length)
    (hnmax : n ≤ Usize.max) (idx : BT) (hc : idx.index.val < kts.val.length)
    (hstk1 : stk1.val.length = n) (hei1 : ei1.val = m + 1) :
    ∃ v, verified.merc_reduction.signature_refinement.count_block_occurrence spb.block_sizes idx = ok v ∧
      SpmeInv n olds (m + 1) id kts
        { spb with index_to_block := { slice := spb.index_to_block.slice.set ei idx }, block_sizes := v }
        stk1 ei1 := by
  have hK := hinv.len_bs
  have hcK : idx.index.val < spb.block_sizes.val.length := by omega
  have hmi : m < spb.index_to_block.val.length := by have := hinv.len_i2b; omega
  have hnew : ({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val
      = spb.index_to_block.val.set m idx := by
    show (spb.index_to_block.slice.set ei idx).val = _
    rw [Slice.set_val_eq, hinv.ei_eq]
    rfl
  have hszlen : (spb.block_sizes.val.map (fun z => z.val)).length = kts.val.length := by simp [hK]
  have hget : (spb.block_sizes.val.get ⟨idx.index.val, hcK⟩).val
      = (spb.block_sizes.val.map (fun z => z.val)).getD idx.index.val 0 := by
    simp [List.getD_eq_getElem?_getD, hcK]
  have hcnt_le : (spb.block_sizes.val.map (fun z => z.val)).getD idx.index.val 0 ≤ m := by
    rw [hinv.sizes idx.index.val hc]
    calc ((spb.index_to_block.val.map (fun x => x.index.val)).take m).count idx.index.val
        ≤ ((spb.index_to_block.val.map (fun x => x.index.val)).take m).length := List.count_le_length
      _ ≤ m := by simp
  have h1 : (1#usize).val = 1 := by simp
  obtain ⟨newelem, hadd, hnv⟩ := spec_imp_exists (Usize.add_spec
    (x := spb.block_sizes.val.get ⟨idx.index.val, hcK⟩) (y := 1#usize) (by
      rw [h1, hget]
      have := hinv.m_le; have := hinv.olds_le; omega))
  obtain ⟨v, hv, newelem', hadd', hvval⟩ :=
    count_block_occurrence_spec_lt spb.block_sizes idx hcK ⟨newelem, hadd⟩
  have hne : newelem' = newelem := by
    have := hadd'.symm.trans hadd
    simpa using this
  subst hne
  refine ⟨v, hv, ?_⟩
  have hszs' : v.val.map (fun z => z.val)
      = (spb.block_sizes.val.map (fun z => z.val)).set idx.index.val
          ((spb.block_sizes.val.map (fun z => z.val)).getD idx.index.val 0 + 1) := by
    rw [hvval, List.map_set, hnv, h1, hget]
  have hcls' : ({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)
      = (spb.index_to_block.val.map (fun x => x.index.val)).set m idx.index.val := by
    rw [hnew, List.map_set]
  have hmc : m < (spb.index_to_block.val.map (fun x => x.index.val)).length := by simpa using hmi
  have hkle := hinv.kts_le
  refine ⟨hei1, by omega, hinv.olds_le, hinv.old, ?_, hstk1, by omega, ?_, ?_, ?_, ?_, ?_, hinv.ids⟩
  · change ({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.length = _
    rw [hnew]; simp [hinv.len_i2b]
  · change v.val.length = _
    rw [hvval]; simp [hK]
  · intro x hx
    change x ∈ (({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)).take (m + 1) at hx
    rw [hcls', list_take_succ_set _ _ _ hmc] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hinv.taken x hx
    · simp at hx; omega
  · intro x hx
    change x ∈ (({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)).drop (m + 1) at hx
    rw [hcls', list_drop_succ_set] at hx
    refine hinv.dropped x ?_
    rw [List.drop_eq_getElem_cons hmc]
    exact List.mem_cons_of_mem _ hx
  · intro j hj
    change (v.val.map (fun z => z.val)).getD j 0 = ((({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)).take (m + 1)).count j
    rw [hszs', hcls', list_take_succ_set _ _ _ hmc, List.count_append]
    have hs := hinv.sizes j hj
    by_cases hjc : j = idx.index.val
    · subst hjc
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simp [hszlen, hj])]
      rw [← hs]
      simp
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjc), ← List.getD_eq_getElem?_getD, hs]
      simp [List.count_singleton, hjc, Ne.symm hjc]
  · intro j hj
    change 0 < (v.val.map (fun z => z.val)).getD j 0
    rw [hszs']
    by_cases hjc : j = idx.index.val
    · subst hjc
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simp [hszlen, hj])]
      simp
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjc), ← List.getD_eq_getElem?_getD]
      exact hinv.pos j hj


/-- Commit step, the signature is new (class `idx = K`, `kts` grows by one). -/
theorem spme_commit_new {n : Nat} {olds : VecTy ST} {m : Nat} {id id1 : InternMap}
    {kts kts1 : VecTy SigKey}
    {spb : BlockPartitionBuilder} {stk stk1 : VecTy BT} {ei ei1 : Sz}
    (hinv : SpmeInv n olds m id kts spb stk ei) (hm : m < olds.val.length)
    (hnmax : n ≤ Usize.max) (idx : BT) (hidx : idx.index.val = kts.val.length)
    (hkts1 : kts1.val.length = kts.val.length + 1)
    (hids1 : std.collections.hash.map.HashMap.AllValues internEqInst internHashInst internBuildHasher id1
      (fun v => v.index.val < kts1.val.length))
    (hstk1 : stk1.val.length = n) (hei1 : ei1.val = m + 1) :
    ∃ v, verified.merc_reduction.signature_refinement.count_block_occurrence spb.block_sizes idx = ok v ∧
      SpmeInv n olds (m + 1) id1 kts1
        { spb with index_to_block := { slice := spb.index_to_block.slice.set ei idx }, block_sizes := v }
        stk1 ei1 := by
  have hK := hinv.len_bs
  have hkle := hinv.kts_le
  have hmi : m < spb.index_to_block.val.length := by have := hinv.len_i2b; omega
  have hnew : ({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val
      = spb.index_to_block.val.set m idx := by
    show (spb.index_to_block.slice.set ei idx).val = _
    rw [Slice.set_val_eq, hinv.ei_eq]
    rfl
  have hge : spb.block_sizes.val.length ≤ idx.index.val := by omega
  obtain ⟨i3, hi3⟩ := add1_ok_of_lt_max idx.index (by
    have := hinv.m_le; have := hinv.olds_le; omega)
  obtain ⟨v, hv, hvval⟩ := count_block_occurrence_spec_ge spb.block_sizes idx hge ⟨i3, hi3⟩
  refine ⟨v, hv, ?_⟩
  have hvval' : v.val = spb.block_sizes.val ++ [1#usize] := by
    rw [hvval, hidx, ← hK]
    simp [List.resize]
  have hszs' : v.val.map (fun z => z.val) = spb.block_sizes.val.map (fun z => z.val) ++ [1] := by
    rw [hvval']; simp
  have hcls' : ({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)
      = (spb.index_to_block.val.map (fun x => x.index.val)).set m idx.index.val := by
    rw [hnew, List.map_set]
  have hmc : m < (spb.index_to_block.val.map (fun x => x.index.val)).length := by simpa using hmi
  have hszlen : (spb.block_sizes.val.map (fun z => z.val)).length = kts.val.length := by simp [hK]
  refine ⟨hei1, by omega, hinv.olds_le, hinv.old, ?_, hstk1, by omega, ?_, ?_, ?_, ?_, ?_, hids1⟩
  · change ({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.length = _
    rw [hnew]; simp [hinv.len_i2b]
  · change v.val.length = _
    rw [hvval']; simp [hK, hkts1]
  · intro x hx
    change x ∈ (({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)).take (m + 1) at hx
    rw [hcls', list_take_succ_set _ _ _ hmc] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hinv.taken x hx; omega
    · simp at hx; omega
  · intro x hx
    change x ∈ (({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)).drop (m + 1) at hx
    rw [hcls', list_drop_succ_set] at hx
    refine hinv.dropped x ?_
    rw [List.drop_eq_getElem_cons hmc]
    exact List.mem_cons_of_mem _ hx
  · intro j hj
    change (v.val.map (fun z => z.val)).getD j 0 = ((({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.map (fun x => x.index.val)).take (m + 1)).count j
    rw [hszs', hcls', list_take_succ_set _ _ _ hmc, List.count_append]
    by_cases hjc : j = kts.val.length
    · subst hjc
      have h0 : ((spb.index_to_block.val.map (fun x => x.index.val)).take m).count kts.val.length = 0 :=
        List.count_eq_zero.mpr (fun h => absurd (hinv.taken _ h) (lt_irrefl _))
      rw [h0, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hszlen, hidx]
    · have hjlt : j < kts.val.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD,
        hinv.sizes j hjlt]
      simp [List.count_singleton, hjc, hidx, Ne.symm hjc]
  · intro j hj
    change 0 < (v.val.map (fun z => z.val)).getD j 0
    rw [hszs']
    by_cases hjc : j = kts.val.length
    · subst hjc
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hszlen]
    · have hjlt : j < kts.val.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact hinv.pos j hjlt


/-- `block_number` on a state of a consistent partition reads `element_to_block`. -/
theorem block_number_ok {n : Nat} {p : BlockPartition} (hp : PartInv n p) (t : ST)
    (ht : t.index.val < n) :
    verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number
      p t = ok (p.element_to_block.val.getD t.index.val zBT) := by
  have h : t.index.val < p.element_to_block.val.length := by rw [hp.len_e2b]; exact ht
  unfold verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number
  simp only [tag_value_id, bind_tc_ok]
  rw [vec_index_ok _ _ h, List.getD_eq_getElem _ _ h]

theorem vec_index_mut_usize_ok {U : Type} (v : alloc.vec.Vec U) (i : Std.Usize)
    (h : i.val < v.val.length) :
    v.index_mut_usize i = ok (v.val[i.val]'h, fun u => ({ slice := v.slice.set i u } : alloc.vec.Vec U)) := by
  rw [← alloc.vec.Vec.index_mut_slice_index]
  exact vec_index_mut_ok v i h

theorem clsAt_set (spb : BlockPartitionBuilder) (ei : Sz) (m : Nat) (hei : ei.val = m) (idx : BT)
    (hm : m < spb.index_to_block.val.length) (v : VecTy Sz) (spb1 : BlockPartitionBuilder)
    (hspb1 : spb1 = { spb with index_to_block := { slice := spb.index_to_block.slice.set ei idx }, block_sizes := v }) (t : Nat) :
    clsAt spb1 t = if t = m then idx.index.val else clsAt spb t := by
  subst hspb1
  have hnew : ({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val
      = spb.index_to_block.val.set m idx := by
    show (spb.index_to_block.slice.set ei idx).val = _
    rw [Slice.set_val_eq, hei]
    rfl
  unfold clsAt
  show (({ slice := spb.index_to_block.slice.set ei idx } : VecTy BT).val.getD t zBT).index.val = _
  rw [hnew]
  by_cases htm : t = m
  · subst htm
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self hm]
    rfl
  · rw [if_neg htm, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm htm),
      ← List.getD_eq_getElem?_getD]

/-- One iteration of `strong_process_marked_elements_loop` on a live element succeeds and keeps
    the invariant (structural and signature-key semantics). -/
theorem spme_step {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU)
    {p : BlockPartition} (hp : PartInv nU.val p) {olds : VecTy ST} {m : Nat} {id : InternMap}
    {kts : VecTy SigKey} {sigb : SigKey} {spb : BlockPartitionBuilder} {stk : VecTy BT} {ei : Sz}
    (hold : ∀ x ∈ olds.val, x.index.val < nU.val)
    (hinv : SpmeInv nU.val olds m id kts spb stk ei)
    (hsem : SpmeSem LTSInst sys (fun t => p.element_to_block.val.getD t.index.val zBT) olds m id kts spb)
    (hm : m < olds.val.length) :
    ∃ id1 kts1 sigb1 spb1 stk1 ei1,
      verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
        LTSInst sys p id kts sigb spb stk ei = ok (cont (id1, kts1, sigb1, spb1, stk1, ei1)) ∧
      SpmeInv nU.val olds (m + 1) id1 kts1 spb1 stk1 ei1 ∧
      SpmeSem LTSInst sys (fun t => p.element_to_block.val.getD t.index.val zBT) olds (m + 1) id1
        kts1 spb1 := by
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hold' := hinv.old
  have hlt : ei.val < spb.old_elements.val.length := by rw [hold', hinv.ei_eq]; exact hm
  obtain ⟨state_index, hsid, hsval⟩ := spec_imp_exists
    (alloc.vec.Vec.index_usize_spec spb.old_elements ei hlt)
  have hsi : state_index ∈ olds.val := by
    rw [hsval, ← hold']; exact List.getElem_mem _
  have hsi_lt := hold _ hsi
  have holdsm : olds.val.getD m zST = state_index := by
    rw [hsval]
    have h1 : olds.val.getD m zST = olds.val[m]'hm := by
      simp [List.getD_eq_getElem?_getD, hm]
    rw [h1]
    subst hold'
    simp [hinv.ei_eq]
  obtain ⟨ts, hout, htgt⟩ := hwf.2.1 nU hns state_index hsi_lt
  obtain ⟨sigb1, hsig, hkmem, hksort⟩ := strong_bisim_signature_key LTSInst
    verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition
    sys p state_index sigb ts hout (fun t => p.element_to_block.val.getD t.index.val zBT)
    (fun t ht => block_number_ok hp t.to (htgt t ht))
  have hkey : IsSigKey LTSInst sys (fun t => p.element_to_block.val.getD t.index.val zBT) state_index
      sigb1 := ⟨hkmem, hksort⟩
  have hm_i2b : ei.val < spb.index_to_block.val.length := by rw [hinv.len_i2b, hinv.ei_eq]; exact hm
  have hstk_b : state_index.index.val < stk.val.length := by rw [hinv.len_stk]; exact hsi_lt
  have hm_i2b' : m < spb.index_to_block.val.length := by rw [hinv.len_i2b]; exact hm
  have hmut1 := vec_index_mut_usize_ok spb.index_to_block ei hm_i2b
  have hmut2 := vec_tagged_index_mut_ok stk state_index hstk_b
  have hstk1 : ∀ u : BT, ({ slice := stk.slice.set state_index.index u } : VecTy BT).val.length = nU.val := by
    intro u
    show (stk.slice.set state_index.index u).val.length = _
    rw [Slice.set_val_eq]; simp only [List.length_set]; exact hinv.len_stk
  have hKm := hinv.kts_le
  have hmn := hinv.olds_le
  have hei1 : ∃ ei1 : Sz, ei + 1#usize = ok ei1 ∧ ei1.val = m + 1 := by
    obtain ⟨ei1, h1⟩ := add1_ok_of_lt_max ei (by rw [hinv.ei_eq]; omega)
    exact ⟨ei1, h1, by rw [usize_add_one_val ei ei1 h1, hinv.ei_eq]⟩
  obtain ⟨ei1, hadd, hei1v⟩ := hei1
  obtain ⟨o, ho⟩ := std.collections.hash.map.HashMap.get_key_value_ok internEqInst internHashInst
    internBuildHasher id sigb1
  have hlt2 : kts.val.length < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; omega
  rcases o with _ | ⟨k, idx⟩
  · -- new signature
    have hlenK : kts.val.length < Usize.max := by omega
    obtain ⟨id1, kts1, hint, hk1, hlook, hall, hother⟩ :=
      strong_intern_signature_absent id kts sigb1 ho hlenK
    have hidx : ({ index := alloc.vec.Vec.len kts, marker := () } : BT).index.val = kts.val.length := by
      simp [alloc.vec.Vec.len]
    have hkts1 : kts1.val.length = kts.val.length + 1 := by rw [hk1]; simp
    have hids1 := hall (fun v => v.index.val < kts1.val.length)
      (fun q k v h => by have := hinv.ids q k v h; simp only []; omega) (by simp only []; rw [hidx]; omega)
    obtain ⟨idx0, hidx0⟩ : ∃ idx0 : BT, idx0 = { index := alloc.vec.Vec.len kts, marker := () } := ⟨_, rfl⟩
    have hidx0t : idx0 = uTag kts.val.length := by rw [hidx0]; exact len_tag_eq kts
    rw [← hidx0] at hidx hint hlook
    obtain ⟨v, hcount, hinv'⟩ := spme_commit_new (stk1 := ({ slice := stk.slice.set state_index.index idx0 } : VecTy BT)) (ei1 := ei1)
      (kts1 := kts1) (id1 := id1) hinv hm hnmax _ hidx hkts1 hids1 (hstk1 _) hei1v
    refine ⟨id1, kts1, sigb1, _, _, ei1, ?_, hinv', ?_⟩
    · exact strong_process_marked_elements_loop.body_some_step LTSInst sys p id kts sigb spb stk ei hlt
        state_index hsid sigb1 hsig _ id1 kts1 hint _ ⟨_, hmut1⟩ v hcount _
        ⟨_, hmut2⟩ ei1 hadd
    · have hlook' : internGet id1 sigb1 = ok (some (sigb1, uTag kts.val.length)) := by
        rw [← hidx0t]; exact hlook
      have hidinv := IdInv.new hsem.idinv ho hk1 hlook' hother hlt2
      refine ⟨hidinv, fun t ht => ?_⟩
      rw [clsAt_set spb ei m hinv.ei_eq idx0 hm_i2b' v _ rfl t]
      by_cases htm : t = m
      · subst htm
        rw [if_pos rfl]
        have hi0 : idx0.index.val = kts.val.length := hidx
        rw [hi0]
        refine ⟨by rw [hkts1]; omega, ?_⟩
        have : kts1.val.getD kts.val.length emptyKey = sigb1 := by
          rw [hk1]; simp [List.getD_eq_getElem?_getD]
        rw [this, holdsm]; exact hkey
      · rw [if_neg htm]
        have ht' : t < m := by omega
        obtain ⟨hc1, hc2⟩ := hsem.cls t ht'
        refine ⟨by rw [hkts1]; omega, ?_⟩
        have : kts1.val.getD (clsAt spb t) emptyKey = kts.val.getD (clsAt spb t) emptyKey := by
          rw [hk1, List.getD_eq_getElem?_getD, List.getElem?_append_left hc1,
            ← List.getD_eq_getElem?_getD]
        rw [this]; exact hc2
  · -- known signature
    have hidxlt := hinv.ids sigb1 k idx ho
    have hint := strong_intern_signature_found' id kts sigb1 k idx ho
    obtain ⟨v, hcount, hinv'⟩ := spme_commit_old (stk1 := ({ slice := stk.slice.set state_index.index idx } : VecTy BT))
      (ei1 := ei1) hinv hm hnmax idx hidxlt (hstk1 _) hei1v
    refine ⟨id, kts, sigb1, _, _, ei1, ?_, hinv', ?_⟩
    · exact strong_process_marked_elements_loop.body_some_step LTSInst sys p id kts sigb spb stk ei hlt
        state_index hsid sigb1 hsig _ id kts hint _ ⟨_, hmut1⟩ v hcount _
        ⟨_, hmut2⟩ ei1 hadd
    · refine ⟨hsem.idinv, fun t ht => ?_⟩
      rw [clsAt_set spb ei m hinv.ei_eq idx hm_i2b' v _ rfl t]
      by_cases htm : t = m
      · subst htm; rw [if_pos rfl]
        obtain ⟨hk, hv, hkv⟩ := hsem.idinv.1 sigb1 k idx ho
        refine ⟨hidxlt, ?_⟩
        have : kts.val.getD idx.index.val emptyKey = sigb1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]; simpa using hkv
        rw [this, holdsm]; exact hkey
      · rw [if_neg htm]; exact hsem.cls t (by omega)


/-- `strong_process_marked_elements` on the builder left by `marked_elements_sorted` (fresh `id`,
    empty `key_to_signature`) succeeds and leaves dense classes. -/
theorem strong_process_marked_elements_dense {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU)
    {p : BlockPartition} (hp : PartInv nU.val p) {olds : VecTy ST}
    (hold : ∀ x ∈ olds.val, x.index.val < nU.val) (holdn : olds.val.length ≤ nU.val)
    (id : InternMap)
    (hid : ∀ q, std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
      internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst internEqInst id q = ok none)
    (kts : VecTy SigKey) (hkts : kts.val = []) (sigb : SigKey) (spb : BlockPartitionBuilder)
    (stk : VecTy BT) (hstk : stk.val.length = nU.val)
    (hspb : spb.old_elements = olds) (hi2b : ∀ x ∈ spb.index_to_block.val, x.index.val = 0)
    (hlen : spb.index_to_block.val.length = olds.val.length) (hbs : spb.block_sizes.val = []) :
    ∃ id1 kts1 sigb1 spb1 stk1,
      verified.merc_reduction.signature_refinement.strong_process_marked_elements LTSInst sys p id kts
        sigb spb stk = ok (id1, kts1, sigb1, spb1, stk1) ∧
      spb1.old_elements = olds ∧ spb1.index_to_block.val.length = olds.val.length ∧
      stk1.val.length = nU.val ∧
      (∀ x ∈ spb1.index_to_block.val.map (fun x => x.index.val),
        x < (spb1.block_sizes.val.map (fun z => z.val)).length) ∧
      (∀ j, j < (spb1.block_sizes.val.map (fun z => z.val)).length →
        (spb1.block_sizes.val.map (fun z => z.val)).getD j 0
          = (spb1.index_to_block.val.map (fun x => x.index.val)).count j) ∧
      (∀ j, j < (spb1.block_sizes.val.map (fun z => z.val)).length →
        0 < (spb1.block_sizes.val.map (fun z => z.val)).getD j 0) ∧
      IdInv id1 kts1 ∧
      (∀ t, t < olds.val.length → clsAt spb1 t < kts1.val.length ∧
        IsSigKey LTSInst sys (fun t => p.element_to_block.val.getD t.index.val zBT)
          (olds.val.getD t zST) (kts1.val.getD (clsAt spb1 t) emptyKey)) := by
  unfold verified.merc_reduction.signature_refinement.strong_process_marked_elements
  have hinv0 : SpmeInv nU.val olds 0 id kts spb stk 0#usize := by
    refine ⟨rfl, by omega, holdn, hspb, hlen, hstk, by simp [hkts], by simp [hkts, hbs], ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; simp at hx
    · intro x hx
      simp only [List.drop_zero, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hi2b y hy
    · intro j hj; simp [hkts] at hj
    · intro j hj; simp [hkts] at hj
    · intro q k v h; rw [hid q] at h; simp at h
  have hsem0 : SpmeSem LTSInst sys (fun t => p.element_to_block.val.getD t.index.val zBT) olds 0 id
      kts spb := ⟨IdInv.of_empty hid hkts, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  obtain ⟨y, hy, hQ⟩ := loop_nat_spec
    (fun (x : SpmeState) =>
      verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body
        LTSInst sys p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun x => x.2.2.2.2.2.val)
    (fun m x => SpmeInv nU.val olds m x.1 x.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧
      SpmeSem LTSInst sys (fun t => p.element_to_block.val.getD t.index.val zBT) olds m x.1 x.2.1
        x.2.2.2.1)
    (fun (y : SpmeFinal) =>
      y.2.2.2.2.2.1 = olds ∧ y.2.2.2.1.val.length = olds.val.length ∧
      y.2.2.2.2.2.2.val.length = nU.val ∧
      (∀ x ∈ y.2.2.2.1.val.map (fun x => x.index.val),
        x < (y.2.2.2.2.1.val.map (fun z => z.val)).length) ∧
      (∀ j, j < (y.2.2.2.2.1.val.map (fun z => z.val)).length →
        (y.2.2.2.2.1.val.map (fun z => z.val)).getD j 0
          = (y.2.2.2.1.val.map (fun x => x.index.val)).count j) ∧
      (∀ j, j < (y.2.2.2.2.1.val.map (fun z => z.val)).length →
        0 < (y.2.2.2.2.1.val.map (fun z => z.val)).getD j 0) ∧
      IdInv y.1 y.2.1 ∧
      (∀ t, t < olds.val.length → (y.2.2.2.1.val.getD t zBT).index.val < y.2.1.val.length ∧
        IsSigKey LTSInst sys (fun t => p.element_to_block.val.getD t.index.val zBT)
          (olds.val.getD t zST) (y.2.1.val.getD (y.2.2.2.1.val.getD t zBT).index.val emptyKey)))
    olds.val.length
    (fun m x hx => hx.1.ei_eq) (fun m x hx => hx.1.m_le)
    (by
      intro m x hm hx
      obtain ⟨id1, kts1, sigb1, spb1, stk1, ei1, hb, hinv', hsem'⟩ :=
        spme_step LTSInst sys hwf nU hns hp hold hx.1 hx.2 hm
      exact ⟨(id1, kts1, sigb1, spb1, stk1, ei1), hb, hinv', hsem'⟩)
    (by
      intro x hxx
      obtain ⟨hx, hxs⟩ := hxx
      refine ⟨_, strong_process_marked_elements_loop.body_done_step LTSInst sys p _ _ _ _ _ _ ?_, ?_⟩
      · rw [hx.old, hx.ei_eq]
      · have hcl : (x.2.2.2.1.index_to_block.val.map (fun x => x.index.val)).length = olds.val.length := by
          simp [hx.len_i2b]
        have htk : (x.2.2.2.1.index_to_block.val.map (fun x => x.index.val)).take olds.val.length
            = x.2.2.2.1.index_to_block.val.map (fun x => x.index.val) :=
          List.take_of_length_le (by omega)
        have hbl : (x.2.2.2.1.block_sizes.val.map (fun z => z.val)).length = x.2.1.val.length := by
          simp [hx.len_bs]
        refine ⟨hx.old, hx.len_i2b, hx.len_stk, ?_, ?_, ?_, hxs.idinv, ?_⟩
        · intro c hc
          have := hx.taken c (by rw [htk]; exact hc)
          rw [hbl]; exact this
        · intro j hj
          rw [hbl] at hj
          have := hx.sizes j hj
          rw [htk] at this
          exact this
        · intro j hj
          rw [hbl] at hj
          exact hx.pos j hj
        · intro t ht
          exact hxs.cls t ht)
    (id, kts, sigb, spb, stk, 0#usize) ⟨hinv0, hsem0⟩
  obtain ⟨id1, kts1, sigb1, i2b, bs, ol, stk1⟩ := y
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hQ
  refine ⟨id1, kts1, sigb1, { index_to_block := i2b, block_sizes := bs, old_elements := ol }, stk1, ?_, h1, h2, h3, h4, h5, h6, h7, h8⟩
  unfold verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop
  rw [hy]
  simp



end MercVerified.Refinement.Proofs
