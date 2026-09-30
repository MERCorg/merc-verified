import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Partition_Proofs
import MercVerified.Refinement.Proofs.PartitionInv_Proofs
import MercVerified.Refinement.Proofs.LoopTools_Proofs
import MercVerified.Refinement.Proofs.SwapBlocks_Proofs
import MercVerified.Refinement.Proofs.CountingSort_Proofs
import MercVerified.Refinement.Proofs.FinishPartition_Proofs
import Aeneas.Std.WP

/-!
# The scatter loop of `finish_partition_marked`

`finish_partition_marked_loop0_loop0` walks the marked elements (in sorted order, with their
class `cls[t]` from `index_to_block`) and writes each into the next free slot of its class:
`elements[posOf t] := old[t]`, `offset[old[t]] := posOf t`, `element_to_block[old[t]] :=
label (cls[t])`, bumping the class cursor. This file proves what the loop does, pointwise.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition Block)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- One overwrite `F[g m] := v m` extends a pointwise "written so far" description
    (`g` injective on the written prefix). -/
theorem write_step {α : Type} (F F0 : List α) (d : α) (g : Nat → Nat) (v : Nat → α) (m : Nat)
    (hlen : g m < F.length) (hinj : ∀ t, t < m → g t ≠ g m)
    (h1 : ∀ t, t < m → F.getD (g t) d = v t)
    (h2 : ∀ i, (∀ t, t < m → g t ≠ i) → F.getD i d = F0.getD i d) :
    (∀ t, t < m + 1 → (F.set (g m) (v m)).getD (g t) d = v t) ∧
    (∀ i, (∀ t, t < m + 1 → g t ≠ i) → (F.set (g m) (v m)).getD i d = F0.getD i d) := by
  constructor
  · intro t ht
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases htm : t = m
    · subst htm; simp [hlen]
    · have hn : g m ≠ g t := (hinj t (by omega)).symm
      rw [if_neg hn]
      have := h1 t (by omega)
      simpa [List.getD_eq_getElem?_getD] using this
  · intro i hi
    have hne : g m ≠ i := hi m (by omega)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hne, if_false]
    have := h2 i (fun t ht => hi t (by omega))
    simpa [List.getD_eq_getElem?_getD] using this

/-- The label `finish_partition_marked` gives to class `j`: the original block for class `0` when
    there is no unmarked part, and `new_block_index + j` otherwise. -/
def scatterLabel (block_index : TagIndex Std.Usize BlockTag) (u : Bool) (_nbi j : Std.Usize)
    (z : Std.Usize) : TagIndex Std.Usize BlockTag :=
  if j.val = 0 ∧ u = false then block_index else ({ index := z, marker := () } : TagIndex Std.Usize BlockTag)

/-- `Block::has_unmarked` is the comparison `begin < marked_split`. -/
theorem block_has_unmarked_contract (b : Block) :
    verified.merc_reduction.block_partition.Block.has_unmarked b
      = ok (decide (b.begin.val < b.marked_split.val)) := by
  unfold verified.merc_reduction.block_partition.Block.has_unmarked
  obtain ⟨u, hu⟩ := merc_reduction.block_partition.Block.assert_consistent_ok b
  rw [hu]; simp

/-- One iteration of the scatter loop on a live element. -/
theorem scatter_body_step
    (block_index : TagIndex Std.Usize BlockTag)
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (block : Block) (nbi : Std.Usize)
    (s : Slice (TagIndex Std.Usize BlockTag)) (cnt : Std.Usize) (hm : cnt.val < s.val.length)
    (E : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (B : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (O : alloc.vec.Vec Std.Usize)
    (bo : alloc.vec.Vec Std.Usize)
    (hmax : cnt.val + 1 ≤ Usize.max)
    (hmold : cnt.val < old.val.length)
    (hobi : (s.val[cnt.val]'hm).index.val < bo.val.length)
    (hi : (bo.val[(s.val[cnt.val]'hm).index.val]'hobi).val < E.val.length)
    (he1 : (old.val[cnt.val]'hmold).index.val < O.val.length)
    (he2 : (old.val[cnt.val]'hmold).index.val < B.val.length)
    (hinc : (bo.val[(s.val[cnt.val]'hm).index.val]'hobi).val + 1 ≤ Usize.max)
    (z : Std.Usize) (hz : nbi + (s.val[cnt.val]'hm).index = ok z) :
    ∃ (cnt' i1 : Std.Usize) (E' : alloc.vec.Vec (TagIndex Std.Usize StateTag))
      (B' : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (O' bo' : alloc.vec.Vec Std.Usize),
      cnt'.val = cnt.val + 1 ∧
      i1.val = (bo.val[(s.val[cnt.val]'hm).index.val]'hobi).val + 1 ∧
      verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0.body
        block_index old block nbi
        ({ iter := { slice := s, i := cnt.val }, count := cnt } :
          core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (TagIndex Std.Usize BlockTag)))
        E B O bo
      = ok (cont ({ iter := { slice := s, i := cnt.val + 1 }, count := cnt' }, E', B', O', bo')) ∧
      E'.val = E.val.set (bo.val[(s.val[cnt.val]'hm).index.val]'hobi).val (old.val[cnt.val]'hmold) ∧
      O'.val = O.val.set (old.val[cnt.val]'hmold).index.val
        (bo.val[(s.val[cnt.val]'hm).index.val]'hobi) ∧
      B'.val = B.val.set (old.val[cnt.val]'hmold).index.val
        (scatterLabel block_index (decide (block.begin.val < block.marked_split.val)) nbi
          (s.val[cnt.val]'hm).index z) ∧
      bo'.val = bo.val.set (s.val[cnt.val]'hm).index.val i1 := by
  have hmlen : cnt.val < s.length := hm
  have hnext : core.slice.iter.IteratorSliceIter.next
      ({ slice := s, i := cnt.val } : core.slice.iter.Iter (TagIndex Std.Usize BlockTag))
      = ok (some (s.val[cnt.val]'hm), ({ slice := s, i := cnt.val + 1 } : core.slice.iter.Iter _)) := by
    unfold core.slice.iter.IteratorSliceIter.next
    simp [hmlen, Slice.len]
    rfl
  obtain ⟨cnt', hcadd, hcv⟩ := spec_imp_exists
    (Usize.add_spec (x := cnt) (y := 1#usize) (by simp; omega))
  obtain ⟨i1, hi1, hi1v⟩ := spec_imp_exists
    (Usize.add_spec (x := bo.val[(s.val[cnt.val]'hm).index.val]'hobi) (y := 1#usize) (by simp; omega))
  have hold : old.index_usize cnt = ok (old.val[cnt.val]'hmold) := by
    obtain ⟨x, hx, hxe⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec old cnt hmold)
    rw [hx, hxe]
  have hEm : E.index_mut_usize (bo.val[(s.val[cnt.val]'hm).index.val]'hobi)
      = ok (E.val[(bo.val[(s.val[cnt.val]'hm).index.val]'hobi).val]'hi,
        E.set (bo.val[(s.val[cnt.val]'hm).index.val]'hobi)) := by
    obtain ⟨⟨x, back⟩, hx, hxe, hb⟩ := spec_imp_exists
      (alloc.vec.Vec.index_mut_usize_spec E (bo.val[(s.val[cnt.val]'hm).index.val]'hobi) hi)
    rw [hx, hxe, hb]
  refine ⟨cnt', i1, E.set (bo.val[(s.val[cnt.val]'hm).index.val]'hobi) (old.val[cnt.val]'hmold),
    { slice := B.slice.set (old.val[cnt.val]'hmold).index
        (scatterLabel block_index (decide (block.begin.val < block.marked_split.val)) nbi
          (s.val[cnt.val]'hm).index z) },
    { slice := O.slice.set (old.val[cnt.val]'hmold).index
        (bo.val[(s.val[cnt.val]'hm).index.val]'hobi) },
    { slice := bo.slice.set (s.val[cnt.val]'hm).index i1 },
    by simp [hcv], by simpa using hi1v, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 1
  · simp [alloc.vec.Vec.set_val_eq]
  · show (O.slice.set _ _).val = _
    rw [Slice.set_val_eq]; rfl
  · show (B.slice.set _ _).val = _
    rw [Slice.set_val_eq]; rfl
  · show (bo.slice.set _ _).val = _
    rw [Slice.set_val_eq]; rfl
  · have heq0 : TagIndex.Insts.CoreCmpPartialEq.eq core.cmp.PartialEqUsize (s.val[cnt.val]'hm) 0#usize
        = ok (decide ((s.val[cnt.val]'hm).index = 0#usize)) := rfl
    have hbs : bo.slice.val = bo.val := rfl
    have hobi0 : (s.val[cnt.val]'hm).index = 0#usize ↔ (s.val[cnt.val]'hm).index.val = 0 := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact UScalar.eq_of_val_eq h
    have hEm' : E.index_mut_usize (bo.slice.val[(s.val[cnt.val]'hm).index.val]'hobi)
        = ok (E.val[(bo.val[(s.val[cnt.val]'hm).index.val]'hobi).val]'hi,
          E.set (bo.val[(s.val[cnt.val]'hm).index.val]'hobi)) := hEm
    unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0.body
    have hlab : scatterLabel block_index (decide (block.begin.val < block.marked_split.val)) nbi
        (s.val[cnt.val]'hm).index z =
        (if (s.val[cnt.val]'hm).index.val = 0 ∧ ¬ (block.begin.val < block.marked_split.val)
          then block_index else ({ index := z, marker := () } : TagIndex Std.Usize BlockTag)) := by
      simp [scatterLabel]
    rw [hlab]
    by_cases h0 : (s.val[cnt.val]'hm).index.val = 0
    · by_cases hu : block.begin.val < block.marked_split.val
      · 
        rw [if_neg (fun h => h.2 hu)]
        have hb : ((s.val[cnt.val]'hm).index = 0#usize) = True := eq_true (hobi0.mpr h0)
        have hub : (block.begin.val < block.marked_split.val) = True := eq_true hu
        simp [hnext, hcadd, hold, vec_tagged_index_val bo _ hobi, hEm, vec_tagged_index_mut_ok O _ he1,
          vec_tagged_index_mut_ok B _ he2, vec_tagged_index_mut_ok bo _ hobi, hi1,
          block_has_unmarked_contract, heq0, hz, hb, hub,
          core.iter.adapters.enumerate.IteratorEnumerate.next, hbs]
      · 
        rw [if_pos ⟨h0, hu⟩]
        have hb : ((s.val[cnt.val]'hm).index = 0#usize) = True := eq_true (hobi0.mpr h0)
        have hub : (block.begin.val < block.marked_split.val) = False := eq_false hu
        simp [hnext, hcadd, hold, vec_tagged_index_val bo _ hobi, hEm, vec_tagged_index_mut_ok O _ he1,
          vec_tagged_index_mut_ok B _ he2, vec_tagged_index_mut_ok bo _ hobi, hi1,
          block_has_unmarked_contract, heq0, hz, hb, hub,
          core.iter.adapters.enumerate.IteratorEnumerate.next, hbs]
    · by_cases hu : block.begin.val < block.marked_split.val
      · 
        rw [if_neg (fun h => h0 h.1)]
        have hb : ((s.val[cnt.val]'hm).index = 0#usize) = False := eq_false (fun h => h0 (hobi0.mp h))
        have hub : (block.begin.val < block.marked_split.val) = True := eq_true hu
        simp [hnext, hcadd, hold, vec_tagged_index_val bo _ hobi, hEm, vec_tagged_index_mut_ok O _ he1,
          vec_tagged_index_mut_ok B _ he2, vec_tagged_index_mut_ok bo _ hobi, hi1,
          block_has_unmarked_contract, heq0, hz, hb, hub,
          core.iter.adapters.enumerate.IteratorEnumerate.next, hbs]
      · 
        rw [if_neg (fun h => h0 h.1)]
        have hb : ((s.val[cnt.val]'hm).index = 0#usize) = False := eq_false (fun h => h0 (hobi0.mp h))
        have hub : (block.begin.val < block.marked_split.val) = False := eq_false hu
        simp [hnext, hcadd, hold, vec_tagged_index_val bo _ hobi, hEm, vec_tagged_index_mut_ok O _ he1,
          vec_tagged_index_mut_ok B _ he2, vec_tagged_index_mut_ok bo _ hobi, hi1,
          block_has_unmarked_contract, heq0, hz, hb, hub,
          core.iter.adapters.enumerate.IteratorEnumerate.next, hbs]

/-- The label of class `j` as a `BlockIndex`. -/
def labelNat (block_index : TagIndex Std.Usize BlockTag) (u : Bool) (nbi : Std.Usize) (j : Nat) :
    TagIndex Std.Usize BlockTag :=
  if j = 0 ∧ u = false then block_index else uTag (nbi.val + j)

theorem scatterLabel_eq (block_index : TagIndex Std.Usize BlockTag) (u : Bool) (nbi j z : Std.Usize)
    (hz : z.val = nbi.val + j.val) :
    scatterLabel block_index u nbi j z = labelNat block_index u nbi j.val := by
  unfold scatterLabel labelNat
  by_cases h : j.val = 0 ∧ u = false
  · simp [h]
  · rw [if_neg h, if_neg h, tag_new_eq_uTag, hz]

theorem count_take_succ_ne (l : List Nat) (m j : Nat) (hm : m < l.length) (h : l[m] ≠ j) :
    (l.take (m + 1)).count j = (l.take m).count j := by
  rw [List.take_succ_eq_append_getElem hm, List.count_append]
  simp [h]

theorem posOf_eq_cursor (ms : Nat) (szs cls : List Nat) (m : Nat) (hm : m < cls.length) :
    posOf ms szs cls m = cumS ms szs cls[m] + (cls.take m).count cls[m] := by
  unfold posOf rankOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  simp

/-- The pointwise description of the arrays after the scatter loop has processed `m` elements. -/
structure ScInv (ms : Nat) (szs cls : List Nat) (K : Nat)
    (old : List (TagIndex Std.Usize StateTag))
    (block_index : TagIndex Std.Usize BlockTag) (u : Bool) (nbi : Std.Usize) (n m : Nat)
    (E0 : List (TagIndex Std.Usize StateTag)) (B0 : List (TagIndex Std.Usize BlockTag))
    (O0 : List Std.Usize)
    (E : List (TagIndex Std.Usize StateTag)) (B : List (TagIndex Std.Usize BlockTag))
    (O bo : List Std.Usize) : Prop where
  lenE : E.length = n
  lenB : B.length = n
  lenO : O.length = n
  lenbo : bo.length = K
  hE1 : ∀ t, t < m → E.getD (posOf ms szs cls t) zST = old.getD t zST
  hE2 : ∀ i, (∀ t, t < m → posOf ms szs cls t ≠ i) → E.getD i zST = E0.getD i zST
  hO1 : ∀ t, t < m → (O.getD (old.getD t zST).index.val 0#usize).val = posOf ms szs cls t
  hO2 : ∀ s, (∀ t, t < m → (old.getD t zST).index.val ≠ s) → O.getD s 0#usize = O0.getD s 0#usize
  hB1 : ∀ t, t < m → B.getD (old.getD t zST).index.val zBT
      = labelNat block_index u nbi (cls.getD t 0)
  hB2 : ∀ s, (∀ t, t < m → (old.getD t zST).index.val ≠ s) → B.getD s zBT = B0.getD s zBT
  hbo : ∀ j, j < K → (bo.getD j 0#usize).val = cumS ms szs j + (cls.take m).count j

theorem old_idx_inj (old : List (TagIndex Std.Usize StateTag)) (hnd : old.Nodup) {t m : Nat}
    (ht : t < old.length) (hm : m < old.length) (hne : t ≠ m)
    (h : (old.getD t zST).index.val = (old.getD m zST).index.val) : False := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm] at h
  simp only [Option.getD_some] at h
  have hidx : old[t].index = old[m].index := UScalar.eq_of_val_eq h
  have : old[t] = old[m] := merc_utilities.tagged_index.TagIndex.ext hidx
  exact hne ((List.Nodup.getElem_inj_iff hnd).mp this)

theorem ScInv.step {ms : Nat} {szs cls : List Nat} {K : Nat} (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    {old : List (TagIndex Std.Usize StateTag)}
    {block_index : TagIndex Std.Usize BlockTag} {u : Bool} {nbi : Std.Usize} {n m : Nat}
    {E0 E : List (TagIndex Std.Usize StateTag)} {B0 B : List (TagIndex Std.Usize BlockTag)}
    {O0 O bo : List Std.Usize}
    (hI : ScInv ms szs cls K old block_index u nbi n m E0 B0 O0 E B O bo)
    (hm : m < cls.length) (hold : old.length = cls.length) (hnd : old.Nodup)
    (hpos : ms + cls.length ≤ n) (hn : n < 2 ^ UScalarTy.Usize.numBits)
    (hoidx : ∀ x ∈ old, x.index.val < n)
    (i1 : Std.Usize) (hi1 : i1.val = (bo.getD cls[m] 0#usize).val + 1) :
    ScInv ms szs cls K old block_index u nbi n (m + 1) E0 B0 O0
      (E.set (bo.getD cls[m] 0#usize).val (old.getD m zST))
      (B.set (old.getD m zST).index.val (labelNat block_index u nbi cls[m]))
      (O.set (old.getD m zST).index.val (bo.getD cls[m] 0#usize))
      (bo.set cls[m] i1) := by
  have hcm : cls[m] < K := hlt _ (List.getElem_mem hm)
  have hpm : (bo.getD cls[m] 0#usize).val = posOf ms szs cls m := by
    rw [hI.hbo _ hcm, posOf_eq_cursor ms szs cls m hm]
  have hb := posOf_bounds ms szs cls K hK hcnt hlt m hm
  have hsum : cumS ms szs (cls[m] + 1) ≤ ms + cls.length := by
    have hs : szs.sum = cls.length := by
      have := sum_count_eq_length K cls hlt
      rw [← this]
      have : szs = (List.range K).map (fun j => cls.count j) := by
        apply List.ext_getElem
        · simp [hK]
        · intro n h1 h2
          simp only [List.getElem_map, List.getElem_range]
          have := hcnt n (by omega)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
          simpa using this
      rw [this]
    have := cumS_mono ms szs (i := cls[m] + 1) (j := szs.length) (by omega)
    rw [cumS_length, hs] at this; exact this
  have hpm_lt : posOf ms szs cls m < n := by omega
  have hmold : m < old.length := by omega
  have hidx_lt : (old.getD m zST).index.val < n := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmold]
    exact hoidx _ (List.getElem_mem hmold)
  have hinjE : ∀ t, t < m → posOf ms szs cls t ≠ posOf ms szs cls m := by
    intro t ht h
    have := posOf_inj ms szs cls K hK hcnt hlt (by omega) hm h
    omega
  have hinjO : ∀ t, t < m → (old.getD t zST).index.val ≠ (old.getD m zST).index.val := by
    intro t ht h
    exact old_idx_inj old hnd (by omega) hmold (by omega) h
  have hposlt : ∀ t, t < cls.length → posOf ms szs cls t < 2 ^ UScalarTy.Usize.numBits := by
    intro t ht
    have b := posOf_bounds ms szs cls K hK hcnt hlt t ht
    have := cumS_mono ms szs (i := cls[t] + 1) (j := szs.length) (by
      have := hlt _ (List.getElem_mem ht); omega)
    have hs : cumS ms szs szs.length ≤ ms + cls.length := by
      rw [cumS_length]
      have hs : szs.sum = cls.length := by
        have := sum_count_eq_length K cls hlt
        rw [← this]
        have : szs = (List.range K).map (fun j => cls.count j) := by
          apply List.ext_getElem
          · simp [hK]
          · intro n h1 h2
            simp only [List.getElem_map, List.getElem_range]
            have := hcnt n (by omega)
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
            simpa using this
        rw [this]
      omega
    omega
  have hbovm : bo.getD cls[m] 0#usize = uTotal (posOf ms szs cls m) := by
    apply UScalar.eq_of_val_eq
    rw [hpm, uTotal_val_of_lt (hposlt m hm)]
  have hEw := write_step E E0 zST (posOf ms szs cls) (fun t => old.getD t zST) m
    (by rw [hI.lenE]; exact hpm_lt) hinjE hI.hE1 hI.hE2
  have hOw := write_step O O0 0#usize (fun t => (old.getD t zST).index.val)
    (fun t => uTotal (posOf ms szs cls t)) m (by rw [hI.lenO]; exact hidx_lt) hinjO
    (fun t ht => by
      apply UScalar.eq_of_val_eq
      rw [hI.hO1 t ht, uTotal_val_of_lt (hposlt t (by omega))]) 
    hI.hO2
  have hBw := write_step B B0 zBT (fun t => (old.getD t zST).index.val)
    (fun t => labelNat block_index u nbi (cls.getD t 0)) m (by rw [hI.lenB]; exact hidx_lt) hinjO
    hI.hB1 hI.hB2
  have hcm' : cls.getD m 0 = cls[m] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]; simp
  rw [hcm'] at hBw
  rw [hpm]
  rw [hbovm]
  refine ⟨by simp [hI.lenE], by simp [hI.lenB], by simp [hI.lenO], by simp [hI.lenbo], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; exact hEw.1 t ht
  · intro i hi; exact hEw.2 i hi
  · intro t ht
    have := hOw.1 t ht
    rw [this, uTotal_val_of_lt (hposlt t (by omega))]
  · intro s hs; exact hOw.2 s hs
  · intro t ht; exact hBw.1 t ht
  · intro s hs; exact hBw.2 s hs
  · intro j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hjc : cls[m] = j
    · subst hjc
      have hlen : cls[m] < bo.length := by rw [hI.lenbo]; exact hj
      have h := hI.hbo _ hj
      have hget : bo.getD cls[m] 0#usize = bo[cls[m]] := by
        simp [List.getD_eq_getElem?_getD, hlen]
      rw [hget] at hi1 h
      rw [if_pos rfl, if_pos hlen]
      simp only [Option.getD_some]
      rw [hi1, h, count_take_succ cls m hm]
      omega
    · rw [if_neg hjc]
      have := hI.hbo j hj
      rw [List.getD_eq_getElem?_getD] at this
      rw [this, count_take_succ_ne cls m j hm hjc]

/-- The state of the scatter loop. -/
abbrev ScState := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (TagIndex Std.Usize BlockTag)) ×
  alloc.vec.Vec (TagIndex Std.Usize StateTag) × alloc.vec.Vec (TagIndex Std.Usize BlockTag) ×
  alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize

/-- The result of the scatter loop. -/
abbrev ScResult := alloc.vec.Vec (TagIndex Std.Usize StateTag) × alloc.vec.Vec (TagIndex Std.Usize BlockTag) ×
  alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize

/-- The scatter loop, pointwise: after processing every marked element, `elements`, `element_offset`
    and `element_to_block` are as described by `ScInv` for the full prefix, and the class cursors
    have moved to the end of their classes. -/
theorem scatter_loop_spec {ms : Nat} {szs cls : List Nat} {K : Nat} (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    (block_index : TagIndex Std.Usize BlockTag)
    (old : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (block : Block) (nbi : Std.Usize)
    (idxv : alloc.vec.Vec (TagIndex Std.Usize BlockTag))
    (hidx : idxv.val.map (fun x => x.index.val) = cls)
    (hold : old.val.length = cls.length) (hnd : old.val.Nodup)
    (E0 : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (B0 : alloc.vec.Vec (TagIndex Std.Usize BlockTag)) (O0 bo0 : alloc.vec.Vec Std.Usize)
    (n : Nat) (hE : E0.val.length = n) (hB : B0.val.length = n) (hO : O0.val.length = n)
    (hbo : bo0.val.length = K)
    (hbo' : ∀ j, j < K → (bo0.val.getD j 0#usize).val = cumS ms szs j)
    (hpos : ms + cls.length ≤ n) (hn : n < 2 ^ UScalarTy.Usize.numBits) (hn' : n ≤ Usize.max)
    (hoidx : ∀ x ∈ old.val, x.index.val < n)
    (hnbi : nbi.val + K ≤ Usize.max) :
    ∃ E' B' O' bo', verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0
        { iter := { slice := alloc.vec.Vec.deref idxv, i := 0 }, count := 0#usize }
        E0 B0 O0 block_index old block nbi bo0 = ok (E', B', O', bo') ∧
      ScInv ms szs cls K old.val block_index (decide (block.begin.val < block.marked_split.val))
        nbi n cls.length E0.val B0.val O0.val E'.val B'.val O'.val bo'.val := by
  unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0
  set s : Slice (TagIndex Std.Usize BlockTag) := alloc.vec.Vec.deref idxv with hs
  have hsval : s.val = idxv.val := by rw [hs]; simp [alloc.vec.Vec.deref]
  have hlenidx : idxv.val.length = cls.length := by
    have := congrArg List.length hidx; simpa using this
  obtain ⟨y, hy, hpost⟩ : ∃ y, loop
      (fun x : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (TagIndex Std.Usize BlockTag)) ×
        alloc.vec.Vec (TagIndex Std.Usize StateTag) × alloc.vec.Vec (TagIndex Std.Usize BlockTag) ×
        alloc.vec.Vec Std.Usize × alloc.vec.Vec Std.Usize =>
        verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0.body
          block_index old block nbi x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      ({ iter := { slice := s, i := 0 }, count := 0#usize }, E0, B0, O0, bo0) = ok y ∧
      ScInv ms szs cls K old.val block_index (decide (block.begin.val < block.marked_split.val))
        nbi n cls.length E0.val B0.val O0.val y.1.val y.2.1.val y.2.2.1.val y.2.2.2.val := by
    apply Std.WP.spec_imp_exists
    refine loop.spec_decr_nat
      (measure := fun x : ScState => cls.length - x.1.iter.i)
      (inv := fun x : ScState => ∃ (m : Nat) (cnt : Std.Usize),
        x.1 = ({ iter := { slice := s, i := m }, count := cnt } :
          core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (TagIndex Std.Usize BlockTag))) ∧
        cnt.val = m ∧ m ≤ cls.length ∧
        ScInv ms szs cls K old.val block_index (decide (block.begin.val < block.marked_split.val))
          nbi n m E0.val B0.val O0.val x.2.1.val x.2.2.1.val x.2.2.2.1.val x.2.2.2.2.val)
      (post := fun y : ScResult => ScInv ms szs cls K old.val block_index
        (decide (block.begin.val < block.marked_split.val)) nbi n cls.length E0.val B0.val O0.val
        y.1.val y.2.1.val y.2.2.1.val y.2.2.2.val) _ _ ?_ ?_
    · rintro ⟨it, E, B, O, bo⟩ ⟨m, cnt, hit, hcm, hml, hI⟩
      simp only at hit hI
      subst hit
      by_cases hlt' : m < cls.length
      · have hm : m < s.val.length := by rw [hsval, hlenidx]; exact hlt'
        have hmold : m < old.val.length := by omega
        have hcm' : (s.val[m]'hm).index.val = cls[m]'hlt' := by
          have hidxlen : m < idxv.val.length := by omega
          have hmap := List.getElem_of_eq hidx (i := m) (by simpa using hidxlen)
          rw [List.getElem_map] at hmap
          have hs_get : s.val[m]'hm = idxv.val[m]'hidxlen := by simp [hsval]
          rw [hs_get]; exact hmap
        have hcK : cls[m]'hlt' < K := hlt _ (List.getElem_mem hlt')
        have hpm : ∀ hb : (s.val[m]'hm).index.val < bo.val.length,
            (bo.val[(s.val[m]'hm).index.val]'hb).val = posOf ms szs cls m := by
          intro hb
          have h := hI.hbo _ (by omega : (s.val[m]'hm).index.val < K)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some] at h
          rw [h, hcm', posOf_eq_cursor ms szs cls m hlt']
        have hbnd := posOf_bounds ms szs cls K hK hcnt hlt m hlt'
        have hsumle : cumS ms szs (cls[m]'hlt' + 1) ≤ ms + cls.length :=
          cumS_le_end ms szs cls K hK hcnt hlt _
        have hpmn : posOf ms szs cls m < n := by omega
        subst hcm
        have hobi : (s.val[cnt.val]'hm).index.val < bo.val.length := by
          rw [hI.lenbo, hcm']; exact hcK
        have hbo_pm := hpm hobi
        have hz : ∃ z : Std.Usize, nbi + (s.val[cnt.val]'hm).index = ok z ∧
            z.val = nbi.val + (s.val[cnt.val]'hm).index.val := by
          obtain ⟨z, hz, hzv⟩ := spec_imp_exists
            (Usize.add_spec (x := nbi) (y := (s.val[cnt.val]'hm).index) (by omega))
          exact ⟨z, hz, hzv⟩
        obtain ⟨z, hz, hzv⟩ := hz
        obtain ⟨cnt', i1, E', B', O', bo', hc', hi1v, hbody, hE', hO', hB', hbo''⟩ :=
          scatter_body_step block_index old block nbi s cnt hm E B O bo (by omega) hmold hobi
            (by rw [hbo_pm, hI.lenE]; exact hpmn) (by
              have := hoidx _ (List.getElem_mem hmold); rw [hI.lenO]; exact this)
            (by have := hoidx _ (List.getElem_mem hmold); rw [hI.lenB]; exact this)
            (by rw [hbo_pm]; omega) z hz
        have hold_get : old.val.getD cnt.val zST = old.val[cnt.val]'hmold := by
          simp [List.getD_eq_getElem?_getD, hmold]
        have hgetbo : bo.val.getD (cls[cnt.val]'hlt') 0#usize
            = bo.val[(s.val[cnt.val]'hm).index.val]'hobi := by
          simp only [hcm']
          simp [List.getD_eq_getElem?_getD, hcm' ▸ hobi]
        have hE'' : E'.val = E.val.set (bo.val.getD (cls[cnt.val]'hlt') 0#usize).val
            (old.val.getD cnt.val zST) := by rw [hE', hgetbo, hold_get]
        have hO'' : O'.val = O.val.set (old.val.getD cnt.val zST).index.val
            (bo.val.getD (cls[cnt.val]'hlt') 0#usize) := by rw [hO', hgetbo, hold_get]
        have hB'' : B'.val = B.val.set (old.val.getD cnt.val zST).index.val
            (labelNat block_index (decide (block.begin.val < block.marked_split.val)) nbi
              (cls[cnt.val]'hlt')) := by
          rw [hB', scatterLabel_eq _ _ _ _ _ hzv, hcm', hold_get]
        have hbo3 : bo'.val = bo.val.set (cls[cnt.val]'hlt') i1 := by
          rw [hbo'']; simp only [hcm']
        have hi1' : i1.val = (bo.val.getD (cls[cnt.val]'hlt') 0#usize).val + 1 := by
          rw [hi1v, hgetbo]
        have hnew := hI.step hK hcnt hlt hlt' hold hnd hpos hn hoidx i1 hi1'
        rw [← hE'', ← hB'', ← hO'', ← hbo3] at hnew
        exact Std.WP.exists_imp_spec ⟨cont ({ iter := { slice := s, i := cnt.val + 1 }, count := cnt' },
          E', B', O', bo'), hbody, ⟨⟨cnt.val + 1, cnt', rfl, hc', by omega, hnew⟩, by simp; omega⟩⟩
      · subst hcm
        have hmeq : cnt.val = cls.length := by omega
        have hnm : ¬ cnt.val < s.length := by
          have : s.length = cls.length := by
            show s.val.length = _
            rw [hsval, hlenidx]
          omega
        have hnext : core.slice.iter.IteratorSliceIter.next
            ({ slice := s, i := cnt.val } : core.slice.iter.Iter (TagIndex Std.Usize BlockTag))
            = ok (none, ({ slice := s, i := cnt.val } : core.slice.iter.Iter _)) := by
          unfold core.slice.iter.IteratorSliceIter.next
          simp [Slice.len] at hnm ⊢
          simp [hnm]
        rw [hmeq] at hI
        have hbody : verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0.body
            block_index old block nbi ({ iter := { slice := s, i := cnt.val }, count := cnt } :
              core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (TagIndex Std.Usize BlockTag)))
            E B O bo = ok (done (E, B, O, bo)) := by
          unfold verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0.body
          simp [core.iter.adapters.enumerate.IteratorEnumerate.next, hnext]
        exact Std.WP.exists_imp_spec ⟨done (E, B, O, bo), hbody, hI⟩
    · refine ⟨0, 0#usize, rfl, rfl, Nat.zero_le _, ?_⟩
      refine ⟨hE, hB, hO, hbo, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht; omega
      · intro i _; rfl
      · intro t ht; omega
      · intro s _; rfl
      · intro t ht; omega
      · intro s _; rfl
      · intro j hj
        have := hbo' j hj
        rw [List.getD_eq_getElem?_getD] at this
        simpa using this
  exact ⟨y.1, y.2.1, y.2.2.1, y.2.2.2, hy, hpost⟩

end MercVerified.Refinement.Proofs
