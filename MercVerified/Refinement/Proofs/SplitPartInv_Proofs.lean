import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.PartitionInv_Proofs
import MercVerified.Refinement.Proofs.CountingSort_Proofs
import MercVerified.Refinement.Proofs.ScatterLoop_Proofs
import Aeneas.Std.WP

/-!
# `PartInv` after splitting a block

When `finish_partition_marked` splits block `b` (whose marked suffix `[ms, end)` is regrouped into
classes of sizes `szs`), the resulting partition is again a `PartInv`. This file proves that from
a pointwise description of the new arrays (the scatter loop's `ScInv`) and of the new block list.
It is pure reasoning about lists; the loops that establish the description are in
`ScatterLoop_Proofs.lean` and `FinishBlocks_Proofs.lean`.

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

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The block record of the piece for class `c`: `[cumS c, cumS (c+1))`, created unmarked
    (`Block::new_unmarked`, so `marked_split = end`). -/
def pieceRec (ms : Nat) (szs : List Nat) (c : Nat) : Block :=
  { begin := uTotal (cumS ms szs c), marked_split := uTotal (cumS ms szs (c + 1)),
    «end» := uTotal (cumS ms szs (c + 1)) }

/-- The record `Block::new_unmarked begin end`. -/
def unmRec (bg e : Std.Usize) : Block := { begin := bg, marked_split := e, «end» := e }

/-- The states of block `b`'s marked region, read off the *old* partition. -/
def regionElems (p : BlockPartition) (ms len : Nat) : List (TagIndex Std.Usize StateTag) :=
  (List.range len).map fun i => eAt p (ms + i)

theorem regionElems_nodup {n : Nat} {p : BlockPartition} (hp : PartInv n p) (ms len : Nat)
    (hle : ms + len ≤ n) : (regionElems p ms len).Nodup := by
  unfold regionElems
  rw [List.nodup_map_iff_inj_on (List.nodup_range)]
  intro a ha b hb hab
  have ha' := List.mem_range.mp ha
  have hb' := List.mem_range.mp hb
  have h1 := (hp.perm (ms + a) (by omega)).2
  have h2 := (hp.perm (ms + b) (by omega)).2
  rw [hab] at h1
  omega

/-- If `old` is a permutation of the region's elements, its members are exactly the elements at
    positions of the region. -/
theorem mem_old_iff {n : Nat} {p : BlockPartition} (old : List (TagIndex Std.Usize StateTag))
    (ms len : Nat) (hperm : old.Perm (regionElems p ms len)) (x : TagIndex Std.Usize StateTag) :
    x ∈ old ↔ ∃ q, ms ≤ q ∧ q < ms + len ∧ eAt p q = x := by
  rw [hperm.mem_iff]
  unfold regionElems
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨ms + i, by omega, by omega, rfl⟩
  · rintro ⟨q, h1, h2, rfl⟩; exact ⟨q - ms, by omega, by congr 1; omega⟩

/-- A state is in `old` exactly when its offset lies in the region. -/
theorem idx_in_old_iff {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (old : List (TagIndex Std.Usize StateTag)) (ms len : Nat)
    (hperm : old.Perm (regionElems p ms len)) (hle : ms + len ≤ n) {s : Nat} (hs : s < n) :
    (∃ x ∈ old, x.index.val = s) ↔ (ms ≤ offAt p s ∧ offAt p s < ms + len) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨q, h1, h2, rfl⟩ := (mem_old_iff (n := n) old ms len hperm x).mp hx
    have := (hp.perm q (by omega)).2
    rw [this]; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨eAt p (offAt p s), ?_, hp.inv s hs⟩
    exact (mem_old_iff (n := n) old ms len hperm _).mpr ⟨offAt p s, h1, h2, rfl⟩

/-- `s0`: the class index of the first *new* block (`0` when the unmarked part keeps the old
    block, `1` when class `0` itself takes the old block). -/
def firstNew (u : Bool) : Nat := if u then 0 else 1

theorem posOf_region (ms : Nat) (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    (t : Nat) (ht : t < cls.length) :
    ms ≤ posOf ms szs cls t ∧ posOf ms szs cls t < ms + cls.length := by
  have b := posOf_bounds ms szs cls K hK hcnt hlt t ht
  have := cumS_ge ms szs cls[t]
  have := cumS_le_end ms szs cls K hK hcnt hlt (cls[t] + 1)
  omega

theorem split_partInv {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (b : TagIndex Std.Usize BlockTag) (hb : b.index.val < p.blocks.val.length)
    (hmark : (blkAt p b.index.val).marked_split.val < (blkAt p b.index.val).«end».val)
    (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    (hszpos : ∀ j, j < K → 0 < szs.getD j 0)
    (hlen : cls.length = (blkAt p b.index.val).«end».val - (blkAt p b.index.val).marked_split.val)
    (old : List (TagIndex Std.Usize StateTag)) (hold : old.length = cls.length)
    (hperm : old.Perm (regionElems p (blkAt p b.index.val).marked_split.val cls.length))
    (u : Bool)
    (hu : u = decide ((blkAt p b.index.val).begin.val < (blkAt p b.index.val).marked_split.val))
    (hn : n < 2 ^ UScalarTy.Usize.numBits)
    (hNK : p.blocks.val.length + K < 2 ^ UScalarTy.Usize.numBits)
    (nbi : Std.Usize) (bo : List Std.Usize) (p2 : BlockPartition)
    (hsc : ScInv (blkAt p b.index.val).marked_split.val szs cls K old b u nbi n cls.length
      p.elements.val p.element_to_block.val p.element_offset.val p2.elements.val
      p2.element_to_block.val p2.element_offset.val bo)
    (hnbi : nbi.val = if u then p.blocks.val.length else p.blocks.val.length - 1)
    (hVlen : p2.blocks.val.length = p.blocks.val.length + (K - firstNew u))
    (hVb : p2.blocks.val.getD b.index.val blk0 =
      (if u then unmRec (blkAt p b.index.val).begin (blkAt p b.index.val).marked_split
        else pieceRec (blkAt p b.index.val).marked_split.val szs 0))
    (hVnew : ∀ c, firstNew u ≤ c → c < K →
      p2.blocks.val.getD (p.blocks.val.length + (c - firstNew u)) blk0 =
        pieceRec (blkAt p b.index.val).marked_split.val szs c)
    (hVold : ∀ j, j < p.blocks.val.length → j ≠ b.index.val →
      p2.blocks.val.getD j blk0 = blkAt p j) :
    PartInv n p2 := by
  set N := p.blocks.val.length with hN
  set bk := blkAt p b.index.val with hbk
  set ms := bk.marked_split.val with hms
  set en := bk.«end».val with hen
  set bg := bk.begin.val with hbg
  have hbkr : bg < en ∧ en ≤ n ∧ bg ≤ ms ∧ ms ≤ en := hp.blk b.index.val hb
  have hlen' : cls.length = en - ms := hlen
  have hmark' : ms < en := hmark
  have hle : ms + cls.length ≤ n := by omega
  have hnd : old.Nodup := (hperm.nodup_iff).mpr (regionElems_nodup hp ms cls.length hle)
  have hpr : ∀ t, t < cls.length → ms ≤ posOf ms szs cls t ∧ posOf ms szs cls t < en := by
    intro t ht
    have := posOf_region ms szs cls K hK hcnt hlt t ht
    omega
  have hoidx : ∀ x ∈ old, x.index.val < n := by
    intro x hx
    obtain ⟨q, h1, h2, rfl⟩ := (mem_old_iff (n := n) old ms cls.length hperm x).mp hx
    exact (hp.perm q (by omega)).1
  have hgetD : ∀ t, t < cls.length → old.getD t zST ∈ old := by
    intro t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hmemD : ∀ x ∈ old, ∃ t, t < cls.length ∧ old.getD t zST = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨i, by omega, by simp [List.getD_eq_getElem?_getD, hi]⟩
  have hidxiff := fun {s : Nat} (hs : s < n) =>
    idx_in_old_iff hp old ms cls.length hperm hle hs
  have hpermP : ∀ i, i < n → (eAt p2 i).index.val < n ∧ offAt p2 (eAt p2 i).index.val = i := by
    intro i hi
    by_cases hr : ms ≤ i ∧ i < en
    · obtain ⟨t, ht, hti⟩ := posOf_surj ms szs cls K hK hcnt hlt hr.1 (by omega)
      have hE := hsc.hE1 t ht
      rw [hti] at hE
      have hO := hsc.hO1 t ht
      have hx : eAt p2 i = old.getD t zST := hE
      rw [hx]
      exact ⟨hoidx _ (hgetD t ht), by
        have : offAt p2 (old.getD t zST).index.val = posOf ms szs cls t := hO
        rw [this, hti]⟩
    · have hE2 : eAt p2 i = eAt p i := by
        exact hsc.hE2 i (fun t ht h => by have := hpr t ht; omega)
      rw [hE2]
      have hp1 := hp.perm i hi
      refine ⟨hp1.1, ?_⟩
      have hO2 := hsc.hO2 (eAt p i).index.val (fun t ht h => by
        have hmem := hgetD t ht
        have := (hidxiff hp1.1).mp ⟨_, hmem, h⟩
        rw [hp1.2] at this
        omega)
      have : offAt p2 (eAt p i).index.val = offAt p (eAt p i).index.val := by
        show ((p2.element_offset.val.getD _ 0#usize).val) = (p.element_offset.val.getD _ 0#usize).val
        rw [hO2]
      rw [this, hp1.2]
  have hinvP : ∀ s, s < n → (eAt p2 (offAt p2 s)).index.val = s := by
    intro s hs
    by_cases hr : ms ≤ offAt p s ∧ offAt p s < en
    · obtain ⟨x, hx, hxs⟩ := (hidxiff hs).mpr ⟨hr.1, by omega⟩
      obtain ⟨t, ht, rfl⟩ := hmemD x hx
      have hO := hsc.hO1 t ht
      rw [hxs] at hO
      have hOs : offAt p2 s = posOf ms szs cls t := hO
      rw [hOs]
      have hE := hsc.hE1 t ht
      have hx2 : eAt p2 (posOf ms szs cls t) = old.getD t zST := hE
      rw [hx2]; exact hxs
    · have hO2 := hsc.hO2 s (fun t ht h => by
        have hmem := hgetD t ht
        have := (hidxiff hs).mp ⟨_, hmem, h⟩
        omega)
      have hOs : offAt p2 s = offAt p s := by
        show ((p2.element_offset.val.getD _ 0#usize).val) = (p.element_offset.val.getD _ 0#usize).val
        rw [hO2]
      rw [hOs]
      have hE2 : eAt p2 (offAt p s) = eAt p (offAt p s) :=
        hsc.hE2 _ (fun t ht h => by have := hpr t ht; omega)
      rw [hE2]; exact hp.inv s hs
  -- shape of the new block list
  set N2 := p2.blocks.val.length with hN2
  have hKpos : 0 < K := by
    have : 0 < cls.length := by omega
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos this
    have := hlt x hx; omega
  have hfn : firstNew u ≤ K := by unfold firstNew; split_ifs <;> omega
  have hcases : ∀ j, j < N2 →
      (j = b.index.val ∧ blkAt p2 j = (if u then unmRec bk.begin bk.marked_split
        else pieceRec ms szs 0)) ∨
      (j < N ∧ j ≠ b.index.val ∧ blkAt p2 j = blkAt p j) ∨
      (∃ c, firstNew u ≤ c ∧ c < K ∧ j = N + (c - firstNew u) ∧ blkAt p2 j = pieceRec ms szs c) := by
    intro j hj
    by_cases hjb : j = b.index.val
    · left; exact ⟨hjb, by rw [hjb]; exact hVb⟩
    · by_cases hjN : j < N
      · right; left; exact ⟨hjN, hjb, hVold j hjN hjb⟩
      · right; right
        refine ⟨j - N + firstNew u, by omega, by omega, by omega, ?_⟩
        have := hVnew (j - N + firstNew u) (by omega) (by omega)
        have e : N + (j - N + firstNew u - firstNew u) = j := by omega
        rw [e] at this; exact this
  have hpiece : ∀ c, c < K → cumS ms szs c < cumS ms szs (c + 1) ∧
      cumS ms szs (c + 1) ≤ en ∧ ms ≤ cumS ms szs c := by
    intro c hc
    have h1 := cumS_succ ms szs c (by omega)
    have h2 := hszpos c hc
    have hg : szs.getD c 0 = szs[c]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show c < szs.length by omega)]
    have h3 := cumS_le_end ms szs cls K hK hcnt hlt (c + 1)
    have h4 := cumS_ge ms szs c
    omega
  have hnbi_lt : ∀ c, c < K → cumS ms szs c < 2 ^ UScalarTy.Usize.numBits := by
    intro c hc
    have := hpiece c hc; omega
  have hnbi_lt' : ∀ c, c ≤ K → cumS ms szs c < 2 ^ UScalarTy.Usize.numBits := by
    intro c hc
    have := cumS_le_end ms szs cls K hK hcnt hlt c
    omega
  -- values of the records
  have hpv : ∀ c, c ≤ K → (pieceRec ms szs c).begin.val = cumS ms szs c := by
    intro c hc; unfold pieceRec; exact uTotal_val_of_lt (hnbi_lt' c hc)
  have hpe : ∀ c, c < K → (pieceRec ms szs c).«end».val = cumS ms szs (c + 1) := by
    intro c hc; unfold pieceRec; exact uTotal_val_of_lt (hnbi_lt' (c + 1) (by omega))
  have hpm : ∀ c, c < K → (pieceRec ms szs c).marked_split.val = cumS ms szs (c + 1) := by
    intro c hc; unfold pieceRec; exact uTotal_val_of_lt (hnbi_lt' (c + 1) (by omega))
  have hbgu : ¬ (bg < ms) → bg = ms := by intro h; omega
  have hcum0 : cumS ms szs 0 = ms := by simp [cumS]
  -- numeric shape of every record of `p2`
  have hnum : ∀ j, j < N2 → ∃ lo mk hi : Nat,
      (blkAt p2 j).begin.val = lo ∧ (blkAt p2 j).marked_split.val = mk ∧
      (blkAt p2 j).«end».val = hi ∧ lo < hi ∧ hi ≤ n ∧ lo ≤ mk ∧ mk ≤ hi ∧
      ((j = b.index.val ∨ N ≤ j) → bg ≤ lo ∧ hi ≤ en) := by
    intro j hj
    rcases hcases j hj with ⟨hjb, hr⟩ | ⟨hjN, hjb, hr⟩ | ⟨c, hc1, hc2, hjc, hr⟩
    · rw [hr]
      by_cases hu' : u = true
      · have hbgms : bg < ms := by simpa [hu'] using hu.symm
        simp only [hu', if_true, unmRec]
        exact ⟨bg, ms, ms, rfl, rfl, rfl, by omega, by omega, by omega, le_refl _, fun _ => ⟨le_refl _, by omega⟩⟩
      · have hu0 : u = false := by simpa using hu'
        simp only [hu0]
        have hb := hpiece 0 hKpos
        refine ⟨cumS ms szs 0, cumS ms szs (0 + 1), cumS ms szs (0 + 1), ?_, ?_, ?_, hb.1, ?_, ?_, le_refl _, ?_⟩
        · exact hpv 0 (by omega)
        · exact hpm 0 hKpos
        · exact hpe 0 hKpos
        · omega
        · omega
        · intro _
          have : ¬ bg < ms := by
            have := hu.symm; simpa [hu0] using this
          omega
    · rw [hr]
      obtain ⟨h1, h2, h3, h4⟩ := hp.blk j hjN
      exact ⟨_, _, _, rfl, rfl, rfl, h1, by omega, h3, h4, fun h => by
        rcases h with h | h
        · exact absurd h hjb
        · omega⟩
    · rw [hr]
      have hb := hpiece c hc2
      refine ⟨cumS ms szs c, cumS ms szs (c + 1), cumS ms szs (c + 1), hpv c (by omega), hpm c hc2,
        hpe c hc2, hb.1, by omega, by omega, le_refl _, fun _ => ⟨by omega, hb.2.1⟩⟩
  refine ⟨hsc.lenE, hsc.lenB, hsc.lenO, hpermP, hinvP, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨lo, mk, hi, h1, h2, h3, h4, h5, h6, h7, -⟩ := hnum j hj
    rw [h1, h2, h3]; exact ⟨h4, h5, h6, h7⟩
  · intro s hs
    have hbN : b.index.val < N := hb
    by_cases hin : ∃ x ∈ old, x.index.val = s
    · obtain ⟨x, hx, hxs⟩ := hin
      obtain ⟨t, ht, rfl⟩ := hmemD x hx
      have hB1 := hsc.hB1 t ht
      rw [hxs] at hB1
      have hO1 := hsc.hO1 t ht
      rw [hxs] at hO1
      have hOs : offAt p2 s = posOf ms szs cls t := hO1
      have hBs : e2bAt p2 s = (labelNat b u nbi (cls.getD t 0)).index.val := by
        show (p2.element_to_block.val.getD s zBT).index.val = _
        rw [hB1]
      have hct : cls.getD t 0 = cls[t]'ht := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; simp
      have hcK : cls[t]'ht < K := hlt _ (List.getElem_mem ht)
      have hposb := posOf_bounds ms szs cls K hK hcnt hlt t ht
      rw [hOs, hBs, hct]
      -- the block carrying class `c`
      obtain ⟨j, hjN2, hjrec⟩ : ∃ j, j < N2 ∧ j = (labelNat b u nbi cls[t]).index.val ∧
          (blkAt p2 j).begin.val = cumS ms szs cls[t] ∧
          (blkAt p2 j).«end».val = cumS ms szs (cls[t] + 1) := by
        by_cases h0 : cls[t] = 0 ∧ u = false
        · have hu0 := h0.2
          have hbc : (blkAt p2 b.index.val) = pieceRec ms szs 0 := by
            rw [show blkAt p2 b.index.val = p2.blocks.val.getD b.index.val blk0 from rfl, hVb, hu0]
            simp
          refine ⟨b.index.val, by omega, ?_, ?_, ?_⟩
          · unfold labelNat; simp [h0]
          · rw [hbc, h0.1]; exact hpv 0 (by omega)
          · rw [hbc, h0.1]; exact hpe 0 hKpos
        · have hnb : nbi.val + cls[t] < 2 ^ UScalarTy.Usize.numBits := by
            rw [hnbi]; split_ifs <;> omega
          have hlab : (labelNat b u nbi cls[t]).index.val = nbi.val + cls[t] := by
            unfold labelNat; rw [if_neg h0]; exact uTotal_val_of_lt hnb
          have hcf : firstNew u ≤ cls[t] := by
            unfold firstNew
            by_cases hu' : u = true
            · simp [hu']
            · have hu0 : u = false := by simpa using hu'
              simp [hu0]
              by_contra hh
              exact h0 ⟨by omega, hu0⟩
          have hidxj : nbi.val + cls[t] = N + (cls[t] - firstNew u) := by
            rw [hnbi]; unfold firstNew at *
            by_cases hu' : u = true
            · simp [hu']
            · have hu0 : u = false := by simpa using hu'
              simp [hu0] at hcf ⊢
              omega
          have hrec := hVnew cls[t] hcf hcK
          refine ⟨N + (cls[t] - firstNew u), by omega, by rw [hlab, hidxj], ?_, ?_⟩
          · show (p2.blocks.val.getD _ blk0).begin.val = _
            rw [hrec]; exact hpv _ (by omega)
          · show (p2.blocks.val.getD _ blk0).«end».val = _
            rw [hrec]; exact hpe _ hcK
      obtain ⟨hj1, hj2, hj3⟩ := hjrec
      rw [← hj1]
      refine ⟨hjN2, ?_, ?_⟩ <;> omega
    · have hoff : ¬ (ms ≤ offAt p s ∧ offAt p s < en) := by
        intro h
        exact hin ((hidxiff hs).mpr ⟨h.1, by omega⟩)
      have hO2 := hsc.hO2 s (fun t ht h => hin ⟨_, hgetD t ht, h⟩)
      have hB2 := hsc.hB2 s (fun t ht h => hin ⟨_, hgetD t ht, h⟩)
      have hOs : offAt p2 s = offAt p s := by
        show ((p2.element_offset.val.getD _ 0#usize).val) = (p.element_offset.val.getD _ 0#usize).val
        rw [hO2]
      have hBs : e2bAt p2 s = e2bAt p s := by
        show (p2.element_to_block.val.getD s zBT).index.val = (p.element_to_block.val.getD s zBT).index.val
        rw [hB2]
      obtain ⟨hk, hk1, hk2⟩ := hp.own s hs
      rw [hOs, hBs]
      by_cases hkb : e2bAt p s = b.index.val
      · rw [hkb] at hk1 hk2 ⊢
        have hbg' : bg ≤ offAt p s := hk1
        have hen' : offAt p s < en := hk2
        have hlt' : offAt p s < ms := by omega
        have hu' : u = true := by rw [hu]; simp; omega
        have hbc : blkAt p2 b.index.val = unmRec bk.begin bk.marked_split := by
          rw [show blkAt p2 b.index.val = p2.blocks.val.getD b.index.val blk0 from rfl, hVb]
          simp [hu']
        rw [hbc]
        refine ⟨by omega, ?_, ?_⟩
        · show bg ≤ _; exact hbg'
        · show offAt p s < ms; exact hlt'
      · have hkN : e2bAt p s < N := hk
        rw [show blkAt p2 (e2bAt p s) = p2.blocks.val.getD (e2bAt p s) blk0 from rfl,
          hVold _ hkN hkb]
        exact ⟨by omega, hk1, hk2⟩
  · intro j k hj hk hjk
    -- classification of every record
    have hcls : ∀ j, j < N2 → ∃ lo hi : Nat,
        (blkAt p2 j).begin.val = lo ∧ (blkAt p2 j).«end».val = hi ∧
        ((j < N ∧ j ≠ b.index.val) → lo = (blkAt p j).begin.val ∧ hi = (blkAt p j).«end».val) ∧
        ((j = b.index.val ∨ N ≤ j) → bg ≤ lo ∧ hi ≤ en) ∧
        (j = b.index.val → (u = true ∧ lo = bg ∧ hi = ms) ∨ (u = false ∧ lo = cumS ms szs 0 ∧ hi = cumS ms szs 1)) ∧
        (N ≤ j → ∃ c, firstNew u ≤ c ∧ c < K ∧ j = N + (c - firstNew u) ∧
          lo = cumS ms szs c ∧ hi = cumS ms szs (c + 1)) := by
      intro j hj
      rcases hcases j hj with ⟨hjb, hr⟩ | ⟨hjN, hjb, hr⟩ | ⟨c, hc1, hc2, hjc, hr⟩
      · rw [hr]
        by_cases hu' : u = true
        · have hbgms : bg < ms := by simpa [hu'] using hu.symm
          rw [if_pos hu']
          refine ⟨bg, ms, rfl, rfl, fun h => absurd hjb h.2, fun _ => ⟨le_refl _, by omega⟩,
            fun _ => Or.inl ⟨hu', rfl, rfl⟩, fun h => ?_⟩
          have : N ≤ b.index.val := by omega
          omega
        · have hu0 : u = false := by simpa using hu'
          have hb := hpiece 0 hKpos
          have hnb : ¬ bg < ms := by have := hu.symm; simpa [hu0] using this
          rw [if_neg hu']
          refine ⟨cumS ms szs 0, cumS ms szs 1, hpv 0 (by omega), hpe 0 hKpos, fun h => absurd hjb h.2,
            fun _ => ⟨by omega, hb.2.1⟩, fun _ => Or.inr ⟨hu0, rfl, rfl⟩, fun h => ?_⟩
          omega
      · rw [hr]
        exact ⟨_, _, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h => by
          rcases h with h | h
          · exact absurd h hjb
          · omega, fun h => by omega, fun h => by omega⟩
      · rw [hr]
        have hb := hpiece c hc2
        refine ⟨cumS ms szs c, cumS ms szs (c + 1), hpv c (by omega), hpe c hc2, fun h => by omega,
          fun _ => ⟨by omega, hb.2.1⟩, fun h => ?_, fun _ => ⟨c, hc1, hc2, hjc, rfl, rfl⟩⟩
        exfalso
        have : N ≤ j := by omega
        omega
    obtain ⟨lo1, hi1, hb1, he1, hold1, hbnd1, hbc1, hnw1⟩ := hcls j hj
    obtain ⟨lo2, hi2, hb2, he2, hold2, hbnd2, hbc2, hnw2⟩ := hcls k hk
    rw [he1, hb2, hb1, he2]
    have hbN : b.index.val < N := hb
    by_cases hj0 : j < N ∧ j ≠ b.index.val
    · obtain ⟨e1, e2⟩ := hold1 hj0
      by_cases hk0 : k < N ∧ k ≠ b.index.val
      · obtain ⟨e3, e4⟩ := hold2 hk0
        have := hp.disj j k hj0.1 hk0.1 hjk
        omega
      · have hkn : k = b.index.val ∨ N ≤ k := by omega
        have hd : (blkAt p j).«end».val ≤ bg ∨ en ≤ (blkAt p j).begin.val :=
          hp.disj j b.index.val hj0.1 hbN hj0.2
        have hq := hbnd2 hkn
        omega
    · have hjn : j = b.index.val ∨ N ≤ j := by omega
      have hb1' := hbnd1 hjn
      by_cases hk0 : k < N ∧ k ≠ b.index.val
      · obtain ⟨e3, e4⟩ := hold2 hk0
        have hd : (blkAt p k).«end».val ≤ bg ∨ en ≤ (blkAt p k).begin.val :=
          hp.disj k b.index.val hk0.1 hbN hk0.2
        omega
      · have hkn : k = b.index.val ∨ N ≤ k := by omega
        have hb2' := hbnd2 hkn
        -- both are new/first records
        by_cases hjb : j = b.index.val
        · have hkN : N ≤ k := by
            rcases Nat.lt_or_ge k N with h | h
            · exact absurd ⟨h, fun h' => hjk (hjb.trans h'.symm)⟩ hk0
            · exact h
          obtain ⟨c, hc1, hc2, hkc, e1', e2'⟩ := hnw2 hkN
          rcases hbc1 hjb with ⟨hu1, l1, h1⟩ | ⟨hu1, l1, h1⟩
          · have := cumS_ge ms szs c; omega
          · have hc1' : 1 ≤ c := by unfold firstNew at hc1; simp [hu1] at hc1; omega
            have := cumS_mono ms szs (i := 1) (j := c) hc1'
            omega
        · have hjN : N ≤ j := by omega
          obtain ⟨c, hc1, hc2, hjc, e1', e2'⟩ := hnw1 hjN
          by_cases hkb : k = b.index.val
          · rcases hbc2 hkb with ⟨hu1, l1, h1⟩ | ⟨hu1, l1, h1⟩
            · have := cumS_ge ms szs c; omega
            · have hc1' : 1 ≤ c := by unfold firstNew at hc1; simp [hu1] at hc1; omega
              have := cumS_mono ms szs (i := 1) (j := c) hc1'
              omega
          · have hkN : N ≤ k := by omega
            obtain ⟨c', hc1', hc2', hkc, e1'', e2''⟩ := hnw2 hkN
            have hne : c ≠ c' := by
              intro h; subst h; exact hjk (hjc.trans hkc.symm)
            rcases Nat.lt_or_gt_of_ne hne with hlt' | hlt'
            · have := cumS_mono ms szs (i := c + 1) (j := c') hlt'
              omega
            · have := cumS_mono ms szs (i := c' + 1) (j := c) hlt'
              omega

end MercVerified.Refinement.Proofs
