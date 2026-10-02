import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Partition_Proofs
import Aeneas.Std.WP

/-!
# The public partition invariant `PartInv`

The invariant of `BlockPartition` that the termination proof of the worklist loop
(`WorklistLoop_Proofs.lean`) carries: `elements` is a permutation of `[0, n)` with
`element_offset` its inverse, the blocks are non-empty, pairwise disjoint ranges of
`elements`, and every state's `element_to_block` entry names the block containing its offset.

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

/-- The default state/block used by the `getD` accessors. -/
abbrev zST : TagIndex Std.Usize StateTag := { index := 0#usize, marker := () }
abbrev zBT : TagIndex Std.Usize BlockTag := { index := 0#usize, marker := () }

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- `N ≤ n`: `k ↦ begin_k` is an injection of the blocks into `range n`. -/
theorem _root_.MercVerified.Refinement.PartInv.blocks_le_n {n : Nat} {p : BlockPartition} (h : PartInv n p) :
    p.blocks.val.length ≤ n := by
  have hmaps : ∀ k ∈ Finset.range p.blocks.val.length,
      (blkAt p k).begin.val ∈ Finset.range n := by
    intro k hk
    have := h.blk k (Finset.mem_range.mp hk)
    simp only [Finset.mem_range]; omega
  have hinj : Set.InjOn (fun k => (blkAt p k).begin.val)
      ↑(Finset.range p.blocks.val.length) := by
    intro j hj k hk hjk
    by_contra hne
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have bj := h.blk j hj'
    have bk := h.blk k hk'
    simp only at hjk
    rcases h.disj j k hj' hk' hne with h1 | h1 <;> omega
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- A position lying in two blocks' ranges forces the blocks to be equal. -/
theorem _root_.MercVerified.Refinement.PartInv.pos_block_unique {n : Nat} {p : BlockPartition} (h : PartInv n p) {j k q : Nat}
    (hj : j < p.blocks.val.length) (hk : k < p.blocks.val.length)
    (hqj : (blkAt p j).begin.val ≤ q ∧ q < (blkAt p j).«end».val)
    (hqk : (blkAt p k).begin.val ≤ q ∧ q < (blkAt p k).«end».val) : j = k := by
  by_contra hne
  rcases h.disj j k hj hk hne with h1 | h1 <;> omega

/-- Content of `swap_elements`: `elements` gets the two entries exchanged, `element_offset` gets
    the two (old) elements' offsets repaired (the later write wins), and `blocks` and
    `element_to_block` are untouched. Unlike `swap_elements_spec` this pins down *where* things
    end up, which `PartInv` preservation needs. -/
theorem swap_elements_content (p : BlockPartition) (a b : Std.Usize)
    (h3 : ∀ x ∈ p.elements.val, x.index.val < p.element_offset.val.length)
    (ha : a.val < p.elements.val.length) (hb : b.val < p.elements.val.length) :
    ∃ p' : BlockPartition,
      verified.merc_reduction.block_partition.BlockPartition.swap_elements p a b = ok p' ∧
      p'.blocks = p.blocks ∧ p'.element_to_block = p.element_to_block ∧
      p'.elements.val = (p.elements.val.set a.val p.elements.val[b.val]).set b.val
        p.elements.val[a.val] ∧
      p'.element_offset.val = (p.element_offset.val.set p.elements.val[b.val].index.val a).set
        p.elements.val[a.val].index.val b := by
  unfold verified.merc_reduction.block_partition.BlockPartition.swap_elements
  have haS : a.val < p.elements.slice.length := ha
  have hbS : b.val < p.elements.slice.length := hb
  obtain ⟨s1, hs1, hl1, hA, hB, hO⟩ :=
    spec_imp_exists (core.slice.Slice.swap_spec p.elements.slice a b haS hbS)
  have hsa : a.val < s1.length := by rw [hl1]; exact haS
  have hsb : b.val < s1.length := by rw [hl1]; exact hbS
  obtain ⟨xa, hxa, hxa'⟩ := spec_imp_exists (Slice.index_usize_spec s1 a hsa)
  obtain ⟨xb, hxb, hxb'⟩ := spec_imp_exists (Slice.index_usize_spec s1 b hsb)
  have hxa_eq : xa = p.elements.val[b.val] := by
    rw [hxa']
    have := hA
    simp only [getElem!_pos, hsa, hbS] at this
    exact this
  have hxb_eq : xb = p.elements.val[a.val] := by
    rw [hxb']
    have := hB
    simp only [getElem!_pos, hsb, haS] at this
    exact this
  have hmem_b : p.elements.val[b.val] ∈ p.elements.val := List.getElem_mem hb
  have hmem_a : p.elements.val[a.val] ∈ p.elements.val := List.getElem_mem ha
  have hbnd_a : (p.elements.val[b.val]).index.val < p.element_offset.slice.length :=
    h3 _ hmem_b
  have hbnd_b : (p.elements.val[a.val]).index.val < p.element_offset.slice.length :=
    h3 _ hmem_a
  obtain ⟨⟨_, back1⟩, hm1, _, hb1⟩ := spec_imp_exists
    (Slice.index_mut_usize_spec p.element_offset.slice (p.elements.val[b.val]).index hbnd_a)
  have hbnd2 : (p.elements.val[a.val]).index.val <
      (p.element_offset.slice.set (p.elements.val[b.val]).index a).length := by
    rw [Slice.set_length]; exact hbnd_b
  obtain ⟨⟨_, back2⟩, hm2, _, hb2⟩ := spec_imp_exists
    (Slice.index_mut_usize_spec (p.element_offset.slice.set (p.elements.val[b.val]).index a)
      (p.elements.val[a.val]).index hbnd2)
  refine ⟨{ elements := ⟨s1⟩, blocks := p.blocks, element_to_block := p.element_to_block,
            element_offset := ⟨back2 b⟩ }, ?_, rfl, rfl, ?_, ?_⟩
  · simp [alloc.vec.Vec.deref_mut, lift, hs1, alloc.vec.Vec.index, core.slice.index.Usize.index,
      hxa, hxb, hxa_eq, hxb_eq, vec_tagged_index_mut_eq, hm1, hm2, hb1]
  · show s1.val = _
    apply List.ext_getElem
    · have h := hl1
      simp only [Slice.length] at h
      have e : p.elements.slice.val.length = p.elements.val.length := rfl
      simp [List.length_set, h, e]
    · intro i h1 h2
      have hi' : i < p.elements.val.length := by
        have h := hl1
        simp only [Slice.length] at h
        have e : p.elements.slice.val.length = p.elements.val.length := rfl
        omega
      have hi3 : i < p.elements.slice.val.length := hi'
      have hi2 : i < s1.val.length := h1
      rw [List.getElem_set]
      by_cases hib : b.val = i
      · subst hib
        simp only [if_true]
        have := hB
        simp only [getElem!_pos, hsb, haS] at this
        exact this
      · rw [if_neg hib, List.getElem_set]
        by_cases hia : a.val = i
        · subst hia
          simp only [if_true]
          have := hA
          simp only [getElem!_pos, hsa, hbS] at this
          exact this
        · rw [if_neg hia]
          have := hO i (Ne.symm hia) (Ne.symm hib)
          simp only [getElem!_pos, hi2, hi3] at this
          exact this
  · show (back2 b).val = _
    rw [hb2]
    show ((p.element_offset.slice.set (p.elements.val[b.val]).index a).set
      (p.elements.val[a.val]).index b).val = _
    rw [Slice.set_val_eq, Slice.set_val_eq]
    rfl

theorem eAt_eq_getElem {p : BlockPartition} {i : Nat} (h : i < p.elements.val.length) :
    eAt p i = p.elements.val[i] := by
  simp [eAt, List.getD_eq_getElem?_getD, h]

theorem _root_.MercVerified.Refinement.PartInv.elem_idx_lt {n : Nat} {p : BlockPartition} (h : PartInv n p)
    {x : TagIndex Std.Usize StateTag} (hx : x ∈ p.elements.val) : x.index.val < n := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < n := h.len_e ▸ hi
  have := (h.perm i hi').1
  rwa [eAt_eq_getElem hi] at this

/-- Swapping two positions of the same block preserves `PartInv` (and `blocks`,
    `element_to_block`). -/
theorem swap_elements_partInv {n : Nat} {p : BlockPartition} (hp : PartInv n p)
    (a b : Std.Usize) (ha : a.val < n) (hb : b.val < n) {k : Nat}
    (hk : k < p.blocks.val.length)
    (hak : (blkAt p k).begin.val ≤ a.val ∧ a.val < (blkAt p k).«end».val)
    (hbk : (blkAt p k).begin.val ≤ b.val ∧ b.val < (blkAt p k).«end».val) :
    ∃ p' : BlockPartition,
      verified.merc_reduction.block_partition.BlockPartition.swap_elements p a b = ok p' ∧
      PartInv n p' ∧ p'.blocks = p.blocks ∧ p'.element_to_block = p.element_to_block ∧
      (∀ s, offAt p' s = if s = (eAt p a.val).index.val then b.val
        else if s = (eAt p b.val).index.val then a.val else offAt p s) := by
  have ha' : a.val < p.elements.val.length := hp.len_e ▸ ha
  have hb' : b.val < p.elements.val.length := hp.len_e ▸ hb
  obtain ⟨p', hswap, hbl, he2b, hel, hoff⟩ := swap_elements_content p a b
    (fun x hx => hp.len_off ▸ hp.elem_idx_lt hx) ha' hb'
  refine ⟨p', hswap, ?_⟩
  set x := p.elements.val[a.val] with hxdef
  set y := p.elements.val[b.val] with hydef
  have hxA : eAt p a.val = x := eAt_eq_getElem ha'
  have hyB : eAt p b.val = y := eAt_eq_getElem hb'
  have hxlt : x.index.val < n := by have := (hp.perm _ ha).1; rwa [hxA] at this
  have hylt : y.index.val < n := by have := (hp.perm _ hb).1; rwa [hyB] at this
  have hxoff : offAt p x.index.val = a.val := by have := (hp.perm _ ha).2; rwa [hxA] at this
  have hyoff : offAt p y.index.val = b.val := by have := (hp.perm _ hb).2; rwa [hyB] at this
  -- pointwise description of the new accessors
  have hE : ∀ i, eAt p' i = if i = b.val then x else if i = a.val then y else eAt p i := by
    intro i
    simp only [eAt, hel, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hib : i = b.val
    · subst hib; simp [hb', List.length_set]
    · by_cases hia : i = a.val
      · subst hia; simp [hib, ha', Ne.symm hib]
      · simp [hib, hia, Ne.symm hib, Ne.symm hia]
  have hxo : x.index.val < p.element_offset.val.length := hp.len_off ▸ hxlt
  have hyo : y.index.val < p.element_offset.val.length := hp.len_off ▸ hylt
  have hO : ∀ s, offAt p' s = if s = x.index.val then b.val
      else if s = y.index.val then a.val else offAt p s := by
    intro s
    simp only [offAt, hoff, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases h1 : s = x.index.val
    · subst h1; simp [hxo, List.length_set]
    · by_cases h2 : s = y.index.val
      · subst h2; simp [hyo, h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have hblk : ∀ j, blkAt p' j = blkAt p j := by intro j; simp [blkAt, hbl]
  have hN : p'.blocks.val.length = p.blocks.val.length := by rw [hbl]
  have he2 : ∀ s, e2bAt p' s = e2bAt p s := by intro s; simp [e2bAt, he2b]
  -- x, y both lie in block `k`
  have hxk : e2bAt p x.index.val = k := by
    obtain ⟨h1, h2, h3⟩ := hp.own _ hxlt
    rw [hxoff] at h2 h3
    exact hp.pos_block_unique h1 hk ⟨h2, h3⟩ hak
  have hyk : e2bAt p y.index.val = k := by
    obtain ⟨h1, h2, h3⟩ := hp.own _ hylt
    rw [hyoff] at h2 h3
    exact hp.pos_block_unique h1 hk ⟨h2, h3⟩ hbk
  have hPI : PartInv n p' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hel, List.length_set, hp.len_e]
    · rw [he2b]; exact hp.len_e2b
    · simp [hoff, List.length_set, hp.len_off]
    · intro i hi
      rw [hE i]
      by_cases hib : i = b.val
      · rw [if_pos hib]
        refine ⟨hxlt, ?_⟩
        rw [hO, if_pos rfl]; exact hib.symm
      · rw [if_neg hib]
        by_cases hia : i = a.val
        · rw [if_pos hia]
          refine ⟨hylt, ?_⟩
          have hne : y.index.val ≠ x.index.val := by
            intro h; apply hib; rw [h] at hyoff; omega
          rw [hO, if_neg hne, if_pos rfl]; exact hia.symm
        · rw [if_neg hia]
          obtain ⟨hz1, hz2⟩ := hp.perm i hi
          refine ⟨hz1, ?_⟩
          have h1 : (eAt p i).index.val ≠ x.index.val := by
            intro h; rw [h] at hz2; omega
          have h2 : (eAt p i).index.val ≠ y.index.val := by
            intro h; rw [h] at hz2; omega
          rw [hO, if_neg h1, if_neg h2]; exact hz2
    · intro s hs
      rw [hO s]
      by_cases h1 : s = x.index.val
      · rw [if_pos h1, hE, if_pos rfl]; exact h1.symm
      · rw [if_neg h1]
        by_cases h2 : s = y.index.val
        · rw [if_pos h2]
          have hab : a.val ≠ b.val := by
            intro hab
            apply h1
            have : x = y := by simp only [hxdef, hydef, hab]
            rw [h2, this]
          rw [hE, if_neg hab, if_pos rfl]; exact h2.symm
        · rw [if_neg h2]
          have hq := hp.inv s hs
          rw [hE]
          by_cases hqb : offAt p s = b.val
          · exfalso; apply h2; rw [hqb, hyB] at hq; exact hq.symm
          · by_cases hqa : offAt p s = a.val
            · exfalso; apply h1; rw [hqa, hxA] at hq; exact hq.symm
            · rw [if_neg hqb, if_neg hqa]; exact hq
    · intro j hj
      rw [hblk, hN] at *
      exact hp.blk j (hN ▸ hj)
    · intro s hs
      rw [he2 s, hblk]
      obtain ⟨o1, o2, o3⟩ := hp.own s hs
      refine ⟨hN ▸ o1, ?_⟩
      rw [hO s]
      split_ifs with h1 h2
      · subst h1; rw [hxk]; exact hbk
      · subst h2; rw [hyk]; exact hak
      · exact ⟨o2, o3⟩
    · intro j j' hj hj' hne
      simp only [hblk]
      exact hp.disj j j' (hN ▸ hj) (hN ▸ hj') hne
  exact ⟨hPI, hbl, he2b, fun s => by rw [hO s, hxA, hyB]⟩

theorem blkAt_eq_getElem {p : BlockPartition} {i : Nat} (h : i < p.blocks.val.length) :
    blkAt p i = p.blocks.val[i] := by
  simp [blkAt, List.getD_eq_getElem?_getD, h]

/-- Overwriting one block's `marked_split` (within `[begin, end]`) preserves `PartInv`;
    `begin`, `end`, the other blocks and all the per-state vectors are unchanged. -/
theorem _root_.MercVerified.Refinement.PartInv.set_marked_split {n : Nat} {q : BlockPartition} (hq : PartInv n q)
    (kk : Std.Usize) (hK : kk.val < q.blocks.val.length) (m : Std.Usize)
    (h1 : (blkAt q kk.val).begin.val ≤ m.val) (h2 : m.val ≤ (blkAt q kk.val).«end».val) :
    PartInv n { q with blocks :=
      ({ slice := q.blocks.slice.set kk { blkAt q kk.val with marked_split := m } } :
        alloc.vec.Vec Block) } := by
  set q' : BlockPartition := { q with blocks :=
      ({ slice := q.blocks.slice.set kk { blkAt q kk.val with marked_split := m } } :
        alloc.vec.Vec Block) } with hq'
  have hval : q'.blocks.val = q.blocks.val.set kk.val { blkAt q kk.val with marked_split := m } := by
    show (q.blocks.slice.set kk _).val = _
    rw [Slice.set_val_eq]; rfl
  have hN : q'.blocks.val.length = q.blocks.val.length := by rw [hval, List.length_set]
  have hbe : ∀ j, (blkAt q' j).begin = (blkAt q j).begin ∧ (blkAt q' j).«end» = (blkAt q j).«end» := by
    intro j
    simp only [blkAt, hval, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hj : kk.val = j
    · subst hj; simp [hK]
    · simp [hj]
  have hms : ∀ j, (blkAt q' j).marked_split.val ≠ (blkAt q j).marked_split.val → j = kk.val := by
    intro j hne
    by_contra hj
    apply hne
    simp only [blkAt, hval, List.getD_eq_getElem?_getD, List.getElem?_set]
    simp [Ne.symm hj]
  have hkk : (blkAt q' kk.val).marked_split = m := by
    simp only [blkAt, hval, List.getD_eq_getElem?_getD, List.getElem?_set]
    simp [hK]
  have hbk := hq.blk kk.val hK
  refine ⟨hq.len_e, hq.len_e2b, hq.len_off, hq.perm, hq.inv, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j < q.blocks.val.length := hN ▸ hj
    obtain ⟨hb1, he1⟩ := hbe j
    have hold := hq.blk j hj'
    by_cases hjk : j = kk.val
    · subst hjk
      rw [hb1, he1, hkk]; omega
    · have hsame : (blkAt q' j).marked_split.val = (blkAt q j).marked_split.val := by
        by_contra hne; exact hjk (hms j hne)
      rw [hb1, he1, hsame]; exact hold
  · intro s hs
    obtain ⟨o1, o2, o3⟩ := hq.own s hs
    have he2 : e2bAt q' s = e2bAt q s := rfl
    rw [he2, (hbe _).1, (hbe _).2]
    exact ⟨hN ▸ o1, o2, o3⟩
  · intro j j' hj hj' hne
    rw [(hbe j).1, (hbe j).2, (hbe j').1, (hbe j').2]
    exact hq.disj j j' (hN ▸ hj) (hN ▸ hj') hne

theorem usize_one_val : (1#usize : Std.Usize).val = 1 := rfl

/-- Reading a block after `Slice.set` on the block vector. -/
theorem blkAt_set {q : BlockPartition} (kk : Std.Usize) (hK : kk.val < q.blocks.val.length)
    (nb : Block) (j : Nat) :
    blkAt { q with blocks := ({ slice := q.blocks.slice.set kk nb } : alloc.vec.Vec Block) } j
      = if kk.val = j then nb else blkAt q j := by
  have hval : ({ slice := q.blocks.slice.set kk nb } : alloc.vec.Vec Block).val
      = q.blocks.val.set kk.val nb := by
    show (q.blocks.slice.set kk nb).val = _
    rw [Slice.set_val_eq]; rfl
  simp only [blkAt, hval, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hj : kk.val = j
  · subst hj; simp [hK]
  · simp [hj]

/-- A state is marked when its offset is at or beyond its block's `marked_split`. -/
def IsMarked (p : BlockPartition) (s : Nat) : Prop :=
  (blkAt p (e2bAt p s)).marked_split.val ≤ offAt p s

/-- Marking an unmarked state `f` (swap it with the last unmarked element and shrink the unmarked
    prefix) marks exactly `f`. -/
theorem isMarked_after_mark {n : Nat} {p p' : BlockPartition} (hp : PartInv n p) (f : Nat) (hf : f < n)
    (hlt : offAt p f < (blkAt p (e2bAt p f)).marked_split.val)
    (he2b : ∀ t, e2bAt p' t = e2bAt p t)
    (hms : ∀ j, (blkAt p' j).marked_split.val =
      if j = e2bAt p f then (blkAt p j).marked_split.val - 1 else (blkAt p j).marked_split.val)
    (hoff : ∀ s, offAt p' s =
      if s = f then (blkAt p (e2bAt p f)).marked_split.val - 1
      else if s = (eAt p ((blkAt p (e2bAt p f)).marked_split.val - 1)).index.val then offAt p f
      else offAt p s) :
    ∀ t, t < n → (IsMarked p' t ↔ IsMarked p t ∨ t = f) := by
  obtain ⟨hK, hf1, hf2⟩ := hp.own f hf
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hp.blk _ hK
  set K := e2bAt p f with hKdef
  set ms := (blkAt p K).marked_split.val with hmsdef
  have hy := hp.perm (ms - 1) (by omega)
  set y := (eAt p (ms - 1)).index.val with hydef
  have hyK : e2bAt p y = K := by
    obtain ⟨h1, h2, h3⟩ := hp.own y hy.1
    rw [hy.2] at h2 h3
    exact hp.pos_block_unique h1 hK ⟨h2, h3⟩ ⟨by omega, by omega⟩
  have hff : eAt p (offAt p f) = (eAt p (offAt p f)) := rfl
  intro t ht
  unfold IsMarked
  rw [he2b, hoff t]
  by_cases htK : e2bAt p t = K
  · rw [hms, if_pos htK, htK]
    by_cases htf : t = f
    · subst htf
      simp only [if_true]
      constructor
      · intro _; exact Or.inr trivial
      · intro _; omega
    · rw [if_neg htf]
      by_cases hty : t = y
      · rw [if_pos hty]
        have hne : offAt p f ≠ ms - 1 := by
          intro h
          apply htf
          have := hp.inv f hf
          rw [h] at this
          rw [hty]; exact this
        have hy2 : offAt p y = ms - 1 := hy.2
        constructor
        · intro h; omega
        · rintro (h | h)
          · rw [hty, hy2] at h; omega
          · exact absurd h htf
      · rw [if_neg hty]
        have hne : offAt p t ≠ ms - 1 := by
          intro h
          apply hty
          have := hp.inv t ht
          rw [h] at this
          exact this.symm
        constructor
        · intro h; exact Or.inl (by omega)
        · rintro (h | h)
          · omega
          · exact absurd h htf
  · rw [hms, if_neg htK]
    have htf : t ≠ f := fun h => htK (by rw [h])
    have hty : t ≠ y := fun h => htK (by rw [h]; exact hyK)
    rw [if_neg htf, if_neg hty]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · exact absurd h htf

theorem mark_element_spec {n : Nat} {p : BlockPartition} (h : PartInv n p)
    (s : TagIndex Std.Usize StateTag) (hs : s.index.val < n) :
    ∃ p', verified.merc_reduction.block_partition.BlockPartition.mark_element p s = ok p' ∧
      PartInv n p' ∧ p'.element_to_block = p.element_to_block ∧
      p'.blocks.val.length = p.blocks.val.length ∧
      (∀ j, j ≠ e2bAt p s.index.val → blkAt p' j = blkAt p j) ∧
      (blkAt p' (e2bAt p s.index.val)).begin = (blkAt p (e2bAt p s.index.val)).begin ∧
      (blkAt p' (e2bAt p s.index.val)).«end» = (blkAt p (e2bAt p s.index.val)).«end» ∧
      (blkAt p' (e2bAt p s.index.val)).marked_split.val ≤
        (blkAt p (e2bAt p s.index.val)).marked_split.val ∧
      (blkAt p' (e2bAt p s.index.val)).marked_split.val <
        (blkAt p (e2bAt p s.index.val)).«end».val ∧
      (∀ t, t < n → (IsMarked p' t ↔ IsMarked p t ∨ t = s.index.val)) := by
  obtain ⟨hK, ho1, ho2⟩ := h.own _ hs
  unfold verified.merc_reduction.block_partition.BlockPartition.mark_element
  have h1 : s.index.val < p.element_to_block.length := by
    have := h.len_e2b
    show s.index.val < p.element_to_block.val.length
    omega
  rw [vec_tagged_index_val _ _ h1]
  simp only [bind_ok]
  have h2 : s.index.val < p.element_offset.length := by
    have := h.len_off
    show s.index.val < p.element_offset.val.length
    omega
  rw [vec_tagged_index_val _ _ h2]
  simp only [bind_ok]
  have hbi : ((p.element_to_block.slice.val)[s.index.val]'h1).index.val = e2bAt p s.index.val := by
    have h1' : s.index.val < p.element_to_block.val.length := h1
    simp [e2bAt, List.getD_eq_getElem?_getD, h1']
    rfl
  have hoo : ((p.element_offset.slice.val)[s.index.val]'h2).val = offAt p s.index.val := by
    have h2' : s.index.val < p.element_offset.val.length := h2
    simp [offAt, List.getD_eq_getElem?_getD, h2']
    rfl
  generalize ((p.element_to_block.slice.val)[s.index.val]'h1) = bi at hbi ⊢
  generalize ((p.element_offset.slice.val)[s.index.val]'h2) = o at hoo ⊢
  generalize hKdef : e2bAt p s.index.val = K at *
  generalize hoffdef : offAt p s.index.val = off at *
  have hbN : bi.index.val < p.blocks.length := by rw [hbi]; exact hK
  rw [vec_tagged_index_val p.blocks bi hbN]
  simp only [bind_ok]
  have hb0 : (p.blocks.slice.val[bi.index.val]'hbN) = blkAt p K := by
    rw [blkAt_eq_getElem hK]; congr 1
  rw [hb0]
  obtain ⟨hbe, hbn, hms1, hms2⟩ := h.blk K hK
  by_cases hlt : o < (blkAt p K).marked_split
  · have hlt' : o.val < (blkAt p K).marked_split.val := hlt
    rw [if_pos hlt]
    have hsub : (1#usize).val ≤ (blkAt p K).marked_split.val := by rw [usize_one_val]; omega
    obtain ⟨i, hi, hival, -⟩ := spec_imp_exists
      (Usize.sub_spec (x := (blkAt p K).marked_split) (y := 1#usize) hsub)
    simp only [usize_one_val] at hival
    rw [hi]
    simp only [bind_ok]
    have hon : o.val < n := by omega
    have hin : i.val < n := by omega
    obtain ⟨self1, hsw, hP1, hbl1, he1, hoff1⟩ := swap_elements_partInv h o i hon hin hK
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    rw [hsw]
    simp only [bind_ok]
    have hbN1 : bi.index.val < self1.blocks.val.length := by rw [hbl1]; omega
    rw [blocks_index_mut_contract self1 bi hbN1]
    simp only [bind_ok]
    have hbk1 : blkAt self1 K = blkAt p K := by simp [blkAt, hbl1]
    have hb1 : self1.blocks.slice.val[bi.index.val]'hbN1 = blkAt p K := by
      rw [← hbk1, blkAt_eq_getElem (by omega)]; congr 1
    rw [hb1]
    obtain ⟨i1, hi1, hi1v, -⟩ := spec_imp_exists
      (Usize.sub_spec (x := (blkAt p K).marked_split) (y := 1#usize) hsub)
    simp only [usize_one_val] at hi1v
    have hbkK : blkAt self1 bi.index.val = blkAt p K := by rw [hbi]; exact hbk1
    have hnb : ({ blkAt self1 bi.index.val with marked_split := i1 } : Block) =
        { begin := (blkAt p K).begin, marked_split := i1, «end» := (blkAt p K).«end» } := by
      rw [hbkK]
    have hwfI : merc_reduction.block_partition.Block.WellFormed
        ({ begin := (blkAt p K).begin, marked_split := i1, «end» := (blkAt p K).«end» } : Block) := by
      refine ⟨hbe, ?_, ?_⟩
      · show (blkAt p K).begin.val ≤ i1.val
        omega
      · show i1.val ≤ (blkAt p K).«end».val
        omega
    obtain ⟨u, hu⟩ := merc_reduction.block_partition.Block.assert_consistent_ok
      ({ begin := (blkAt p K).begin, marked_split := i1, «end» := (blkAt p K).«end» } : Block) hwfI
    have hlen : bi.index.val <
        (({ slice := self1.blocks.slice.set bi.index ({ begin := (blkAt p K).begin, marked_split := i1, «end» := (blkAt p K).«end» } : Block) } :
          alloc.vec.Vec Block)).length := by
      show bi.index.val < (self1.blocks.slice.set _ _).length
      rw [Slice.set_length]; exact hbN1
    refine ⟨{ self1 with blocks :=
        ({ slice := self1.blocks.slice.set bi.index ({ begin := (blkAt p K).begin, marked_split := i1, «end» := (blkAt p K).«end» } : Block) } :
          alloc.vec.Vec Block) },
      ?_, ?_, he1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hi1, vec_tagged_index_val _ bi hlen, Slice.set_val_eq, hu]
    · have := hP1.set_marked_split bi.index hbN1 i1 (by rw [hbkK]; omega) (by rw [hbkK]; omega)
      rw [hnb] at this
      exact this
    · show (self1.blocks.slice.set _ _).val.length = _
      rw [Slice.set_val_eq, List.length_set, hbl1]
      rfl
    · intro j hj
      rw [blkAt_set bi.index hbN1, if_neg (by omega)]
      simp [blkAt, hbl1]
    · rw [blkAt_set bi.index hbN1, if_pos hbi]
    · rw [blkAt_set bi.index hbN1, if_pos hbi]
    · rw [blkAt_set bi.index hbN1, if_pos hbi]; simp only []; omega
    · rw [blkAt_set bi.index hbN1, if_pos hbi]; simp only []; omega
    · -- exactly `s` becomes marked
      have hoK : o.val = offAt p s.index.val := by rw [hoo, hoffdef]
      have hef : (eAt p o.val).index.val = s.index.val := by rw [hoK]; exact h.inv _ hs
      refine isMarked_after_mark h s.index.val hs ?_ ?_ ?_ ?_
      · rw [hKdef, ← hoK]; exact hlt'
      · intro t
        show (self1.element_to_block.val.getD t zBT).index.val = _
        rw [he1]; rfl
      · intro j
        rw [blkAt_set bi.index hbN1, hKdef]
        by_cases hj : j = K
        · rw [if_pos (by omega : bi.index.val = j), if_pos hj]
          simp only []
          rw [hi1v, hj]
        · rw [if_neg (by omega : ¬ bi.index.val = j), if_neg hj]
          simp [blkAt, hbl1]
      · intro s'
        show offAt self1 s' = _
        rw [hoff1 s', hef, hKdef, ← hoK]
        have hi1' : i.val = (blkAt p K).marked_split.val - 1 := hival
        rw [hi1']
  · rw [if_neg hlt]
    simp only [bind_ok]
    obtain ⟨u, hu⟩ := merc_reduction.block_partition.Block.assert_consistent_ok (blkAt p K)
      ⟨hbe, hms1, hms2⟩
    have hlt' : ¬ o.val < (blkAt p K).marked_split.val := fun hh => hlt hh
    refine ⟨p, ?_, h, rfl, rfl, fun _ _ => rfl, rfl, rfl, le_refl _, ?_, ?_⟩
    · simp [vec_tagged_index_val p.blocks bi hbN, hb0, hu]
    · omega
    · intro t ht
      constructor
      · intro h1; exact Or.inl h1
      · rintro (h1 | h1)
        · exact h1
        · unfold IsMarked
          rw [h1, hKdef, hoffdef]
          have := hlt'
          rw [hoo] at this
          omega

/-- The initial partition `BlockPartition::new n` satisfies `PartInv`. -/
theorem init_partInv (num : Std.Usize) (hpos : 0 < num.val) :
    ∃ p : BlockPartition,
      verified.merc_reduction.block_partition.BlockPartition.new num = ok p ∧
      PartInv num.val p ∧ p.blocks.val.length = 1 := by
  obtain ⟨p, hnew, hbl, hel, he2b, hoff⟩ := block_partition_new_spec num hpos
  have hlt : ∀ i, i < num.val → i < 2 ^ UScalarTy.Usize.numBits :=
    fun i hi => lt_trans hi (sz_val_lt_two_pow num)
  have hblk : ∀ k, blkAt p k = if k = 0 then
      ({ begin := 0#usize, marked_split := 0#usize, «end» := num } : Block) else blk0 := by
    intro k
    simp only [blkAt, hbl, List.getD_eq_getElem?_getD]
    cases k <;> simp
  refine ⟨p, hnew, ?_, by rw [hbl]; rfl⟩
  have hN : p.blocks.val.length = 1 := by rw [hbl]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hel]
  · simp [he2b]
  · simp [hoff]
  · intro i hi
    have e : eAt p i = uTag i := by
      simp [eAt, hel, List.getD_eq_getElem?_getD, hi]
    have o : offAt p i = i := by
      simp [offAt, hoff, List.getD_eq_getElem?_getD, hi, uTotal_val_of_lt (hlt i hi)]
    rw [e]
    have : (uTag (Tag := StateTag) i).index.val = i := uTotal_val_of_lt (hlt i hi)
    refine ⟨by rw [this]; exact hi, ?_⟩
    rw [this]; exact o
  · intro s hs
    have e : eAt p s = uTag s := by
      simp [eAt, hel, List.getD_eq_getElem?_getD, hs]
    have o : offAt p s = s := by
      simp [offAt, hoff, List.getD_eq_getElem?_getD, hs, uTotal_val_of_lt (hlt s hs)]
    rw [o, e]
    exact uTotal_val_of_lt (hlt s hs)
  · intro k hk
    rw [hN] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [hblk, if_true]
    simp
    omega
  · intro s hs
    have e : e2bAt p s = 0 := by
      simp [e2bAt, he2b, List.getD_eq_getElem?_getD, hs]
      exact uTotal_val_of_lt (by have := sz_val_lt_two_pow num; omega)
    have o : offAt p s = s := by
      simp [offAt, hoff, List.getD_eq_getElem?_getD, hs, uTotal_val_of_lt (hlt s hs)]
    rw [e, o, hN]
    simp only [hblk, if_true]
    simp
    omega
  · intro j k hj hk hne
    rw [hN] at hj hk
    omega

end MercVerified.Refinement.Proofs
