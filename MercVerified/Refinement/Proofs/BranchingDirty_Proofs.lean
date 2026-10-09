import MercVerified.Refinement.Proofs.MarkDirty_Proofs
import MercVerified.Refinement.Proofs.WorklistLoop_Proofs
import Aeneas.Std.WP

/-!
# `mark_dirty_states` / `mark_dirty_new_blocks` with `BRANCHING = true`

The branching marking rule: the source of a transition into a new block is marked, except for the
τ-transitions (hidden labels) whose source lies in a block created in this iteration (block number
at least `num_blocks`).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The branching marking guard of an incoming transition: a hidden transition is skipped when its
source lies in a block created in this iteration. -/
def BGuard (p : BlockPartition) (num_blocks : Sz) (i : FromTransition) : Prop :=
  ¬ i.label.index.val = 0 ∨ e2bAt p i.«from».index.val < num_blocks.val

theorem bdirty_inner_loop {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (num_blocks : Sz) {n : Nat} (hn : n ≤ Usize.max)
    (hE : ∀ l : TagIndex Std.Usize LabelTag, LTSInst.is_hidden_label lts l = ok (decide (l.index.val = 0)))
    (iter : alloc.vec.into_iter.IntoIter FromTransition) (l : List FromTransition)
    (hl : iter.val = l) (hf : ∀ i ∈ l, i.«from».index.val < n)
    {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (h : DirtyInv n p w)
    (hsem : DirtySem n p1 p w D) :
    ∃ p' w', verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0 true LTSInst
        iter lts p w num_blocks = ok (p', w') ∧ DirtyInv n p' w' ∧
      p'.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 p' w' (fun t => D t ∨ ∃ i ∈ l, BGuard p num_blocks i ∧
        i.«from».index.val = t.index.val) := by
  unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0
  have hDm : ∀ m (hm : m < l.length) (t : ST),
      ((D t ∨ ∃ i ∈ l.take m, BGuard p num_blocks i ∧ i.«from».index.val = t.index.val) ∨
        (BGuard p num_blocks l[m] ∧ t.index.val = l[m].«from».index.val)) ↔
      (D t ∨ ∃ i ∈ l.take (m + 1), BGuard p num_blocks i ∧ i.«from».index.val = t.index.val) := by
    intro m hm t
    rw [List.take_succ_eq_append_getElem hm]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ((h | ⟨i, hi, e⟩) | ⟨g, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, Or.inl hi, e⟩
      · exact Or.inr ⟨l[m], Or.inr rfl, g, e.symm⟩
    · rintro (h | ⟨i, hi | hi, e⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨i, hi, e⟩)
      · subst hi; exact Or.inr ⟨e.1, e.2.symm⟩
  obtain ⟨y, hy, hp', hw', hyl, hysem⟩ := loop_nat_spec
    (fun (x : alloc.vec.into_iter.IntoIter FromTransition × BlockPartition × VecTy BT) =>
      verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body true LTSInst lts
        num_blocks x.1 x.2.1 x.2.2)
    (fun x => l.length - x.1.val.length)
    (fun m x => m ≤ l.length ∧ x.1.val = l.drop m ∧ DirtyInv n x.2.1 x.2.2 ∧
      x.2.1.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 x.2.1 x.2.2 (fun t => D t ∨ ∃ i ∈ l.take m, BGuard p num_blocks i ∧
        i.«from».index.val = t.index.val))
    (fun y => DirtyInv n y.1 y.2 ∧ y.1.blocks.val.length = p.blocks.val.length ∧ True ∧
      DirtySem n p1 y.1 y.2 (fun t => D t ∨ ∃ i ∈ l, BGuard p num_blocks i ∧
        i.«from».index.val = t.index.val))
    l.length
    (by intro m x hx; obtain ⟨h1, h2, -⟩ := hx; rw [h2]; simp; omega)
    (by intro m x hx; exact hx.1)
    (by
      intro m x hm hx
      obtain ⟨-, h2, h3, h4, h5⟩ := hx
      have hdrop : l.drop m = l[m] :: l.drop (m + 1) := List.drop_eq_getElem_cons hm
      obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' x.1 l[m] (l.drop (m + 1)) (by rw [h2, hdrop])
      have hfm : l[m].«from».index.val < n := hf _ (List.getElem_mem hm)
      have hpp : ∀ s, e2bAt x.2.1 s = e2bAt p s := fun s => by
        simp [e2bAt, h5.1, hsem.1]
      have hHid := hE l[m].label
      have hbody : ∀ y, (verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body
          true LTSInst lts num_blocks x.1 x.2.1 x.2.2 = y) ↔ (_ = y) := fun y => Iff.rfl
      by_cases hh : l[m].label.index.val = 0
      · by_cases hlt : e2bAt p l[m].«from».index.val < num_blocks.val
        · -- hidden, source in an old block: marked
          obtain ⟨oB, bm, p1', w1, hbn, ⟨blk, hblk, hhm⟩, hcase, hmk, hI, hlen, hsem'⟩ :=
            dirty_transition_step h3 h5 hn l[m].«from» hfm
          have hoB : oB.index.val = e2bAt p l[m].«from».index.val := by
            have h1 := block_number_ok h3.1 l[m].«from» hfm
            rw [hbn] at h1
            simp only [ok.injEq] at h1
            rw [h1, e2bAt_eq h3.1 _ hfm, hpp]
          have hlt' : oB.index < num_blocks := by
            rw [UScalar.lt_equiv]; rw [hoB]; exact hlt
          have hltn : (x.2.1.element_to_block.val.getD l[m].«from».index.val zBT).index.val <
              num_blocks.val := by
            rw [e2bAt_eq h3.1 _ hfm, hpp]; exact hlt
          have hltn' := hltn
          simp only [List.getD_eq_getElem?_getD] at hltn'
          have hltN : oB.index.val < num_blocks.val := by rw [hoB]; exact hlt
          refine ⟨(it1, p1', w1), ?_, hm, by rw [hit1], hI, by rw [hlen, h4],
            hsem'.congr (fun t _ => ?_)⟩
          · show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body true
              LTSInst lts num_blocks x.1 x.2.1 x.2.2 = _
            unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body
            rw [hnext]
            rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, hpush⟩
            · simp [hHid, hh, hbn, tag_value_id, hltN, hblk, hhm, hmk]
            · simp [hHid, hh, hbn, tag_value_id, hltN, hblk, hhm, hpush, hmk]
          · rw [List.take_succ_eq_append_getElem hm]
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · rintro ((h | ⟨i, hi, g, e⟩) | e)
              · exact Or.inl h
              · exact Or.inr ⟨i, Or.inl hi, g, e⟩
              · exact Or.inr ⟨l[m], Or.inr rfl, Or.inr hlt, e.symm⟩
            · rintro (h | ⟨i, hi | hi, g, e⟩)
              · exact Or.inl (Or.inl h)
              · exact Or.inl (Or.inr ⟨i, hi, g, e⟩)
              · subst hi; exact Or.inr e.symm
        · -- hidden, source in a new block: skipped
          have hbn := block_number_ok h3.1 l[m].«from» hfm
          have hge' : ¬ (x.2.1.element_to_block.val.getD l[m].«from».index.val zBT).index < num_blocks := by
            rw [UScalar.lt_equiv, e2bAt_eq h3.1 _ hfm, hpp]; exact hlt
          refine ⟨(it1, x.2.1, x.2.2), ?_, hm, by rw [hit1], h3, h4,
            h5.congr (fun t _ => ?_)⟩
          · show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body true
              LTSInst lts num_blocks x.1 x.2.1 x.2.2 = _
            unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body
            rw [hnext]
            have hgeN : ¬ (x.2.1.element_to_block.val.getD l[m].«from».index.val zBT).index.val <
                num_blocks.val := by
              rw [e2bAt_eq h3.1 _ hfm, hpp]; exact hlt
            have hgeN' := hgeN
            simp only [List.getD_eq_getElem?_getD] at hgeN'
            simp [hHid, hh, hbn, tag_value_id, hgeN']
          · rw [List.take_succ_eq_append_getElem hm]
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · rintro (h | ⟨i, hi, g, e⟩)
              · exact Or.inl h
              · exact Or.inr ⟨i, Or.inl hi, g, e⟩
            · rintro (h | ⟨i, hi | hi, g, e⟩)
              · exact Or.inl h
              · exact Or.inr ⟨i, hi, g, e⟩
              · subst hi
                rcases g with g | g
                · exact absurd hh g
                · exact absurd g hlt
      · -- not hidden: always marked
        obtain ⟨oB, bm, p1', w1, hbn, ⟨blk, hblk, hhm⟩, hcase, hmk, hI, hlen, hsem'⟩ :=
          dirty_transition_step h3 h5 hn l[m].«from» hfm
        refine ⟨(it1, p1', w1), ?_, hm, by rw [hit1], hI, by rw [hlen, h4],
          hsem'.congr (fun t _ => ?_)⟩
        · show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body true
            LTSInst lts num_blocks x.1 x.2.1 x.2.2 = _
          unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body
          rw [hnext]
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, hpush⟩
          · simp [hHid, hh, hbn, hblk, hhm, hmk]
          · simp [hHid, hh, hbn, hblk, hhm, hpush, hmk]
        · rw [List.take_succ_eq_append_getElem hm]
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro ((h | ⟨i, hi, g, e⟩) | e)
            · exact Or.inl h
            · exact Or.inr ⟨i, Or.inl hi, g, e⟩
            · exact Or.inr ⟨l[m], Or.inr rfl, Or.inl hh, e.symm⟩
          · rintro (h | ⟨i, hi | hi, g, e⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨i, hi, g, e⟩)
            · subst hi; exact Or.inr e.symm)
    (by
      intro x hx
      obtain ⟨hm, h2, h3, h4, h5⟩ := hx
      have : x.1.val = [] := by rw [h2]; simp
      refine ⟨(x.2.1, x.2.2), ?_, h3, h4, trivial, by simpa using h5⟩
      show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body true LTSInst lts
        num_blocks x.1 x.2.1 x.2.2 = _
      unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body
      rw [into_iter_next_none' _ this]
      simp)
    (iter, p, w) ⟨by omega, by rw [hl]; simp, h, rfl, by simpa using hsem⟩
  exact ⟨y.1, y.2, hy, hp', hw', hysem⟩

theorem bguard_congr {p p' : BlockPartition} (num_blocks : Sz)
    (h : ∀ s, e2bAt p s = e2bAt p' s) (i : FromTransition) :
    BGuard p num_blocks i ↔ BGuard p' num_blocks i := by
  unfold BGuard; rw [h]

/-- The states that have a guarded incoming transition recorded in `incoming` from a state of `S`'s
    successors. -/
def PredOfG (p : BlockPartition) (num_blocks : Sz) (incoming : IncomingTransitions) (S : List ST)
    (t : ST) : Prop :=
  ∃ s ∈ S, ∃ res : alloc.vec.Vec FromTransition,
    IncomingTransitions.incoming_transitions incoming s = ok res ∧
      ∃ i ∈ res.val, BGuard p num_blocks i ∧ i.«from».index.val = t.index.val

/-- The states with a guarded transition into block `bl` of `p`. -/
def PredBlkG (p : BlockPartition) (num_blocks : Sz) (incoming : IncomingTransitions) (n : Nat)
    (bl : Nat) (t : ST) : Prop :=
  ∃ s : ST, s.index.val < n ∧ e2bAt p s.index.val = bl ∧
    ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∃ i ∈ res.val, BGuard p num_blocks i ∧ i.«from».index.val = t.index.val

theorem bdirty_outer_loop {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : IncomingTransitions) (num_blocks : Sz) {n : Nat} (hn : n ≤ Usize.max)
    (hE : ∀ l : TagIndex Std.Usize LabelTag, LTSInst.is_hidden_label lts l = ok (decide (l.index.val = 0)))
    (hinc : ∀ s : ST, s.index.val < n → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n)
    (sl : Slice ST) (hsl : ∀ s ∈ sl.val, s.index.val < n)
    {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (h : DirtyInv n p w)
    (hsem : DirtySem n p1 p w D) :
    ∃ p' w', verified.merc_reduction.signature_refinement.mark_dirty_states_loop0 true LTSInst
        ({ slice := sl, i := 0 } : core.slice.iter.Iter ST) lts p incoming w num_blocks = ok (p', w') ∧
      DirtyInv n p' w' ∧ p'.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 p' w' (fun t => D t ∨ PredOfG p num_blocks incoming sl.val t) := by
  unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0
  have hPm : ∀ m (hm : m < sl.val.length) (res : alloc.vec.Vec FromTransition)
      (hres : IncomingTransitions.incoming_transitions incoming sl.val[m] = ok res) (t : ST),
      ((D t ∨ PredOfG p num_blocks incoming (sl.val.take m) t) ∨
        ∃ i ∈ res.val, BGuard p num_blocks i ∧ i.«from».index.val = t.index.val) ↔
      (D t ∨ PredOfG p num_blocks incoming (sl.val.take (m + 1)) t) := by
    intro m hm res hres t
    unfold PredOfG
    rw [List.take_succ_eq_append_getElem hm]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ((h | ⟨s, hs, r, hr, i, hi, e⟩) | ⟨i, hi, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, Or.inl hs, r, hr, i, hi, e⟩
      · exact Or.inr ⟨sl.val[m], Or.inr rfl, res, hres, i, hi, e⟩
    · rintro (h | ⟨s, hs | hs, r, hr, i, hi, e⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨s, hs, r, hr, i, hi, e⟩)
      · subst hs
        have : r = res := by simpa using hr.symm.trans hres
        subst this
        exact Or.inr ⟨i, hi, e⟩
  obtain ⟨y, hy, hp', hw', hysem⟩ := loop_nat_spec
    (fun (x : core.slice.iter.Iter ST × BlockPartition × VecTy BT) =>
      verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body true LTSInst lts
        incoming num_blocks x.1 x.2.1 x.2.2)
    (fun x => x.1.i)
    (fun m x => x.1.slice = sl ∧ x.1.i = m ∧ m ≤ sl.val.length ∧ DirtyInv n x.2.1 x.2.2 ∧
      x.2.1.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 x.2.1 x.2.2 (fun t => D t ∨ PredOfG p num_blocks incoming (sl.val.take m) t))
    (fun y => DirtyInv n y.1 y.2 ∧ y.1.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 y.1 y.2 (fun t => D t ∨ PredOfG p num_blocks incoming sl.val t))
    sl.val.length
    (by intro m x hx; exact hx.2.1) (by intro m x hx; exact hx.2.2.1)
    (by
      intro m x hm hx
      obtain ⟨h1, h2, -, h3, h4, h5⟩ := hx
      obtain ⟨x1, x2, x3⟩ := x
      obtain ⟨xs, xi⟩ := x1
      simp only at h1 h2 h3 h4 h5
      subst h1; subst h2
      have hml : xi < xs.length := by simpa [Slice.length] using hm
      have hnext : core.slice.iter.IteratorSliceIter.next
          ({ slice := xs, i := xi } : core.slice.iter.Iter ST)
          = ok (some (xs.val[xi]'hml), ({ slice := xs, i := xi + 1 } : core.slice.iter.Iter ST)) := by
        unfold core.slice.iter.IteratorSliceIter.next
        simp [hml, Slice.len]
        rfl
      obtain ⟨res, hres, hresn⟩ := hinc _ (hsl _ (List.getElem_mem hml))
      obtain ⟨p1', w1, hloop, hI, hlen, hsem'⟩ := bdirty_inner_loop LTSInst lts num_blocks hn hE
        (res : alloc.vec.into_iter.IntoIter FromTransition) res.val rfl hresn h3 h5
      have hpp : ∀ s, e2bAt x2 s = e2bAt p s := fun s => by simp [e2bAt, h5.1, hsem.1]
      refine ⟨(⟨xs, xi + 1⟩, p1', w1), ?_, rfl, rfl, by omega, hI, by rw [hlen, h4],
        hsem'.congr (fun t _ => ?_)⟩
      · show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body true LTSInst lts
          incoming num_blocks ⟨xs, xi⟩ x2 x3 = _
        unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body
        rw [hnext]
        simp [hres, alloc.vec.IntoIteratorVec.into_iter, hloop]
      · rw [← hPm xi hml res hres t]
        have hg : ∀ i, BGuard x2 num_blocks i ↔ BGuard p num_blocks i := fun i => bguard_congr num_blocks hpp i
        constructor
        · rintro (h | ⟨i, hi, g, e⟩)
          · exact Or.inl h
          · exact Or.inr ⟨i, hi, (hg i).1 g, e⟩
        · rintro (h | ⟨i, hi, g, e⟩)
          · exact Or.inl h
          · exact Or.inr ⟨i, hi, (hg i).2 g, e⟩)
    (by
      intro x hx
      obtain ⟨h1, h2, -, h3, h4, h5⟩ := hx
      obtain ⟨x1, x2, x3⟩ := x
      obtain ⟨xs, xi⟩ := x1
      simp only at h1 h2 h3 h4 h5
      subst h1
      have hml : ¬ xi < xs.length := by
        intro hh; have := hh; simp [Slice.length] at this; omega
      have hnext : core.slice.iter.IteratorSliceIter.next ({ slice := xs, i := xi } : core.slice.iter.Iter ST)
          = ok (none, ({ slice := xs, i := xi } : core.slice.iter.Iter ST)) := by
        unfold core.slice.iter.IteratorSliceIter.next
        simp [hml, Slice.len]
      refine ⟨(x2, x3), ?_, h3, h4, by simpa using h5⟩
      show verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body true LTSInst lts
          incoming num_blocks ⟨xs, xi⟩ x2 x3 = _
      unfold verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body
      rw [hnext]
      simp)
    (⟨sl, 0⟩, p, w) ⟨rfl, rfl, by omega, h, rfl, by simpa [PredOfG] using hsem⟩
  exact ⟨y.1, y.2, hy, hp', hw', hysem⟩

theorem bdirty_states_spec {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : IncomingTransitions) (num_blocks : Sz) {n : Nat} (hn : n ≤ Usize.max)
    (hE : ∀ l : TagIndex Std.Usize LabelTag, LTSInst.is_hidden_label lts l = ok (decide (l.index.val = 0)))
    (hinc : ∀ s : ST, s.index.val < n → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n)
    {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (h : DirtyInv n p w)
    (hsem : DirtySem n p1 p w D)
    (states : VecTy ST) (nb : BT) (hnb : nb.index.val < p.blocks.val.length) :
    ∃ p' w' states',
      verified.merc_reduction.signature_refinement.mark_dirty_states true LTSInst lts p incoming w
        states nb num_blocks = ok (p', w', states') ∧
      DirtyInv n p' w' ∧ p'.blocks.val.length = p.blocks.val.length ∧
      DirtySem n p1 p' w' (fun t => D t ∨ PredBlkG p num_blocks incoming n nb.index.val t) := by
  have hp := h.1
  have hbk := hp.blk nb.index.val hnb
  obtain ⟨v1, hv1, hv10⟩ := alloc.vec.Vec.clear_spec Global states
  have hnle : n ≤ Usize.max := hn
  have hlenE : (alloc.vec.Vec.deref p.elements).val.length = n := by
    simp [alloc.vec.Vec.deref, hp.len_e]
  have hbi : verified.merc_reduction.block_partition.BlockPartition.iter_block p nb
      = ok { elements := alloc.vec.Vec.deref p.elements, index := (blkAt p nb.index.val).begin,
             «end» := (blkAt p nb.index.val).«end» } := by
    unfold verified.merc_reduction.block_partition.BlockPartition.iter_block
    rw [vec_tagged_index_val p.blocks nb hnb]
    have hrd : p.blocks.slice.val[nb.index.val]'hnb = blkAt p nb.index.val := (blkAt_eq_getElem hnb).symm
    simp [hrd]
  obtain ⟨v2, hv2, hv2v⟩ := alloc.vec.Vec.extend_blockIter_spec v1
    { elements := alloc.vec.Vec.deref p.elements, index := (blkAt p nb.index.val).begin,
      «end» := (blkAt p nb.index.val).«end» }
    (by simp only []; omega) (by simp only []; rw [hv10]; simp; omega)
  have hwin : ((alloc.vec.Vec.deref p.elements).val.drop (blkAt p nb.index.val).begin.val).take
      ((blkAt p nb.index.val).«end».val - (blkAt p nb.index.val).begin.val)
      = regionElems p (blkAt p nb.index.val).begin.val
        ((blkAt p nb.index.val).«end».val - (blkAt p nb.index.val).begin.val) := by
    rw [region_eq_window hp _ _ (by omega)]
    simp [alloc.vec.Vec.deref, Slice.from_val]
  have hv2mem : ∀ s, s ∈ v2.val ↔ (s.index.val < n ∧ e2bAt p s.index.val = nb.index.val) := by
    intro s
    rw [hv2v, hv10]
    simp only [List.nil_append]
    rw [hwin]
    exact regionElems_mem_iff hp hnb s
  have hsl : ∀ s ∈ (alloc.vec.Vec.deref v2).val, s.index.val < n := by
    intro s hs
    have hs' : s ∈ v2.val := by simpa [alloc.vec.Vec.deref, Slice.from_val] using hs
    exact ((hv2mem s).mp hs').1
  obtain ⟨p', w', hloop, hI, hlen, hsem'⟩ := bdirty_outer_loop LTSInst lts incoming num_blocks hn hE hinc
    (alloc.vec.Vec.deref v2) hsl h hsem
  refine ⟨p', w', v2, ?_, hI, hlen, hsem'.congr (fun t _ => ?_)⟩
  · unfold verified.merc_reduction.signature_refinement.mark_dirty_states
    simp [hv1, hbi, hv2, core.slice.Slice.iter, hloop]
  · have hval : (alloc.vec.Vec.deref v2).val = v2.val := by simp [alloc.vec.Vec.deref, Slice.from_val]
    rw [hval]
    constructor
    · rintro (h | ⟨s, hs, r⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, ((hv2mem s).mp hs).1, ((hv2mem s).mp hs).2, r⟩
    · rintro (h | ⟨s, hs1, hs2, r⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s, (hv2mem s).mpr ⟨hs1, hs2⟩, r⟩

theorem bmarkDirtyAcc_spec {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label) (lts : L)
    (incoming : IncomingTransitions) (block_index : BT) (num_blocks : Sz) {n : Nat}
    (hn : n ≤ Usize.max)
    (hE : ∀ l : TagIndex Std.Usize LabelTag, LTSInst.is_hidden_label lts l = ok (decide (l.index.val = 0)))
    (hinc : ∀ s : ST, s.index.val < n → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < n) :
    ∀ (l : List BT) {p1 p : BlockPartition} {w : VecTy BT} {D : ST → Prop} (s : VecTy ST),
      (∀ nb ∈ l, nb.index.val < p.blocks.val.length) → DirtyInv n p w → DirtySem n p1 p w D →
      ∃ p' w' s', markDirtyAcc true LTSInst lts incoming block_index num_blocks p w s l
          = ok (p', w', s') ∧ DirtyInv n p' w' ∧ p'.blocks.val.length = p.blocks.val.length ∧
        DirtySem n p1 p' w' (fun t => D t ∨ ∃ nb ∈ l, nb ≠ block_index ∧
          PredBlkG p1 num_blocks incoming n nb.index.val t) := by
  intro l
  induction l with
  | nil =>
    intro p1 p w D s _ h hsem
    exact ⟨p, w, s, by simp [markDirtyAcc], h, rfl, hsem.congr (fun t _ => by simp)⟩
  | cons nb tl ih =>
    intro p1 p w D s hl h hsem
    rw [markDirtyAcc_cons]
    by_cases hb : block_index = nb
    · rw [markDirtyStep_pos true LTSInst lts incoming block_index num_blocks nb p w s hb]
      simp only [bind_ok]
      obtain ⟨p2, w2, s2, hrest, hI2, hlen2, hsem2⟩ :=
        ih s (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h hsem
      refine ⟨p2, w2, s2, hrest, hI2, hlen2, hsem2.congr (fun t _ => ?_)⟩
      constructor
      · rintro (h | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl h
        · exact Or.inr ⟨nb', List.mem_cons_of_mem _ hnb', hne, r⟩
      · rintro (h | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hnb' with rfl | hnb'
          · exact absurd hb.symm hne
          · exact Or.inr ⟨nb', hnb', hne, r⟩
    · rw [markDirtyStep_neg true LTSInst lts incoming block_index num_blocks nb p w s hb]
      obtain ⟨p1', w1, s1, hst, hI, hlen, hsem1⟩ := bdirty_states_spec LTSInst lts incoming num_blocks hn hE
        hinc h hsem s nb (hl nb (List.mem_cons_self ..))
      rw [hst]
      simp only [bind_ok]
      obtain ⟨p2, w2, s2, hrest, hI2, hlen2, hsem2⟩ := ih s1
        (fun x hx => by rw [hlen]; exact hl x (List.mem_cons_of_mem _ hx)) hI hsem1
      refine ⟨p2, w2, s2, hrest, hI2, by rw [hlen2, hlen], hsem2.congr (fun t _ => ?_)⟩
      have hpp1 : ∀ x, e2bAt p x = e2bAt p1 x := fun x => by simp [e2bAt, hsem.1]
      have hPB : ∀ bl, PredBlkG p num_blocks incoming n bl t ↔ PredBlkG p1 num_blocks incoming n bl t := by
        intro bl
        unfold PredBlkG
        simp only [hpp1]
        constructor
        · rintro ⟨s, hs, he, r, hr, i, hi, g, e⟩
          exact ⟨s, hs, he, r, hr, i, hi, (bguard_congr num_blocks hpp1 i).1 g, e⟩
        · rintro ⟨s, hs, he, r, hr, i, hi, g, e⟩
          exact ⟨s, hs, he, r, hr, i, hi, (bguard_congr num_blocks hpp1 i).2 g, e⟩
      constructor
      · rintro ((h | hP) | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl h
        · exact Or.inr ⟨nb, List.mem_cons_self .., hb ∘ Eq.symm, (hPB _).mp hP⟩
        · exact Or.inr ⟨nb', List.mem_cons_of_mem _ hnb', hne, r⟩
      · rintro (h | ⟨nb', hnb', hne, r⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hnb' with rfl | hnb'
          · exact Or.inl (Or.inr ((hPB _).mpr r))
          · exact Or.inr ⟨nb', hnb', hne, r⟩

end MercVerified.Refinement.Proofs
