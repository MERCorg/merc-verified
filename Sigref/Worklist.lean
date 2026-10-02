import Sigref.Refinable

/-!
# `MarkDirty` with the worklist (paper Algorithm 3)

`markW` is the paper's `MarkDirty`: if the block has no dirty state yet it is pushed on the
worklist, then the state is swapped into the marked suffix. `WLInv` is the worklist invariant of
the algorithm: the worklist has no duplicates, every queued block is valid and contains a dirty
state, and every dirty state's block is queued.
-/

namespace Sigref

namespace RP

open Classical

variable {n : ℕ}

/-- A refinable partition together with its worklist of blocks that contain dirty states. -/
structure Ctx (n : ℕ) where
  rp : RP n
  wl : List ℕ

/-- Worklist invariant. -/
structure WLInv (c : Ctx n) : Prop where
  wf : c.rp.WF
  nodup : c.wl.Nodup
  queued : ∀ b ∈ c.wl, b < c.rp.nb ∧ ∃ x, c.rp.blk x = b ∧ c.rp.Dirty x
  dirty : ∀ x, c.rp.Dirty x → c.rp.blk x ∈ c.wl

/-- `MarkDirty`: queue the block if it has no dirty state yet, then mark. -/
noncomputable def markW (c : Ctx n) (x : Fin n) : Ctx n :=
  if c.rp.Dirty x then c
  else ⟨c.rp.mark x, if c.rp.bm (c.rp.blk x) = c.rp.be (c.rp.blk x) then c.rp.blk x :: c.wl else c.wl⟩

noncomputable def markAllW : List (Fin n) → Ctx n → Ctx n
  | [], c => c
  | x :: xs, c => markAllW xs (markW c x)

theorem mark_of_dirty (rp : RP n) (x : Fin n) (h : rp.Dirty x) : rp.mark x = rp := by
  unfold mark
  rw [dif_neg]
  intro hc
  unfold Dirty at h
  omega

/-- Some state of a block with a non-empty marked suffix is dirty. -/
theorem exists_dirty_of_lt {rp : RP n} (hwf : rp.WF) {b : ℕ} (hb : b < rp.nb)
    (h : rp.bm b < rp.be b) : ∃ y, rp.blk y = b ∧ rp.Dirty y := by
  have hbl := hwf.block b hb
  let y := rp.loc.symm ⟨rp.be b - 1, by omega⟩
  have hy : (rp.loc y).val = rp.be b - 1 := by simp [y]
  have hyb : rp.blk y = b := hwf.unique y b hb (by omega) (by omega)
  exact ⟨y, hyb, by unfold Dirty; rw [hyb]; omega⟩

theorem markW_inv {c : Ctx n} (h : WLInv c) (x : Fin n) : WLInv (markW c x) := by
  unfold markW
  split_ifs with hd hbm
  · exact h
  · -- the block had no dirty state: push it
    have hwf := mark_wf h.wf x
    have hbx : c.rp.blk x < c.rp.nb := (h.wf.state x).1
    refine ⟨hwf, ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hmem => ?_, h.nodup⟩
      obtain ⟨_, y, hyb, hyd⟩ := h.queued _ hmem
      unfold Dirty at hyd
      have := (h.wf.state y).2.2
      rw [hyb] at hyd this
      omega
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · refine ⟨by rw [mark_nb]; exact hbx, x, by rw [mark_blk], ?_⟩
        exact (mark_dirty h.wf x x).2 (Or.inr rfl)
      · obtain ⟨hlt, y, hyb, hyd⟩ := h.queued b hb
        exact ⟨by rw [mark_nb]; exact hlt, y, by rw [mark_blk]; exact hyb,
          (mark_dirty h.wf x y).2 (Or.inl hyd)⟩
    · intro z hz
      rw [mark_dirty h.wf x z] at hz
      rw [mark_blk]
      rcases hz with hz | rfl
      · exact List.mem_cons_of_mem _ (h.dirty z hz)
      · exact List.mem_cons_self
  · -- the block already has a dirty state
    have hwf := mark_wf h.wf x
    have hbx : c.rp.blk x < c.rp.nb := (h.wf.state x).1
    have hlt : c.rp.bm (c.rp.blk x) < c.rp.be (c.rp.blk x) := by
      have := (h.wf.block _ hbx).2.2.2; omega
    have hmem : c.rp.blk x ∈ c.wl := by
      obtain ⟨y, hyb, hyd⟩ := exists_dirty_of_lt h.wf hbx hlt
      exact hyb ▸ h.dirty y hyd
    refine ⟨hwf, h.nodup, ?_, ?_⟩
    · intro b hb
      obtain ⟨hlt, y, hyb, hyd⟩ := h.queued b hb
      exact ⟨by rw [mark_nb]; exact hlt, y, by rw [mark_blk]; exact hyb,
        (mark_dirty h.wf x y).2 (Or.inl hyd)⟩
    · intro z hz
      rw [mark_dirty h.wf x z] at hz
      rw [mark_blk]
      rcases hz with hz | rfl
      · exact h.dirty z hz
      · exact hmem

theorem markAllW_inv (l : List (Fin n)) {c : Ctx n} (h : WLInv c) : WLInv (markAllW l c) := by
  induction l generalizing c with
  | nil => exact h
  | cons x xs ih => exact ih (markW_inv h x)

theorem markW_rp (c : Ctx n) (x : Fin n) : (markW c x).rp = c.rp.mark x := by
  unfold markW
  by_cases hd : c.rp.Dirty x
  · rw [if_pos hd]; exact (mark_of_dirty _ _ hd).symm
  · rw [if_neg hd]

theorem markAllW_dirty {c : Ctx n} (h : WLInv c) (l : List (Fin n)) (z : Fin n) :
    (markAllW l c).rp.Dirty z ↔ c.rp.Dirty z ∨ z ∈ l := by
  induction l generalizing c with
  | nil => simp [markAllW]
  | cons x xs ih =>
    simp only [markAllW]
    rw [ih (markW_inv h x), markW_rp, mark_dirty h.wf x z]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (by simp [h])
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem markAllW_blk (l : List (Fin n)) (c : Ctx n) : (markAllW l c).rp.blk = c.rp.blk := by
  induction l generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [markAllW]; rw [ih, markW_rp, mark_blk]

theorem markAllW_nb (l : List (Fin n)) (c : Ctx n) : (markAllW l c).rp.nb = c.rp.nb := by
  induction l generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [markAllW]; rw [ih, markW_rp, mark_nb]

end RP

end Sigref
