import Sigref.Refinable

/-!
# Proofs: Refinable

The refinable partition: `MarkDirty` and the backwards-closure loop with its invariant.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/Refinable_Pins.lean` (human-vetted).
-/

namespace Sigref

namespace RP

variable {n : ℕ}

theorem mark_blk (rp : RP n) (s : Fin n) : (rp.mark s).blk = rp.blk := by
  unfold mark; split_ifs <;> rfl

theorem mark_nb (rp : RP n) (s : Fin n) : (rp.mark s).nb = rp.nb := by
  unfold mark; split_ifs <;> rfl

section MarkProofs

variable {rp : RP n} (hwf : rp.WF) (s : Fin n)

theorem mark_eq (hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n) :
    rp.mark s = { rp with
      loc := (Equiv.swap s (lastClean s hc)).trans rp.loc
      bm := Function.update rp.bm (rp.blk s) (rp.bm (rp.blk s) - 1) } := by
  unfold mark lastClean; rw [dif_pos hc]

theorem loc_lastClean (hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n) :
    (rp.loc (lastClean s hc)).val = rp.bm (rp.blk s) - 1 := by
  unfold lastClean; simp

theorem mark_loc (hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n) (x : Fin n) :
    ((rp.mark s).loc x) = rp.loc (Equiv.swap s (lastClean s hc) x) := by
  rw [mark_eq s hc]; rfl

include hwf

theorem mark_wf : (rp.mark s).WF := by
  by_cases hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n
  swap
  · unfold mark; rw [dif_neg hc]; exact hwf
  set s' := lastClean s hc with hs'
  have hb : rp.blk s < rp.nb := (hwf.state s).1
  have hbs := (hwf.state s).2.1
  have hbe := (hwf.state s).2.2
  have hbblk := hwf.block _ hb
  have hlast : (rp.loc s').val = rp.bm (rp.blk s) - 1 := loc_lastClean s hc
  have hlast_lt : rp.bm (rp.blk s) - 1 < rp.be (rp.blk s) := by omega
  have hlast_ge : rp.bs (rp.blk s) ≤ rp.bm (rp.blk s) - 1 := by omega
  -- the swapped state `s'` lies in the block of `s`
  have hblk' : rp.blk s' = rp.blk s := hwf.unique s' _ hb (by omega) (by omega)
  have hswap : ∀ x, rp.blk (Equiv.swap s s' x) = rp.blk x := by
    intro x
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hblk']
    · rw [h2, ← hblk']
    · rfl
  rw [mark_eq s hc]
  refine ⟨?_, ?_, ?_⟩
  · intro b' hb'
    simp only [Function.update_apply]
    by_cases h : b' = rp.blk s
    · subst h; simp; omega
    · simp [h]; exact hwf.block b' hb'
  · intro x
    have hy := hwf.state (Equiv.swap s s' x)
    rw [hswap x] at hy
    exact hy
  · intro x b' hb' h1 h2
    have := hwf.unique (Equiv.swap s s' x) b' hb' h1 h2
    rw [hswap x] at this
    exact this

/-- `MarkDirty` adds exactly the state `s` to the dirty set and leaves the partition alone. -/
theorem mark_dirty (x : Fin n) : (rp.mark s).Dirty x ↔ rp.Dirty x ∨ x = s := by
  unfold Dirty
  rw [mark_blk]
  by_cases hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n
  swap
  · have hb := hwf.block _ (hwf.state s).1
    have hbound : rp.bm (rp.blk s) - 1 < n := by have := s.pos; omega
    have hs : rp.bm (rp.blk s) ≤ (rp.loc s).val := by
      by_contra h; exact hc ⟨by omega, hbound⟩
    unfold mark; rw [dif_neg hc]
    exact ⟨Or.inl, fun h => h.elim id (fun hx => hx ▸ hs)⟩
  set s' := lastClean s hc with hs'
  have hb : rp.blk s < rp.nb := (hwf.state s).1
  have hbs := (hwf.state s).2.1
  have hbe := (hwf.state s).2.2
  have hbblk := hwf.block _ hb
  have hlast : (rp.loc s').val = rp.bm (rp.blk s) - 1 := loc_lastClean s hc
  have hblk' : rp.blk s' = rp.blk s := hwf.unique s' _ hb (by omega) (by omega)
  rw [mark_eq s hc]
  show (Function.update rp.bm (rp.blk s) (rp.bm (rp.blk s) - 1)) (rp.blk x) ≤
    (rp.loc (Equiv.swap s s' x)).val ↔ _
  by_cases hxb : rp.blk x = rp.blk s
  · rw [hxb]
    simp only [Function.update_self]
    by_cases hxs : x = s
    · subst hxs
      rw [Equiv.swap_apply_left, hlast]
      simp
    · by_cases hxs' : x = s'
      · rw [hxs', Equiv.swap_apply_right]
        have hne : s ≠ s' := fun h => hxs (hxs'.trans h.symm)
        have : (rp.loc s).val ≠ (rp.loc s').val := fun h => hne (rp.loc.injective (Fin.ext h))
        constructor
        · intro h; omega
        · intro h
          rcases h with h | h
          · omega
          · exact absurd h.symm hne
      · rw [Equiv.swap_apply_of_ne_of_ne hxs hxs']
        have : (rp.loc x).val ≠ rp.bm (rp.blk s) - 1 := fun h =>
          hxs' (rp.loc.injective (Fin.ext (h.trans hlast.symm)))
        constructor
        · intro h; exact Or.inl (by omega)
        · intro h
          rcases h with h | h
          · omega
          · exact absurd h hxs
  · have hxs : x ≠ s := fun h => hxb (h ▸ rfl)
    have hxs' : x ≠ s' := fun h => hxb (by rw [h, hblk'])
    rw [Function.update_of_ne hxb, Equiv.swap_apply_of_ne_of_ne hxs hxs']
    exact ⟨Or.inl, fun h => h.elim id (fun h => absurd h hxs)⟩

end MarkProofs

section MarkMore

variable {rp : RP n} (s : Fin n)

theorem mark_bs (rp : RP n) (s : Fin n) : (rp.mark s).bs = rp.bs := by
  unfold mark; split_ifs <;> rfl

theorem mark_be (rp : RP n) (s : Fin n) : (rp.mark s).be = rp.be := by
  unfold mark; split_ifs <;> rfl

theorem mark_bm_le (rp : RP n) (s : Fin n) (b : ℕ) : (rp.mark s).bm b ≤ rp.bm b := by
  unfold mark
  split_ifs with h
  · show Function.update rp.bm (rp.blk s) (rp.bm (rp.blk s) - 1) b ≤ rp.bm b
    by_cases hb : b = rp.blk s
    · subst hb; simp
    · simp [Function.update_of_ne hb]
  · exact le_rfl

/-- `MarkDirty` only moves states at locations below the split of their block. -/
theorem mark_loc_of_ge (rp : RP n) (s x : Fin n) (hx : rp.bm (rp.blk s) ≤ (rp.loc x).val) :
    (rp.mark s).loc x = rp.loc x := by
  by_cases hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n
  · rw [mark_loc s hc]
    have hxs : x ≠ s := fun h => by rw [h] at hx; omega
    have hxs' : x ≠ lastClean s hc := fun h => by
      have := loc_lastClean s hc
      rw [h] at hx; omega
    rw [Equiv.swap_apply_of_ne_of_ne hxs hxs']
  · unfold mark; rw [dif_neg hc]

end MarkMore

theorem markList_blk (b : ℕ) (l : List (Fin n)) (rp : RP n) : (markList b l rp).blk = rp.blk := by
  induction l generalizing rp with
  | nil => rfl
  | cons x xs ih => simp only [markList]; rw [ih]; split_ifs <;> simp [mark_blk]

theorem markList_nb (b : ℕ) (l : List (Fin n)) (rp : RP n) : (markList b l rp).nb = rp.nb := by
  induction l generalizing rp with
  | nil => rfl
  | cons x xs ih => simp only [markList]; rw [ih]; split_ifs <;> simp [mark_nb]

theorem markList_bs (b : ℕ) (l : List (Fin n)) (rp : RP n) : (markList b l rp).bs = rp.bs := by
  induction l generalizing rp with
  | nil => rfl
  | cons x xs ih => simp only [markList]; rw [ih]; split_ifs <;> simp [mark_bs]

theorem markList_be (b : ℕ) (l : List (Fin n)) (rp : RP n) : (markList b l rp).be = rp.be := by
  induction l generalizing rp with
  | nil => rfl
  | cons x xs ih => simp only [markList]; rw [ih]; split_ifs <;> simp [mark_be]

theorem markList_wf (b : ℕ) (l : List (Fin n)) (rp : RP n) (h : rp.WF) : (markList b l rp).WF := by
  induction l generalizing rp with
  | nil => exact h
  | cons x xs ih =>
    simp only [markList]
    apply ih
    split_ifs
    · exact mark_wf h x
    · exact h

theorem markList_bm_le (b : ℕ) (l : List (Fin n)) (rp : RP n) (b' : ℕ) :
    (markList b l rp).bm b' ≤ rp.bm b' := by
  induction l generalizing rp with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [markList]
    refine le_trans (ih _) ?_
    split_ifs
    · exact mark_bm_le rp x b'
    · exact le_rfl

/-- Locations at or above the split of block `b` are untouched when marking states of block `b`. -/
theorem markList_loc_of_ge (b : ℕ) (l : List (Fin n)) (rp : RP n) (x : Fin n)
    (hx : rp.bm b ≤ (rp.loc x).val) : (markList b l rp).loc x = rp.loc x := by
  induction l generalizing rp with
  | nil => rfl
  | cons y ys ih =>
    simp only [markList]
    by_cases hy : rp.blk y = b
    · rw [if_pos hy]
      have h1 : (rp.mark y).loc x = rp.loc x := mark_loc_of_ge rp y x (by rw [hy]; exact hx)
      have h2 : (rp.mark y).bm b ≤ rp.bm b := mark_bm_le rp y b
      rw [ih (rp.mark y) (by rw [h1]; omega), h1]
    · rw [if_neg hy]; exact ih rp hx

/-- Effect of `markList` on the dirty set. -/
theorem markList_dirty (hwf : rp.WF) (b : ℕ) (l : List (Fin n)) (x : Fin n) :
    (markList b l rp).Dirty x ↔ rp.Dirty x ∨ (x ∈ l ∧ rp.blk x = b) := by
  induction l generalizing rp with
  | nil => simp [markList]
  | cons y ys ih =>
    simp only [markList]
    by_cases hy : rp.blk y = b
    · rw [if_pos hy, ih (mark_wf hwf y), mark_dirty hwf y x, mark_blk]
      constructor
      · rintro ((h | h) | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨by simp [h], by rw [h]; exact hy⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 h1 with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨h, h2⟩
    · rw [if_neg hy, ih hwf]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 h1 with h | h
          · exact absurd (h ▸ h2) hy
          · exact Or.inr ⟨h, h2⟩

theorem mark_loc_lt (rp : RP n) (s x : Fin n) (M : ℕ) (hM : rp.bm (rp.blk s) ≤ M)
    (hx : (rp.loc x).val < M) : ((rp.mark s).loc x).val < M := by
  by_cases hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n
  · rw [mark_loc s hc, Equiv.swap_apply_def]
    have hl := loc_lastClean s hc
    have h1 := hc.1
    split_ifs
    · omega
    · omega
    · exact hx
  · unfold mark; rw [dif_neg hc]; exact hx

theorem markList_loc_lt (b : ℕ) (l : List (Fin n)) (rp : RP n) (x : Fin n) (M : ℕ)
    (hM : rp.bm b ≤ M) (hx : (rp.loc x).val < M) : ((markList b l rp).loc x).val < M := by
  induction l generalizing rp with
  | nil => exact hx
  | cons y ys ih =>
    simp only [markList]
    by_cases hy : rp.blk y = b
    · rw [if_pos hy]
      have h2 := mark_bm_le rp y b
      refine ih _ (le_trans h2 hM) (mark_loc_lt rp y x M (by rw [hy]; exact hM) hx)
    · rw [if_neg hy]; exact ih rp hM hx

/-! ### The backwards closure (first phase of `SortedClosure`) -/

/-- Invariant of the closure loop. -/
structure LoopInv (tau : Fin n → Fin n → Prop) (b : ℕ) (rp₀ rp : RP n) (it k : ℕ) : Prop where
  wf : rp.WF
  blk : rp.blk = rp₀.blk
  nb : rp.nb = rp₀.nb
  bs : rp.bs = rp₀.bs
  be : rp.be = rp₀.be
  mono : ∀ x, rp₀.Dirty x → rp.Dirty x
  sound : ∀ x, rp.Dirty x → (rp.blk x = b → DirtyClosure tau rp₀ b x) ∧
    (rp.blk x ≠ b → rp₀.Dirty x)
  scanned : ∀ x, rp.blk x = b → it < (rp.loc x).val → ∀ y, tau y x → rp.blk y = b → rp.Dirty y
  reach : rp.bm b ≤ it + 1
  below : it < rp.be b
  fuel : it + 1 ≤ rp.bs b + k

/-- Closedness of the dirty set within the block, the loop's postcondition. -/
def Closed (tau : Fin n → Fin n → Prop) (b : ℕ) (rp : RP n) : Prop :=
  ∀ x, rp.blk x = b → rp.Dirty x → ∀ y, tau y x → rp.blk y = b → rp.Dirty y

section ClosureProofs

variable {tau : Fin n → Fin n → Prop} {b : ℕ} {preds : Fin n → List (Fin n)}
  {rp₀ rp : RP n}

theorem LoopInv.init (hwf : rp₀.WF) (hb : b < rp₀.nb) :
    LoopInv tau b rp₀ rp₀ (rp₀.be b - 1) (rp₀.be b - rp₀.bs b) := by
  have hbl := hwf.block b hb
  refine ⟨hwf, rfl, rfl, rfl, rfl, fun x h => h, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨fun hxb => ⟨x, hxb, hx, Relation.ReflTransGen.refl⟩, fun hxb => ?_⟩
    exact hx
  · intro x hx hlt
    have := (hwf.state x).2.2
    rw [hx] at this
    omega
  · omega
  · omega
  · omega

theorem LoopInv.step (hpreds : ∀ x y, y ∈ preds x ↔ tau y x) {it k : ℕ}
    (hb : b < rp₀.nb) (inv : LoopInv tau b rp₀ rp it (k + 1))
    (h : rp.bs b < rp.bm b ∧ rp.bm b ≤ it ∧ it < n) :
    LoopInv tau b rp₀ (markList b (preds (rp.loc.symm ⟨it, h.2.2⟩)) rp) (it - 1) k := by
  set x0 := rp.loc.symm ⟨it, h.2.2⟩ with hx0
  have hbnb : b < rp.nb := inv.nb ▸ hb
  have hloc0 : (rp.loc x0).val = it := by simp [hx0]
  have hbelow := inv.below
  have hblk0 : rp.blk x0 = b :=
    inv.wf.unique x0 b hbnb (by omega) (by omega)
  have hD0 : rp.Dirty x0 := by unfold Dirty; rw [hblk0]; omega
  have hcl0 := ((inv.sound x0 hD0).1 hblk0)
  have hit1 : 1 ≤ it := by omega
  have hblk' : (markList b (preds x0) rp).blk = rp.blk := markList_blk _ _ _
  refine ⟨markList_wf _ _ _ inv.wf, hblk'.trans inv.blk,
    (markList_nb _ _ _).trans inv.nb, (markList_bs _ _ _).trans inv.bs,
    (markList_be _ _ _).trans inv.be, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (markList_dirty inv.wf b _ x).2 (Or.inl (inv.mono x hx))
  · intro y hy
    rw [markList_dirty inv.wf] at hy
    rw [hblk']
    rcases hy with hy | ⟨hy1, hy2⟩
    · exact inv.sound y hy
    · refine ⟨fun _ => ?_, fun hne => absurd hy2 hne⟩
      obtain ⟨d, hd1, hd2, hpath⟩ := hcl0
      refine ⟨d, hd1, hd2, Relation.ReflTransGen.head ⟨(hpreds x0 y).1 hy1, ?_⟩ hpath⟩
      rw [← inv.blk, hy2, hblk0]
  · intro x hx hlt y hty hyb
    rw [hblk'] at hx hyb
    have hge : rp.bm b ≤ (rp.loc x).val := by
      by_contra hlt'
      have := markList_loc_lt b (preds x0) rp x (rp.bm b) le_rfl (by omega)
      omega
    have hsame := markList_loc_of_ge b (preds x0) rp x hge
    rw [hsame] at hlt
    rcases Nat.lt_or_ge it (rp.loc x).val with hgt | hle
    · exact (markList_dirty inv.wf b _ y).2 (Or.inl (inv.scanned x hx hgt y hty hyb))
    · have heq : (rp.loc x).val = it := by omega
      have hxx : x = x0 := rp.loc.injective (Fin.ext (heq.trans hloc0.symm))
      exact (markList_dirty inv.wf b _ y).2 (Or.inr ⟨by rw [← hxx]; exact (hpreds x y).2 hty, hyb⟩)
  · have := markList_bm_le b (preds x0) rp b
    omega
  · rw [markList_be]; have := inv.below; omega
  · rw [markList_bs]; have := inv.fuel; omega

theorem closureLoop_spec (hpreds : ∀ x y, y ∈ preds x ↔ tau y x) (hb : b < rp₀.nb) :
    ∀ (k it : ℕ) (rp : RP n), LoopInv tau b rp₀ rp it k →
      ∃ it' k', LoopInv tau b rp₀ (closureLoop b preds k it rp) it' k' ∧
        Closed tau b (closureLoop b preds k it rp)
  | 0, it, rp, inv => by
    refine ⟨it, 0, by simpa [closureLoop] using inv, ?_⟩
    simp only [closureLoop]
    intro x hx _ y hty hyb
    apply inv.scanned x hx _ y hty hyb
    have := (inv.wf.state x).2.1
    rw [hx] at this
    have := inv.fuel
    omega
  | k + 1, it, rp, inv => by
    by_cases h : rp.bs b < rp.bm b ∧ rp.bm b ≤ it ∧ it < n
    · have hstep := inv.step hpreds hb h
      obtain ⟨it', k', hinv, hcl⟩ := closureLoop_spec hpreds hb k (it - 1) _ hstep
      refine ⟨it', k', ?_, ?_⟩
      · simpa [closureLoop, h] using hinv
      · simpa [closureLoop, h] using hcl
    · refine ⟨it, k + 1, by simpa [closureLoop, h] using inv, ?_⟩
      simp only [closureLoop, dif_neg h]
      intro x hx hxd y hty hyb
      have hbnb : b < rp.nb := inv.nb ▸ hb
      have hbl := inv.wf.block b hbnb
      have hitn : it < n := by have := inv.below; omega
      by_cases hlt : it < rp.bm b
      · apply inv.scanned x hx _ y hty hyb
        unfold Dirty at hxd; rw [hx] at hxd; omega
      · have hbm : rp.bm b ≤ rp.bs b := by
          by_contra hh; exact h ⟨by omega, by omega, hitn⟩
        have := (inv.wf.state y).2.1
        unfold Dirty
        rw [hyb] at this ⊢
        omega

/-- **Backwards closure** (the first phase of `SortedClosure`): the closure loop keeps the partition
and every other block, and makes the dirty states of block `b` exactly those that reach an originally
dirty state of the block by τ-steps inside the block. -/
theorem closure_spec (hpreds : ∀ x y, y ∈ preds x ↔ tau y x) (hwf : rp₀.WF) (hb : b < rp₀.nb) :
    (closure b preds rp₀).WF ∧ (closure b preds rp₀).blk = rp₀.blk ∧
    (∀ x, rp₀.blk x ≠ b → ((closure b preds rp₀).Dirty x ↔ rp₀.Dirty x)) ∧
    (∀ x, rp₀.blk x = b → ((closure b preds rp₀).Dirty x ↔ DirtyClosure tau rp₀ b x)) ∧
    (closure b preds rp₀).nb = rp₀.nb := by
  obtain ⟨it', k', hinv, hcl⟩ :=
    closureLoop_spec hpreds hb (rp₀.be b - rp₀.bs b) (rp₀.be b - 1) rp₀ (LoopInv.init hwf hb)
  change LoopInv tau b rp₀ (closure b preds rp₀) it' k' at hinv
  change Closed tau b (closure b preds rp₀) at hcl
  refine ⟨hinv.wf, hinv.blk, ?_, ?_, hinv.nb⟩
  · intro x hx
    refine ⟨fun h => (hinv.sound x h).2 (hinv.blk ▸ hx), hinv.mono x⟩
  · intro x hx
    refine ⟨fun h => (hinv.sound x h).1 (hinv.blk ▸ hx), ?_⟩
    rintro ⟨d, hd1, hd2, hpath⟩
    have key : ∀ u, Relation.ReflTransGen (fun u v => tau u v ∧ rp₀.blk u = rp₀.blk v) u d →
        rp₀.blk u = b → (closure b preds rp₀).Dirty u := by
      intro u hu
      induction hu using Relation.ReflTransGen.head_induction_on with
      | refl => intro _; exact hinv.mono d hd2
      | head hstep hrest ih =>
        rename_i u v
        intro hub
        have hvb : rp₀.blk v = b := hstep.2 ▸ hub
        have hdv := ih hvb
        refine hcl v (hinv.blk ▸ hvb) hdv u hstep.1 (hinv.blk ▸ hub)
    exact key x hpath hx
/-- Headline: `MarkDirty` correctness. -/
theorem markDirtyCorrect {n : ℕ} (rp : RP n) (s : Fin n) : MarkDirtyCorrect rp s :=
  fun hwf => ⟨mark_wf hwf s, mark_blk rp s, mark_dirty hwf s⟩

/-- Headline: backwards closure correctness. -/
theorem closureCorrect {n : ℕ} (tau : Fin n → Fin n → Prop) (b : ℕ)
    (preds : Fin n → List (Fin n)) (rp : RP n) : ClosureCorrect tau b preds rp :=
  fun hpreds hwf hb => closure_spec hpreds hwf hb


end ClosureProofs

end RP

end Sigref
