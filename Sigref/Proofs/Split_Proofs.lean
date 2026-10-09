import Sigref.Iteration
import Sigref.Proofs.Refinable_Proofs
import Sigref.Proofs.CountingSort_Proofs

/-!
# Proofs: Split

Existence of the split layout (the paper's `finish_partition_marked`): the states of a block are
regrouped by `grp` with a counting sort (`CountingSort_Proofs`), the pieces get dense block ids (one
piece keeps the old id) and every piece is unmarked.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The headline theorem is
pinned in `Sigref/Pins/Split_Pins.lean` (human-vetted).
-/

namespace Sigref

namespace RP

open Classical

section Data

variable {n : ℕ} {G : Type} (rp : RP n) (b : ℕ) (grp : Fin n → G)

/-- The states of block `b`. -/
noncomputable def blockStates : List (Fin n) :=
  (List.finRange n).filter fun x => decide (rp.blk x = b)

/-- The distinct pieces of the split, as values of `grp`. -/
noncomputable def pieces : List G := ((blockStates rp b).map grp).dedup

/-- The dense number of the piece of `x`. -/
noncomputable def rr (x : Fin n) : ℕ := (pieces rp b grp).idxOf (grp x)

/-- The number of pieces. -/
noncomputable def numPieces : ℕ := (pieces rp b grp).length

/-- Number of states of block `b`. -/
def blockSize : ℕ := rp.be b - rp.bs b

/-- Piece of the state at location `p`. -/
noncomputable def rAt (p : ℕ) : ℕ := if h : p < n then rr rp b grp (rp.loc.symm ⟨p, h⟩) else 0

/-- The class list of the counting sort: piece of the `t`-th location of the block. -/
noncomputable def clsL : List ℕ := (List.range (blockSize rp b)).map fun t => rAt rp b grp (rp.bs b + t)

/-- Piece sizes. -/
noncomputable def szsL : List ℕ := (List.range (numPieces rp b grp)).map fun j => (clsL rp b grp).count j

/-- The piece that keeps the old block id `b`: the one of the first state of the block. -/
noncomputable def keepPiece : ℕ := rAt rp b grp (rp.bs b)

/-- Block id of piece `j`: the kept piece keeps `b`, the others get fresh dense ids. -/
noncomputable def pid (j : ℕ) : ℕ :=
  if j = keepPiece rp b grp then b
  else if j < keepPiece rp b grp then rp.nb + j else rp.nb + j - 1

/-- Inverse of `pid` on the new ids. -/
noncomputable def pieceOf (i : ℕ) : ℕ :=
  if i = b then keepPiece rp b grp
  else if i - rp.nb < keepPiece rp b grp then i - rp.nb else i - rp.nb + 1

end Data

section Lemmas

variable {n : ℕ} {G : Type} {rp : RP n} {b : ℕ} {grp : Fin n → G}

theorem mem_blockStates {x : Fin n} : x ∈ blockStates rp b ↔ rp.blk x = b := by
  simp [blockStates]

theorem mem_pieces {g : G} : g ∈ pieces rp b grp ↔ ∃ x, rp.blk x = b ∧ grp x = g := by
  simp [pieces, mem_blockStates]

theorem pieces_nodup : (pieces rp b grp).Nodup := List.nodup_dedup _

theorem rr_lt {x : Fin n} (hx : rp.blk x = b) : rr rp b grp x < numPieces rp b grp := by
  unfold rr numPieces
  exact List.idxOf_lt_length_iff.2 (mem_pieces.2 ⟨x, hx, rfl⟩)

theorem rr_eq_iff {x y : Fin n} (hx : rp.blk x = b) (_hy : rp.blk y = b) :
    rr rp b grp x = rr rp b grp y ↔ grp x = grp y := by
  unfold rr
  exact List.idxOf_inj (mem_pieces.2 ⟨x, hx, rfl⟩)

theorem rr_surj {j : ℕ} (hj : j < numPieces rp b grp) : ∃ x, rp.blk x = b ∧ rr rp b grp x = j := by
  unfold numPieces at hj
  have hmem : (pieces rp b grp)[j] ∈ pieces rp b grp := List.getElem_mem hj
  obtain ⟨x, hx, hg⟩ := mem_pieces.1 hmem
  refine ⟨x, hx, ?_⟩
  unfold rr
  rw [hg]
  have h1 : (pieces rp b grp).idxOf (pieces rp b grp)[j] < (pieces rp b grp).length :=
    List.idxOf_lt_length_iff.2 hmem
  have h2 : (pieces rp b grp)[(pieces rp b grp).idxOf (pieces rp b grp)[j]] =
      (pieces rp b grp)[j] := List.getElem_idxOf h1
  exact (List.Nodup.getElem_inj_iff pieces_nodup).1 h2

section Positions

theorem blockSize_pos (hwf : rp.WF) (hb : b < rp.nb) : 0 < blockSize rp b := by
  have := hwf.block b hb; unfold blockSize; omega

theorem bs_add_blockSize (hwf : rp.WF) (hb : b < rp.nb) : rp.bs b + blockSize rp b = rp.be b := by
  have := hwf.block b hb; unfold blockSize; omega

theorem be_le_n (hwf : rp.WF) (hb : b < rp.nb) : rp.be b ≤ n := (hwf.block b hb).2.1

theorem blk_at (hwf : rp.WF) (hb : b < rp.nb) {p : ℕ} (h1 : rp.bs b ≤ p) (h2 : p < rp.be b) (hpn : p < n) :
    rp.blk (rp.loc.symm ⟨p, hpn⟩) = b :=
  hwf.unique _ b hb (by simpa using h1) (by simpa using h2)

theorem loc_mem (hwf : rp.WF) (_hb : b < rp.nb) {x : Fin n} (hx : rp.blk x = b) :
    rp.bs b ≤ (rp.loc x).val ∧ (rp.loc x).val < rp.be b := by
  have := hwf.state x; rw [hx] at this; exact this.2

theorem rAt_loc {x : Fin n} : rAt rp b grp (rp.loc x).val = rr rp b grp x := by
  unfold rAt
  rw [dif_pos (rp.loc x).isLt]
  simp

theorem clsL_length : (clsL rp b grp).length = blockSize rp b := by simp [clsL]

theorem clsL_getElem {t : ℕ} (ht : t < (clsL rp b grp).length) :
    (clsL rp b grp)[t] = rAt rp b grp (rp.bs b + t) := by simp [clsL]

theorem clsL_lt (hwf : rp.WF) (hb : b < rp.nb) : ∀ c ∈ clsL rp b grp, c < numPieces rp b grp := by
  intro c hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
  have ht' : t < blockSize rp b := List.mem_range.1 ht
  have h1 := bs_add_blockSize hwf hb
  have h2 := be_le_n hwf hb
  have hpn : rp.bs b + t < n := by omega
  unfold rAt
  rw [dif_pos hpn]
  exact rr_lt (blk_at hwf hb (by omega) (by omega) hpn)

theorem keepPiece_lt (hwf : rp.WF) (hb : b < rp.nb) : keepPiece rp b grp < numPieces rp b grp := by
  have h := bs_add_blockSize hwf hb
  have h2 := be_le_n hwf hb
  have h3 := blockSize_pos hwf hb
  unfold keepPiece
  have hpn : rp.bs b < n := by omega
  unfold rAt
  rw [dif_pos hpn]
  exact rr_lt (blk_at hwf hb le_rfl (by omega) hpn)

theorem numPieces_pos (hwf : rp.WF) (hb : b < rp.nb) : 0 < numPieces rp b grp :=
  lt_of_le_of_lt (Nat.zero_le _) (keepPiece_lt hwf hb)

theorem clsL_getElem_state (hwf : rp.WF) (hb : b < rp.nb) {x : Fin n} (hx : rp.blk x = b)
    (ht : (rp.loc x).val - rp.bs b < (clsL rp b grp).length) :
    (clsL rp b grp)[(rp.loc x).val - rp.bs b] = rr rp b grp x := by
  rw [clsL_getElem ht]
  have := loc_mem hwf hb hx
  have e : rp.bs b + ((rp.loc x).val - rp.bs b) = (rp.loc x).val := by omega
  rw [e, rAt_loc]

theorem szs_length : (szsL rp b grp).length = numPieces rp b grp := by simp [szsL]

theorem szs_count {j : ℕ} (hj : j < numPieces rp b grp) :
    (szsL rp b grp).getD j 0 = (clsL rp b grp).count j := by
  simp [szsL, hj]

theorem count_pos (hwf : rp.WF) (hb : b < rp.nb) {j : ℕ} (hj : j < numPieces rp b grp) : 0 < (clsL rp b grp).count j := by
  obtain ⟨x, hx, hxj⟩ := rr_surj hj (rp := rp) (b := b) (grp := grp)
  have hl := loc_mem hwf hb hx
  have hlen : (rp.loc x).val - rp.bs b < (clsL rp b grp).length := by
    rw [clsL_length]; unfold blockSize; omega
  have := clsL_getElem_state hwf hb hx hlen (grp := grp)
  rw [hxj] at this
  exact List.count_pos_iff.2 (this ▸ List.getElem_mem hlen)

/-- New location (before the cast to `Fin`) of a state of the block. -/
noncomputable def Pfun (rp : RP n) (b : ℕ) (grp : Fin n → G) (x : Fin n) : ℕ :=
  posOf (rp.bs b) (szsL rp b grp) (clsL rp b grp) ((rp.loc x).val - rp.bs b)

theorem Pfun_bounds (hwf : rp.WF) (hb : b < rp.nb) {x : Fin n} (hx : rp.blk x = b) :
    cumS (rp.bs b) (szsL rp b grp) (rr rp b grp x) ≤ Pfun rp b grp x ∧
      Pfun rp b grp x < cumS (rp.bs b) (szsL rp b grp) (rr rp b grp x + 1) := by
  have hl := loc_mem hwf hb hx
  have hlen : (rp.loc x).val - rp.bs b < (clsL rp b grp).length := by
    rw [clsL_length]; unfold blockSize; omega
  have := posOf_bounds (rp.bs b) (szsL rp b grp) (clsL rp b grp) (numPieces rp b grp)
    (szs_length) (fun j hj => szs_count hj) (clsL_lt hwf hb) _ hlen
  have e := clsL_getElem_state hwf hb hx hlen (grp := grp)
  rw [e] at this
  exact this

theorem Pfun_inj (hwf : rp.WF) (hb : b < rp.nb) {x y : Fin n} (hx : rp.blk x = b)
    (hy : rp.blk y = b) (h : Pfun rp b grp x = Pfun rp b grp y) : x = y := by
  have hlx := loc_mem hwf hb hx
  have hly := loc_mem hwf hb hy
  have hlenx : (rp.loc x).val - rp.bs b < (clsL rp b grp).length := by
    rw [clsL_length]; unfold blockSize; omega
  have hleny : (rp.loc y).val - rp.bs b < (clsL rp b grp).length := by
    rw [clsL_length]; unfold blockSize; omega
  have := posOf_inj (rp.bs b) (szsL rp b grp) (clsL rp b grp) (numPieces rp b grp)
    (szs_length) (fun j hj => szs_count hj) (clsL_lt hwf hb) hlenx hleny h
  exact rp.loc.injective (Fin.ext (by omega))

theorem cumS_end_le (hwf : rp.WF) (hb : b < rp.nb) (j : ℕ) :
    cumS (rp.bs b) (szsL rp b grp) j ≤ rp.be b := by
  have := cumS_le_end (rp.bs b) (szsL rp b grp) (clsL rp b grp) (numPieces rp b grp)
    (szs_length) (fun j hj => szs_count hj) (clsL_lt hwf hb) j
  rw [clsL_length] at this
  have h2 := bs_add_blockSize hwf hb
  omega

theorem cumS_lt_succ (hwf : rp.WF) (hb : b < rp.nb) {j : ℕ} (hj : j < numPieces rp b grp) :
    cumS (rp.bs b) (szsL rp b grp) j < cumS (rp.bs b) (szsL rp b grp) (j + 1) := by
  have hlen : j < (szsL rp b grp).length := by rw [szs_length]; exact hj
  rw [cumS_succ _ _ _ hlen]
  have h1 := count_pos hwf hb hj (grp := grp)
  have h2 := szs_count hj (rp := rp) (b := b) (grp := grp)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] at h2
  simp only [Option.getD_some] at h2
  omega

theorem Pfun_lt_n (hwf : rp.WF) (hb : b < rp.nb) {x : Fin n} (hx : rp.blk x = b) :
    Pfun rp b grp x < rp.be b ∧ rp.bs b ≤ Pfun rp b grp x := by
  have h := Pfun_bounds hwf hb hx (grp := grp)
  have h2 := cumS_end_le hwf hb (rr rp b grp x + 1) (grp := grp)
  have h3 := cumS_ge (rp.bs b) (szsL rp b grp) (rr rp b grp x)
  omega

theorem range_unique (_hwf : rp.WF) (_hb : b < rp.nb) {j j' p : ℕ}
    (_hj : j < numPieces rp b grp) (_hj' : j' < numPieces rp b grp)
    (h1 : cumS (rp.bs b) (szsL rp b grp) j ≤ p) (h2 : p < cumS (rp.bs b) (szsL rp b grp) (j + 1))
    (h3 : cumS (rp.bs b) (szsL rp b grp) j' ≤ p) (h4 : p < cumS (rp.bs b) (szsL rp b grp) (j' + 1)) :
    j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · have := cumS_mono (rp.bs b) (szsL rp b grp) (show j + 1 ≤ j' by omega)
    omega
  · exact h
  · have := cumS_mono (rp.bs b) (szsL rp b grp) (show j' + 1 ≤ j by omega)
    omega

/-- The new location function, as a function to `Fin n`. -/
noncomputable def locFun (hwf : rp.WF) (hb : b < rp.nb) (grp : Fin n → G) (x : Fin n) : Fin n :=
  if h : rp.blk x = b then
    ⟨Pfun rp b grp x, lt_of_lt_of_le (Pfun_lt_n hwf hb h).1 (be_le_n hwf hb)⟩
  else rp.loc x

theorem locFun_inj (hwf : rp.WF) (hb : b < rp.nb) : Function.Injective (locFun hwf hb grp) := by
  intro x y hxy
  unfold locFun at hxy
  by_cases hx : rp.blk x = b <;> by_cases hy : rp.blk y = b
  · rw [dif_pos hx, dif_pos hy] at hxy
    exact Pfun_inj hwf hb hx hy (congrArg Fin.val hxy)
  · rw [dif_pos hx, dif_neg hy] at hxy
    exfalso
    have hP := Pfun_lt_n hwf hb hx (grp := grp)
    have := hwf.unique y b hb (by rw [← hxy]; exact hP.2) (by rw [← hxy]; exact hP.1)
    exact hy this
  · rw [dif_neg hx, dif_pos hy] at hxy
    exfalso
    have hP := Pfun_lt_n hwf hb hy (grp := grp)
    have := hwf.unique x b hb (by rw [hxy]; exact hP.2) (by rw [hxy]; exact hP.1)
    exact hx this
  · rw [dif_neg hx, dif_neg hy] at hxy
    exact rp.loc.injective hxy

/-- The new location permutation. -/
noncomputable def newLoc (hwf : rp.WF) (hb : b < rp.nb) (grp : Fin n → G) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (locFun hwf hb grp) (Finite.injective_iff_bijective.1 (locFun_inj hwf hb))

theorem newLoc_apply (hwf : rp.WF) (hb : b < rp.nb) (x : Fin n) :
    newLoc hwf hb grp x = locFun hwf hb grp x := rfl

theorem locFun_val_in (hwf : rp.WF) (hb : b < rp.nb) {x : Fin n} (hx : rp.blk x = b) :
    (locFun hwf hb grp x).val = Pfun rp b grp x := by
  unfold locFun; rw [dif_pos hx]

theorem locFun_val_out (hwf : rp.WF) (hb : b < rp.nb) {x : Fin n} (hx : ¬ rp.blk x = b) :
    locFun hwf hb grp x = rp.loc x := by
  unfold locFun; rw [dif_neg hx]

end Positions

section Ids

variable (hwf : rp.WF) (hb : b < rp.nb)
include hwf hb

set_option linter.unusedSectionVars false in
theorem pid_cases {j : ℕ} : pid rp b grp j = b ∨ rp.nb ≤ pid rp b grp j := by
  unfold pid; split_ifs <;> omega

theorem pid_lt {j : ℕ} (hj : j < numPieces rp b grp) :
    pid rp b grp j < rp.nb + numPieces rp b grp - 1 := by
  have := keepPiece_lt hwf hb (grp := grp)
  unfold pid; split_ifs <;> omega

theorem pieceOf_pid {j : ℕ} (_hj : j < numPieces rp b grp) : pieceOf rp b grp (pid rp b grp j) = j := by
  have := keepPiece_lt hwf hb (grp := grp)
  unfold pid pieceOf; split_ifs <;> omega

theorem pid_pieceOf {i : ℕ} (hi : i = b ∨ rp.nb ≤ i) (hi2 : i < rp.nb + numPieces rp b grp - 1) :
    pid rp b grp (pieceOf rp b grp i) = i := by
  have := keepPiece_lt hwf hb (grp := grp)
  unfold pid pieceOf; split_ifs <;> omega

theorem pieceOf_lt {i : ℕ} (hi : i = b ∨ rp.nb ≤ i) (hi2 : i < rp.nb + numPieces rp b grp - 1) :
    pieceOf rp b grp i < numPieces rp b grp := by
  have := keepPiece_lt hwf hb (grp := grp)
  unfold pieceOf; split_ifs <;> omega

end Ids

/-- The split partition. -/
noncomputable def newRP (hwf : rp.WF) (hb : b < rp.nb) (grp : Fin n → G) : RP n where
  loc := newLoc hwf hb grp
  blk := fun x => if rp.blk x = b then pid rp b grp (rr rp b grp x) else rp.blk x
  nb := rp.nb + numPieces rp b grp - 1
  bs := fun i => if i = b ∨ rp.nb ≤ i then
    cumS (rp.bs b) (szsL rp b grp) (pieceOf rp b grp i) else rp.bs i
  bm := fun i => if i = b ∨ rp.nb ≤ i then
    cumS (rp.bs b) (szsL rp b grp) (pieceOf rp b grp i + 1) else rp.bm i
  be := fun i => if i = b ∨ rp.nb ≤ i then
    cumS (rp.bs b) (szsL rp b grp) (pieceOf rp b grp i + 1) else rp.be i

section NewFacts

variable (hwf : rp.WF) (hb : b < rp.nb) (grp : Fin n → G)

theorem newRP_blk_in {x : Fin n} (hx : rp.blk x = b) :
    (newRP hwf hb grp).blk x = pid rp b grp (rr rp b grp x) := by simp [newRP, hx]

theorem newRP_blk_out {x : Fin n} (hx : ¬ rp.blk x = b) :
    (newRP hwf hb grp).blk x = rp.blk x := by simp [newRP, hx]

theorem newRP_loc_in {x : Fin n} (hx : rp.blk x = b) :
    ((newRP hwf hb grp).loc x).val = Pfun rp b grp x := locFun_val_in hwf hb hx

theorem newRP_loc_out {x : Fin n} (hx : ¬ rp.blk x = b) :
    (newRP hwf hb grp).loc x = rp.loc x := locFun_val_out hwf hb hx

theorem newRP_tab_new {i : ℕ} (hi : i = b ∨ rp.nb ≤ i) :
    (newRP hwf hb grp).bs i = cumS (rp.bs b) (szsL rp b grp) (pieceOf rp b grp i) ∧
    (newRP hwf hb grp).be i = cumS (rp.bs b) (szsL rp b grp) (pieceOf rp b grp i + 1) ∧
    (newRP hwf hb grp).bm i = cumS (rp.bs b) (szsL rp b grp) (pieceOf rp b grp i + 1) := by
  simp [newRP, hi]

theorem newRP_tab_old {i : ℕ} (hi : ¬ (i = b ∨ rp.nb ≤ i)) :
    (newRP hwf hb grp).bs i = rp.bs i ∧ (newRP hwf hb grp).be i = rp.be i ∧
    (newRP hwf hb grp).bm i = rp.bm i := by
  simp [newRP, hi]

theorem newRP_nb : (newRP hwf hb grp).nb = rp.nb + numPieces rp b grp - 1 := rfl

theorem newRP_wf : (newRP hwf hb grp).WF := by
  have hK := keepPiece_lt hwf hb (grp := grp)
  have hn := numPieces_pos hwf hb (grp := grp)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [newRP_nb] at hi
    by_cases h : i = b ∨ rp.nb ≤ i
    · obtain ⟨h1, h2, h3⟩ := newRP_tab_new hwf hb grp h
      have hlt := pieceOf_lt hwf hb h hi (grp := grp)
      have h4 := cumS_lt_succ hwf hb hlt
      have h5 := cumS_end_le hwf hb (pieceOf rp b grp i + 1) (grp := grp)
      have h6 := be_le_n hwf hb
      rw [h1, h2, h3]
      exact ⟨h4, by omega, by omega, le_rfl⟩
    · obtain ⟨h1, h2, h3⟩ := newRP_tab_old hwf hb grp h
      have hib : i < rp.nb := by omega
      rw [h1, h2, h3]
      exact hwf.block i hib
  · intro x
    by_cases hx : rp.blk x = b
    · rw [newRP_blk_in hwf hb grp hx, newRP_loc_in hwf hb grp hx]
      have hlt := rr_lt hx (rp := rp) (b := b) (grp := grp)
      have hp := pid_lt hwf hb hlt
      obtain ⟨h1, h2, h3⟩ := newRP_tab_new hwf hb grp (pid_cases hwf hb (j := rr rp b grp x))
      rw [pieceOf_pid hwf hb hlt] at h1 h2
      have hbd := Pfun_bounds hwf hb hx (grp := grp)
      rw [newRP_nb]
      exact ⟨hp, by rw [h1]; exact hbd.1, by rw [h2]; exact hbd.2⟩
    · rw [newRP_blk_out hwf hb grp hx, newRP_loc_out hwf hb grp hx, newRP_nb]
      have hs := hwf.state x
      have hne : ¬ (rp.blk x = b ∨ rp.nb ≤ rp.blk x) := by
        push Not; exact ⟨hx, hs.1⟩
      obtain ⟨h1, h2, h3⟩ := newRP_tab_old hwf hb grp hne
      rw [h1, h2]
      exact ⟨by omega, hs.2.1, hs.2.2⟩
  · intro x i hi h1 h2
    rw [newRP_nb] at hi
    by_cases h : i = b ∨ rp.nb ≤ i
    · obtain ⟨t1, t2, t3⟩ := newRP_tab_new hwf hb grp h
      have hlt := pieceOf_lt hwf hb h hi (grp := grp)
      rw [t1] at h1; rw [t2] at h2
      by_cases hx : rp.blk x = b
      · rw [newRP_loc_in hwf hb grp hx] at h1 h2
        have hbd := Pfun_bounds hwf hb hx (grp := grp)
        have heq := range_unique hwf hb (rr_lt hx) hlt hbd.1 hbd.2 h1 h2 (grp := grp)
        rw [newRP_blk_in hwf hb grp hx, heq]
        exact pid_pieceOf hwf hb h hi
      · exfalso
        rw [newRP_loc_out hwf hb grp hx] at h1 h2
        have h3 := cumS_ge (rp.bs b) (szsL rp b grp) (pieceOf rp b grp i)
        have h4 := cumS_end_le hwf hb (pieceOf rp b grp i + 1) (grp := grp)
        exact hx (hwf.unique x b hb (by omega) (by omega))
    · obtain ⟨t1, t2, t3⟩ := newRP_tab_old hwf hb grp h
      rw [t1] at h1; rw [t2] at h2
      have hib : i < rp.nb := by omega
      have hne : i ≠ b := fun e => h (Or.inl e)
      by_cases hx : rp.blk x = b
      · exfalso
        rw [newRP_loc_in hwf hb grp hx] at h1 h2
        have hP := Pfun_lt_n hwf hb hx (grp := grp)
        have hn' : Pfun rp b grp x < n := lt_of_lt_of_le hP.1 (be_le_n hwf hb)
        have e1 := blk_at hwf hb hP.2 hP.1 hn'
        have e2 := hwf.unique (rp.loc.symm ⟨Pfun rp b grp x, hn'⟩) i hib (by simpa using h1)
          (by simpa using h2)
        exact hne (e2.symm.trans e1)
      · rw [newRP_blk_out hwf hb grp hx]
        rw [newRP_loc_out hwf hb grp hx] at h1 h2
        exact hwf.unique x i hib h1 h2

theorem newRP_isSplit : IsSplit rp (newRP hwf hb grp) b grp := by
  have hn := numPieces_pos hwf hb (grp := grp)
  refine ⟨newRP_wf hwf hb grp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [newRP_nb]; omega
  · intro x hx
    have hs := hwf.state x
    have hne : ¬ (rp.blk x = b ∨ rp.nb ≤ rp.blk x) := by push Not; exact ⟨hx, hs.1⟩
    obtain ⟨h1, h2, h3⟩ := newRP_tab_old hwf hb grp hne
    refine ⟨newRP_blk_out hwf hb grp hx, ?_⟩
    unfold Dirty
    rw [newRP_blk_out hwf hb grp hx, newRP_loc_out hwf hb grp hx, h3]
  · intro x y
    have hx' := fun (hx : ¬ rp.blk x = b) => (hwf.state x).1
    by_cases hx : rp.blk x = b <;> by_cases hy : rp.blk y = b
    · rw [newRP_blk_in hwf hb grp hx, newRP_blk_in hwf hb grp hy]
      have hlx := rr_lt hx (rp := rp) (b := b) (grp := grp)
      have hly := rr_lt hy (rp := rp) (b := b) (grp := grp)
      constructor
      · intro h
        have := congrArg (pieceOf rp b grp) h
        rw [pieceOf_pid hwf hb hlx, pieceOf_pid hwf hb hly] at this
        exact ⟨by rw [hx, hy], Or.inr ((rr_eq_iff hx hy).1 this)⟩
      · rintro ⟨_, h⟩
        rcases h with h | h
        · exact absurd hx h
        · rw [(rr_eq_iff hx hy).2 h]
    · rw [newRP_blk_in hwf hb grp hx, newRP_blk_out hwf hb grp hy]
      have hy1 := (hwf.state y).1
      have hc := pid_cases hwf hb (j := rr rp b grp x) (grp := grp)
      constructor
      · intro h; omega
      · rintro ⟨h, _⟩; exact absurd (hx.symm.trans h).symm hy
    · rw [newRP_blk_out hwf hb grp hx, newRP_blk_in hwf hb grp hy]
      have hx1 := (hwf.state x).1
      have hc := pid_cases hwf hb (j := rr rp b grp y) (grp := grp)
      constructor
      · intro h; omega
      · rintro ⟨h, _⟩; exact absurd (h.trans hy) hx
    · rw [newRP_blk_out hwf hb grp hx, newRP_blk_out hwf hb grp hy]
      exact ⟨fun h => ⟨h, Or.inl hx⟩, fun h => h.1⟩
  · intro x hx
    unfold Dirty
    rw [newRP_blk_in hwf hb grp hx, newRP_loc_in hwf hb grp hx]
    have hlt := rr_lt hx (rp := rp) (b := b) (grp := grp)
    obtain ⟨h1, h2, h3⟩ := newRP_tab_new hwf hb grp (pid_cases hwf hb (j := rr rp b grp x))
    rw [pieceOf_pid hwf hb hlt] at h3
    rw [h3]
    have := (Pfun_bounds hwf hb hx (grp := grp)).2
    omega
  · intro x hx
    rw [newRP_blk_in hwf hb grp hx]
    rcases pid_cases hwf hb (j := rr rp b grp x) (grp := grp) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have h1 := bs_add_blockSize hwf hb
    have h2 := be_le_n hwf hb
    have h3 := blockSize_pos hwf hb
    have hpn : rp.bs b < n := by omega
    refine ⟨rp.loc.symm ⟨rp.bs b, hpn⟩, blk_at hwf hb le_rfl (by omega) hpn, ?_⟩
    rw [newRP_blk_in hwf hb grp (blk_at hwf hb le_rfl (by omega) hpn)]
    have : rr rp b grp (rp.loc.symm ⟨rp.bs b, hpn⟩) = keepPiece rp b grp := by
      unfold keepPiece rAt; rw [dif_pos hpn]
    rw [this]
    unfold pid; simp

end NewFacts

/-- Headline: the split layout exists. -/
theorem splitExists {n : ℕ} {G : Type} (rp : RP n) (b : ℕ) (grp : Fin n → G) :
    SplitExists rp b grp :=
  fun hwf hb => ⟨newRP hwf hb grp, newRP_isSplit hwf hb grp⟩

end Lemmas

end RP

end Sigref
