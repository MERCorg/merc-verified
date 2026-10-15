module

public import MercLib.TwoSided.TwoSidedCostCorrect
public import MercLib.TwoSided.Proofs.TwoSidedCost_Proofs
public import MercLib.TwoSided.Proofs.TwoSidedLifting_Proofs
public import Mathlib.Data.List.GetD

@[expose] public section TwoSidedCostCorrectOrderProofs

namespace MercLib.ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Order facts for the correctness proof of `ParityGame.TwoSidedCost.solve`: the program's value
comparison (`lexCmp`, `cmpVal`) is a total preorder, and on lists of length `≥ k` it agrees with
the library's truncated lexicographic order `LexLE (2 k)` on the interleaved tuples `tup`. -/

variable {n : ℕ}

/-! ### Pair comparison -/

/-- The comparison of pairs used by `lexCmp`. -/
def pcmp (x y : ℕ × ℕ) : Ordering := (compare x.1 y.1).then (compare x.2 y.2)

theorem pcmp_eq (x y : ℕ × ℕ) : pcmp x y = if x.1 < y.1 then .lt else if y.1 < x.1 then .gt else
    if x.2 < y.2 then .lt else if y.2 < x.2 then .gt else .eq := by
  unfold pcmp
  simp only [compare, compareOfLessAndEq]
  split_ifs <;> first | rfl | omega

theorem pcmp_swap (x y : ℕ × ℕ) : pcmp y x = (pcmp x y).swap := by
  rw [pcmp_eq, pcmp_eq]
  split_ifs <;> first | rfl | omega

theorem pcmp_eq_eq (x y : ℕ × ℕ) : pcmp x y = .eq ↔ x = y := by
  rw [pcmp_eq]
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all <;> omega

theorem pcmp_lt (x y : ℕ × ℕ) : pcmp x y = .lt ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) := by
  rw [pcmp_eq]
  split_ifs <;> simp_all <;> omega

theorem pcmp_gt (x y : ℕ × ℕ) : pcmp x y = .gt ↔ y.1 < x.1 ∨ (x.1 = y.1 ∧ y.2 < x.2) := by
  rw [pcmp_eq]
  split_ifs <;> simp_all <;> omega

theorem lexCmp_ret_zero (a b : List (ℕ × ℕ)) : (lexCmp 0 a b).ret = .eq := by
  simp [lexCmp]

theorem lexCmp_ret_nil_nil (k : ℕ) : (lexCmp (k + 1) [] []).ret = .eq := by
  simp [lexCmp]

theorem lexCmp_ret_nil_cons (k : ℕ) (y : ℕ × ℕ) (ys : List (ℕ × ℕ)) :
    (lexCmp (k + 1) [] (y :: ys)).ret = .lt := by
  simp [lexCmp]

theorem lexCmp_ret_cons_nil (k : ℕ) (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    (lexCmp (k + 1) (x :: xs) []).ret = .gt := by
  simp [lexCmp]

theorem lexCmp_ret_cons (k : ℕ) (x y : ℕ × ℕ) (xs ys : List (ℕ × ℕ)) :
    (lexCmp (k + 1) (x :: xs) (y :: ys)).ret =
      if pcmp x y = .eq then (lexCmp k xs ys).ret else pcmp x y := by
  simp only [lexCmp, ret_bind]
  unfold pcmp
  split <;> simp_all

theorem lexCmp_swap : ∀ (k : ℕ) (a b : List (ℕ × ℕ)),
    (lexCmp k b a).ret = (lexCmp k a b).ret.swap
  | 0, a, b => by simp [lexCmp_ret_zero]
  | k + 1, [], [] => by simp [lexCmp_ret_nil_nil]
  | k + 1, [], _ :: _ => by simp [lexCmp_ret_nil_cons, lexCmp_ret_cons_nil]
  | k + 1, _ :: _, [] => by simp [lexCmp_ret_nil_cons, lexCmp_ret_cons_nil]
  | k + 1, x :: xs, y :: ys => by
    rw [lexCmp_ret_cons, lexCmp_ret_cons, lexCmp_swap k xs ys, pcmp_swap x y]
    cases h : pcmp x y <;> simp [Ordering.swap]

theorem lexCmp_trans : ∀ (k : ℕ) (a b c : List (ℕ × ℕ)), (lexCmp k a b).ret ≠ .gt →
    (lexCmp k b c).ret ≠ .gt → (lexCmp k a c).ret ≠ .gt
  | 0, a, b, c, _, _ => by simp [lexCmp_ret_zero]
  | k + 1, [], b, [], _, _ => by simp [lexCmp_ret_nil_nil]
  | k + 1, [], b, _ :: _, _, _ => by simp [lexCmp_ret_nil_cons]
  | k + 1, _ :: _, [], c, h, _ => by simp [lexCmp_ret_cons_nil] at h
  | k + 1, _ :: _, _ :: _, [], _, h => by simp [lexCmp_ret_cons_nil] at h
  | k + 1, x :: xs, y :: ys, z :: zs, h1, h2 => by
    rw [lexCmp_ret_cons] at h1 h2 ⊢
    by_cases hxy : pcmp x y = .eq
    · obtain rfl := (pcmp_eq_eq x y).1 hxy
      rw [ite_eq_left hxy] at h1
      by_cases hyz : pcmp x z = .eq
      · rw [ite_eq_left hyz] at h2 ⊢
        exact lexCmp_trans k xs ys zs h1 h2
      · rw [ite_eq_right hyz] at h2 ⊢
        exact h2
    · rw [ite_eq_right hxy] at h1
      by_cases hyz : pcmp y z = .eq
      · rw [← (pcmp_eq_eq y z).1 hyz, ite_eq_right hxy]
        exact h1
      · rw [ite_eq_right hyz] at h2
        have h1' : pcmp x y = .lt := by cases h : pcmp x y <;> simp_all
        have h2' : pcmp y z = .lt := by cases h : pcmp y z <;> simp_all
        rw [pcmp_lt] at h1' h2'
        have h3 : pcmp x z = .lt := by rw [pcmp_lt]; omega
        rw [h3]
        simp

/-! ### Values -/

theorem cmpVal_swap (c : Ctx n) (a b : Val) : (cmpVal c b a).ret = (cmpVal c a b).ret.swap := by
  cases a <;> cases b
  · rfl
  · rfl
  · rfl
  · exact lexCmp_swap _ _ _

/-- The program's order on values (`none` = ⊤): `a ≤ b` iff the comparison is not `.gt`. -/
def VLe (c : Ctx n) (a b : Val) : Prop := (cmpVal c a b).ret ≠ .gt

theorem VLe.refl (c : Ctx n) (a : Val) : VLe c a a := by
  have := cmpVal_swap c a a
  unfold VLe
  intro h
  rw [h] at this
  simp [Ordering.swap] at this

theorem VLe.trans {c : Ctx n} {a b d : Val} (h1 : VLe c a b) (h2 : VLe c b d) : VLe c a d := by
  unfold VLe at *
  cases a <;> cases b <;> cases d <;> simp_all [cmpVal]
  exact lexCmp_trans _ _ _ _ h1 h2

theorem VLe.total (c : Ctx n) (a b : Val) : VLe c a b ∨ VLe c b a := by
  unfold VLe
  rw [cmpVal_swap c a b]
  cases (cmpVal c a b).ret <;> simp [Ordering.swap]

theorem cmpVal_lt_iff (c : Ctx n) (a b : Val) : (cmpVal c a b).ret = .lt ↔ ¬ VLe c b a := by
  unfold VLe
  rw [cmpVal_swap c a b]
  cases (cmpVal c a b).ret <;> simp [Ordering.swap]

theorem cmpVal_gt_iff (c : Ctx n) (a b : Val) : (cmpVal c a b).ret = .gt ↔ ¬ VLe c a b := by
  unfold VLe
  simp

theorem VLe.top (c : Ctx n) (a : Val) : VLe c a none := by
  cases a <;> simp [VLe, cmpVal]

theorem VLe.top_iff (c : Ctx n) (b : Val) : VLe c none b ↔ b = none := by
  cases b <;> simp [VLe, cmpVal]

theorem VLe.trans_lt {c : Ctx n} {a b d : Val} (h1 : VLe c a b) (h2 : ¬ VLe c d b) :
    ¬ VLe c d a := fun h => h2 (h.trans h1)

/-! ### Truncated lexicographic order on tuples -/

theorem lexLE_iff {m : ℕ} {f g : ℕ → ℕ} :
    LexLE m f g ↔ ∀ i < m, (∀ j < i, f j = g j) → f i ≤ g i := by
  constructor
  · rintro (h | ⟨i₀, hi₀, hpre, hlt⟩) i hi hpre'
    · exact (h i hi).le
    · rcases Nat.lt_trichotomy i i₀ with h | rfl | h
      · exact (hpre i h).le
      · exact hlt.le
      · exact absurd (hpre' i₀ h) hlt.ne
  · intro h
    by_cases hall : ∀ i < m, f i = g i
    · exact Or.inl hall
    · push Not at hall
      have hex : ∃ i, i < m ∧ f i ≠ g i := hall
      classical
      let i₀ := Nat.find hex
      have hi₀ : i₀ < m ∧ f i₀ ≠ g i₀ := Nat.find_spec hex
      have hpre : ∀ j < i₀, f j = g j := fun j hj => by
        by_contra hne
        exact Nat.find_min hex hj ⟨by omega, hne⟩
      exact Or.inr ⟨i₀, hi₀.1, hpre, lt_of_le_of_ne (h i₀ hi₀.1 hpre) hi₀.2⟩

theorem lexLE_total (m : ℕ) (f g : ℕ → ℕ) : LexLE m f g ∨ LexLE m g f := by
  by_cases hall : ∀ i < m, f i = g i
  · exact Or.inl (Or.inl hall)
  · push Not at hall
    have hex : ∃ i, i < m ∧ f i ≠ g i := hall
    classical
    let i₀ := Nat.find hex
    have hi₀ : i₀ < m ∧ f i₀ ≠ g i₀ := Nat.find_spec hex
    have hpre : ∀ j < i₀, f j = g j := fun j hj => by
      by_contra hne
      exact Nat.find_min hex hj ⟨by omega, hne⟩
    rcases Nat.lt_or_gt_of_ne hi₀.2 with h | h
    · exact Or.inl (Or.inr ⟨i₀, hi₀.1, hpre, h⟩)
    · exact Or.inr (Or.inr ⟨i₀, hi₀.1, fun j hj => (hpre j hj).symm, h⟩)

theorem lexLE_congr {m : ℕ} {f g f' g' : ℕ → ℕ} (hf : ∀ i < m, f i = f' i)
    (hg : ∀ i < m, g i = g' i) : LexLE m f g ↔ LexLE m f' g' := by
  rw [lexLE_iff, lexLE_iff]
  constructor
  · intro h i hi hpre
    rw [← hf i hi, ← hg i hi]
    exact h i hi fun j hj => by rw [hf j (by omega), hg j (by omega)]; exact hpre j hj
  · intro h i hi hpre
    rw [hf i hi, hg i hi]
    exact h i hi fun j hj => by rw [← hf j (by omega), ← hg j (by omega)]; exact hpre j hj

/-- A tuple below another at depth `m` that vanishes from `m` on is below it at every depth. -/
theorem lexLE_of_zero_tail {m : ℕ} {f g : ℕ → ℕ} (h : LexLE m f g) (hz : ∀ i, m ≤ i → f i = 0) :
    ∀ m', LexLE m' f g := by
  intro m'
  rw [lexLE_iff] at h ⊢
  intro i hi hpre
  by_cases him : i < m
  · exact h i him hpre
  · rw [hz i (by omega)]; exact Nat.zero_le _

theorem lexLE_zero_left (m : ℕ) (g : ℕ → ℕ) : LexLE m (fun _ => 0) g :=
  LexLE.of_le fun _ _ => Nat.zero_le _

/-! ### Interleaved tuples of lists -/

theorem tup_even (x : List (ℕ × ℕ)) (l : ℕ) : tup x (2 * l) = (x.getD l (0, 0)).1 := by
  unfold tup
  rw [ite_eq_left (by omega), show 2 * l / 2 = l by omega]

theorem tup_odd (x : List (ℕ × ℕ)) (l : ℕ) : tup x (2 * l + 1) = (x.getD l (0, 0)).2 := by
  unfold tup
  rw [ite_eq_right (by omega), show (2 * l + 1) / 2 = l by omega]

theorem tup_eq_of_getD {x y : List (ℕ × ℕ)} {m : ℕ}
    (h : ∀ l < m, x.getD l (0, 0) = y.getD l (0, 0)) : ∀ i < 2 * m, tup x i = tup y i := by
  intro i hi
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [tup_even, tup_even, h l (by omega)]
  · rw [tup_odd, tup_odd, h l (by omega)]

theorem tup_zero_tail (x : List (ℕ × ℕ)) : ∀ i, 2 * x.length ≤ i → tup x i = 0 := by
  intro i hi
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [tup_even, List.getD_eq_default _ _ (by omega)]
  · rw [tup_odd, List.getD_eq_default _ _ (by omega)]

theorem tup_cons_zero (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) : tup (x :: xs) 0 = x.1 := by
  simp [tup]

theorem tup_cons_one (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) : tup (x :: xs) 1 = x.2 := by
  simp [tup]

theorem tup_cons_add_two (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) (i : ℕ) :
    tup (x :: xs) (i + 2) = tup xs i := by
  unfold tup
  rw [show (i + 2) / 2 = i / 2 + 1 by omega, show (i + 2) % 2 = i % 2 by omega]
  simp

theorem lexLE_add_two {m : ℕ} {f g : ℕ → ℕ} :
    LexLE (m + 2) f g ↔ f 0 < g 0 ∨ (f 0 = g 0 ∧ (f 1 < g 1 ∨ (f 1 = g 1 ∧
      LexLE m (fun i => f (i + 2)) (fun i => g (i + 2))))) := by
  rw [lexLE_iff, lexLE_iff]
  constructor
  · intro h
    rcases Nat.lt_or_ge (f 0) (g 0) with h0 | h0
    · exact Or.inl h0
    have e0 : f 0 = g 0 := le_antisymm (h 0 (by omega) (by simp)) h0
    right; refine ⟨e0, ?_⟩
    rcases Nat.lt_or_ge (f 1) (g 1) with h1 | h1
    · exact Or.inl h1
    have e1 : f 1 = g 1 := le_antisymm (h 1 (by omega) (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact e0)) h1
    right; refine ⟨e1, fun i hi hpre => h (i + 2) (by omega) fun j hj => ?_⟩
    rcases j with _ | _ | j
    · exact e0
    · exact e1
    · exact hpre j (by omega)
  · rintro (h0 | ⟨e0, h1 | ⟨e1, h⟩⟩) i hi hpre
    · rcases i with _ | i
      · exact h0.le
      · exact absurd (hpre 0 (by omega)) h0.ne
    · rcases i with _ | _ | i
      · exact e0.le
      · exact h1.le
      · exact absurd (hpre 1 (by omega)) h1.ne
    · rcases i with _ | _ | i
      · exact e0.le
      · exact e1.le
      · exact h i (by omega) fun j hj => hpre (j + 2) (by omega)

/-- On lists of length `≥ k`, the program's comparison is `LexLE (2 k)` on the tuples. -/
theorem lexCmp_le_iff : ∀ (k : ℕ) (a b : List (ℕ × ℕ)), k ≤ a.length → k ≤ b.length →
    ((lexCmp k a b).ret ≠ .gt ↔ LexLE (2 * k) (tup a) (tup b))
  | 0, a, b, _, _ => by simp [lexCmp_ret_zero, LexLE]
  | k + 1, [], _, ha, _ => by simp at ha
  | k + 1, _, [], _, hb => by simp at hb
  | k + 1, x :: xs, y :: ys, ha, hb => by
    simp only [List.length_cons] at ha hb
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, lexLE_add_two, tup_cons_zero, tup_cons_zero,
      tup_cons_one, tup_cons_one, lexCmp_ret_cons]
    have ih := lexCmp_le_iff k xs ys (by omega) (by omega)
    simp only [tup_cons_add_two]
    have ih' : (lexCmp k xs ys).ret ≠ .gt ↔ LexLE (2 * k) (fun i => tup xs i)
        (fun i => tup ys i) := ih
    by_cases hxy : pcmp x y = .eq
    · rw [ite_eq_left hxy, ih']
      obtain rfl := (pcmp_eq_eq x y).1 hxy
      simp
    · rw [ite_eq_right hxy]
      have hne : x ≠ y := fun h => hxy ((pcmp_eq_eq x y).2 h)
      constructor
      · intro hg
        have hl : pcmp x y = .lt := by cases h : pcmp x y <;> simp_all
        rw [pcmp_lt] at hl
        rcases hl with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, Or.inl h2⟩
      · intro h hg
        rw [pcmp_gt] at hg
        obtain ⟨x1, x2⟩ := x
        obtain ⟨y1, y2⟩ := y
        simp only at hg h
        rcases h with h | ⟨h1, h2 | ⟨h2, -⟩⟩
        · omega
        · omega
        · exact hne (by rw [h1, h2])

end MercLib.ParityGame.TwoSidedCost

end TwoSidedCostCorrectOrderProofs
