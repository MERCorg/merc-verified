module

public import MercLib.Algorithms.LDD.SetOperations
import all MercLib.Theory.LDD.Proofs.Ldd_Proofs

@[expose] public section

/-!
# Proofs: set operations on list decision diagrams

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/LDD.lean` (human-vetted).
-/

namespace MercLib.LDD

namespace Ldd

variable {α : Type*} [LinearOrder α]

private theorem pos_of_wf_node {v : α} {d r : Ldd α} {n : ℕ} (h : (node v d r).WellFormed n) :
    ∃ k, n = k + 1 := by
  cases n with
  | zero => simp [WellFormed] at h
  | succ k => exact ⟨k, rfl⟩

omit [LinearOrder α] in
private theorem ne_zero_of_mem {a : Ldd α} {x : List α} (hx : x ∈ a.denote) : a ≠ zero := by
  rintro rfl; simp [denote] at hx

/-- A well-formed LDD whose head is above `v` contains no vector starting with `v` or below. -/
private theorem lt_of_headAbove {a : Ldd α} {k : ℕ} {v : α} (ha : a.WellFormed (k + 1))
    (h : HeadAbove v a) {b : α} {xs : List α} (hx : b :: xs ∈ a.denote) : v < b := by
  obtain ⟨b', xs', hb, hlt⟩ := head_of_mem a k ha _ hx
  cases hb
  exact hlt v h

/-- Conversely, a well-formed LDD whose vectors all start above `v` has its head above `v`. -/
private theorem headAbove_of_lt {a : Ldd α} {k : ℕ} {v : α} (ha : a.WellFormed (k + 1))
    (h : ∀ b xs, b :: xs ∈ a.denote → v < b) : HeadAbove v a := by
  match a, ha with
  | zero, _ => trivial
  | node w e s, ha =>
    obtain ⟨he0, he, -, -⟩ := ha
    obtain ⟨y, hy⟩ := nonempty_of_ne_zero e k he he0
    exact h w y (Or.inl ⟨y, hy, rfl⟩)

private theorem headAbove_of_subset {a b : Ldd α} {k : ℕ} {v : α} (ha : a.WellFormed (k + 1))
    (hb : b.WellFormed (k + 1)) (h : HeadAbove v b) (hsub : a.denote ⊆ b.denote) :
    HeadAbove v a :=
  headAbove_of_lt ha fun _ _ hx => lt_of_headAbove hb h (hsub hx)

private theorem not_mem_of_lt_node {v w : α} {e s : Ldd α} {k : ℕ}
    (hb : (node w e s).WellFormed (k + 1)) (hvw : v < w) (y : List α) :
    v :: y ∉ (node w e s).denote := fun hm =>
  absurd (head_le_of_mem hb hm) (not_le.mpr hvw)

private theorem not_mem_of_headAbove {a : Ldd α} {k : ℕ} {v : α} (ha : a.WellFormed (k + 1))
    (h : HeadAbove v a) (y : List α) : v :: y ∉ a.denote := fun hm =>
  lt_irrefl v (lt_of_headAbove ha h hm)

omit [LinearOrder α] in
private theorem denote_node (v : α) (d r : Ldd α) :
    (node v d r).denote = (List.cons v '' d.denote) ∪ r.denote := rfl

omit [LinearOrder α] in
private theorem denote_mk (v : α) (d r : Ldd α) :
    (mk v d r).denote = (List.cons v '' d.denote) ∪ r.denote := by
  cases d <;> simp [mk, denote]

private theorem wellFormed_mk {v : α} {d r : Ldd α} {k : ℕ} (hd : d.WellFormed k)
    (hr : r.WellFormed (k + 1)) (h : HeadAbove v r) : (mk v d r).WellFormed (k + 1) := by
  cases d with
  | zero => exact hr
  | one => exact ⟨by simp, hd, hr, h⟩
  | node w e s => exact ⟨by simp, hd, hr, h⟩

private theorem eq_of_not_lt {v w : α} (h1 : ¬v < w) (h2 : ¬w < v) : v = w :=
  le_antisymm (not_lt.mp h2) (not_lt.mp h1)

/-! ## Induction principles

Private copies of the functional induction principles of `union`, `inter` and `diff` (which share
a shape), so that this module does not export the generated `.induct` theorems. -/

omit [LinearOrder α] in
private theorem size_lt_left {v : α} {d r b : Ldd α} :
    sizeOf r + sizeOf b < sizeOf (node v d r) + sizeOf b := by simp; omega

omit [LinearOrder α] in
private theorem size_lt_right {a : Ldd α} {w : α} {e s : Ldd α} :
    sizeOf a + sizeOf s < sizeOf a + sizeOf (node w e s) := by simp; omega

omit [LinearOrder α] in
private theorem size_lt_both {v w : α} {d r e s : Ldd α} :
    sizeOf r + sizeOf s < sizeOf (node v d r) + sizeOf (node w e s) := by simp; omega

omit [LinearOrder α] in
private theorem size_lt_down {v w : α} {d r e s : Ldd α} :
    sizeOf d + sizeOf e < sizeOf (node v d r) + sizeOf (node w e s) := by simp; omega

private theorem union_induct (motive : Ldd α → Ldd α → Prop)
    (case1 : ∀ b, motive zero b)
    (case2 : ∀ a, (a = zero → False) → motive a zero)
    (case3 : ∀ x, (x = zero → False) → motive one x)
    (case4 : ∀ v d r, motive (node v d r) one)
    (case5 : ∀ v d r w e s, v < w → motive r (node w e s) → motive (node v d r) (node w e s))
    (case6 : ∀ v d r w e s, ¬v < w → w < v → motive (node v d r) s →
      motive (node v d r) (node w e s))
    (case7 : ∀ v d r w e s, ¬v < w → ¬w < v → motive d e → motive r s →
      motive (node v d r) (node w e s)) :
    ∀ a b, motive a b := by
  intro a b
  induction h : sizeOf a + sizeOf b using Nat.strong_induction_on generalizing a b with
  | _ k ih =>
    subst h
    match a, b with
    | zero, b => exact case1 b
    | one, zero => exact case2 one (by simp)
    | node .., zero => exact case2 _ (by simp)
    | one, one => exact case3 one (by simp)
    | one, node .. => exact case3 _ (by simp)
    | node v d r, one => exact case4 v d r
    | node v d r, node w e s =>
      if h1 : v < w then exact case5 v d r w e s h1 (ih _ size_lt_left _ _ rfl)
      else if h2 : w < v then exact case6 v d r w e s h1 h2 (ih _ size_lt_right _ _ rfl)
      else exact case7 v d r w e s h1 h2 (ih _ size_lt_down _ _ rfl) (ih _ size_lt_both _ _ rfl)

private theorem inter_induct (motive : Ldd α → Ldd α → Prop)
    (case1 : ∀ x, motive zero x)
    (case2 : ∀ x, (x = zero → False) → motive x zero)
    (case3 : motive one one)
    (case4 : ∀ v d r, motive one (node v d r))
    (case5 : ∀ v d r, motive (node v d r) one)
    (case6 : ∀ v d r w e s, v < w → motive r (node w e s) → motive (node v d r) (node w e s))
    (case7 : ∀ v d r w e s, ¬v < w → w < v → motive (node v d r) s →
      motive (node v d r) (node w e s))
    (case8 : ∀ v d r w e s, ¬v < w → ¬w < v → motive d e → motive r s →
      motive (node v d r) (node w e s)) :
    ∀ a b, motive a b := by
  intro a b
  induction h : sizeOf a + sizeOf b using Nat.strong_induction_on generalizing a b with
  | _ k ih =>
    subst h
    match a, b with
    | zero, b => exact case1 b
    | one, zero => exact case2 one (by simp)
    | node .., zero => exact case2 _ (by simp)
    | one, one => exact case3
    | one, node v d r => exact case4 v d r
    | node v d r, one => exact case5 v d r
    | node v d r, node w e s =>
      if h1 : v < w then exact case6 v d r w e s h1 (ih _ size_lt_left _ _ rfl)
      else if h2 : w < v then exact case7 v d r w e s h1 h2 (ih _ size_lt_right _ _ rfl)
      else exact case8 v d r w e s h1 h2 (ih _ size_lt_down _ _ rfl) (ih _ size_lt_both _ _ rfl)

private theorem union_correct (a b : Ldd α) : ∀ n, a.WellFormed n → b.WellFormed n →
    (union a b).WellFormed n ∧ (union a b).denote = a.denote ∪ b.denote := by
  induction a, b using union_induct with
  | case1 b => intro n _ hb; simp [union, denote, hb]
  | case2 a ha0 =>
    intro n ha _
    cases a with
    | zero => exact absurd rfl ha0
    | one => simp [union, denote, ha]
    | node v d r => simp [union, denote, ha]
  | case3 x hx0 =>
    intro n ha hb
    simp only [WellFormed] at ha; subst ha
    match x, hb with
    | zero, _ => exact absurd rfl hx0
    | one, _ => simp [union, denote, WellFormed]
  | case4 v d r =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    simp [WellFormed] at hb
  | case5 v d r w e s hvw ih =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    obtain ⟨hd0, hd, hr, hvr⟩ := ha
    obtain ⟨ih1, ih2⟩ := ih (k + 1) hr hb
    simp only [union, hvw, ↓reduceIte]
    refine ⟨⟨hd0, hd, ih1, headAbove_of_lt ih1 fun b xs hx => ?_⟩, ?_⟩
    · rw [ih2] at hx
      rcases hx with hx | hx
      · exact lt_of_headAbove hr hvr hx
      · exact lt_of_lt_of_le hvw (head_le_of_mem hb hx)
    · rw [denote_node, ih2]; simp only [denote, Set.union_assoc]
  | case6 v d r w e s h1 hwv ih =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node hb
    obtain ⟨he0, he, hs, hws⟩ := hb
    obtain ⟨ih1, ih2⟩ := ih (k + 1) ha hs
    simp only [union, h1, hwv, ↓reduceIte]
    refine ⟨⟨he0, he, ih1, headAbove_of_lt ih1 fun b xs hx => ?_⟩, ?_⟩
    · rw [ih2] at hx
      rcases hx with hx | hx
      · exact lt_of_lt_of_le hwv (head_le_of_mem ha hx)
      · exact lt_of_headAbove hs hws hx
    · rw [denote_node, ih2]; simp only [denote]
      ext x; simp only [Set.mem_union]; tauto
  | case7 v d r w e s h1 h2 ihd ihr =>
    intro n ha hb
    obtain rfl := eq_of_not_lt h1 h2
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    obtain ⟨hd0, hd, hr, hvr⟩ := ha
    obtain ⟨he0, he, hs, hvs⟩ := hb
    obtain ⟨ihd1, ihd2⟩ := ihd k hd he
    obtain ⟨ihr1, ihr2⟩ := ihr (k + 1) hr hs
    simp only [union, h1, ↓reduceIte]
    obtain ⟨y, hy⟩ := nonempty_of_ne_zero d k hd hd0
    refine ⟨⟨ne_zero_of_mem (x := y) (by rw [ihd2]; exact Or.inl hy), ihd1, ihr1,
      headAbove_of_lt ihr1 fun b xs hx => ?_⟩, ?_⟩
    · rw [ihr2] at hx
      rcases hx with hx | hx
      · exact lt_of_headAbove hr hvr hx
      · exact lt_of_headAbove hs hvs hx
    · simp only [denote]; rw [ihd2, ihr2, Set.image_union]
      ext x; simp only [Set.mem_union]; tauto

private theorem inter_correct (a b : Ldd α) : ∀ n, a.WellFormed n → b.WellFormed n →
    (inter a b).WellFormed n ∧ (inter a b).denote = a.denote ∩ b.denote := by
  induction a, b using inter_induct with
  | case1 x => intro n _ _; simp [inter, denote, WellFormed]
  | case2 x hx0 =>
    intro n _ _
    cases x with
    | zero => exact absurd rfl hx0
    | one => simp [inter, denote, WellFormed]
    | node v d r => simp [inter, denote, WellFormed]
  | case3 => intro n ha _; simp [inter, denote, ha]
  | case4 v d r =>
    intro n ha hb
    simp only [WellFormed] at ha; subst ha
    simp [WellFormed] at hb
  | case5 v d r =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    simp [WellFormed] at hb
  | case6 v d r w e s hvw ih =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    obtain ⟨-, -, hr, -⟩ := ha
    obtain ⟨ih1, ih2⟩ := ih (k + 1) hr hb
    simp only [inter, hvw, ↓reduceIte]
    refine ⟨ih1, ?_⟩
    rw [ih2]; simp only [denote]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
    · rintro ⟨⟨y, -, rfl⟩ | h1, h2⟩
      · exact absurd h2 (not_mem_of_lt_node hb hvw y)
      · exact ⟨h1, h2⟩
  | case7 v d r w e s h1 hwv ih =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node hb
    obtain ⟨-, -, hs, -⟩ := hb
    obtain ⟨ih1, ih2⟩ := ih (k + 1) ha hs
    simp only [inter, h1, hwv, ↓reduceIte]
    refine ⟨ih1, ?_⟩
    rw [ih2]; simp only [denote]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
    · rintro ⟨h1, ⟨y, -, rfl⟩ | h2⟩
      · exact absurd h1 (not_mem_of_lt_node ha hwv y)
      · exact ⟨h1, h2⟩
  | case8 v d r w e s h1 h2 ihd ihr =>
    intro n ha hb
    obtain rfl := eq_of_not_lt h1 h2
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    obtain ⟨-, hd, hr, hvr⟩ := ha
    obtain ⟨-, he, hs, hvs⟩ := hb
    obtain ⟨ihd1, ihd2⟩ := ihd k hd he
    obtain ⟨ihr1, ihr2⟩ := ihr (k + 1) hr hs
    simp only [inter, h1, ↓reduceIte]
    refine ⟨wellFormed_mk ihd1 ihr1
      (headAbove_of_subset ihr1 hr hvr (by rw [ihr2]; exact Set.inter_subset_left)), ?_⟩
    rw [denote_mk, ihd2, ihr2]; simp only [denote]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_image]
    constructor
    · rintro (⟨y, ⟨hyd, hye⟩, rfl⟩ | ⟨hxr, hxs⟩)
      · exact ⟨Or.inl ⟨y, hyd, rfl⟩, Or.inl ⟨y, hye, rfl⟩⟩
      · exact ⟨Or.inr hxr, Or.inr hxs⟩
    · rintro ⟨⟨y, hyd, rfl⟩ | hxr, ⟨y', hye, hy'⟩ | hxs⟩
      · obtain rfl := List.cons_injective hy'; exact Or.inl ⟨_, ⟨hyd, hye⟩, rfl⟩
      · exact absurd hxs (not_mem_of_headAbove hs hvs y)
      · subst hy'; exact absurd hxr (not_mem_of_headAbove hr hvr y')
      · exact Or.inr ⟨hxr, hxs⟩

private theorem diff_correct (a b : Ldd α) : ∀ n, a.WellFormed n → b.WellFormed n →
    (diff a b).WellFormed n ∧ (diff a b).denote = a.denote \ b.denote := by
  induction a, b using inter_induct with
  | case1 x => intro n _ _; simp [diff, denote, WellFormed]
  | case2 a ha0 =>
    intro n ha _
    cases a with
    | zero => exact absurd rfl ha0
    | one => simp [diff, denote, ha]
    | node v d r => simp [diff, denote, ha]
  | case3 => intro n _ _; simp [diff, denote, WellFormed]
  | case4 v d r =>
    intro n ha hb
    simp only [WellFormed] at ha; subst ha
    simp [WellFormed] at hb
  | case5 v d r =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    simp [WellFormed] at hb
  | case6 v d r w e s hvw ih =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    obtain ⟨hd0, hd, hr, hvr⟩ := ha
    obtain ⟨ih1, ih2⟩ := ih (k + 1) hr hb
    simp only [diff, hvw, ↓reduceIte]
    refine ⟨⟨hd0, hd, ih1,
      headAbove_of_subset ih1 hr hvr (by rw [ih2]; exact Set.sdiff_subset)⟩, ?_⟩
    rw [denote_node, ih2]; simp only [denote]
    ext x
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl ⟨y, hy, rfl⟩, not_mem_of_lt_node hb hvw y⟩
      · exact ⟨Or.inr h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
  | case7 v d r w e s h1 hwv ih =>
    intro n ha hb
    obtain ⟨k, rfl⟩ := pos_of_wf_node hb
    obtain ⟨-, -, hs, -⟩ := hb
    obtain ⟨ih1, ih2⟩ := ih (k + 1) ha hs
    simp only [diff, h1, hwv, ↓reduceIte]
    refine ⟨ih1, ?_⟩
    rw [ih2]; simp only [denote]
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_, h2⟩
      rintro ⟨y, -, rfl⟩
      exact not_mem_of_lt_node ha hwv y h1
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  | case8 v d r w e s h1 h2 ihd ihr =>
    intro n ha hb
    obtain rfl := eq_of_not_lt h1 h2
    obtain ⟨k, rfl⟩ := pos_of_wf_node ha
    obtain ⟨-, hd, hr, hvr⟩ := ha
    obtain ⟨-, he, hs, hvs⟩ := hb
    obtain ⟨ihd1, ihd2⟩ := ihd k hd he
    obtain ⟨ihr1, ihr2⟩ := ihr (k + 1) hr hs
    simp only [diff, h1, ↓reduceIte]
    refine ⟨wellFormed_mk ihd1 ihr1
      (headAbove_of_subset ihr1 hr hvr (by rw [ihr2]; exact Set.sdiff_subset)), ?_⟩
    rw [denote_mk, ihd2, ihr2]; simp only [denote]
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_image, not_or, not_exists, not_and]
    constructor
    · rintro (⟨y, ⟨hyd, hye⟩, rfl⟩ | ⟨hxr, hxs⟩)
      · refine ⟨Or.inl ⟨y, hyd, rfl⟩, fun y' hy' heq => ?_, not_mem_of_headAbove hs hvs y⟩
        cases List.cons_injective heq; exact hye hy'
      · refine ⟨Or.inr hxr, fun y' _ heq => ?_, hxs⟩
        subst heq; exact not_mem_of_headAbove hr hvr y' hxr
    · rintro ⟨⟨y, hyd, rfl⟩ | hxr, hne, hxs⟩
      · exact Or.inl ⟨y, ⟨hyd, fun hye => hne y hye rfl⟩, rfl⟩
      · exact Or.inr ⟨hxr, hxs⟩

end Ldd

open Ldd

variable {α : Type*} [LinearOrder α]

/-- **Union is correct.** -/
theorem unionCorrect (a b : Ldd α) (n : ℕ) : UnionCorrect a b n := union_correct a b n

/-- **Intersection is correct.** -/
theorem interCorrect (a b : Ldd α) (n : ℕ) : InterCorrect a b n := inter_correct a b n

/-- **Difference is correct.** -/
theorem diffCorrect (a b : Ldd α) (n : ℕ) : DiffCorrect a b n := diff_correct a b n

end MercLib.LDD
