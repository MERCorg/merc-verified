import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Counting-sort positions

Pure combinatorics behind the scatter loop of `finish_partition_marked`: given the class `cls[t]`
of each processed element `t` and the class sizes `szs`, element `t` is placed at
`cumS ms szs (cls[t]) + rank t`, where `rank t` counts the earlier elements of the same class.
The placement is a bijection from element indices onto `[ms, ms + |cls|)`.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

namespace MercVerified.Refinement.Proofs

/-- Start position of class `j`: `ms` plus the sizes of all earlier classes. -/
def cumS (ms : Nat) (szs : List Nat) (j : Nat) : Nat := ms + (szs.take j).sum

/-- Number of earlier elements of the same class as element `t`. -/
def rankOf (cls : List Nat) (t : Nat) : Nat := (cls.take t).count (cls.getD t 0)

/-- Target position of element `t`. -/
def posOf (ms : Nat) (szs cls : List Nat) (t : Nat) : Nat :=
  cumS ms szs (cls.getD t 0) + rankOf cls t

theorem cumS_succ (ms : Nat) (szs : List Nat) (j : Nat) (hj : j < szs.length) :
    cumS ms szs (j + 1) = cumS ms szs j + szs[j] := by
  unfold cumS
  rw [List.sum_take_succ _ _ hj]; omega

theorem cumS_mono (ms : Nat) (szs : List Nat) {i j : Nat} (h : i ≤ j) :
    cumS ms szs i ≤ cumS ms szs j := by
  induction h with
  | refl => exact le_refl _
  | step h ih =>
    rename_i m
    by_cases hm : m < szs.length
    · rw [cumS_succ ms szs m hm]; omega
    · have : szs.take (m + 1) = szs.take m := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      unfold cumS at *; rw [this]; exact ih

theorem cumS_ge (ms : Nat) (szs : List Nat) (j : Nat) : ms ≤ cumS ms szs j := by
  unfold cumS; omega

theorem cumS_length (ms : Nat) (szs : List Nat) : cumS ms szs szs.length = ms + szs.sum := by
  simp [cumS]

/-- The class sizes add up to the number of elements. -/
theorem sum_count_eq_length (K : Nat) (cls : List Nat) (hcls : ∀ x ∈ cls, x < K) :
    ((List.range K).map (fun j => cls.count j)).sum = cls.length := by
  induction cls with
  | nil => simp
  | cons x xs ih =>
    have hx : x < K := hcls x (by simp)
    have ih' := ih (fun y hy => hcls y (by simp [hy]))
    have hmap : (List.range K).map (fun j => (x :: xs).count j) =
        (List.range K).map (fun j => xs.count j + if j = x then 1 else 0) := by
      apply List.map_congr_left
      intro j _
      by_cases h : j = x
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hmap]
    have hsplit : ∀ (l : List Nat) , ((l.map (fun j => xs.count j + if j = x then 1 else 0)).sum) =
        (l.map (fun j => xs.count j)).sum + (l.map (fun j => if j = x then 1 else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih2 => simp [ih2]; omega
    rw [hsplit, ih']
    have : ((List.range K).map (fun j => if j = x then 1 else 0)).sum = 1 := by
      have key : ∀ K', ((List.range K').map (fun j => if j = x then 1 else 0)).sum
          = if x < K' then 1 else 0 := by
        intro K'
        induction K' with
        | zero => simp
        | succ k ihk =>
          rw [List.range_succ, List.map_append, List.sum_append, ihk]
          by_cases h1 : x < k
          · simp [h1, show ¬ k = x by omega, show x < k + 1 by omega]
          · by_cases h2 : x = k
            · subst h2; simp
            · simp [h1, show ¬ k = x by omega, show ¬ x < k + 1 by omega]
      rw [key]; simp [hx]
    simp [this]

theorem count_take_mono (l : List Nat) (x : Nat) {a b : Nat} (h : a ≤ b) :
    (l.take a).count x ≤ (l.take b).count x := by
  have h1 := List.take_append_drop a (l.take b)
  rw [List.take_take, min_eq_left h] at h1
  conv_rhs => rw [← h1]
  rw [List.count_append]; omega

theorem count_take_succ (l : List Nat) (t : Nat) (ht : t < l.length) :
    (l.take (t + 1)).count l[t] = (l.take t).count l[t] + 1 := by
  rw [List.take_succ_eq_append_getElem ht, List.count_append, List.count_singleton_self]

theorem rank_lt_count (cls : List Nat) (t : Nat) (ht : t < cls.length) :
    rankOf cls t < cls.count (cls[t]) := by
  unfold rankOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  simp only [Option.getD_some]
  have h1 := count_take_succ cls t ht
  have h2 := count_take_mono cls cls[t] (a := t + 1) (b := cls.length) (by omega)
  rw [List.take_length] at h2
  omega

theorem rank_strict (cls : List Nat) {t u : Nat} (htu : t < u) (hu : u < cls.length)
    (hc : cls[t]'(by omega) = cls[u]) : rankOf cls t < rankOf cls u := by
  have ht : t < cls.length := by omega
  unfold rankOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
  simp only [Option.getD_some]
  have h1 := count_take_succ cls t ht
  have h2 := count_take_mono cls cls[t] (a := t + 1) (b := u) (by omega)
  rw [← hc]
  omega

/-- Bounds on the target position. -/
theorem posOf_bounds (ms : Nat) (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    (t : Nat) (ht : t < cls.length) :
    cumS ms szs cls[t] ≤ posOf ms szs cls t ∧
      posOf ms szs cls t < cumS ms szs (cls[t] + 1) := by
  have hc : cls[t] < K := hlt _ (List.getElem_mem ht)
  have hsz : szs.getD cls[t] 0 = cls.count cls[t] := hcnt _ hc
  have hr := rank_lt_count cls t ht
  have hs := cumS_succ ms szs cls[t] (by omega)
  have hgd : szs.getD cls[t] 0 = szs[cls[t]]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show cls[t] < szs.length by omega)]
  unfold posOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  simp only [Option.getD_some]
  omega

theorem posOf_inj (ms : Nat) (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    {t u : Nat} (ht : t < cls.length) (hu : u < cls.length)
    (h : posOf ms szs cls t = posOf ms szs cls u) : t = u := by
  have bt := posOf_bounds ms szs cls K hK hcnt hlt t ht
  have bu := posOf_bounds ms szs cls K hK hcnt hlt u hu
  by_contra hne
  rcases lt_trichotomy cls[t] cls[u] with hlt' | heq | hgt
  · have := cumS_mono ms szs (i := cls[t] + 1) (j := cls[u]) (by omega); omega
  · rcases Nat.lt_or_gt_of_ne hne with htu | htu
    · have := rank_strict cls htu hu heq
      unfold posOf at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu] at h
      simp only [Option.getD_some] at h
      rw [heq] at h; omega
    · have := rank_strict cls htu ht heq.symm
      unfold posOf at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu] at h
      simp only [Option.getD_some] at h
      rw [heq] at h; omega
  · have := cumS_mono ms szs (i := cls[u] + 1) (j := cls[t]) (by omega); omega

/-- Every position of `[ms, ms + |cls|)` is the target of some element. -/
theorem posOf_surj (ms : Nat) (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K)
    {i : Nat} (h1 : ms ≤ i) (h2 : i < ms + cls.length) :
    ∃ t, ∃ _ : t < cls.length, posOf ms szs cls t = i := by
  have hsum : szs.sum = cls.length := by
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
  have hsub : (Finset.range cls.length).image (posOf ms szs cls) ⊆ Finset.Ico ms (ms + cls.length) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have ht' := Finset.mem_range.mp ht
    have b := posOf_bounds ms szs cls K hK hcnt hlt t ht'
    have := cumS_mono ms szs (i := cls[t] + 1) (j := szs.length)
      (by have := hlt _ (List.getElem_mem ht'); omega)
    rw [cumS_length, hsum] at this
    have := cumS_ge ms szs cls[t]
    simp only [Finset.mem_Ico]
    omega
  have hcard : ((Finset.range cls.length).image (posOf ms szs cls)).card = cls.length := by
    have hinj : Set.InjOn (posOf ms szs cls) ↑(Finset.range cls.length) := by
      intro a ha b hb hab
      exact posOf_inj ms szs cls K hK hcnt hlt (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab
    rw [Finset.card_image_of_injOn hinj]; simp
  have heq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have hi : i ∈ Finset.Ico ms (ms + cls.length) := Finset.mem_Ico.mpr ⟨h1, h2⟩
  rw [← heq] at hi
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hi
  exact ⟨t, Finset.mem_range.mp ht, hti⟩

/-- The class sizes add up to the number of elements. -/
theorem szs_sum_eq (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K) :
    szs.sum = cls.length := by
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

/-- Every class ends at or before the end of the region. -/
theorem cumS_le_end (ms : Nat) (szs cls : List Nat) (K : Nat) (hK : szs.length = K)
    (hcnt : ∀ j, j < K → szs.getD j 0 = cls.count j) (hlt : ∀ x ∈ cls, x < K) (j : Nat) :
    cumS ms szs j ≤ ms + cls.length := by
  have hs := szs_sum_eq szs cls K hK hcnt hlt
  by_cases hj : j ≤ szs.length
  · have := cumS_mono ms szs (i := j) (j := szs.length) hj
    rw [cumS_length, hs] at this; exact this
  · have : szs.take j = szs := List.take_of_length_le (by omega)
    unfold cumS; rw [this, hs]

end MercVerified.Refinement.Proofs
