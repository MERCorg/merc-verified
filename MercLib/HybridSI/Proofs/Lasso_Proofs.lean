module

public import MercLib.HybridSI.Valuation
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Fintype.Pigeonhole

@[expose] public section HybridSILassoProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Lasso structure of the play under a profile `f`: the vertices occurring infinitely often
(`Recurs`), the cycle maximum `cycMax` as their greatest element, the first-hit time `stepsTo`
and the set `bSet`, with their one-step recursions. -/

open Function

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V] (f : V → V)

theorem iter_eq : ∀ (k : ℕ) (v : V), iter f k v = f^[k] v
  | 0, _ => rfl
  | k + 1, v => by rw [iter, iter_eq k (f v), iterate_succ_apply]

theorem mem_playPrefix (k : ℕ) (v y : V) : y ∈ playPrefix f k v ↔ ∃ i < k, f^[i] v = y := by
  simp [playPrefix, iter_eq]

/-- `y` occurs infinitely often on the play from `x`. -/
def Recurs (x y : V) : Prop := ∀ N, ∃ i, N ≤ i ∧ f^[i] x = y

variable {f}

theorem recurs_apply_iff {x y : V} : Recurs f (f x) y ↔ Recurs f x y := by
  constructor
  · intro h N
    obtain ⟨i, hi, e⟩ := h N
    exact ⟨i + 1, by omega, by rw [iterate_succ_apply]; exact e⟩
  · intro h N
    obtain ⟨i, hi, e⟩ := h (N + 1)
    refine ⟨i - 1, by omega, ?_⟩
    rw [← iterate_succ_apply, show (i - 1).succ = i by omega]
    exact e

theorem recurs_trans {x y z : V} (hxy : Recurs f x y) (hyz : Recurs f y z) : Recurs f x z := by
  intro N
  obtain ⟨i, -, hi⟩ := hxy 0
  obtain ⟨j, hj, e⟩ := hyz N
  exact ⟨j + i, by omega, by rw [iterate_add_apply, hi, e]⟩

/-- A periodic point reachable from `x` recurs, and so does every point of its orbit. -/
theorem recurs_of_periodic {x c : V} {p a : ℕ} (hp : 0 < p) (hc : IsPeriodicPt f p c)
    (ha : f^[a] x = c) (i : ℕ) : Recurs f x (f^[i] c) := by
  intro N
  refine ⟨i + p * N + a, ?_, ?_⟩
  · have : N ≤ p * N := Nat.le_mul_of_pos_left N hp
    omega
  · rw [iterate_add_apply, iterate_add_apply, ha, (hc.mul_const N).eq]

/-- A recurring vertex is periodic. -/
theorem periodic_of_recurs {x y : V} (h : Recurs f x y) : ∃ p, 0 < p ∧ IsPeriodicPt f p y := by
  obtain ⟨i, -, hi⟩ := h 0
  obtain ⟨j, hj, hj'⟩ := h (i + 1)
  refine ⟨j - i, by omega, ?_⟩
  show f^[j - i] y = y
  rw [← hi, ← iterate_add_apply, show j - i + i = j by omega, hj', hi]

theorem recurs_self_of_recurs {x y : V} (h : Recurs f x y) : Recurs f y y := by
  obtain ⟨p, hp, hpy⟩ := periodic_of_recurs h
  simpa using recurs_of_periodic (a := 0) hp hpy rfl 0

/-- After `|V|` steps the play is periodic, with a period of at most `|V|`. -/
theorem exists_period (x : V) :
    ∃ p, 0 < p ∧ p ≤ Fintype.card V ∧ IsPeriodicPt f p (f^[Fintype.card V] x) := by
  obtain ⟨a, b, hab, e⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) => f^[i] x) (by simp)
  have key : ∀ a b : Fin (Fintype.card V + 1), a < b → f^[a] x = f^[b] x →
      ∃ p, 0 < p ∧ p ≤ Fintype.card V ∧ IsPeriodicPt f p (f^[Fintype.card V] x) := by
    intro a b hlt e
    have hlt' : (a : ℕ) < b := hlt
    refine ⟨b - a, by omega, by omega, ?_⟩
    have ha : IsPeriodicPt f (b - a) (f^[a] x) := by
      show f^[b - a] (f^[a] x) = f^[a] x
      rw [← iterate_add_apply, show (b : ℕ) - a + a = b by omega, e]
    have := ha.apply_iterate (Fintype.card V - a)
    rwa [← iterate_add_apply, show Fintype.card V - a + a = Fintype.card V by omega] at this
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h e
  · exact key b a h e.symm

theorem le_foldl_max : ∀ (l : List V) (c : V), c ≤ l.foldl max c ∧ ∀ y ∈ l, y ≤ l.foldl max c
  | [], c => by simp
  | x :: l, c => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max c x)
    refine ⟨(le_max_left c x).trans h1, ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp, List.foldl_cons]
    exact ⟨(le_max_right c x).trans h1, h2⟩

theorem foldl_max_mem : ∀ (l : List V) (c : V), l.foldl max c = c ∨ l.foldl max c ∈ l
  | [], c => by simp
  | x :: l, c => by
    simp only [List.foldl_cons, List.mem_cons]
    rcases foldl_max_mem l (max c x) with h | h
    · rw [h]
      rcases max_choice c x with h' | h' <;> simp [h']
    · exact Or.inr (Or.inr h)

/-- The cycle maximum recurs. -/
theorem recurs_cycMax (x : V) : Recurs f x (cycMax f x) := by
  obtain ⟨p, hp, -, hc⟩ := exists_period (f := f) x
  unfold cycMax
  simp only [iter_eq]
  rcases foldl_max_mem (playPrefix f (Fintype.card V) (f^[Fintype.card V] x))
      (f^[Fintype.card V] x) with h | h
  · rw [h]; simpa using recurs_of_periodic hp hc rfl 0
  · rw [mem_playPrefix] at h
    obtain ⟨i, -, hi⟩ := h
    rw [← hi]
    exact recurs_of_periodic hp hc rfl i

/-- Every recurring vertex is at most the cycle maximum. -/
theorem le_cycMax {x y : V} (h : Recurs f x y) : y ≤ cycMax f x := by
  obtain ⟨p, hp, hpn, hc⟩ := exists_period (f := f) x
  obtain ⟨i, hi, e⟩ := h (Fintype.card V)
  have hy : y = f^[(i - Fintype.card V) % p] (f^[Fintype.card V] x) := by
    rw [hc.iterate_mod_apply, ← iterate_add_apply, show i - Fintype.card V + Fintype.card V = i
      by omega, e]
  unfold cycMax
  simp only [iter_eq]
  refine (le_foldl_max _ _).2 y ?_
  rw [mem_playPrefix]
  exact ⟨_, lt_of_lt_of_le (Nat.mod_lt _ hp) hpn, hy.symm⟩

theorem cycMax_apply (x : V) : cycMax f (f x) = cycMax f x :=
  le_antisymm (le_cycMax (recurs_apply_iff.1 (recurs_cycMax (f x))))
    (le_cycMax (recurs_apply_iff.2 (recurs_cycMax x)))

theorem cycMax_cycMax (x : V) : cycMax f (cycMax f x) = cycMax f x := by
  have h := recurs_cycMax (f := f) x
  exact le_antisymm (le_cycMax (recurs_trans h (recurs_cycMax _)))
    (le_cycMax (recurs_self_of_recurs h))

/-- The play from `x` reaches its cycle maximum within `2 |V|` steps. -/
theorem exists_hit (x : V) : ∃ i, i < 2 * Fintype.card V + 1 ∧ f^[i] x = cycMax f x := by
  have h := foldl_max_mem (playPrefix f (Fintype.card V) (f^[Fintype.card V] x))
    (f^[Fintype.card V] x)
  have hc : cycMax f x = (playPrefix f (Fintype.card V) (f^[Fintype.card V] x)).foldl max
      (f^[Fintype.card V] x) := by
    unfold cycMax; simp only [iter_eq]
  rw [hc]
  rcases h with h | h
  · exact ⟨Fintype.card V, by omega, h.symm⟩
  · rw [mem_playPrefix] at h
    obtain ⟨i, hi, e⟩ := h
    exact ⟨i + Fintype.card V, by omega, by rw [iterate_add_apply, e]⟩

/-- `stepsTo` is the first time the play reaches its cycle maximum. -/
theorem stepsTo_spec (x : V) :
    f^[stepsTo f x] x = cycMax f x ∧ ∀ j < stepsTo f x, f^[j] x ≠ cycMax f x := by
  obtain ⟨i, hi, e⟩ := exists_hit (f := f) x
  have hne : (List.range (2 * Fintype.card V + 1)).find?
      (fun i => iter f i x == cycMax f x) ≠ none := by
    rw [Ne, List.find?_range_eq_none]
    intro h
    have := h i hi
    simp [iter_eq, e] at this
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hne
  rw [List.find?_range_eq_some] at hk
  have hs : stepsTo f x = k := by
    unfold stepsTo
    rw [show (List.range (2 * Fintype.card V + 1)).find? (fun i => iter f i x == cycMax f x)
      = some k from List.find?_range_eq_some.2 hk]
    rfl
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hs]; simpa [iter_eq] using hk.1
  · rw [hs] at hj
    simpa [iter_eq] using hk.2.2 j hj

theorem stepsTo_eq_zero {x : V} (h : x = cycMax f x) : stepsTo f x = 0 := by
  by_contra hne
  exact (stepsTo_spec (f := f) x).2 0 (by omega) (by simpa using h)

theorem stepsTo_apply {x : V} (h : x ≠ cycMax f x) : stepsTo f x = stepsTo f (f x) + 1 := by
  obtain ⟨h1, h2⟩ := stepsTo_spec (f := f) x
  obtain ⟨h1', h2'⟩ := stepsTo_spec (f := f) (f x)
  rw [cycMax_apply] at h1' h2'
  have hpos : 0 < stepsTo f x := by
    by_contra h0
    rw [show stepsTo f x = 0 by omega] at h1
    exact h h1
  have hle : stepsTo f (f x) ≤ stepsTo f x - 1 := by
    by_contra hlt
    apply h2' (stepsTo f x - 1) (by omega)
    rw [← iterate_succ_apply, show (stepsTo f x - 1).succ = stepsTo f x by omega, h1]
  have hge : stepsTo f x ≤ stepsTo f (f x) + 1 := by
    by_contra hlt
    exact h2 (stepsTo f (f x) + 1) (by omega) (by rw [iterate_succ_apply, h1'])
  omega

theorem mem_bSet {x y : V} :
    y ∈ bSet f x ↔ (∃ i < stepsTo f x, f^[i] x = y) ∧ cycMax f x < y := by
  simp [bSet, mem_playPrefix]

theorem bSet_eq_empty {x : V} (h : x = cycMax f x) : bSet f x = ∅ := by
  ext y
  simp [mem_bSet, stepsTo_eq_zero h]

theorem bSet_apply {x : V} (h : x ≠ cycMax f x) :
    bSet f x = if cycMax f x < x then insert x (bSet f (f x)) else bSet f (f x) := by
  ext y
  simp only [mem_bSet, stepsTo_apply h]
  constructor
  · rintro ⟨⟨i, hi, e⟩, hlt⟩
    rcases i with _ | i
    · simp only [iterate_zero, id_eq] at e
      subst e
      simp [hlt, mem_bSet, cycMax_apply]
    · rw [iterate_succ_apply] at e
      have hy : y ∈ bSet f (f x) := mem_bSet.2 ⟨⟨i, by omega, e⟩, by rwa [cycMax_apply]⟩
      split_ifs <;> simp [hy]
  · intro hy
    split_ifs at hy with hlt
    · rcases Finset.mem_insert.1 hy with rfl | hy
      · exact ⟨⟨0, by omega, rfl⟩, hlt⟩
      · obtain ⟨⟨i, hi, e⟩, hlt'⟩ := mem_bSet.1 hy
        rw [cycMax_apply] at hlt'
        exact ⟨⟨i + 1, by omega, by rw [iterate_succ_apply, e]⟩, hlt'⟩
    · obtain ⟨⟨i, hi, e⟩, hlt'⟩ := mem_bSet.1 hy
      rw [cycMax_apply] at hlt'
      exact ⟨⟨i + 1, by omega, by rw [iterate_succ_apply, e]⟩, hlt'⟩

/-- A vertex more relevant than the cycle maximum is not revisited. -/
theorem not_mem_bSet_apply {x : V} (h : cycMax f x < x) : x ∉ bSet f (f x) := by
  intro hx
  obtain ⟨⟨i, -, e⟩, -⟩ := mem_bSet.1 hx
  have hper : IsPeriodicPt f (i + 1) x := by
    show f^[i + 1] x = x
    rw [iterate_succ_apply, e]
  have := le_cycMax (recurs_of_periodic (a := 0) (by omega) hper rfl 0)
  simp at this
  exact absurd this (not_le.2 h)

/-- From the successor of the cycle maximum no vertex above it is visited before it is reached. -/
theorem bSet_apply_cycMax (x : V) : bSet f (f (cycMax f x)) = ∅ := by
  ext y
  simp only [Finset.notMem_empty, iff_false]
  intro hy
  obtain ⟨⟨i, -, e⟩, hlt⟩ := mem_bSet.1 hy
  rw [cycMax_apply, cycMax_cycMax] at hlt
  have hl := recurs_self_of_recurs (recurs_cycMax (f := f) x)
  obtain ⟨p, hp, hper⟩ := periodic_of_recurs hl
  have hy' : Recurs f (cycMax f x) y := by
    rw [← e, ← iterate_succ_apply f i (cycMax f x)]
    exact recurs_of_periodic (a := 0) hp hper rfl (i + 1)
  have := le_cycMax hy'
  rw [cycMax_cycMax] at this
  exact absurd this (not_le.2 hlt)

end MercLib.HybridSI

end HybridSILassoProofs
