module

public import MercLib.Algorithms.LDD.Cube
import all MercLib.Theory.LDD.Proofs.Ldd_Proofs

@[expose] public section

/-!
# Proofs: adding one vector to a list decision diagram

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/LDD.lean` (human-vetted).
-/

namespace MercLib.LDD

namespace Ldd

variable {α : Type*} [LinearOrder α]

private theorem singleton_correct : ∀ x : List α,
    (singleton x).WellFormed x.length ∧ (singleton x).denote = {x}
  | [] => ⟨rfl, rfl⟩
  | a :: x => by
    obtain ⟨hw, hd⟩ := singleton_correct x
    refine ⟨⟨?_, hw, trivial, trivial⟩, ?_⟩
    · intro h
      have : x ∈ (singleton x).denote := by rw [hd]; rfl
      rw [h] at this
      simp [denote] at this
    · simp [singleton, denote, hd]

/-- The first value of the result is the first value of `X` or the first value of the vector. -/
private theorem headAbove_unionCube {w a : α} {x : List α} (ha : w < a) :
    ∀ {X : Ldd α}, HeadAbove w X → HeadAbove w (unionCube X (a :: x))
  | zero, _ => ha
  | one, _ => ha
  | node v d r, h => by
    simp only [unionCube]
    split_ifs <;> first | exact h | exact ha

private theorem unionCube_correct : ∀ (X : Ldd α) (x : List α) (n : ℕ), X.WellFormed n →
    x.length = n → (unionCube X x).WellFormed n ∧ (unionCube X x).denote = insert x X.denote
  | X, [], n, hX, hx => by
    subst hx
    cases X with
    | zero => exact ⟨by simp [unionCube, WellFormed], by simp [unionCube, denote]⟩
    | one => exact ⟨by simp [unionCube, WellFormed], by simp [unionCube, denote]⟩
    | node v d r => exact absurd hX (by simp [WellFormed])
  | zero, a :: x, n, _, hx => by
    obtain ⟨hw, hd⟩ := singleton_correct x
    subst hx
    refine ⟨⟨fun h => by rw [h] at hd; simp [denote] at hd, hw, trivial, trivial⟩, ?_⟩
    simp [unionCube, denote, hd]
  | one, a :: x, n, hX, hx => by
    subst hx
    exact absurd hX (by simp [WellFormed])
  | node v d r, a :: x, n, hX, hx => by
    subst hx
    obtain ⟨hd0, hdw, hrw, hha⟩ := hX
    simp only [unionCube]
    split_ifs with h1 h2
    · obtain ⟨ihw, ihd⟩ := unionCube_correct r (a :: x) (x.length + 1) hrw rfl
      refine ⟨⟨hd0, hdw, ihw, headAbove_unionCube h1 hha⟩, ?_⟩
      rw [show (node v d (unionCube r (a :: x))).denote =
        (List.cons v '' d.denote) ∪ (unionCube r (a :: x)).denote from rfl, ihd]
      ext z
      simp only [denote, Set.mem_union, Set.mem_insert_iff]
      tauto
    · subst h2
      obtain ⟨ihw, ihd⟩ := unionCube_correct d x x.length hdw rfl
      refine ⟨⟨?_, ihw, hrw, hha⟩, ?_⟩
      · intro h
        have : x ∈ (unionCube d x).denote := by rw [ihd]; exact Set.mem_insert _ _
        rw [h] at this
        simp [denote] at this
      · rw [show (node v (unionCube d x) r).denote =
          (List.cons v '' (unionCube d x).denote) ∪ r.denote from rfl, ihd]
        ext z
        simp only [denote, Set.mem_union, Set.mem_insert_iff, Set.mem_image]
        constructor
        · rintro (⟨y, rfl | hy, rfl⟩ | hz)
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
          · exact Or.inr (Or.inr hz)
        · rintro (rfl | ⟨y, hy, rfl⟩ | hz)
          · exact Or.inl ⟨x, Or.inl rfl, rfl⟩
          · exact Or.inl ⟨y, Or.inr hy, rfl⟩
          · exact Or.inr hz
    · have h3 : a < v := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      obtain ⟨hw, hd⟩ := singleton_correct x
      refine ⟨⟨?_, hw, ⟨hd0, hdw, hrw, hha⟩, h3⟩, ?_⟩
      · intro h
        rw [h] at hd
        simp [denote] at hd
      · rw [show (node a (singleton x) (node v d r)).denote =
          (List.cons a '' (singleton x).denote) ∪ (node v d r).denote from rfl, hd]
        ext z
        simp [Set.mem_insert_iff]

end Ldd

open Ldd

variable {α : Type*} [LinearOrder α]

/-- **The singleton is correct.** -/
theorem singletonCorrect (x : List α) : SingletonCorrect x := singleton_correct x

/-- **Adding one vector is correct.** -/
theorem unionCubeCorrect (X : Ldd α) (x : List α) (n : ℕ) : UnionCubeCorrect X x n :=
  unionCube_correct X x n

end MercLib.LDD
