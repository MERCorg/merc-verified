module

public import MercLib.ParityGame.FatalAttractor

open Cslib (ωSequence)

@[expose] public section

namespace MercLib.ParityGame

/-! Machine-generated; may be freely edited or regenerated. -/

variable {V : Type*}

section
variable (G : Game V) (X : Set V) (i : Player) (c : ℕ) (T : Set V)

theorem Game.mpre_mono {A B : Set V} (h : A ⊆ B) : G.mpre X i c T A ⊆ G.mpre X i c T B := by
  rintro v ⟨hvX, hc, (⟨ho, w, hwX, he, hw⟩ | ⟨ho, hall⟩)⟩
  · exact ⟨hvX, hc, Or.inl ⟨ho, w, hwX, he, Set.union_subset_union_left T h hw⟩⟩
  · exact ⟨hvX, hc, Or.inr ⟨ho, fun w hwX he => Set.union_subset_union_left T h (hall w hwX he)⟩⟩

theorem Game.mattrStage_succ_subset (k : ℕ) :
    G.mattrStage X i c T k ⊆ G.mattrStage X i c T (k + 1) := by
  induction k with
  | zero => exact Set.empty_subset _
  | succ k ih => exact G.mpre_mono X i c T ih

theorem Game.mattrStage_mono : Monotone (G.mattrStage X i c T) :=
  monotone_nat_of_le_succ (G.mattrStage_succ_subset X i c T)

theorem Game.mem_mattr_iff {v : V} :
    v ∈ G.mattr X i c T ↔ ∃ k, v ∈ G.mattrStage X i c T k := Iff.rfl

/-- A node of the monotone attractor lies in the stage given by its rank, the rank is positive,
    and every stage containing it is at least its rank. -/
theorem Game.mattrRank_spec {v : V} (hv : v ∈ G.mattr X i c T) :
    0 < G.mattrRank X i c T v ∧ v ∈ G.mattrStage X i c T (G.mattrRank X i c T v) ∧
      ∀ k, v ∈ G.mattrStage X i c T k → G.mattrRank X i c T v ≤ k := by
  classical
  have hv' : ∃ k, v ∈ G.mattrStage X i c T k := hv
  have hr : G.mattrRank X i c T v = Nat.find hv' := by simp [Game.mattrRank, hv']
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]
    rcases Nat.eq_zero_or_pos (Nat.find hv') with h | h
    · have := Nat.find_spec hv'
      rw [h] at this
      exact absurd this (Set.notMem_empty v)
    · exact h
  · rw [hr]; exact Nat.find_spec hv'
  · intro k hk; rw [hr]; exact Nat.find_min' hv' hk

/-- Unfolding the stage of a node at its rank. -/
theorem Game.mem_mpre_of_mattr {v : V} (hv : v ∈ G.mattr X i c T) :
    v ∈ G.mpre X i c T (G.mattrStage X i c T (G.mattrRank X i c T v - 1)) := by
  obtain ⟨hpos, hmem, -⟩ := G.mattrRank_spec X i c T hv
  obtain ⟨k, hk⟩ : ∃ k, G.mattrRank X i c T v = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at hmem ⊢
  exact hmem

theorem Game.mattr_subset_X : G.mattr X i c T ⊆ X := fun _ hv =>
  (G.mem_mpre_of_mattr X i c T hv).1

theorem Game.prio_le_of_mattr {v : V} (hv : v ∈ G.mattr X i c T) : G.prio v ≤ c :=
  (G.mem_mpre_of_mattr X i c T hv).2.1

/-- The monotone attractor strategy moves from a node of `i` along an edge inside `X` into the
    previous stage or the target. -/
theorem Game.mattrStrategy_spec {v : V} (hv : v ∈ G.mattr X i c T) (ho : G.owner v = i) :
    G.mattrStrategy X i c T v ∈ X ∧ G.edge v (G.mattrStrategy X i c T v) ∧
      G.mattrStrategy X i c T v ∈
        G.mattrStage X i c T (G.mattrRank X i c T v - 1) ∪ T := by
  have hpos := (G.mattrRank_spec X i c T hv).1
  obtain ⟨-, -, hcase⟩ := G.mem_mpre_of_mattr X i c T hv
  have hex : ∃ w ∈ X, G.edge v w ∧
      w ∈ G.mattrStage X i c T (G.mattrRank X i c T v - 1) ∪ T := by
    rcases hcase with ⟨-, h⟩ | ⟨hne, -⟩
    · exact h
    · exact absurd ho hne
  have h : 0 < G.mattrRank X i c T v ∧ ∃ w ∈ X, G.edge v w ∧
      w ∈ G.mattrStage X i c T (G.mattrRank X i c T v - 1) ∪ T := ⟨hpos, hex⟩
  simp only [Game.mattrStrategy, dite_eq_left h]
  obtain ⟨hX, he, hw⟩ := h.2.choose_spec
  exact ⟨hX, he, hw⟩

/-- Every conforming move out of the monotone attractor goes into the previous stage or the
    target. -/
theorem Game.step_of_mattr {v w : V} (hv : v ∈ G.mattr X i c T)
    (hs : G.Step X i (G.mattrStrategy X i c T) v w) :
    w ∈ G.mattrStage X i c T (G.mattrRank X i c T v - 1) ∪ T := by
  obtain ⟨-, hwX, he, hσ⟩ := hs
  by_cases ho : G.owner v = i
  · rw [hσ ho]; exact (G.mattrStrategy_spec X i c T hv ho).2.2
  · obtain ⟨-, -, hcase⟩ := G.mem_mpre_of_mattr X i c T hv
    rcases hcase with ⟨ho', -⟩ | ⟨-, hall⟩
    · exact absurd ho' ho
    · exact hall w hwX he

end

section
variable (G : Game V) (X : Set V) (c : ℕ) (T : Set V)

/-- With a fatal attractor, conforming moves stay inside `MA(T)`. -/
theorem Game.step_mem_ma (hfat : G.IsFatal X c T) {v w : V} (hv : v ∈ G.ma X c T)
    (hs : G.Step X (Player.ofPrio c) (G.mattrStrategy X (Player.ofPrio c) c T) v w) :
    w ∈ G.ma X c T := by
  rcases G.step_of_mattr X _ c T hv hs with h | h
  · exact ⟨_, h⟩
  · exact hfat h

/-- From every node of `MA(T)`, a conforming play reaches `T` after at least one step. -/
theorem Game.exists_visit_target {p : ωSequence V}
    (hp : G.ConformingPlay X (Player.ofPrio c) (G.mattrStrategy X (Player.ofPrio c) c T) p) :
    ∀ r N, G.mattrRank X (Player.ofPrio c) c T (p N) = r → p N ∈ G.ma X c T →
      ∃ n, N < n ∧ p n ∈ T := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro N hr hN
    rcases G.step_of_mattr X _ c T hN (hp N) with h | h
    · have hlt : G.mattrRank X (Player.ofPrio c) c T (p (N + 1)) < r := by
        have hle := (G.mattrRank_spec X _ c T ⟨_, h⟩).2.2 _ h
        have hpos := (G.mattrRank_spec X _ c T hN).1
        omega
      obtain ⟨n, hn, hT⟩ := ih _ hlt (N + 1) rfl ⟨_, h⟩
      exact ⟨n, by omega, hT⟩
    · exact ⟨N + 1, by omega, h⟩

/-- Fatal attractors (Theorem 2 of [Huth2014]): if `T ⊆ X` consists of nodes of priority `c` and
    is fatal, then the player `Player.ofPrio c` favoured by `c` wins from every node of the
    monotone attractor `MA(T)` using the monotone attractor strategy. -/
theorem Game.fatalAttractorWins (G : Game V) (X : Set V) (c : ℕ) (T : Set V) :
    G.FatalAttractorWins X c T := by
  intro hsub _ hTc hfat v hv
  set i := Player.ofPrio c
  set σ := G.mattrStrategy X i c T
  refine ⟨?_, ?_⟩
  · intro w hw
    have hwM : w ∈ G.ma X c T := by
      induction hw with
      | refl => exact hv
      | tail _ hs ih => exact G.step_mem_ma X c T hfat ih hs
    have hwX := G.mattr_subset_X X i c T hwM
    by_cases ho : G.owner w = i
    · obtain ⟨hX, he, -⟩ := G.mattrStrategy_spec X i c T hwM ho
      exact ⟨σ w, hwX, hX, he, fun _ => rfl⟩
    · obtain ⟨u, huX, he⟩ := hsub w hwX
      exact ⟨u, hwX, huX, he, fun h => absurd h ho⟩
  · intro p hp0 hp
    have hM : ∀ n, p n ∈ G.ma X c T := by
      intro n
      induction n with
      | zero => rw [hp0]; exact hv
      | succ n ih => exact G.step_mem_ma X c T hfat ih (hp n)
    refine ⟨c, ⟨?_, ?_⟩, rfl⟩
    · show ∃ᶠ k in Filter.atTop, G.prio (p k) = c
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn, hT⟩ := G.exists_visit_target X c T hp _ N rfl (hM N)
      exact ⟨n, hn.le, hTc _ hT⟩
    · rintro m (hm : ∃ᶠ k in Filter.atTop, G.prio (p k) = m)
      obtain ⟨k, hk⟩ := hm.exists
      rw [← hk]
      exact G.prio_le_of_mattr X i c T (hM k)

end

end MercLib.ParityGame
