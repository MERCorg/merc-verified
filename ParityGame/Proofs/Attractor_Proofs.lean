module

public import ParityGame.Attractor
public import ParityGame.Proofs.Defs_Proofs
public import Mathlib.Data.Fintype.Order

open Cslib (ωSequence)

@[expose] public section AttractorProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorem below live in `ParityGame/Pins/Attractor_Pins.lean`. -/

variable {V : Type*}

section
variable (G : Game V) (X : Set V) (i : Player) (U : Set V)

theorem Game.attrStage_succ_mem {k : ℕ} {v : V} (h : v ∈ G.attrStage X i U (k + 1))
    (hv : v ∉ G.attrStage X i U k) :
    v ∈ X ∧ ((G.owner v = i ∧ ∃ w ∈ G.attrStage X i U k, G.edge v w) ∨
      (G.owner v ≠ i ∧ ∀ w ∈ X, G.edge v w → w ∈ G.attrStage X i U k)) := by
  simp only [Game.attrStage, Set.mem_union, Set.mem_setOf_eq] at h
  rcases h with h | h
  · exact absurd h hv
  · exact h

theorem Game.attrStage_mono : Monotone (G.attrStage X i U) :=
  monotone_nat_of_le_succ fun k => by
    intro _ hv
    simp only [Game.attrStage, Set.mem_union]
    exact Or.inl hv

theorem Game.subset_attr : U ⊆ G.attr X i U := fun _ hv => ⟨0, hv⟩

theorem Game.attrStage_subset (hU : U ⊆ X) (k : ℕ) : G.attrStage X i U k ⊆ X := by
  induction k with
  | zero => exact hU
  | succ k ih =>
    intro v hv
    simp only [Game.attrStage, Set.mem_union, Set.mem_setOf_eq] at hv
    rcases hv with hv | ⟨hvX, -⟩
    · exact ih hv
    · exact hvX

theorem Game.attr_subset (hU : U ⊆ X) : G.attr X i U ⊆ X := by
  rintro v ⟨k, hk⟩
  exact G.attrStage_subset X i U hU k hk

/-- A node of `i` with an edge into the attractor is in the attractor. -/
theorem Game.mem_attr_of_owner {v w : V} (hv : v ∈ X) (ho : G.owner v = i)
    (he : G.edge v w) (hw : w ∈ G.attr X i U) : v ∈ G.attr X i U := by
  obtain ⟨k, hk⟩ := hw
  refine ⟨k + 1, ?_⟩
  simp only [Game.attrStage, Set.mem_union, Set.mem_setOf_eq]
  exact Or.inr ⟨hv, Or.inl ⟨ho, w, hk, he⟩⟩

/-- All the attractor lies in a single stage (finite games). -/
theorem Game.exists_attr_subset_stage [Finite V] : ∃ K, G.attr X i U ⊆ G.attrStage X i U K := by
  classical
  let f : V → ℕ := fun w => if h : w ∈ G.attr X i U then h.choose else 0
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun w hw => ?_⟩
  have := hM w
  simp only [f, dif_pos hw] at this
  exact G.attrStage_mono X i U this hw.choose_spec

/-- A node of `1 - i` all of whose successors in `X` are in the attractor is in the attractor. -/
theorem Game.mem_attr_of_opp [Finite V] {v : V} (hv : v ∈ X) (ho : G.owner v ≠ i)
    (h : ∀ w ∈ X, G.edge v w → w ∈ G.attr X i U) : v ∈ G.attr X i U := by
  obtain ⟨K, hK⟩ := G.exists_attr_subset_stage X i U
  refine ⟨K + 1, ?_⟩
  simp only [Game.attrStage, Set.mem_union, Set.mem_setOf_eq]
  exact Or.inr ⟨hv, Or.inr ⟨ho, fun w hw he => hK (h w hw he)⟩⟩

theorem Game.attrRank_eq {k : ℕ} {v : V} (h : v ∈ G.attrStage X i U (k + 1))
    (hv : v ∉ G.attrStage X i U k) : G.attrRank X i U v = k + 1 := by
  classical
  have hex : ∃ k, v ∈ G.attrStage X i U k := ⟨_, h⟩
  unfold Game.attrRank
  rw [dif_pos hex, Nat.find_eq_iff]
  refine ⟨h, fun n hn hvn => hv ?_⟩
  exact G.attrStage_mono X i U (by omega) hvn

/-- The attractor strategy moves a node first reached at stage `k + 1` into stage `k`. -/
theorem Game.attrStrategy_spec {k : ℕ} {v : V} (h : v ∈ G.attrStage X i U (k + 1))
    (hv : v ∉ G.attrStage X i U k) (ho : G.owner v = i) :
    G.attrStrategy X i U v ∈ G.attrStage X i U k ∧ G.edge v (G.attrStrategy X i U v) := by
  classical
  obtain ⟨-, h1 | ⟨h2, -⟩⟩ := G.attrStage_succ_mem X i U h hv
  · have hr := G.attrRank_eq X i U h hv
    have hc : 0 < G.attrRank X i U v ∧
        ∃ w ∈ G.attrStage X i U (G.attrRank X i U v - 1), G.edge v w := by
      rw [hr]; exact ⟨by omega, by simpa using h1.2⟩
    unfold Game.attrStrategy
    rw [dif_pos hc]
    have h3 := hc.2.choose_spec
    exact ⟨(show G.attrRank X i U v - 1 = k by omega) ▸ h3.1, h3.2⟩
  · exact absurd ho h2

/-- Every play conforming to an attractor strategy reaches `U` from the attractor. -/
theorem Game.reach_of_mem_stage (σ : Strategy V)
    (hσ : ∀ v ∈ G.attr X i U, v ∉ U → G.owner v = i → σ v = G.attrStrategy X i U v)
    (p : ωSequence V) (hp : G.ConformingPlay X i σ p) :
    ∀ k N, p N ∈ G.attrStage X i U k → ∃ n, N ≤ n ∧ p n ∈ U := by
  intro k
  induction k with
  | zero => exact fun N h => ⟨N, le_rfl, h⟩
  | succ k ih =>
    intro N hN
    by_cases hk : p N ∈ G.attrStage X i U k
    · exact ih N hk
    · obtain ⟨hX, hc⟩ := G.attrStage_succ_mem X i U hN hk
      obtain ⟨-, hnX, he, hs⟩ := hp N
      have hnext : p (N + 1) ∈ G.attrStage X i U k := by
        rcases hc with ⟨ho, -⟩ | ⟨-, hall⟩
        · have hU : p N ∉ U := fun hU => hk (G.attrStage_mono X i U (Nat.zero_le k) hU)
          have := hσ _ ⟨_, hN⟩ hU ho
          rw [hs ho, this]
          exact (G.attrStrategy_spec X i U hN hk ho).1
        · exact hall _ hnX he
      obtain ⟨n, hn, hnU⟩ := ih (N + 1) hnext
      exact ⟨n, by omega, hnU⟩

/-- Nodes of `i` in the attractor (outside `U`) are moved by the attractor strategy to the
    attractor. -/
theorem Game.attrStrategy_mem {v : V} (hv : v ∈ G.attr X i U) (hvU : v ∉ U)
    (ho : G.owner v = i) :
    G.attrStrategy X i U v ∈ G.attr X i U ∧ G.edge v (G.attrStrategy X i U v) := by
  obtain ⟨k, hk⟩ := hv
  induction k with
  | zero => exact absurd hk hvU
  | succ k ih =>
    by_cases hk' : v ∈ G.attrStage X i U k
    · exact ih hk'
    · have := G.attrStrategy_spec X i U hk hk' ho
      exact ⟨⟨k, this.1⟩, this.2⟩

/-- Nodes of `1 - i` in the attractor (outside `U`) have all their successors in `X` in the
    attractor. -/
theorem Game.attr_opp_closed {v : V} (hv : v ∈ G.attr X i U) (hvU : v ∉ U)
    (ho : G.owner v ≠ i) : ∀ w ∈ X, G.edge v w → w ∈ G.attr X i U := by
  obtain ⟨k, hk⟩ := hv
  induction k with
  | zero => exact absurd hk hvU
  | succ k ih =>
    by_cases hk' : v ∈ G.attrStage X i U k
    · exact ih hk'
    · obtain ⟨-, h1 | ⟨-, h2⟩⟩ := G.attrStage_succ_mem X i U hk hk'
      · exact absurd h1.1 ho
      · exact fun w hw he => ⟨k, h2 w hw he⟩

end

/-- Contract for the attractor (Section 2). -/
theorem Game.attractorCorrect (G : Game V) [Finite V] (X : Set V) (i : Player) (U : Set V) :
    G.AttractorCorrect X i U := by
  intro hX hU
  have htrap : ∀ v ∈ X \ G.attr X i U, G.owner v = i → ∀ w ∈ X, G.edge v w →
      w ∉ G.attr X i U := fun v hv ho w hw he hwa =>
    hv.2 (G.mem_attr_of_owner X i U hv.1 ho he hwa)
  refine ⟨⟨G.subset_attr X i U, G.attr_subset X i U hU⟩, ?_, htrap, ?_⟩
  · intro v hv
    by_cases ho : G.owner v = i
    · obtain ⟨w, hw, he⟩ := hX v hv.1
      exact ⟨w, ⟨hw, htrap v hv ho w hw he⟩, he⟩
    · by_contra hcon
      refine hv.2 (G.mem_attr_of_opp X i U hv.1 ho fun w hw he => ?_)
      by_contra hwa
      exact hcon ⟨w, ⟨hw, hwa⟩, he⟩
  · intro σ hσ p hp h0
    obtain ⟨k, hk⟩ := h0
    obtain ⟨n, -, hn⟩ := G.reach_of_mem_stage X i U σ hσ p hp k 0 hk
    exact ⟨n, hn⟩

end ParityGame

end AttractorProofs
