import ParityGame.Defs
import ParityGame.ProgressMeasure
import ParityGame.Proofs.ProgressMeasure_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `Game.progressMeasureSound`'s signature drifts: in a finite
-- game, a progress measure `μ` with domain `D` over ANY priority-indexed codomain `C` (each level a
-- preorder, coarser at higher priorities, well-founded strict part at odd levels) certifies that
-- its witnessing strategy `σ` wins for player `0` from every node of `D`.
example {V M : Type*} [Finite V] (G : Game V) (X : Set V) (C : Codomain M) (D : Set V)
    (μ : V → M) (σ : V → V) :
    G.IsSubgame X →
    (D ⊆ X ∧
      (∀ v ∈ D, G.owner v = .zero → σ v ∈ D ∧ G.edge v (σ v) ∧
        (C.le (G.prio v) (μ (σ v)) (μ v) ∧
          (G.prio v % 2 = 1 → ¬ C.le (G.prio v) (μ v) (μ (σ v))))) ∧
      (∀ v ∈ D, G.owner v = .one → ∀ w ∈ X, G.edge v w → w ∈ D ∧
        (C.le (G.prio v) (μ w) (μ v) ∧ (G.prio v % 2 = 1 → ¬ C.le (G.prio v) (μ v) (μ w))))) →
    ∀ v ∈ D,
      (∀ w, Relation.ReflTransGen (G.Step X .zero σ) v w → ∃ u, G.Step X .zero σ w u) ∧
      ∀ p : ωSequence V, p 0 = v → G.ConformingPlay X .zero σ p → G.PlayWonBy .zero p :=
  Game.progressMeasureSound G X C D μ σ

-- Contract pin: fails to compile if `Game.progCycleEven`'s signature drifts: for ANY codomain `C`
-- and labelling `μ`, a cycle `c 0 → … → c k = c 0` (`k ≥ 1`) all of whose edges satisfy the
-- progress condition has an even greatest priority.
example {V M : Type*} (G : Game V) (C : Codomain M) (μ : V → M) :
    ∀ (k : ℕ) (c : ℕ → V), 0 < k → c k = c 0 →
      (∀ i < k, C.le (G.prio (c i)) (μ (c (i + 1))) (μ (c i)) ∧
        (G.prio (c i) % 2 = 1 → ¬ C.le (G.prio (c i)) (μ (c i)) (μ (c (i + 1))))) →
      ∀ i < k, (∀ j < k, G.prio (c j) ≤ G.prio (c i)) → G.prio (c i) % 2 = 0 :=
  Game.progCycleEven G C μ
