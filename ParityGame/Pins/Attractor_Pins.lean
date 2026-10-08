import ParityGame.Defs
import ParityGame.Attractor
import ParityGame.Proofs.Attractor_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `attractorCorrect`'s signature drifts (Section 2).
example {V : Type*} [Finite V] (G : Game V) (X : Set V) (i : Player) (U : Set V) :
    G.IsSubgame X → U ⊆ X →
      (U ⊆ G.attr X i U ∧ G.attr X i U ⊆ X) ∧
      G.IsSubgame (X \ G.attr X i U) ∧
      (∀ v ∈ X \ G.attr X i U, G.owner v = i → ∀ w ∈ X, G.edge v w → w ∉ G.attr X i U) ∧
      ∀ σ : Strategy V,
        (∀ v ∈ G.attr X i U, v ∉ U → G.owner v = i → σ v = G.attrStrategy X i U v) →
        ∀ p : ωSequence V, G.ConformingPlay X i σ p → p 0 ∈ G.attr X i U → ∃ n, p n ∈ U :=
  Game.attractorCorrect G X i U
