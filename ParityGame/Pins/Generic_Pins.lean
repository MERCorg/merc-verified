import ParityGame.Generic
import ParityGame.Proofs.Generic_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `genericSolve_correct`'s signature drifts (Section 3.5): the
-- generic solver with any sound backend solves every finite parity game.
example {V : Type*} [Finite V] (G : Game V) (S : Game V → Set V → Solution V) :
    (∀ (H : Game V) (X : Set V), H.IsSubgame X → H.Solves X (S H X)) →
      G.Solves Set.univ (G.genericSolve S) :=
  G.genericSolve_correct S

-- Contract pin: fails to compile if `genericSolve_zielonka_correct`'s signature drifts: the
-- generic solver with Zielonka's algorithm as backend partitions the nodes of any finite parity
-- game into the winning regions and returns winning strategies for both players.
example {V : Type*} [Finite V] (G : Game V) :
    (G.genericSolve zielonkaBackend).win .zero ∪ (G.genericSolve zielonkaBackend).win .one
        = Set.univ ∧
    Disjoint ((G.genericSolve zielonkaBackend).win .zero)
      ((G.genericSolve zielonkaBackend).win .one) ∧
    ∀ i, ∀ v ∈ (G.genericSolve zielonkaBackend).win i,
      (∀ w, Relation.ReflTransGen
          (G.Step Set.univ i ((G.genericSolve zielonkaBackend).strat i)) v w →
        ∃ u, G.Step Set.univ i ((G.genericSolve zielonkaBackend).strat i) w u) ∧
      ∀ p : ωSequence V, p 0 = v →
        G.ConformingPlay Set.univ i ((G.genericSolve zielonkaBackend).strat i) p →
          G.PlayWonBy i p :=
  G.genericSolve_zielonka_correct
