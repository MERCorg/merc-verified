import ParityGame.Defs
import ParityGame.Attractor
import ParityGame.Zielonka
import ParityGame.Proofs.Zielonka_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `zielonka_correct`'s signature drifts: Zielonka's algorithm
-- partitions the nodes of any finite parity game into the winning regions of the two players, and
-- the returned positional strategies win from every node of the respective region.
example {V : Type*} [Finite V] (G : Game V) :
    (G.zielonka.win .zero ∪ G.zielonka.win .one = Set.univ) ∧
    Disjoint (G.zielonka.win .zero) (G.zielonka.win .one) ∧
    ∀ i, ∀ v ∈ G.zielonka.win i,
      (∀ w, Relation.ReflTransGen (G.Step Set.univ i (G.zielonka.strat i)) v w →
          ∃ u, G.Step Set.univ i (G.zielonka.strat i) w u) ∧
      ∀ p : ωSequence V, p 0 = v → G.ConformingPlay Set.univ i (G.zielonka.strat i) p →
        G.PlayWonBy i p :=
  Game.zielonka_correct G
