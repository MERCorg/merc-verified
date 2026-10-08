import ParityGame.Special
import ParityGame.Proofs.Special_Proofs
import ParityGame.Proofs.Generic_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `selfCycleSolve_correct`'s signature drifts (Section 3.2).
example {V : Type*} (G : Game V) (X : Set V) (v : V) :
    G.IsSubgame X → G.IsSelfCycle X v →
      G.WinsFrom X (Player.ofPrio (G.prio v))
        ((G.selfCycleSolve v).strat (Player.ofPrio (G.prio v))) v :=
  G.selfCycleSolve_correct X v

-- Contract pin: fails to compile if `oneParitySolve_correct`'s signature drifts (Section 3.2).
example {V : Type*} [Finite V] (G : Game V) (C : Set V) (i : Player) :
    G.IsSubgame C → (∀ v ∈ C, Player.ofPrio (G.prio v) = i) →
      G.Solves C (G.oneParitySolve C i) :=
  G.oneParitySolve_correct C i

-- Contract pin: fails to compile if `onePlayerSolve_correct`'s signature drifts (Section 3.2).
example {V : Type*} [Finite V] (G : Game V) (C : Set V) (i : Player) :
    G.IsSubgame C → (∀ u ∈ C, ∀ v ∈ C, G.Reach C u v) →
      (∀ v ∈ C, G.owner v ≠ i → ∀ w ∈ C, ∀ w' ∈ C, G.edge v w → G.edge v w' → w = w') →
        G.Solves C (G.onePlayerSolve C i) :=
  G.onePlayerSolve_correct C i
