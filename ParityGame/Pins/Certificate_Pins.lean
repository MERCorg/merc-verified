import ParityGame.Certificate
import ParityGame.Proofs.Certificate_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `certSound`'s signature drifts: if both labellings of `c` are
-- certificate labellings (the second one in the dual game) and their domains cover all nodes,
-- then `D₀` is exactly the set of nodes won by player `0` and `D₁` exactly the set won by player
-- `1`.
example {V : Type*} [Finite V] (G : Game V) (c : Game.Cert V) :
    G.CertValid c → ∀ v, (v ∈ c.D₀ ↔ G.Wins Set.univ .zero v) ∧
      (v ∈ c.D₁ ↔ G.Wins Set.univ .one v) :=
  Game.certSound G c

-- Contract pin: fails to compile if `certComplete`'s signature drifts: every finite game has a
-- valid certificate whose labels have at most `2 * height` non-zero coordinates, each at most the
-- number of nodes, with the height (of the game and of its dual) at most the number of nodes.
example {V : Type*} [Finite V] (G : Game V) :
    G.height Set.univ ≤ Nat.card V ∧ G.dual.height Set.univ ≤ Nat.card V ∧
    ∃ c : Game.Cert V, G.CertValid c ∧
      (∀ v ∈ c.D₀, ∀ i, c.μ₀ v i ≤ Nat.card V ∧ (2 * G.height Set.univ ≤ i → c.μ₀ v i = 0)) ∧
      (∀ v ∈ c.D₁, ∀ i,
        c.μ₁ v i ≤ Nat.card V ∧ (2 * G.dual.height Set.univ ≤ i → c.μ₁ v i = 0)) :=
  Game.certComplete G
