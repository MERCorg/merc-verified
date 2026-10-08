import ParityGame.Transform
import ParityGame.Proofs.Transform_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `solves_of_withPrio`'s signature drifts: a solution of the game
-- with changed priorities is a solution of the original when no play changes winner.
example {V : Type*} (G : Game V) (X : Set V) (f : V → ℕ) :
    (∀ p : ωSequence V, (∀ n, p n ∈ X ∧ G.edge (p n) (p (n + 1))) →
        ∀ i, (G.withPrio f).PlayWonBy i p ↔ G.PlayWonBy i p) →
      ∀ r : Solution V, (G.withPrio f).Solves X r → G.Solves X r :=
  G.solves_of_withPrio X f

-- Contract pin: fails to compile if `compressionSound`'s signature drifts (Section 3.3).
example {V : Type*} [Finite V] (G : Game V) (X : Set V) :
    ∀ p : ωSequence V, (∀ n, p n ∈ X ∧ G.edge (p n) (p (n + 1))) →
      ∀ i, (G.withPrio (compress (G.prio '' X) ∘ G.prio)).PlayWonBy i p ↔ G.PlayWonBy i p :=
  G.compressionSound X

-- Contract pin: fails to compile if `compress_isCompression`'s signature drifts (Section 3.3).
example (S : Set ℕ) : S.Nonempty →
    (∀ x ∈ S, ∀ y ∈ S, x ≤ y → compress S x ≤ compress S y) ∧
    (∀ x ∈ S, compress S x ≤ x) ∧
    (∀ x ∈ S, compress S x % 2 = x % 2) ∧
    (∀ x ∈ S, ∀ y ∈ S, compress S x + 1 < compress S y →
      ∃ z ∈ S, compress S x < compress S z ∧ compress S z < compress S y) ∧
    (∃ x ∈ S, compress S x < 2) :=
  compress_isCompression S

-- Contract pin: fails to compile if `propagationSound`'s signature drifts (Section 3.4).
example {V : Type*} [Finite V] (G : Game V) (X : Set V) :
    (∀ p : ωSequence V, (∀ n, p n ∈ X ∧ G.edge (p n) (p (n + 1))) →
      ∀ i, (G.withPrio (G.propagateBwd X)).PlayWonBy i p ↔ G.PlayWonBy i p) ∧
    (∀ p : ωSequence V, (∀ n, p n ∈ X ∧ G.edge (p n) (p (n + 1))) →
      ∀ i, (G.withPrio (G.propagateFwd X)).PlayWonBy i p ↔ G.PlayWonBy i p) :=
  G.propagationSound X
