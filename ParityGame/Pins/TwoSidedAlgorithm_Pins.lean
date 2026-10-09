import ParityGame.Defs
import ParityGame.Attractor
import ParityGame.ProgressMeasure
import ParityGame.TwoSidedAlgorithm
import ParityGame.Proofs.TwoSidedAlgorithm_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `Game.dualWinsFrom`'s signature drifts: a positional strategy
-- wins for `i` in the dual subgame `X` (priorities `+ 1`, owners swapped) exactly when it wins
-- for the opponent in the original subgame `X`.
example {V : Type*} (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) (v : V) :
    G.dual.WinsFrom X i σ v ↔ G.WinsFrom X i.opp σ v :=
  Game.dualWinsFrom G X i σ v

-- Contract pin: the dual game is the one of the Rust `View` for the odd player.
example {V : Type*} (G : Game V) (v w : V) :
    G.dual.owner v = (G.owner v).opp ∧ (G.dual.edge v w ↔ G.edge v w) ∧
      G.dual.prio v = G.prio v + 1 :=
  ⟨rfl, Iff.rfl, rfl⟩

-- Contract pin: fails to compile if `Game.dominionRemoval`'s signature drifts: removing the
-- `i`-attractor `A` of an `i`-dominion `D` of the subgame `X` leaves a subgame, `A` is again an
-- `i`-dominion, and every remaining node has the same winners in `X` and in `X \ A`.
example {V : Type*} [Finite V] (G : Game V) (X : Set V) (i : Player) (D : Set V)
    (σ : Strategy V) :
    G.IsSubgame X →
    (D ⊆ X ∧ (∀ v ∈ D, G.WinsFrom X i σ v) ∧ ∀ v ∈ D, ∀ w, G.Step X i σ v w → w ∈ D) →
    (∃ τ, G.attr X i D ⊆ X ∧ (∀ v ∈ G.attr X i D, G.WinsFrom X i τ v) ∧
      ∀ v ∈ G.attr X i D, ∀ w, G.Step X i τ v w → w ∈ G.attr X i D) ∧
    G.IsSubgame (X \ G.attr X i D) ∧
    ∀ v ∈ X \ G.attr X i D, ∀ j,
      (∃ τ, G.WinsFrom X j τ v) ↔ ∃ τ, G.WinsFrom (X \ G.attr X i D) j τ v :=
  Game.dominionRemoval G X i D σ

-- Contract pin: fails to compile if `Game.certificationSound`'s signature drifts: a progress
-- measure of player `i` (in `G` for `0`, in the dual game for `1`), over any codomain, on `D`
-- witnessed by `σ` makes `D` a dominion of `i` witnessed by `σ`.
example {V M : Type*} [Finite V] (G : Game V) (X : Set V) (i : Player) (C : Codomain M)
    (D : Set V) (μ : V → M) (σ : Strategy V) :
    G.IsSubgame X → (G.forPlayer i).IsProgressMeasure X C D μ σ →
    D ⊆ X ∧ (∀ v ∈ D, G.WinsFrom X i σ v) ∧ ∀ v ∈ D, ∀ w, G.Step X i σ v w → w ∈ D :=
  Game.certificationSound G X i C D μ σ

-- Contract pin: `Game.forPlayer` is `G` for player `0` and the dual game for player `1`.
example {V : Type*} (G : Game V) : G.forPlayer .zero = G ∧ G.forPlayer .one = G.dual :=
  ⟨rfl, rfl⟩

-- Contract pin: fails to compile if `Game.certifiedSetGreatest`'s signature drifts: the union of
-- all progress-measure domains of `μ` is itself one.
example {V M : Type*} (G : Game V) (X : Set V) (C : Codomain M) (μ : V → M) :
    (∃ σ, G.IsProgressMeasure X C {v | ∃ D σ, G.IsProgressMeasure X C D μ σ ∧ v ∈ D} μ σ) ∧
    ∀ D σ, G.IsProgressMeasure X C D μ σ →
      D ⊆ {v | ∃ D σ, G.IsProgressMeasure X C D μ σ ∧ v ∈ D} :=
  Game.certifiedSetGreatest G X C μ

-- Contract pin: fails to compile if `Game.simultaneousRemoval`'s signature drifts: player `1`'s
-- certified set stays certified after removing the `0`-attractor of player `0`'s certified set.
example {V M N : Type*} [Finite V] (G : Game V) (X : Set V) (C₀ : Codomain M) (D₀ : Set V)
    (μ₀ : V → M) (σ₀ : Strategy V) (C₁ : Codomain N) (D₁ : Set V) (μ₁ : V → N)
    (σ₁ : Strategy V) :
    G.IsSubgame X → G.IsProgressMeasure X C₀ D₀ μ₀ σ₀ → G.dual.IsProgressMeasure X C₁ D₁ μ₁ σ₁ →
      G.dual.IsProgressMeasure (X \ G.attr X .zero D₀) C₁ D₁ μ₁ σ₁ :=
  Game.simultaneousRemoval G X C₀ D₀ μ₀ σ₀ C₁ D₁ μ₁ σ₁

-- Contract pin: fails to compile if `Game.algInvStep`'s signature drifts: every removal step
-- preserves the invariant.
example {V : Type*} [Finite V] (G : Game V) (s s' : AlgState V) :
    (G.IsSubgame s.rest ∧
      (∀ i v, v ∈ s.won i ↔ v ∉ s.rest ∧ ∃ σ, G.WinsFrom Set.univ i σ v) ∧
      ∀ v ∈ s.rest, ∀ i, (∃ σ, G.WinsFrom s.rest i σ v) ↔ ∃ σ, G.WinsFrom Set.univ i σ v) →
    G.RemovalStep s s' →
    (G.IsSubgame s'.rest ∧
      (∀ i v, v ∈ s'.won i ↔ v ∉ s'.rest ∧ ∃ σ, G.WinsFrom Set.univ i σ v) ∧
      ∀ v ∈ s'.rest, ∀ i, (∃ σ, G.WinsFrom s'.rest i σ v) ↔ ∃ σ, G.WinsFrom Set.univ i σ v) :=
  Game.algInvStep G s s'

-- Contract pin: fails to compile if `Game.twoSidedCorrect`'s signature drifts: every run of
-- removal steps from the initial state that ends in a completion step returns exactly the
-- winning regions of the whole game.
example {V : Type*} [Finite V] (G : Game V) :
    ∀ (s : AlgState V) (r : Player → Set V),
      Relation.ReflTransGen G.RemovalStep ⟨fun _ => ∅, Set.univ⟩ s → G.Completion s r →
      ∀ i v, v ∈ r i ↔ ∃ σ, G.WinsFrom Set.univ i σ v :=
  Game.twoSidedCorrect G

-- Contract pin: fails to compile if `Game.removalShrinks`'s signature drifts.
example {V : Type*} (G : Game V) (s s' : AlgState V) :
    G.RemovalStep s s' → s'.rest ⊂ s.rest :=
  Game.removalShrinks G s s'

-- Contract pin: fails to compile if `Game.removalBound`'s signature drifts: at most `|V|`
-- removal steps (restarts) in any run from the initial state.
example {V : Type*} [Finite V] (G : Game V) :
    ∀ (run : ℕ → AlgState V) (N : ℕ), run 0 = ⟨fun _ => ∅, Set.univ⟩ →
      (∀ k < N, G.RemovalStep (run k) (run (k + 1))) → N ≤ Nat.card V :=
  Game.removalBound G
