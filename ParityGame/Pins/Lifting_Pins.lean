import ParityGame.Defs
import ParityGame.ProgressMeasure
import ParityGame.TwoSidedLifting
import ParityGame.Lifting
import ParityGame.Proofs.Lifting_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `Game.liftMonotone`'s signature drifts: for an
-- order-respecting interpretation `val` of the values, the lifting operator is monotone.
example {V M T : Type*} [CompleteLinearOrder T] (G : Game V) (X : Set V) (C : Codomain M)
    (val : T → M) :
    (∀ p a b, a ≠ ⊤ → b ≠ ⊤ → a ≤ b → C.le p (val a) (val b)) →
      Monotone (G.lift X C val) :=
  Game.liftMonotone G X C val

-- Contract pin: fails to compile if `Game.liftingLfpCorrect`'s signature drifts: in a finite
-- game, for an order-respecting `val` whose values are complete for the subgame `X` (every
-- positional winning strategy on a closed set has a progress measure with proper values), the
-- lifting operator has a least fixpoint, and every least fixpoint is not `⊤` exactly at the
-- nodes won by player `0`.
example {V M T : Type*} [Finite V] [CompleteLinearOrder T] [WellFoundedLT T] (G : Game V)
    (X : Set V) (C : Codomain M) (val : T → M) :
    G.IsSubgame X → (∀ p a b, a ≠ ⊤ → b ≠ ⊤ → a ≤ b → C.le p (val a) (val b)) →
    (∀ (W : Set V) (σ : V → V), (∀ v ∈ W, G.WinsFrom X .zero σ v) →
      (∀ v ∈ W, ∀ w, G.Step X .zero σ v w → w ∈ W) →
      ∃ μ : V → T, (∀ v ∈ W, μ v ≠ ⊤) ∧ G.IsProgressMeasure X C W (fun v => val (μ v)) σ) →
    (∃ μ, IsLeast {μ | G.lift X C val μ = μ} μ) ∧
    ∀ μ, IsLeast {μ | G.lift X C val μ = μ} μ → ∀ v, μ v ≠ ⊤ ↔ ∃ σ, G.WinsFrom X .zero σ v :=
  Game.liftingLfpCorrect G X C val

-- Contract pin: fails to compile if `Game.chainLiftingCorrect`'s signature drifts: lifting over
-- any representation of the chain-tree leaves of `X` (plus `⊤`), with the truncated
-- lexicographic codomain of depth `Game.chainDepth`, has a least fixpoint, and every least
-- fixpoint is not `⊤` exactly on player `0`'s winning region in `X`.
example {V T : Type*} [Finite V] [CompleteLinearOrder T] [WellFoundedLT T] (G : Game V)
    (X : Set V) (C : Codomain (ℕ → ℕ)) (val : T → ℕ → ℕ) :
    G.IsSubgame X → (∀ p a b, C.le p a b ↔ LexLE (G.chainDepth X p) a b) →
    ((∀ a b, a ≠ ⊤ → b ≠ ⊤ → (a ≤ b ↔ LexLE (2 * G.height X) (val a) (val b))) ∧
      (∀ a, a ≠ ⊤ → G.IsChainLeaf X (val a)) ∧
      (∀ l, G.IsChainLeaf X l → ∃ a, a ≠ ⊤ ∧ val a = l)) →
    (∃ μ, IsLeast {μ | G.lift X C val μ = μ} μ) ∧
    ∀ μ, IsLeast {μ | G.lift X C val μ = μ} μ → ∀ v, μ v ≠ ⊤ ↔ ∃ σ, G.WinsFrom X .zero σ v :=
  Game.chainLiftingCorrect G X C val

-- Contract pin: fails to compile if `Game.chainReprExists`'s signature drifts: the chain tree of
-- every subgame of a finite game has a representation as a complete linear order with
-- well-founded `<` (so `Game.chainLiftingCorrect` is not vacuous).
example {V : Type*} [Finite V] (G : Game V) (X : Set V) :
    ∃ (T : Type) (_ : CompleteLinearOrder T) (_ : WellFoundedLT T) (val : T → ℕ → ℕ),
      (∀ a b, a ≠ ⊤ → b ≠ ⊤ → (a ≤ b ↔ LexLE (2 * G.height X) (val a) (val b))) ∧
      (∀ a, a ≠ ⊤ → G.IsChainLeaf X (val a)) ∧
      (∀ l, G.IsChainLeaf X l → ∃ a, a ≠ ⊤ ∧ val a = l) :=
  Game.chainReprExists G X

-- Contract pin: fails to compile if `Game.accelSound`'s signature drifts: below a fixpoint `ν`,
-- for a finite `S ⊆ X`, an in-`X` choice `τ` of player `1` on `S`, and all cycles inside `S` of
-- the graphs (any edge into `X` for player `0`, `τ` for player `1`) odd-max, the minimum over
-- paths inside `S` to an exit of the composed least progressing values is `≤ ν` on `S`.
example {V M T : Type*} [Finite V] [CompleteLinearOrder T] [WellFoundedLT T] (G : Game V)
    (X : Set V) (C : Codomain M) (val : T → M) (ν μ : V → T) (S : Set V) (τ : V → V) :
    G.IsSubgame X → (∀ p a b, a ≠ ⊤ → b ≠ ⊤ → a ≤ b → C.le p (val a) (val b)) →
    G.lift X C val ν = ν → μ ≤ ν → S ⊆ X → S.Finite →
    (∀ s ∈ S, G.owner s = .one → τ s ∈ X ∧ G.edge s (τ s)) →
    (∀ f : V → V, (∀ s ∈ S, G.owner s = .zero → G.edge s (f s) ∧ f s ∈ X) →
      (∀ s ∈ S, G.owner s = .one → f s = τ s) → G.OddCyclesIn f S) →
    ∀ s ∈ S, sInf {t | G.ExitPath X S C val τ μ s t} ≤ ν s :=
  Game.accelSound G X C val ν μ S τ
