import ParityGame.Defs
import ParityGame.ProgressMeasure
import ParityGame.TwoSidedLifting
import ParityGame.Proofs.TwoSidedLifting_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `truncLexCodomainAxioms`' signature drifts: for every
-- antitone `depth`, comparing tuples lexicographically on their first `depth p` coordinates is a
-- preorder at every level, coarser at higher levels, with a well-founded strict part.
example (depth : ℕ → ℕ) :
    Antitone depth →
    (∀ p a, LexLE (depth p) a a) ∧
    (∀ p a b c, LexLE (depth p) a b → LexLE (depth p) b c → LexLE (depth p) a c) ∧
    (∀ p q a b, p ≤ q → LexLE (depth p) a b → LexLE (depth q) a b) ∧
    (∀ p, WellFounded (fun a b => LexLE (depth p) a b ∧ ¬ LexLE (depth p) b a)) :=
  truncLexCodomainAxioms depth

-- Contract pin: the codomain built from those axioms compares exactly by `LexLE (depth p)`.
example (depth : ℕ → ℕ) (hd : Antitone depth) (p : ℕ) (a b : ℕ → ℕ) :
    (truncLexCodomain depth hd).le p a b ↔ LexLE (depth p) a b :=
  Iff.rfl

-- Contract pin: fails to compile if `Game.funCycleEven`'s signature drifts: if the progress
-- condition (any codomain, any labelling) holds on every edge `s → f s` of a finite non-empty set
-- `S` closed under `f`, some `f`-cycle in `S` has an even greatest priority.
example {V M : Type*} (G : Game V) (C : Codomain M) (μ : V → M) (f : V → V) (S : Set V) :
    S.Finite → S.Nonempty → (∀ s ∈ S, f s ∈ S) → (∀ s ∈ S, G.Prog C μ s (f s)) →
      ∃ s ∈ S, ∃ k, 0 < k ∧ f^[k] s = s ∧
        ∃ i < k, (∀ j < k, G.prio (f^[j] s) ≤ G.prio (f^[i] s)) ∧ G.prio (f^[i] s) % 2 = 0 :=
  Game.funCycleEven G C μ f S

-- Contract pin: fails to compile if `Game.funExit`'s signature drifts: if the progress condition
-- holds on every edge `s → f s` from a finite non-empty `S` all of whose `f`-cycles inside `S`
-- have an odd maximum, then `f` leaves `S`.
example {V M : Type*} (G : Game V) (C : Codomain M) (μ : V → M) (f : V → V) (S : Set V) :
    S.Finite → S.Nonempty → (∀ s ∈ S, G.Prog C μ s (f s)) →
      (∀ s ∈ S, ∀ k, 0 < k → f^[k] s = s → (∀ j < k, f^[j] s ∈ S) →
        ∀ i < k, (∀ j < k, G.prio (f^[j] s) ≤ G.prio (f^[i] s)) → G.prio (f^[i] s) % 2 = 1) →
      ∃ s ∈ S, f s ∉ S :=
  Game.funExit G C μ f S

-- Contract pin: fails to compile if `Game.strategyExit`'s signature drifts: for a progress
-- measure with domain `D` witnessed by `σ` and any choice `τ` of in-`X` successors for player
-- `1`'s nodes, the functional graph (`σ` on player `0`, `τ` on player `1`) leaves every finite
-- non-empty `S ⊆ D` all of whose cycles inside `S` have an odd maximum.
example {V M : Type*} (G : Game V) (X : Set V) (C : Codomain M) (D : Set V) (μ : V → M)
    (σ τ : V → V) (S : Set V) :
    G.IsProgressMeasure X C D μ σ → S ⊆ D → S.Finite → S.Nonempty →
      (∀ v ∈ S, G.owner v = .one → τ v ∈ X ∧ G.edge v (τ v)) →
      G.OddCyclesIn (fun v => if G.owner v = .zero then σ v else τ v) S →
      ∃ s ∈ S, (if G.owner s = .zero then σ s else τ s) ∉ S :=
  Game.strategyExit G X C D μ σ τ S

-- Contract pin: fails to compile if `Game.chainTreeComplete`'s signature drifts: in a finite
-- game, for the truncated lexicographic codomain of depth `Game.chainDepth`, every positional
-- strategy `σ` of player `0` winning from all nodes of a `σ`-closed `W` is witnessed by a progress
-- measure on `W` whose values are chain-tree leaves.
example {V : Type*} [Finite V] (G : Game V) (X : Set V) (C : Codomain (ℕ → ℕ)) :
    (∀ p a b, C.le p a b ↔ LexLE (G.chainDepth X p) a b) →
    ∀ (W : Set V) (σ : V → V), (∀ v ∈ W, G.WinsFrom X .zero σ v) →
      (∀ v ∈ W, ∀ w, G.Step X .zero σ v w → w ∈ W) →
      ∃ μ : V → ℕ → ℕ, G.IsProgressMeasure X C W μ σ ∧ ∀ v ∈ W, G.IsChainLeaf X (μ v) :=
  Game.chainTreeComplete G X C
