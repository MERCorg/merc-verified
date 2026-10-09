module

public import ParityGame.Attractor
public import ParityGame.Lifting
public import Mathlib.Data.Set.Card

@[expose] public section TwoSidedAlgorithm

namespace ParityGame

/-!
# Two-sided lifting: duality, dominion removal, certification and end-to-end correctness

The outer loop of "two-sided lifting over instance-derived trees" (`experiments/FINDINGS.md` §5;
Rust `merc/crates/vpg/src/two_sided_lifting.rs`, function `solve_game`; Python
`experiments/lifting/solver.py`, function `solve`). The lifting itself is specified in
`ParityGame.Lifting`; this file specifies how its results are used.

1. **Duality** (`Game.dual`, `Game.DualWinsFrom`): player `1`'s lifting runs on the dual game
   (priorities `+ 1`, owners swapped, edges unchanged), in which player `0` wins exactly where
   player `1` wins in the original game, with the same positional strategy.
2. **Dominion removal** (`Game.IsDominion`, `Game.DominionRemoval`): removing the `i`-attractor
   of an `i`-dominion of `X` from `X` is sound — the attractor is won by `i`, the rest is a
   subgame, and every remaining node has the same winner in the smaller subgame.
3. **Certification** (`Game.CertificationSound`, `Game.certifiedSet`,
   `Game.CertifiedSetGreatest`): any set on which some labelling is a progress measure of
   player `i` (in `Game.forPlayer i`) is an `i`-dominion; the union of all such sets is again one.
   `Game.SimultaneousRemoval` justifies removing both players' certified sets in one round.
4. **The algorithm** (`AlgState`, `Game.RemovalStep`, `Game.Completion`) and its correctness:
   the invariant `Game.AlgInv` (`Game.AlgInvInit`, `Game.AlgInvStep`), the final step
   (`Game.CompletionCorrect`), the headline `Game.TwoSidedCorrect`, and the bound on the number
   of removals (`Game.RemovalShrinks`, `Game.RemovalBound`).

**Modeling choices**
* *Dual game.* `Game.dual` adds `1` to every priority and swaps owners; edges are unchanged.
  This matches the Rust `View` for `Player::Odd` (`prio + 1`, "mine" = owned by the lifting
  player). `Game.forPlayer i` is the game in which `i` plays the role of player `0`.
* *Certification.* The Rust `Lifter::certified` computes the greatest set `D` of non-`⊤` nodes
  on which the current values form a progress measure for an argmin choice of the lifting player
  (restricted to `D`). Here a removal step may use *any* non-empty `D` that is the domain of a
  progress measure of player `i` (in `Game.forPlayer i`), for *any* labelling into *any* codomain
  and *any* witnessing strategy; the Rust set is one such `D` (its argmin choices are the
  strategy), so the model over-approximates the Rust behaviour. Empty certified sets remove
  nothing; the model requires `D` to be non-empty so that every step makes progress.
* *Attractor.* Removal uses the stage-wise attractor `Game.attr` of the *original* game for the
  certifying player inside the current subgame, as the Rust `attractor`. The Rust code removes
  both players' sets in one round, computing player `1`'s attractor after player `0`'s removal
  but certifying it before; `Game.SimultaneousRemoval` shows such a set is still a certified set
  of the smaller subgame, so one Rust round is two `Game.RemovalStep`s.
* *Completion.* The Rust loop ends when one player's lifting queue is empty, at which point its
  values are taken to be the least fixpoint of lifting over that player's chain tree. The model
  takes that least fixpoint as given (`IsLeast` of the fixpoints of `Game.lift` over a
  `Game.ChainRepr` of the chain tree of `Game.forPlayer i` on the current subgame); that the
  Rust lifting, with its acceleration, actually reaches it is *not* claimed here
  (`Game.AccelSound` in `ParityGame.Lifting` is the relevant ingredient). Nodes of the subgame
  with a proper value go to `i`, the others to the opponent.
* *Winning.* "`i` wins `v` in `X`" is `Game.Wins`: some positional strategy wins from `v`
  (`Game.WinsFrom`). Positional determinacy is not assumed: proofs take it from Zielonka's
  algorithm.
-/

variable {V M N : Type*}

/-! ### 1. Duality -/

/-- The dual game: priorities `+ 1`, owners swapped, edges unchanged. -/
def Game.dual (G : Game V) : Game V where
  owner v := (G.owner v).opp
  edge := G.edge
  prio v := G.prio v + 1
  total := G.total

/-- The game in which player `i` plays the role of player `0`: `G` for `0`, its dual for `1`. -/
def Game.forPlayer (G : Game V) : Player → Game V
  | .zero => G
  | .one => G.dual

/-- Player `i` wins from `v` in the subgame `X` (with some positional strategy). -/
def Game.Wins (G : Game V) (X : Set V) (i : Player) (v : V) : Prop :=
  ∃ σ, G.WinsFrom X i σ v

/-- Contract (duality): a positional strategy wins for `i` in the dual subgame `X` exactly when
    it wins for the opponent `1 - i` in the original subgame `X`. For `i = 0`: player `0` wins
    from `v` in the dual iff player `1` wins from `v` in `G`. -/
def Game.DualWinsFrom (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) (v : V) : Prop :=
  G.dual.WinsFrom X i σ v ↔ G.WinsFrom X i.opp σ v

/-! ### 2. Dominion removal -/

/-- `D` is a dominion of player `i` in the subgame `X`, witnessed by `σ`: `D ⊆ X`, `σ` wins for
    `i` from every node of `D`, and every `σ`-conforming move from `D` stays in `D`. -/
def Game.IsDominion (G : Game V) (X : Set V) (i : Player) (D : Set V) (σ : Strategy V) : Prop :=
  D ⊆ X ∧ (∀ v ∈ D, G.WinsFrom X i σ v) ∧ ∀ v ∈ D, ∀ w, G.Step X i σ v w → w ∈ D

/-- Contract (dominion removal): in a finite game, for a dominion `D` of `i` in the subgame `X`
    and `A` its `i`-attractor inside `X`: (i) `A` is again a dominion of `i` (so `i` wins from
    all of it), (ii) `X \ A` is a subgame, and (iii) every node of `X \ A` has, for each player,
    the same winning status in `X` and in `X \ A`. -/
def Game.DominionRemoval [Finite V] (G : Game V) (X : Set V) (i : Player) (D : Set V)
    (σ : Strategy V) : Prop :=
  G.IsSubgame X → G.IsDominion X i D σ →
    (∃ τ, G.IsDominion X i (G.attr X i D) τ) ∧
    G.IsSubgame (X \ G.attr X i D) ∧
    ∀ v ∈ X \ G.attr X i D, ∀ j, G.Wins X j v ↔ G.Wins (X \ G.attr X i D) j v

/-! ### 3. Certification -/

/-- Contract (certification is sound): in a finite game, if `μ` (into any codomain) is a
    progress measure of player `i` — in `Game.forPlayer i` — on `D ⊆ X`, witnessed by `σ`, then
    `D` is a dominion of `i` in `X`, witnessed by the same `σ`. -/
def Game.CertificationSound [Finite V] (G : Game V) (X : Set V) (i : Player) (C : Codomain M)
    (D : Set V) (μ : V → M) (σ : Strategy V) : Prop :=
  G.IsSubgame X → (G.forPlayer i).IsProgressMeasure X C D μ σ → G.IsDominion X i D σ

/-- The certified set of the labelling `μ`: the union of all domains on which `μ` is a progress
    measure (for some witnessing strategy). -/
def Game.certifiedSet (G : Game V) (X : Set V) (C : Codomain M) (μ : V → M) : Set V :=
  {v | ∃ D σ, G.IsProgressMeasure X C D μ σ ∧ v ∈ D}

/-- Contract: the certified set is the greatest domain of a progress measure for `μ`. -/
def Game.CertifiedSetGreatest (G : Game V) (X : Set V) (C : Codomain M) (μ : V → M) : Prop :=
  (∃ σ, G.IsProgressMeasure X C (G.certifiedSet X C μ) μ σ) ∧
  ∀ D σ, G.IsProgressMeasure X C D μ σ → D ⊆ G.certifiedSet X C μ

/-- Contract (simultaneous removal, as in one Rust round): if `D₀` is certified for player `0`
    and `D₁` for player `1` (in the dual) on the same subgame `X`, then `D₁` is still certified
    for player `1` on what remains after removing the `0`-attractor of `D₀`. -/
def Game.SimultaneousRemoval [Finite V] (G : Game V) (X : Set V) (C₀ : Codomain M)
    (D₀ : Set V) (μ₀ : V → M) (σ₀ : Strategy V) (C₁ : Codomain N) (D₁ : Set V) (μ₁ : V → N)
    (σ₁ : Strategy V) : Prop :=
  G.IsSubgame X → G.IsProgressMeasure X C₀ D₀ μ₀ σ₀ → G.dual.IsProgressMeasure X C₁ D₁ μ₁ σ₁ →
    G.dual.IsProgressMeasure (X \ G.attr X .zero D₀) C₁ D₁ μ₁ σ₁

/-! ### 4. The algorithm -/

/-- A state of the algorithm: the regions `won i` decided for each player so far and the
    undecided subgame `rest`. -/
structure AlgState (V : Type*) where
  won : Player → Set V
  rest : Set V

/-- The initial state: nothing decided, the whole game undecided. -/
def AlgState.init : AlgState V := ⟨fun _ => ∅, Set.univ⟩

/-- Remove the `i`-attractor of `D` from the undecided subgame and record it as won by `i`. -/
def AlgState.remove (G : Game V) (s : AlgState V) (i : Player) (D : Set V) : AlgState V :=
  ⟨fun j => if j = i then s.won j ∪ G.attr s.rest i D else s.won j, s.rest \ G.attr s.rest i D⟩

/-- A removal step: some player `i` certifies a non-empty set `D` — the domain of a progress
    measure of `i` (in `Game.forPlayer i`) on the undecided subgame, for some labelling into some
    codomain — and its `i`-attractor is removed. -/
def Game.RemovalStep (G : Game V) (s s' : AlgState V) : Prop :=
  ∃ (i : Player) (M : Type) (C : Codomain M) (μ : V → M) (σ : Strategy V) (D : Set V),
    D.Nonempty ∧ (G.forPlayer i).IsProgressMeasure s.rest C D μ σ ∧ s' = s.remove G i D

/-- The completion step from `s` with result `r`: player `i`'s lifting (in `Game.forPlayer i`)
    over (a representation of) its chain tree of the undecided subgame has reached a least
    fixpoint `ν`; the undecided nodes with a proper value go to `i`, the others to the
    opponent. -/
def Game.Completion [Finite V] (G : Game V) (s : AlgState V) (r : Player → Set V) : Prop :=
  ∃ (i : Player) (T : Type) (_ : CompleteLinearOrder T) (_ : WellFoundedLT T)
    (val : T → ℕ → ℕ) (C : Codomain (ℕ → ℕ)) (ν : V → T),
    (∀ p a b, C.le p a b ↔ LexLE ((G.forPlayer i).chainDepth s.rest p) a b) ∧
    (G.forPlayer i).ChainRepr s.rest val ∧
    IsLeast {μ | (G.forPlayer i).lift s.rest C val μ = μ} ν ∧
    r = fun j => if j = i then s.won j ∪ {v | v ∈ s.rest ∧ ν v ≠ ⊤}
      else s.won j ∪ {v | v ∈ s.rest ∧ ν v = ⊤}

/-- The invariant: the undecided part is a subgame, the decided regions are exactly the nodes
    outside it won by the respective player in the whole game, and every undecided node has the
    same winners in the undecided subgame as in the whole game. -/
def Game.AlgInv (G : Game V) (s : AlgState V) : Prop :=
  G.IsSubgame s.rest ∧
  (∀ i v, v ∈ s.won i ↔ v ∉ s.rest ∧ G.Wins Set.univ i v) ∧
  ∀ v ∈ s.rest, ∀ i, G.Wins s.rest i v ↔ G.Wins Set.univ i v

/-- Contract: the invariant holds initially. -/
def Game.AlgInvInit (G : Game V) : Prop := G.AlgInv AlgState.init

/-- Contract: in a finite game, every removal step preserves the invariant. -/
def Game.AlgInvStep [Finite V] (G : Game V) (s s' : AlgState V) : Prop :=
  G.AlgInv s → G.RemovalStep s s' → G.AlgInv s'

/-- Contract: in a finite game, a completion step from a state satisfying the invariant returns
    exactly the winning regions of the whole game. -/
def Game.CompletionCorrect [Finite V] (G : Game V) (s : AlgState V) (r : Player → Set V) :
    Prop :=
  G.AlgInv s → G.Completion s r → ∀ i v, v ∈ r i ↔ G.Wins Set.univ i v

/-- Contract (headline): in a finite game, every run of removal steps from the initial state
    that ends in a completion step returns exactly the winning regions of the whole game. -/
def Game.TwoSidedCorrect [Finite V] (G : Game V) : Prop :=
  ∀ s r, Relation.ReflTransGen G.RemovalStep AlgState.init s → G.Completion s r →
    ∀ i v, v ∈ r i ↔ G.Wins Set.univ i v

/-- Contract: every removal step strictly shrinks the undecided subgame. -/
def Game.RemovalShrinks (G : Game V) (s s' : AlgState V) : Prop :=
  G.RemovalStep s s' → s'.rest ⊂ s.rest

/-- Contract (bound on restarts): in a finite game, every run of `N` removal steps from the
    initial state has `N ≤ |V|`. -/
def Game.RemovalBound [Finite V] (G : Game V) : Prop :=
  ∀ (run : ℕ → AlgState V) (N : ℕ), run 0 = AlgState.init →
    (∀ k < N, G.RemovalStep (run k) (run (k + 1))) → N ≤ Nat.card V

end ParityGame

end TwoSidedAlgorithm
