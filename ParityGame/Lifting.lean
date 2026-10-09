module

public import ParityGame.TwoSidedLifting
public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section Lifting

namespace ParityGame

/-!
# The lifting operator, its least fixpoint, and acceleration soundness

Specifications for the fixpoint view of "two-sided lifting over instance-derived trees"
(`experiments/FINDINGS.md` §3–§6; Rust `merc/crates/vpg/src/two_sided_lifting.rs`, Python
`experiments/lifting/solver.py`). As in `ParityGame.TwoSidedLifting`, everything is for player `0`
in the MAX-parity convention.

1. **Lifting operator** (`leastProg`, `Game.lift`): a node of the subgame `X` owned by player `0`
   gets the least value progressing (`Game.Prog`) towards *some* successor in `X`, a node owned by
   player `1` the least value progressing towards *all* of them; nodes outside `X` get `⊤`.
   Headlines: `Game.LiftMonotone`, `Game.LiftingLfpCorrect` (the least fixpoint is not `⊤`
   exactly on player `0`'s winning region, for any codomain complete for `X`), and its chain-tree
   instance `Game.ChainLiftingCorrect`; `Game.ChainReprExists` shows the chain-tree
   representation `Game.ChainRepr` is satisfiable.
2. **Acceleration soundness** (`Game.ExitPath`, `Game.accelBound`, `Game.AccelSound`): raising a
   set `S` to the best "path to an exit" bound never overshoots any fixpoint.
3. **The open conjecture** (`Game.PolyLiftingConjecture`): an open research problem stated
   for precision only — *not* a contract; nothing claims or assumes it.

**Modeling choices**
* *Values.* The value type `T` is an arbitrary complete linear order with well-founded `<`; its
  top `⊤` is Jurdziński's "⊤" (no progress measure value) and `val : T → M` interprets the other
  values in a `Codomain M`. Completeness of `T` is only used to write `min`/`max` as
  `sInf`/`sSup` (and `sInf ∅ = ⊤` makes "no progressing value" come out as `⊤`); well-foundedness
  makes every non-empty `sInf` attained. The compatibility hypothesis (`a ≤ b` in `T` implies
  `a ≤ b` at every level of the codomain) is what makes the operator monotone.
* *Chain tree.* `Game.ChainRepr X val` says the non-`⊤` values of `T` are, via `val`, exactly the
  chain-tree leaves of `X` (`Game.IsChainLeaf`), ordered lexicographically on the first
  `2 * Game.height X` coordinates (= the full lexicographic order, since leaves vanish beyond).
  `Game.ChainLiftingCorrect` is stated for *every* such representation (so it does not depend on
  how the leaves are enumerated), and `Game.ChainReprExists` exhibits one (`Fin (n + 1)`, `n` the
  number of leaves, the last element being `⊤`).
* *Least fixpoint.* Stated as `IsLeast` of the set of fixpoints of `Game.lift` (existence is part
  of the claim), so the spec needs no monotonicity proof term.
* *Positional determinacy* is not assumed: the proof gets it from Zielonka's algorithm.
-/

variable {V M T : Type*}

/-! ### 1. Lifting operator -/

section Lift

variable [CompleteLinearOrder T]

/-- The value `a` (at a node of priority `p`) progresses to the value `b` (at its successor): both
    are proper (not `⊤`) and their interpretations satisfy the progress condition `Game.Prog`. -/
def ProgVal (C : Codomain M) (val : T → M) (p : ℕ) (a b : T) : Prop :=
  a ≠ ⊤ ∧ b ≠ ⊤ ∧ C.le p (val b) (val a) ∧ (p % 2 = 1 → ¬ C.le p (val a) (val b))

/-- The least value progressing (at priority `p`) to `b`; `⊤` if there is none (`sInf ∅ = ⊤`). -/
def leastProg (C : Codomain M) (val : T → M) (p : ℕ) (b : T) : T :=
  sInf {a | ProgVal C val p a b}

/-- The least progressing values (at `v`'s priority) towards the successors of `v` inside `X`. -/
def Game.succProg (G : Game V) (X : Set V) (C : Codomain M) (val : T → M) (μ : V → T) (v : V) :
    Set T :=
  (fun w => leastProg C val (G.prio v) (μ w)) '' {w | w ∈ X ∧ G.edge v w}

open scoped Classical in
/-- The lifting operator on the subgame `X`: `min` over successors for player `0`, `max` for
    player `1`, `⊤` outside `X`. -/
noncomputable def Game.lift (G : Game V) (X : Set V) (C : Codomain M) (val : T → M) (μ : V → T) :
    V → T := fun v =>
  if v ∈ X then
    (if G.owner v = .zero then sInf (G.succProg X C val μ v) else sSup (G.succProg X C val μ v))
  else ⊤

/-- `val` respects the order: proper values compare at every level as they compare in `T`. -/
def ValMono (C : Codomain M) (val : T → M) : Prop :=
  ∀ p a b, a ≠ ⊤ → b ≠ ⊤ → a ≤ b → C.le p (val a) (val b)

/-- Contract: for an order-respecting `val` the lifting operator is monotone. -/
def Game.LiftMonotone (G : Game V) (X : Set V) (C : Codomain M) (val : T → M) : Prop :=
  ValMono C val → Monotone (G.lift X C val)

/-- The values are complete for `X`: every positional winning strategy of player `0` on a
    `σ`-closed set `W` of nodes is witnessed by a progress measure with proper values in `T`. -/
def Game.LiftComplete (G : Game V) (X : Set V) (C : Codomain M) (val : T → M) : Prop :=
  ∀ (W : Set V) (σ : Strategy V), (∀ v ∈ W, G.WinsFrom X .zero σ v) →
    (∀ v ∈ W, ∀ w, G.Step X .zero σ v w → w ∈ W) →
    ∃ μ : V → T, (∀ v ∈ W, μ v ≠ ⊤) ∧ G.IsProgressMeasure X C W (fun v => val (μ v)) σ

/-- Contract (generic): in a finite game, for an order-respecting `val` with values complete for
    the subgame `X`, the lifting operator has a least fixpoint, and every least fixpoint is not `⊤`
    exactly at the nodes from which player `0` has a winning (positional) strategy in `X`. -/
def Game.LiftingLfpCorrect [Finite V] [WellFoundedLT T] (G : Game V) (X : Set V) (C : Codomain M)
    (val : T → M) : Prop :=
  G.IsSubgame X → ValMono C val → G.LiftComplete X C val →
    (∃ μ, IsLeast {μ | G.lift X C val μ = μ} μ) ∧
    ∀ μ, IsLeast {μ | G.lift X C val μ = μ} μ → ∀ v, μ v ≠ ⊤ ↔ ∃ σ, G.WinsFrom X .zero σ v

/-- `T` (via `val`) represents the chain tree of `X`: its proper values are exactly the chain-tree
    leaves, ordered lexicographically on the first `2 * Game.height X` coordinates. -/
def Game.ChainRepr [Finite V] (G : Game V) (X : Set V) (val : T → ℕ → ℕ) : Prop :=
  (∀ a b, a ≠ ⊤ → b ≠ ⊤ → (a ≤ b ↔ LexLE (2 * G.height X) (val a) (val b))) ∧
  (∀ a, a ≠ ⊤ → G.IsChainLeaf X (val a)) ∧
  (∀ l, G.IsChainLeaf X l → ∃ a, a ≠ ⊤ ∧ val a = l)

/-- Contract (headline, chain tree): in a finite game, lifting over the chain-tree leaves of the
    subgame `X` (plus `⊤`) with the truncated lexicographic codomain of depth `Game.chainDepth`
    has a least fixpoint, and every least fixpoint is not `⊤` exactly on player `0`'s winning
    region in `X`. -/
def Game.ChainLiftingCorrect [Finite V] [WellFoundedLT T] (G : Game V) (X : Set V)
    (C : Codomain (ℕ → ℕ)) (val : T → ℕ → ℕ) : Prop :=
  G.IsSubgame X → (∀ p a b, C.le p a b ↔ LexLE (G.chainDepth X p) a b) → G.ChainRepr X val →
    (∃ μ, IsLeast {μ | G.lift X C val μ = μ} μ) ∧
    ∀ μ, IsLeast {μ | G.lift X C val μ = μ} μ → ∀ v, μ v ≠ ⊤ ↔ ∃ σ, G.WinsFrom X .zero σ v

end Lift

/-- Contract (non-vacuity of `Game.ChainLiftingCorrect`): some complete linear order with
    well-founded `<` represents the chain tree of `X`. -/
def Game.ChainReprExists [Finite V] (G : Game V) (X : Set V) : Prop :=
  ∃ (T : Type) (_ : CompleteLinearOrder T) (_ : WellFoundedLT T) (val : T → ℕ → ℕ),
    G.ChainRepr X val

/-! ### 2. Acceleration -/

section Accel

variable [CompleteLinearOrder T]

/-- A move of the acceleration graph on `S`: player `0` may take any edge into `X`, player `1`
    takes its fixed choice `τ`. -/
def Game.AccelMove (G : Game V) (X : Set V) (τ : Strategy V) (s w : V) : Prop :=
  if G.owner s = .zero then G.edge s w ∧ w ∈ X else w = τ s

/-- `Game.ExitPath … s t`: `t` is the value obtained at `s ∈ S` by following acceleration moves
    inside `S` to an exit `s' → w` (`w ∉ S`) and composing the least progressing values backwards,
    starting from the exit's current value `μ w`. -/
inductive Game.ExitPath (G : Game V) (X S : Set V) (C : Codomain M) (val : T → M) (τ : Strategy V)
    (μ : V → T) : V → T → Prop
  | exit {s w : V} : s ∈ S → G.AccelMove X τ s w → w ∉ S →
      G.ExitPath X S C val τ μ s (leastProg C val (G.prio s) (μ w))
  | step {s w : V} {t : T} : s ∈ S → G.AccelMove X τ s w → w ∈ S → G.ExitPath X S C val τ μ w t →
      G.ExitPath X S C val τ μ s (leastProg C val (G.prio s) t)

/-- The acceleration bound at `s`: the minimum over all paths to an exit (`⊤` if there is none);
    what a Bellman–Ford pass over `S` computes. -/
def Game.accelBound (G : Game V) (X S : Set V) (C : Codomain M) (val : T → M) (τ : Strategy V)
    (μ : V → T) (s : V) : T :=
  sInf {t | G.ExitPath X S C val τ μ s t}

/-- Contract (acceleration soundness): in a finite game, let `ν` be a fixpoint of the lifting
    operator (e.g. the least one) and `μ ≤ ν` the current values. Let `S ⊆ X` be finite, `τ` an
    in-`X` successor choice for player `1`'s nodes of `S`, and suppose every cycle inside `S` of
    every functional graph following edges into `X` on player `0`'s nodes and `τ` on player
    `1`'s has an odd maximum. Then the acceleration bound never exceeds `ν` on `S`. -/
def Game.AccelSound [Finite V] [WellFoundedLT T] (G : Game V) (X : Set V) (C : Codomain M)
    (val : T → M) (ν μ : V → T) (S : Set V) (τ : Strategy V) : Prop :=
  G.IsSubgame X → ValMono C val → G.lift X C val ν = ν → μ ≤ ν → S ⊆ X → S.Finite →
    (∀ s ∈ S, G.owner s = .one → τ s ∈ X ∧ G.edge s (τ s)) →
    (∀ f : V → V, (∀ s ∈ S, G.owner s = .zero → G.edge s (f s) ∧ f s ∈ X) →
      (∀ s ∈ S, G.owner s = .one → f s = τ s) → G.OddCyclesIn f S) →
    ∀ s ∈ S, G.accelBound X S C val τ μ s ≤ ν s

end Accel

/-! ### 3. The open conjecture (NOT a contract) -/

section Conjecture

variable [CompleteLinearOrder T]

/-- `τ` is a current best choice of player `1` for the values `μ`: at every player-`1` node of `X`
    an in-`X` successor maximising the least progressing value. -/
def Game.ArgmaxChoice (G : Game V) (X : Set V) (C : Codomain M) (val : T → M) (μ : V → T)
    (τ : Strategy V) : Prop :=
  ∀ u ∈ X, G.owner u = .one → τ u ∈ X ∧ G.edge u (τ u) ∧
    ∀ w ∈ X, G.edge u w → leastProg C val (G.prio u) (μ w) ≤ leastProg C val (G.prio u) (μ (τ u))

/-- `S` is an admissible acceleration set for the lifted node `v` and player-`1` choice `τ`: the
    hypotheses of `Game.AccelSound` on `S` hold and `v ∈ S`. -/
def Game.AccelAdmissible (G : Game V) (X : Set V) (τ : Strategy V) (v : V) (S : Set V) : Prop :=
  v ∈ S ∧ S ⊆ X ∧
    ∀ f : V → V, (∀ s ∈ S, G.owner s = .zero → G.edge s (f s) ∧ f s ∈ X) →
      (∀ s ∈ S, G.owner s = .one → f s = τ s) → G.OddCyclesIn f S

open scoped Classical in
/-- Raise every node of `S` to its acceleration bound (if that is higher). -/
noncomputable def Game.accelerate (G : Game V) (X S : Set V) (C : Codomain M) (val : T → M) (τ : Strategy V)
    (μ : V → T) : V → T := fun u =>
  if u ∈ S then max (μ u) (G.accelBound X S C val τ μ u) else μ u

open scoped Classical in
/-- One round of chaotic lifting with mandatory maximal acceleration: lift some node `v ∈ X` whose
    lifted value is strictly larger (in any order — the scheduler is adversarial); then, for a
    current best choice `τ` of player `1`, accelerate on an inclusion-maximal admissible set
    containing `v` if there is one. -/
def Game.LiftAccelStep (G : Game V) (X : Set V) (C : Codomain M) (val : T → M)
    (μ μ' : V → T) : Prop :=
  ∃ v ∈ X, μ v < G.lift X C val μ v ∧
    ∃ τ, G.ArgmaxChoice X C val (Function.update μ v (G.lift X C val μ v)) τ ∧
      (((¬ ∃ S, G.AccelAdmissible X τ v S) ∧ μ' = Function.update μ v (G.lift X C val μ v)) ∨
       ∃ S, G.AccelAdmissible X τ v S ∧
         (∀ S', G.AccelAdmissible X τ v S' → S ⊆ S' → S' = S) ∧
         μ' = G.accelerate X S C val τ (Function.update μ v (G.lift X C val μ v)))

end Conjecture

/-- **OPEN CONJECTURE — not a contract, not claimed, not proved anywhere in this repository.**
    There is a polynomial bound `c · (|V| + 1)^k` on the number of rounds of
    `Game.LiftAccelStep` (each round: one strict lift plus at most one acceleration, which raises
    at most `|V|` values, so counting individual strict increases instead changes the bound by a
    factor `≤ |V| + 1`) in every run from the all-`⊥` labelling, over the chain-tree codomain of
    any subgame of any finite game, whatever the lift order and the tie-breaking.

    Caveats for readers: this is the *one-sided* lifting of player `0` with an idealised
    acceleration (inclusion-maximal admissible sets, not the SCC-with-peeling sets of the Rust and
    Python solvers), and without the two-sided interleaving, early certification and rebuilds of
    `experiments/FINDINGS.md` §5; it may be false even if the implemented algorithm is
    polynomial. -/
def Game.PolyLiftingConjecture : Prop :=
  ∃ c k : ℕ, ∀ (V : Type) [Finite V] (G : Game V) (X : Set V) (T : Type) [CompleteLinearOrder T]
    [WellFoundedLT T] (val : T → ℕ → ℕ) (C : Codomain (ℕ → ℕ)),
    G.IsSubgame X → (∀ p a b, C.le p a b ↔ LexLE (G.chainDepth X p) a b) → G.ChainRepr X val →
    ∀ (run : ℕ → V → T) (N : ℕ), run 0 = ⊥ →
      (∀ i < N, G.LiftAccelStep X C val (run i) (run (i + 1))) → N ≤ c * (Nat.card V + 1) ^ k

end ParityGame

end Lifting
