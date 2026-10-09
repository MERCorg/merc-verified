module

public import ParityGame.ProgressMeasure
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section TwoSidedLifting

namespace ParityGame

/-!
# Two-sided lifting over instance-derived trees: codomain, acceleration, chain tree

Specifications for the algorithm "two-sided lifting over instance-derived trees" of
`experiments/FINDINGS.md` (§3–§6; Rust prototype `merc/crates/vpg/src/two_sided_lifting.rs`,
Python reference `experiments/lifting/{solver,trees}.py`). Everything is stated for player `0` in
the MAX-parity convention of `ParityGame.Defs`; player `1` is handled by the algorithm through the
dual game (priorities `+ 1`, owners swapped), which is not modelled here.

1. **Truncated lexicographic codomain** (`LexLE`, `TruncLexCodomainAxioms`): tuples `ℕ → ℕ`
   compared lexicographically on their first `depth p` coordinates, `depth` antitone. With
   `depth p` = the number of odd levels `≥ p` this is Jurdziński's codomain (one counter per odd
   priority); with `2 * depth p` and coordinates interleaved as
   `(k₀, c₀, k₁, c₁, …)` (component index, counter) it is the chain tree's codomain
   (`Game.chainDepth`), compared like the Python `ImplicitTree` (lexicographic on `(k, c)` pairs,
   truncated to the first `depth` pairs).
2. **Acceleration** (`Game.FunCycleEven`, `Game.FunExit`, `Game.StrategyExit`): the set version
   of `Game.progCycleEven` behind pump acceleration.
3. **Chain tree** (`Game.chainBound`, `Game.IsChainLeaf`) and its **completeness**
   (`Game.ChainTreeComplete`).

**Modeling choices** (the chain tree)
* Odd levels `q₀ > q₁ > … > q_{h-1}` (`Game.level`, 0-based, `h = Game.height`) are the odd
  priorities of nodes of the subgame `X`.
* Regions: `X` at level `0`; below a region `R` at level `l` sit the weakly connected components
  (`Game.lowComp`: `Relation.EqvGen` of the edges between nodes of `R` of priority `< q_l`) of
  `R ∩ {prio < q_l}`. Sibling components are numbered `0, 1, …` by an *arbitrary* (classical)
  bijection `Game.compIdx` / `Game.compAt` (Python sorts them by least vertex; completeness does
  not depend on the order). As in Python, a region without components still has the single child
  index `0` (whose region is `∅`).
* Chain bound (`Game.chainBound`): the supremum, over finite paths inside `R ∩ {prio ≤ q}` on
  which no priority-`q` node repeats, of the number of priority-`q` positions. A path through the
  SCC condensation visits SCCs in topological order and its priority-`q` nodes are distinct, so
  this is `≤` the Rust/Python bound (longest path through the condensation of `R ∩ {prio ≤ q}`,
  each SCC weighted by its number of priority-`q` nodes): the chain tree defined here has the same
  shape with smaller or equal counter ranges, so completeness for it implies completeness for the
  Rust tree. (It is `≥` the bound over simple paths only.)
* Leaves (`Game.IsChainLeaf`) are `ℕ → ℕ` tuples, interleaved `a (2l) = k_l`, `a (2l+1) = c_l`,
  zero from coordinate `2h` on; `k₀ = 0` (the root region `X`), each `k_{l+1}` a valid child index
  of the region selected so far, each `c_l ≤` the chain bound of that region at `q_l`.
-/

variable {V M : Type*}

/-! ### 1. Truncated lexicographic codomain -/

/-- `a ≤ b` lexicographically on the first `n` coordinates. -/
def LexLE (n : ℕ) (a b : ℕ → ℕ) : Prop :=
  (∀ i < n, a i = b i) ∨ ∃ i < n, (∀ j < i, a j = b j) ∧ a i < b i

/-- Contract: for an antitone `depth`, `p ↦ LexLE (depth p)` satisfies the `Codomain` axioms
    (preorder at every level, coarser at higher levels, well-founded strict part — at every level,
    in particular the odd ones). -/
def TruncLexCodomainAxioms (depth : ℕ → ℕ) : Prop :=
  Antitone depth →
  (∀ p a, LexLE (depth p) a a) ∧
  (∀ p a b c, LexLE (depth p) a b → LexLE (depth p) b c → LexLE (depth p) a c) ∧
  (∀ p q a b, p ≤ q → LexLE (depth p) a b → LexLE (depth q) a b) ∧
  (∀ p, WellFounded (fun a b => LexLE (depth p) a b ∧ ¬ LexLE (depth p) b a))

/-! ### 2. Acceleration -/

/-- Contract (set version of `Game.progCycleEven`): if the progress condition holds along every
    edge `s → f s` of the functional graph `f` from a finite non-empty set `S` closed under `f`,
    then some `f`-cycle inside `S` has an even greatest priority. -/
def Game.FunCycleEven (G : Game V) (C : Codomain M) (μ : V → M) (f : V → V) (S : Set V) : Prop :=
  S.Finite → S.Nonempty → (∀ s ∈ S, f s ∈ S) → (∀ s ∈ S, G.Prog C μ s (f s)) →
    ∃ s ∈ S, ∃ k, 0 < k ∧ f^[k] s = s ∧
      ∃ i < k, (∀ j < k, G.prio (f^[j] s) ≤ G.prio (f^[i] s)) ∧ G.prio (f^[i] s) % 2 = 0

/-- Every cycle of the functional graph `f` that stays inside `S` has an odd greatest priority. -/
def Game.OddCyclesIn (G : Game V) (f : V → V) (S : Set V) : Prop :=
  ∀ s ∈ S, ∀ k, 0 < k → f^[k] s = s → (∀ j < k, f^[j] s ∈ S) →
    ∀ i < k, (∀ j < k, G.prio (f^[j] s) ≤ G.prio (f^[i] s)) → G.prio (f^[i] s) % 2 = 1

/-- Contract (acceleration, functional-graph form): if the progress condition holds along every
    edge `s → f s` from a finite non-empty `S` all of whose `f`-cycles have an odd maximum, then
    `f` leaves `S` somewhere. -/
def Game.FunExit (G : Game V) (C : Codomain M) (μ : V → M) (f : V → V) (S : Set V) : Prop :=
  S.Finite → S.Nonempty → (∀ s ∈ S, G.Prog C μ s (f s)) → G.OddCyclesIn f S → ∃ s ∈ S, f s ∉ S

/-- Contract (acceleration, as used by the algorithm): let `μ` be a progress measure with domain
    `D` witnessed by `σ`, and `τ` any choice of a successor in `X` for player `1`'s nodes of
    `S ⊆ D`. If every cycle of the functional graph "`σ` on player `0`'s nodes, `τ` on player
    `1`'s" inside the finite non-empty `S` has an odd maximum, that graph leaves `S`. -/
def Game.StrategyExit (G : Game V) (X : Set V) (C : Codomain M) (D : Set V) (μ : V → M)
    (σ τ : Strategy V) (S : Set V) : Prop :=
  G.IsProgressMeasure X C D μ σ → S ⊆ D → S.Finite → S.Nonempty →
    (∀ v ∈ S, G.owner v = .one → τ v ∈ X ∧ G.edge v (τ v)) →
    G.OddCyclesIn (fun v => if G.owner v = .zero then σ v else τ v) S →
    ∃ s ∈ S, (if G.owner s = .zero then σ s else τ s) ∉ S

/-! ### 3. The chain tree -/

/-- The odd priorities of nodes of `X`. -/
noncomputable def Game.oddPrios [Finite V] (G : Game V) (X : Set V) : Finset ℕ :=
  (Set.toFinite (G.prio '' X ∩ {p | p % 2 = 1})).toFinset

/-- The number `h` of odd levels. -/
noncomputable def Game.height [Finite V] (G : Game V) (X : Set V) : ℕ := (G.oddPrios X).card

/-- The odd level `q_l`: the `l`-th largest odd priority of `X` (`l = 0` is the largest);
    `0` for `l ≥ h`. -/
noncomputable def Game.level [Finite V] (G : Game V) (X : Set V) (l : ℕ) : ℕ :=
  if h : l < (G.oddPrios X).card then
    (G.oddPrios X).orderEmbOfFin rfl ⟨(G.oddPrios X).card - 1 - l, by omega⟩
  else 0

open scoped Classical in
/-- The number of odd levels `q_l ≥ p`: Jurdziński's truncation depth for a node of priority `p`
    (antitone in `p`). -/
noncomputable def Game.levelDepth [Finite V] (G : Game V) (X : Set V) (p : ℕ) : ℕ :=
  ((Finset.range (G.height X)).filter fun l => p ≤ G.level X l).card

/-- The truncation depth of the chain tree's interleaved (component index, counter) tuples. -/
noncomputable def Game.chainDepth [Finite V] (G : Game V) (X : Set V) (p : ℕ) : ℕ :=
  2 * G.levelDepth X p

/-- An edge between two nodes of `R` both of priority `< q`. -/
def Game.LowEdge (G : Game V) (R : Set V) (q : ℕ) (a b : V) : Prop :=
  a ∈ R ∧ b ∈ R ∧ G.prio a < q ∧ G.prio b < q ∧ G.edge a b

/-- The weakly connected component of `v` in `R ∩ {prio < q}` (meaningful for `v` in that set). -/
def Game.lowComp (G : Game V) (R : Set V) (q : ℕ) (v : V) : Set V :=
  {w | Relation.EqvGen (G.LowEdge R q) v w}

/-- The weakly connected components of `R ∩ {prio < q}`. -/
def Game.lowComps (G : Game V) (R : Set V) (q : ℕ) : Set (Set V) :=
  {K | ∃ v ∈ R, G.prio v < q ∧ K = G.lowComp R q v}

open scoped Classical in
/-- The index of the component `K` among the components of `R ∩ {prio < q}` (an arbitrary
    numbering `0, …, #components - 1`; `0` if `K` is not a component). -/
noncomputable def Game.compIdx [Finite V] (G : Game V) (R : Set V) (q : ℕ) (K : Set V) : ℕ :=
  if h : K ∈ G.lowComps R q then (Finite.equivFin (G.lowComps R q) ⟨K, h⟩ : ℕ) else 0

/-- The component with index `k` (`∅` if there is none). -/
noncomputable def Game.compAt [Finite V] (G : Game V) (R : Set V) (q : ℕ) (k : ℕ) : Set V :=
  if h : k < Nat.card (G.lowComps R q) then ((Finite.equivFin (G.lowComps R q)).symm ⟨k, h⟩ : Set V)
  else ∅

open scoped Classical in
/-- `n` is the number of priority-`q` positions on some finite path `a 0 → … → a m` inside
    `R ∩ {prio ≤ q}` on which no priority-`q` node repeats. -/
def Game.ChainPath (G : Game V) (R : Set V) (q n : ℕ) : Prop :=
  ∃ (m : ℕ) (a : ℕ → V), (∀ i ≤ m, a i ∈ R ∧ G.prio (a i) ≤ q) ∧
    (∀ i < m, G.edge (a i) (a (i + 1))) ∧
    (∀ i ≤ m, ∀ j ≤ m, G.prio (a i) = q → a i = a j → i = j) ∧
    n = ((Finset.range (m + 1)).filter fun i => G.prio (a i) = q).card

/-- The chain bound of region `R` at odd level `q`: the largest `n` with `G.ChainPath R q n` (at
    most the number of nodes in a finite game; `0` if `R ∩ {prio ≤ q}` is empty). -/
noncomputable def Game.chainBound (G : Game V) (R : Set V) (q : ℕ) : ℕ :=
  sSup {n | G.ChainPath R q n}

/-- The region at level `l` selected by the component indices `a 2, a 4, …, a (2l)` of a tuple. -/
noncomputable def Game.leafRegion [Finite V] (G : Game V) (X : Set V) (a : ℕ → ℕ) : ℕ → Set V
  | 0 => X
  | l + 1 => G.compAt (G.leafRegion X a l) (G.level X l) (a (2 * (l + 1)))

/-- `a` is a leaf of the chain tree of `X` (for player `0`): `a (2l)` is the component index and
    `a (2l+1)` the counter at level `l`. -/
def Game.IsChainLeaf [Finite V] (G : Game V) (X : Set V) (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧
  (∀ l, l + 1 < G.height X →
    a (2 * (l + 1)) < max 1 (Nat.card (G.lowComps (G.leafRegion X a l) (G.level X l)))) ∧
  (∀ l < G.height X, a (2 * l + 1) ≤ G.chainBound (G.leafRegion X a l) (G.level X l)) ∧
  ∀ i, 2 * G.height X ≤ i → a i = 0

/-- Contract (completeness of the chain tree): let `C` be the truncated lexicographic codomain of
    depth `Game.chainDepth`. If player `0`'s positional strategy `σ` wins (in the subgame `X`) from
    every node of `W`, and `W` is closed under `σ`-conforming moves, then there is a progress
    measure with domain `W`, witnessed by `σ`, all of whose values on `W` are chain-tree leaves. -/
def Game.ChainTreeComplete [Finite V] (G : Game V) (X : Set V) (C : Codomain (ℕ → ℕ)) : Prop :=
  (∀ p a b, C.le p a b ↔ LexLE (G.chainDepth X p) a b) →
  ∀ (W : Set V) (σ : Strategy V), (∀ v ∈ W, G.WinsFrom X .zero σ v) →
    (∀ v ∈ W, ∀ w, G.Step X .zero σ v w → w ∈ W) →
    ∃ μ : V → ℕ → ℕ, G.IsProgressMeasure X C W μ σ ∧ ∀ v ∈ W, G.IsChainLeaf X (μ v)

end ParityGame

end TwoSidedLifting
