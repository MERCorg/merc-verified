module

public import MercLib.ParityGame.Game

@[expose] public section

namespace MercLib.ParityGame

/-!
# Monotone and fatal attractors

Section 3 (Definitions 3 and 4, Theorem 2) of
[M. Huth, J. H.-P. Kuo and N. Piterman, *Fatal Attractors in Parity Games: Building Blocks for
Partial Solvers*][Huth2014].

**Dualised priority convention.** The paper decides a play by the *least* colour occurring
infinitely often, whereas `Game.PlayWonBy` uses the *greatest* priority. Every colour comparison
is therefore flipped: the monotone attractor for target priority `c` only passes through nodes of
priority *at most* `c` (the paper: at least `c`).

**Modeling choices**
* As in `Attractor.lean`, everything is relative to a subgame `X`; moves leaving `X` are
  ignored. The attractor lies in `X` by construction; the target `T` need not.
* The least fixed point `μZ. mpre(Z, T, c)` is presented as the union of the stages
  `MAttr⁰ = ∅`, `MAttrᵏ⁺¹ = mpre(MAttrᵏ, T, c)`; for finite games this is the least fixed point.
* The paper writes `MA(X)` for `MAttr_{p}(X, c)` with `X` a set of nodes of colour `c` and
  `p = c % 2`; here that is `G.mattr X (Player.ofPrio c) c T` (named `Game.ma`), with the
  same-colour requirement on the target `T` stated as a hypothesis where needed.
-/

variable {V : Type*}

/-- The monotone control predecessor `mpreᵢ(A, T, c)` inside `X` (Definition 3, dualised): nodes
    of `X` with priority at most `c` from which player `i` can force the next move into `A ∪ T`. -/
def Game.mpre (G : Game V) (X : Set V) (i : Player) (c : ℕ) (T A : Set V) : Set V :=
  {v | v ∈ X ∧ G.prio v ≤ c ∧
    ((G.owner v = i ∧ ∃ w ∈ X, G.edge v w ∧ w ∈ A ∪ T) ∨
     (G.owner v ≠ i ∧ ∀ w ∈ X, G.edge v w → w ∈ A ∪ T))}

/-- The `k`-th stage of the monotone attractor computation: `MAttr⁰ = ∅` and
    `MAttrᵏ⁺¹ = mpreᵢ(MAttrᵏ, T, c)`. The target `T` itself is not included in stage `0`. -/
def Game.mattrStage (G : Game V) (X : Set V) (i : Player) (c : ℕ) (T : Set V) : ℕ → Set V
  | 0 => ∅
  | k + 1 => G.mpre X i c T (G.mattrStage X i c T k)

/-- The monotone attractor `MAttrᵢ(T, c) = μZ. mpreᵢ(Z, T, c)` inside `X` (Definition 3): the nodes
    from which player `i` can force the play into `T` in *one or more* moves, meeting only nodes of
    priority at most `c` on the way (the target node reached is not constrained). -/
def Game.mattr (G : Game V) (X : Set V) (i : Player) (c : ℕ) (T : Set V) : Set V :=
  {v | ∃ k, v ∈ G.mattrStage X i c T k}

/-- `MA(T)` (Definition 4.1): the monotone attractor for the player favoured by `c`, with target
    `T` (intended to be a set of nodes of priority `c`). -/
def Game.ma (G : Game V) (X : Set V) (c : ℕ) (T : Set V) : Set V :=
  G.mattr X (Player.ofPrio c) c T

/-- `MA(T)` is a *fatal attractor* (Definition 4.2): every target node is attracted back to `T`. -/
def Game.IsFatal (G : Game V) (X : Set V) (c : ℕ) (T : Set V) : Prop :=
  T ⊆ G.ma X c T

open scoped Classical in
/-- The stage at which `v` first enters the monotone attractor (`0` for nodes outside it; nodes
    inside it have rank at least `1`, since stage `0` is empty). -/
noncomputable def Game.mattrRank (G : Game V) (X : Set V) (i : Player) (c : ℕ) (T : Set V)
    (v : V) : ℕ :=
  if h : ∃ k, v ∈ G.mattrStage X i c T k then Nat.find h else 0

open scoped Classical in
/-- The monotone attractor strategy: a node first reached at stage `k > 0` moves to a successor in
    `X` lying in stage `k - 1` or in the target `T`; every other node maps to itself. -/
noncomputable def Game.mattrStrategy (G : Game V) (X : Set V) (i : Player) (c : ℕ) (T : Set V) :
    Strategy V := fun v =>
  if h : 0 < G.mattrRank X i c T v ∧
      ∃ w ∈ X, G.edge v w ∧ w ∈ G.mattrStage X i c T (G.mattrRank X i c T v - 1) ∪ T
  then h.2.choose else v

/-- Contract for fatal attractors (Theorem 2): if `T ⊆ X` consists of nodes of priority `c` and
    `MA(T)` is fatal in the subgame `X`, then the monotone attractor strategy for the player
    favoured by `c` wins from every node of `MA(T)`. -/
def Game.FatalAttractorWins (G : Game V) (X : Set V) (c : ℕ) (T : Set V) : Prop :=
  G.IsSubgame X → T ⊆ X → (∀ v ∈ T, G.prio v = c) → G.IsFatal X c T →
    ∀ v ∈ G.ma X c T,
      G.WinsFrom X (Player.ofPrio c) (G.mattrStrategy X (Player.ofPrio c) c T) v

end MercLib.ParityGame
