module

public import MercLib.ParityGame.Attractor
public import MercLib.ParityGame.FatalAttractor
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MercLib.ParityGame

/-!
# Implementation of fatal-attractor detection

A functional model of `FatalAttractorOriginal`, the implementation of the partial solver `psolB`
of [M. Huth, J. H.-P. Kuo and N. Piterman, *Fatal Attractors in Parity Games: Building Blocks for
Partial Solvers*][Huth2014] (Figure 3) that accumulates the decided regions `S₀, S₁` and the
strategies `τ₀, τ₁` instead of removing the decided nodes from the game. The decided regions and
strategies are a `Solution` `r` with `r.win i = Sᵢ` and `r.strat i = τᵢ`.

**Translation from Figure 3.**
* Figure 3 runs on a structure graph. Its ranks `rnk` become priorities `prio`. Its
  decorations `▼`/`▲` become ownership by player `0`/`1`. The `true`/`false` decorations are
  not needed, because a `Game` is total, so the decoration conditions on `U` disappear.
* As in `FatalAttractor.lean`, the priority order is dualised. `AttrMinRankOriginal(T, α, V, j)`
  only passes through nodes of rank *at least* `j` (min-parity). Here it is the monotone
  attractor `G.mattr X α j T`, which only passes through nodes of priority *at most* `j`.
* The rank set `J` is iterated in an unspecified order, so the order is a parameter `js`.
  Theorem 6 of the paper says the result does not depend on it.
* Everything is relative to a subgame `X` (the paper's `V`, renamed so it does not clash
  with the loop variable `X`, which is called `prev` here).
* The `while` loop has no termination proof in the definition. On a finite game the candidate
  set `U` shrinks strictly in each non-breaking iteration, so it terminates; the soundness proof
  shows this.
* `AttrDefaultWithTau` is `attrWithTau`, and the `then`-branch that updates `τα` on `Y \ Sα` and
  adds `Y` to `Sα` is `acceptFatal`.
* `τ(v)` in Figure 3 is the strategy of the monotone attractor `Y`, i.e.
  `G.mattrStrategy X α j (U ∪ Sα)`. For `v ∈ U` an arbitrary successor in `Y` (inside `X`) is
  chosen. It exists because `Sα` is closed under the `α`-attractor, so `v ∉ Sα` has no move
  into `Sα` and its attracting move lands in `Y`.
-/

variable {V : Type*}

open scoped Classical in
/-- `AttrDefaultWithTau(Sᵢ, i, τᵢ)`: close `Sᵢ` under the ordinary `i`-attractor inside `X`, and
    let `τᵢ` follow the attractor strategy on the newly added nodes. -/
noncomputable def Game.attrWithTau (G : Game V) (X : Set V) (i : Player) (r : Solution V) :
    Solution V where
  win := Function.update r.win i (G.attr X i (r.win i))
  strat := Function.update r.strat i fun v =>
    if v ∈ G.attr X i (r.win i) \ r.win i then G.attrStrategy X i (r.win i) v else r.strat i v

open scoped Classical in
/-- The `then`-branch for candidate set `U` of priority `j` whose monotone attractor `Y` (with
    target `U ∪ Sα`, `α = Player.ofPrio j`) is fatal. On `α`'s nodes in `Y \ Sα`, `τα` moves to
    some successor in `Y` for nodes of `U`, and follows the monotone attractor strategy otherwise.
    Then `Y` is added to `Sα` and the result is closed under the ordinary `α`-attractor. If no
    successor in `Y` exists (excluded by the attractor-closure of `Sα`), `τα` is left unchanged. -/
noncomputable def Game.acceptFatal (G : Game V) (X : Set V) (j : ℕ) (U Y : Set V)
    (r : Solution V) : Solution V :=
  let α := Player.ofPrio j
  G.attrWithTau X α
    { win := Function.update r.win α (r.win α ∪ Y)
      strat := Function.update r.strat α fun v =>
        if v ∈ Y \ r.win α ∧ G.owner v = α then
          if v ∈ U then
            if h : ∃ w ∈ X, G.edge v w ∧ w ∈ Y then h.choose else r.strat α v
          else G.mattrStrategy X α j (U ∪ r.win α) v
        else r.strat α v }

open scoped Classical in
/-- `FatalAttractorOriginal(X, S₀, S₁, τ₀, τ₁)`, processing the priorities in the order `js`:
    the input regions/strategies are given by `r` (`r.win i = Sᵢ`, `r.strat i = τᵢ`). -/
noncomputable def Game.fatalAttractorOriginal (G : Game V) (X : Set V) (js : List ℕ)
    (r : Solution V) : Solution V := Id.run do
  let mut r := G.attrWithTau X .one (G.attrWithTau X .zero r)
  for j in js do
    let α := Player.ofPrio j
    let mut U := {u | u ∈ X ∧ G.prio u = j} \ r.win α.opp
    let mut prev := ∅
    while U ≠ ∅ ∧ U ≠ prev do
      prev := U
      let Y := G.mattr X α j (U ∪ r.win α)
      if U ⊆ Y then
        r := G.acceptFatal X j U Y r
        break
      else
        U := U ∩ Y
  return r

/-- `W` is a region won by player `i` with `σ` inside `X`, and plays conforming to `σ` cannot
    leave it. That is, `W ⊆ X`, `σ` moves along an edge into `W` from `i`'s nodes in `W`, every
    move of the opponent from `W` stays in `W`, and `σ` wins from every node of `W`. The closure
    clauses make the invariant robust under changing `σ` outside `W`. -/
def Game.IsClosedWinningRegion (G : Game V) (X : Set V) (i : Player) (W : Set V)
    (σ : Strategy V) : Prop :=
  W ⊆ X ∧
    (∀ v ∈ W, G.owner v = i → G.edge v (σ v) ∧ σ v ∈ W) ∧
    (∀ v ∈ W, G.owner v ≠ i → ∀ w ∈ X, G.edge v w → w ∈ W) ∧
    ∀ v ∈ W, G.WinsFrom X i σ v

/-- `r` is a sound partial solution of the subgame `X`: each `r.win i` is a closed region won by
    `i` with `r.strat i`. -/
def Game.SoundPartial (G : Game V) (X : Set V) (r : Solution V) : Prop :=
  ∀ i, G.IsClosedWinningRegion X i (r.win i) (r.strat i)

/-- Contract for `FatalAttractorOriginal`: on a finite game, for any processing order `js` of the
    priorities, a sound partial solution of the subgame `X` is mapped to a sound partial solution
    that extends it. -/
def Game.FatalAttractorOriginalSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : Prop :=
  G.IsSubgame X → G.SoundPartial X r →
    G.SoundPartial X (G.fatalAttractorOriginal X js r) ∧
      ∀ i, r.win i ⊆ (G.fatalAttractorOriginal X js r).win i

end MercLib.ParityGame
