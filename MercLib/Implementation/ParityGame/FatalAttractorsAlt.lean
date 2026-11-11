module

public import MercLib.Implementation.ParityGame.FatalAttractor
public import MercLib.Algorithms.ParityGame.Zielonka

@[expose] public section

namespace MercLib.ParityGame

/-!
# The alternative fatal-attractor implementation of mCRL2

A functional model of `fatal_attractors_generic` in mCRL2's
`libraries/pbes/include/mcrl2/pbes/pbesinst_fatal_attractors.h`: the partial solver used by
`pbessolve` for the strategies `detect_winning_loops_using_fatal_attractor` (via `find_loops2`) and
`solve_subgames_using_fatal_attractor_local` (via `fatal_attractors`). It refines the candidate
region with a greatest fixed point, like `psolC` of [M. Huth, J. H.-P. Kuo and N. Piterman, *Fatal
Attractors in Parity Games: Building Blocks for Partial Solvers*][Huth2014], instead of shrinking
the candidate set `U` as `FatalAttractorOriginal` (`FatalAttractor.lean`) does.

The file models two versions of the loop. `Game.fatalAttractorsAltBuggy` is the version before the
fix, which can report a node as won by the wrong player (`Game.FatalAttractorsAltBuggyUnsound`).
`Game.fatalAttractorsAlt` is the fixed version, which is sound
(`Game.FatalAttractorsAltSound`). The fix rests on `Game.SubgameAttrCorrect`. `README.md` in this
directory explains the bug and the fix.

**Translation from the C++ code.** The conventions of `FatalAttractor.lean` apply. Ranks become
priorities, decorations become owners, and the priority order is dualised: `compare = >=` in the
min-parity C++ code becomes `≤ j` here. `S[α], τ[α]` are a `Solution`, the rank order is a parameter
`js`, and everything is relative to a subgame `X` (the C++ code uses the whole graph `V`).
* `attr_min_rank_generic(G, A, α, R, j, >=)` is `Game.attrMinRank R α j A`: the target `A` together
  with the monotone attractor of `A` inside `R`. In the C++ code a node `u` of the opponent is
  attracted when *all* its successors in the graph are in the attractor; here only its successors
  in `R` count. This agrees whenever `R` is a trap for the opponent, which is the case for the
  calls in the fixed loop.
* `attr_default(G, A, 1 - α)` is `G.attr X α.opp A`.
* The strategy set by `attr_min_rank_generic` for a node of `α` that it adds is the monotone
  attractor strategy `G.mattrStrategy R α j A`.
* The final strategy step and `S[α] := S[α] ∪ X` followed by `attr_default_with_tau` is
  `Game.acceptAlt`. For a node of `U_j` the C++ code uses `find_successor_in(G, v, Y)`; here that is
  some successor in `Y`, if there is one.
* The loop variables are `R` (the set `Y` of the previous iteration, in which `X` is computed) and
  `Y`. The C++ variable `X` is the attractor computed from `R`.
-/

variable {V : Type*}

/-- `AttrMinRank(A, α, R, j)` (`attr_min_rank_generic` with `compare = >=`, dualised): the target
    `A` together with the nodes of `R` from which `α` can force the play into `A` through nodes of
    priority at most `j`, moving inside `R`. -/
def Game.attrMinRank (G : Game V) (R : Set V) (α : Player) (j : ℕ) (A : Set V) : Set V :=
  A ∪ G.mattr R α j A

open scoped Classical in
/-- The strategy step and region update after the loop for priority `j`, `α = Player.ofPrio j`. The
    candidate nodes are `U` (`U_j`), the region found is `Y`, and the last call of
    `attrMinRank` used the subgame `R` and the target `A`. On `α`'s nodes in `Y \ Sα`, `τα` moves to
    some successor in `Y` for nodes of `U`, and follows the monotone attractor strategy otherwise.
    Then `Y` is added to `Sα` and the result is closed under the ordinary `α`-attractor. If a node of
    `U` has no successor in `Y`, `τα` is left unchanged there (the C++ code stores
    `undefined_vertex()`). -/
noncomputable def Game.acceptAlt (G : Game V) (X : Set V) (j : ℕ) (U R A Y : Set V)
    (r : Solution V) : Solution V :=
  let α := Player.ofPrio j
  G.attrWithTau X α
    { win := Function.update r.win α (r.win α ∪ Y)
      strat := Function.update r.strat α fun v =>
        if v ∈ Y \ r.win α ∧ G.owner v = α then
          if v ∈ U then
            if h : ∃ w ∈ X, G.edge v w ∧ w ∈ Y then h.choose else r.strat α v
          else G.mattrStrategy R α j A v
        else r.strat α v }

open scoped Classical in
/-- `fatal_attractors_generic` **before the fix**, processing the priorities in the order `js`. The
    loop computes `X := AttrMinRank(T ∩ Y, α, X, j)` in the whole subgame and updates
    `Y := Y \ Attr_{1-α}(Y \ X)`, also computed in the whole subgame. Here `P` is the previous `Y`. -/
noncomputable def Game.fatalAttractorsAltBuggy (G : Game V) (X : Set V) (js : List ℕ)
    (r : Solution V) : Solution V := Id.run do
  let mut r := G.attrWithTau X .one (G.attrWithTau X .zero r)
  for j in js do
    let α := Player.ofPrio j
    let U := {u | u ∈ X ∧ G.prio u = j} \ r.win α.opp
    let T := U ∪ r.win α
    let mut P := X
    let mut Y := X \ G.attr X α.opp (X \ G.attrMinRank X α j (T ∩ X))
    while G.attrMinRank X α j (T ∩ P) ≠ Y do
      P := Y
      Y := P \ G.attr X α.opp (P \ G.attrMinRank X α j (T ∩ P))
    r := G.acceptAlt X j U X (T ∩ P) Y r
  return r

open scoped Classical in
/-- `fatal_attractors_generic` **after the fix**, processing the priorities in the order `js`. The
    loop computes `X := AttrMinRank(T ∩ Y, α, Y, j)` inside the subgame `Y`, and updates
    `Y := X_sub \ Attr_{1-α}(X_sub \ X)`, the complement of an attractor in the whole subgame
    `X_sub` (the `X` parameter here, `V` in the C++ code). Here `R` is the previous `Y`. -/
noncomputable def Game.fatalAttractorsAlt (G : Game V) (X : Set V) (js : List ℕ)
    (r : Solution V) : Solution V := Id.run do
  let mut r := G.attrWithTau X .one (G.attrWithTau X .zero r)
  for j in js do
    let α := Player.ofPrio j
    let U := {u | u ∈ X ∧ G.prio u = j} \ r.win α.opp
    let T := U ∪ r.win α
    let mut R := X
    let mut Y := X \ G.attr X α.opp (X \ G.attrMinRank X α j (T ∩ X))
    while G.attrMinRank R α j (T ∩ R) ≠ Y do
      R := Y
      Y := X \ G.attr X α.opp (X \ G.attrMinRank R α j (T ∩ R))
    r := G.acceptAlt X j U R (T ∩ R) Y r
  return r

/-- Contract for the fixed `fatal_attractors_generic`: on a finite game, for any processing order
    `js` of the priorities, a sound partial solution of the subgame `X` is mapped to a sound partial
    solution that extends it. -/
def Game.FatalAttractorsAltSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : Prop :=
  G.IsSubgame X → G.SoundPartial X r →
    G.SoundPartial X (G.fatalAttractorsAlt X js r) ∧
      ∀ i, r.win i ⊆ (G.fatalAttractorsAlt X js r).win i

/-- The attractor update of the fixed loop is the refinement inside the subgame `Y`: if `Y ⊆ X` is
    a trap for player `i` (every node of `i` in `Y` has all its successors in `X` inside `Y`) and
    `W ⊆ Y`, then removing from `X` the `i`-attractor of `X \ W` computed in `X` leaves the same set
    as removing from `Y` the `i`-attractor of `Y \ W` computed in the subgame `Y`. -/
def Game.SubgameAttrCorrect (G : Game V) (X Y W : Set V) (i : Player) : Prop :=
  Y ⊆ X → W ⊆ Y → (∀ v ∈ Y, G.owner v = i → ∀ w ∈ X, G.edge v w → w ∈ Y) →
    X \ G.attr X i (X \ W) = Y \ G.attr Y i (Y \ W)

/-! ## The counterexample -/

/-- The nodes of the counterexample. -/
inductive CexNode where
  | v | u | w | z | d
  deriving DecidableEq

/-- The edges of the counterexample. -/
def cexEdges : List (CexNode × CexNode) :=
  [(.v, .d), (.v, .w), (.u, .d), (.w, .u), (.w, .z), (.z, .w), (.d, .d)]

/-- The counterexample of `README.md`, with the min-parity ranks `0, 1` of the C++ code turned into
    the max-parity priorities `2, 1`. Player `1` wins every node: every play ends in the self-loop
    at `d` or cycles between `w` and `z`, and the greatest priority on both cycles is `1`. -/
def cexGame : Game CexNode where
  owner
    | .v => .zero | .u => .one | .w => .zero | .z => .zero | .d => .one
  edge a b := (a, b) ∈ cexEdges
  prio
    | .v => 2 | .u => 2 | .w => 1 | .z => 1 | .d => 1
  total a := by
    cases a
    · exact ⟨.d, by decide⟩
    · exact ⟨.d, by decide⟩
    · exact ⟨.u, by decide⟩
    · exact ⟨.w, by decide⟩
    · exact ⟨.d, by decide⟩

/-- The loop before the fix is unsound: on `cexGame`, starting from the empty partial solution
    (which is sound) and processing priority `2`, it puts `v` in the region of player `0`, and the
    result is not a sound partial solution. -/
def Game.FatalAttractorsAltBuggyUnsound : Prop :=
  cexGame.SoundPartial Set.univ Solution.empty ∧
    CexNode.v ∈ (cexGame.fatalAttractorsAltBuggy Set.univ [2] Solution.empty).win .zero ∧
    ¬ cexGame.SoundPartial Set.univ (cexGame.fatalAttractorsAltBuggy Set.univ [2] Solution.empty)

end MercLib.ParityGame
