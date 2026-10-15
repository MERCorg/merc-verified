import MercLib.ParityGame.Game
import MercLib.ParityGame.Attractor
import MercLib.ParityGame.FatalAttractor
import MercLib.ParityGame.Implementation
import MercLib.ParityGame.Zielonka

/-!
# Comparator challenge: parity games (human-vetted)

The headline theorems of `MercLib/ParityGame/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

open Cslib (ωSequence)

namespace MercLib.ParityGame

variable {V : Type*}

/-! ## Plays (Section 2) -/

/-- Sanity check on the winning condition: in a finite game every play has exactly one winner. -/
theorem Game.playHasUniqueWinner (G : Game V) [Finite V] :
    ∀ p : ωSequence V, ∃! i, G.PlayWonBy i p := sorry

/-! ## Attractors (Section 2) -/

/-- Correctness of the attractor (Section 2): for a subgame `X` and `U ⊆ X`, the attractor lies
    between `U` and `X`, its complement in `X` is again a subgame in which player `i` cannot
    escape (a *trap* for `i`), and every play conforming to a strategy for `i` that agrees with
    the attractor strategy on the attractor outside `U` reaches `U` from within the attractor. -/
theorem Game.attractorCorrect (G : Game V) [Finite V] (X : Set V) (i : Player) (U : Set V)
    (hX : G.IsSubgame X) (hU : U ⊆ X) :
    (U ⊆ G.attr X i U ∧ G.attr X i U ⊆ X) ∧
    G.IsSubgame (X \ G.attr X i U) ∧
    (∀ v ∈ X \ G.attr X i U, G.owner v = i → ∀ w ∈ X, G.edge v w → w ∉ G.attr X i U) ∧
    ∀ σ : Strategy V,
      (∀ v ∈ G.attr X i U, v ∉ U → G.owner v = i → σ v = G.attrStrategy X i U v) →
      ∀ p : ωSequence V, G.ConformingPlay X i σ p → p 0 ∈ G.attr X i U → ∃ n, p n ∈ U := sorry

/-! ## Fatal attractors (Theorem 2 of [Huth2014]) -/

/-- Fatal attractors (Theorem 2 of [Huth2014]): if `T ⊆ X` consists of nodes of priority `c` and
    is fatal, then the player `Player.ofPrio c` favoured by `c` wins from every node of the
    monotone attractor `MA(T)` using the monotone attractor strategy. -/
theorem Game.fatalAttractorWins (G : Game V) (X : Set V) (c : ℕ) (T : Set V) :
    G.FatalAttractorWins X c T := sorry

/-! ## Fatal-attractor implementation (`FatalAttractorOriginal`, Figure 3 of [Huth2014]) -/

/-- The implementation `FatalAttractorOriginal` is sound: on a finite game, for any processing
    order `js` of the priorities, a sound partial solution of the subgame `X` (closed winning
    regions with their strategies) is mapped to a sound partial solution that extends it. -/
theorem Game.fatalAttractorOriginalSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : G.FatalAttractorOriginalSound X js r := sorry

/-! ## Zielonka's recursive algorithm ([Zielonka1998]) -/

/-- Zielonka's algorithm is correct (positional determinacy of parity games): the returned winning
    regions partition the game, and each player's positional strategy wins from every node of
    that player's region. -/
theorem Game.zielonka_correct (G : Game V) [Finite V] : G.ZielonkaCorrect := sorry

end MercLib.ParityGame
