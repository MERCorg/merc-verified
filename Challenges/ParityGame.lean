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

/-- **Every play has exactly one winner.** In a game on a finite vertex type, exactly one player
`i` wins each infinite play `p` (`PlayWonBy`: the parity of the highest priority seen infinitely
often). This is a sanity check on the winning condition. -/
theorem Game.playHasUniqueWinner (G : Game V) [Finite V] :
    ∀ p : ωSequence V, ∃! i, G.PlayWonBy i p := sorry

/-! ## Attractors (Section 2) -/

/-- **The attractor is correct (Section 2).** Let `X` be a subgame (`IsSubgame`) of a game on a
finite vertex type, `i` a player, `U ⊆ X`, and `A = attr X i U`. Then `U ⊆ A ⊆ X`; the
complement `X \ A` is again a subgame and a trap for `i` (no `i`-vertex there has an edge into `A`
within `X`); and every play in `X` that starts in `A` and conforms to a strategy of `i` agreeing
with the attractor strategy on `A \ U` reaches `U`. -/
theorem Game.attractorCorrect (G : Game V) [Finite V] (X : Set V) (i : Player) (U : Set V)
    (hX : G.IsSubgame X) (hU : U ⊆ X) :
    (U ⊆ G.attr X i U ∧ G.attr X i U ⊆ X) ∧
    G.IsSubgame (X \ G.attr X i U) ∧
    (∀ v ∈ X \ G.attr X i U, G.owner v = i → ∀ w ∈ X, G.edge v w → w ∉ G.attr X i U) ∧
    ∀ σ : Strategy V,
      (∀ v ∈ G.attr X i U, v ∉ U → G.owner v = i → σ v = G.attrStrategy X i U v) →
      ∀ p : ωSequence V, G.ConformingPlay X i σ p → p 0 ∈ G.attr X i U → ∃ n, p n ∈ U := sorry

/-! ## Fatal attractors (Theorem 2 of [Huth2014]) -/

/-- **Fatal attractors are won (Theorem 2 of [Huth2014]).** Let `X` be a subgame, `c` a priority,
and `T ⊆ X` a set of vertices of priority `c` that is fatal in `X` (`IsFatal`). Then the player
favoured by `c` (`Player.ofPrio c`) wins from every vertex of the monotone attractor `MA(T)` within
`X`, with the monotone attractor strategy. See `Game.FatalAttractorWins`
(`ParityGame/FatalAttractor.lean`). -/
theorem Game.fatalAttractorWins (G : Game V) (X : Set V) (c : ℕ) (T : Set V) :
    G.FatalAttractorWins X c T := sorry

/-! ## Fatal-attractor implementation (`FatalAttractorOriginal`, Figure 3 of [Huth2014]) -/

/-- **The fatal-attractor solver is sound (Figure 3 of [Huth2014]).** Let `X` be a subgame of a
game on a finite vertex type, `js` any processing order of the priorities, and `r` a sound partial
solution of `X` (`SoundPartial`: each `r.win i` is a closed region that `i` wins with
`r.strat i`). Then `fatalAttractorOriginal X js r` is again a sound partial solution of `X`, and
its winning regions contain those of `r`. See `Game.FatalAttractorOriginalSound`
(`ParityGame/Implementation.lean`). -/
theorem Game.fatalAttractorOriginalSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : G.FatalAttractorOriginalSound X js r := sorry

/-! ## Zielonka's recursive algorithm ([Zielonka1998]) -/

/-- **Zielonka's algorithm is correct ([Zielonka1998]).** For a game on a finite vertex type, the
solution `G.zielonka` solves the whole game (`Solves Set.univ`): the two winning regions partition
the vertices, and each player's positional strategy wins from every vertex of that player's
region. In particular, parity games are positionally determined. See `Game.ZielonkaCorrect`
(`ParityGame/Zielonka.lean`). -/
theorem Game.zielonka_correct (G : Game V) [Finite V] : G.ZielonkaCorrect := sorry

end MercLib.ParityGame
