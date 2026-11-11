import MercLib.Theory.ParityGame.Game
import MercLib.Theory.ParityGame.Attractor
import MercLib.Theory.ParityGame.FatalAttractor
import MercLib.Implementation.ParityGame.FatalAttractor
import MercLib.Implementation.ParityGame.FatalAttractorsAlt
import MercLib.Algorithms.ParityGame.Zielonka
import MercLib.Algorithms.ParityGame.ZielonkaSymbolic
import MercLib.Theory.ParityGame.Valuation
import MercLib.Theory.ParityGame.Incomplete
import MercLib.Algorithms.ParityGame.Incomplete

/-!
# Comparator challenge: parity games (human-vetted)

The headline theorems of `MercLib/{Theory,Algorithms,Implementation}/ParityGame/`, stated with `sorry` against the human-vetted spec
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
with the attractor strategy on `A \ U` reaches `U`. See `Game.AttractorCorrect`
(`Theory/ParityGame/Attractor.lean`). -/
theorem Game.attractorCorrect (G : Game V) [Finite V] (X : Set V) (i : Player) (U : Set V) :
    G.AttractorCorrect X i U := sorry

/-! ## Fatal attractors (Theorem 2 of [Huth2014]) -/

/-- **Fatal attractors are won (Theorem 2 of [Huth2014]).** Let `X` be a subgame, `c` a priority,
and `T ⊆ X` a set of vertices of priority `c` that is fatal in `X` (`IsFatal`). Then the player
favoured by `c` (`Player.ofPrio c`) wins from every vertex of the monotone attractor `MA(T)` within
`X`, with the monotone attractor strategy. See `Game.FatalAttractorWins`
(`Theory/ParityGame/FatalAttractor.lean`). -/
theorem Game.fatalAttractorWins (G : Game V) (X : Set V) (c : ℕ) (T : Set V) :
    G.FatalAttractorWins X c T := sorry

/-- **Fatal attractors are won, as stated in the paper (Theorem 2 of [Huth2014]).** The same claim
as `Game.fatalAttractorWins`, in the convention of the paper: on a finite game, plays are decided by
the *least* colour occurring infinitely often and the monotone attractor passes through colours at
least `c`. Let `X` be a subgame, and `T ⊆ X` a set of vertices of colour `c` that is fatal in `X`
(`IsFatalMin`). Then the player favoured by `c` wins from every vertex of `MA(T)` with the attractor
strategy. See `Game.FatalAttractorWinsMin` (`Theory/ParityGame/FatalAttractor.lean`). -/
theorem Game.fatalAttractorWinsMin (G : Game V) [Finite V] (X : Set V) (c : ℕ) (T : Set V) :
    G.FatalAttractorWinsMin X c T := sorry

/-! ## Fatal-attractor implementation (`FatalAttractorOriginal`, Figure 3 of [Huth2014]) -/

/-- **The fatal-attractor solver is sound (Figure 3 of [Huth2014]).** Let `X` be a subgame of a
game on a finite vertex type, `js` any processing order of the priorities, and `r` a sound partial
solution of `X` (`SoundPartial`: each `r.win i` is a closed region that `i` wins with
`r.strat i`). Then `fatalAttractorOriginal X js r` is again a sound partial solution of `X`, and
its winning regions contain those of `r`. See `Game.FatalAttractorOriginalSound`
(`Implementation/ParityGame/FatalAttractor.lean`). -/
theorem Game.fatalAttractorOriginalSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : G.FatalAttractorOriginalSound X js r := sorry

/-! ## The alternative fatal-attractor implementation of mCRL2 (`fatal_attractors_generic`) -/

/-- **The fixed alternative fatal-attractor solver is sound.** Let `X` be a subgame of a game on a
finite vertex type, `js` any processing order of the priorities, and `r` a sound partial solution of
`X` (`SoundPartial`). Then `fatalAttractorsAlt X js r`, the model of mCRL2's
`fatal_attractors_generic` after the fix, is again a sound partial solution of `X`, and its winning
regions contain those of `r`. In particular the loop terminates. See `Game.FatalAttractorsAltSound`
(`Implementation/ParityGame/FatalAttractorsAlt.lean`). -/
theorem Game.fatalAttractorsAltSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : G.FatalAttractorsAltSound X js r := sorry

/-- **The alternative solver before the fix is unsound.** On the five-node game `cexGame`, starting
from the empty partial solution, which is sound, and processing priority `2`, the model
`fatalAttractorsAltBuggy` of `fatal_attractors_generic` before the fix puts the node `v` in the
region of player `0`, and its result is not a sound partial solution. See
`Game.FatalAttractorsAltBuggyUnsound` (`Implementation/ParityGame/FatalAttractorsAlt.lean`). -/
theorem Game.fatalAttractorsAltBuggyUnsound : Game.FatalAttractorsAltBuggyUnsound := sorry

/-- **Attractors in a trap can be computed in the whole game.** On a finite vertex type, if `Y ⊆ X`
is a trap for player `i` (every node of `i` in `Y` has all its successors in `X` inside `Y`) and
`W ⊆ Y`, then `X \ Attr_i(X \ W)`, with the attractor computed in `X`, equals `Y \ Attr_i(Y \ W)`,
with the attractor computed in the subgame `Y`. This is the update of the fixed loop. See
`Game.SubgameAttrCorrect` (`Implementation/ParityGame/FatalAttractorsAlt.lean`). -/
theorem Game.subgameAttrCorrect (G : Game V) [Finite V] (X Y W : Set V) (i : Player) :
    G.SubgameAttrCorrect X Y W i := sorry

/-! ## Zielonka's recursive algorithm ([Zielonka1998]) -/

/-- **Zielonka's algorithm is correct ([Zielonka1998]).** For a game on a finite vertex type, the
solution `G.zielonka` solves the whole game (`Solves Set.univ`): the two winning regions partition
the vertices, and each player's positional strategy wins from every vertex of that player's
region. In particular, parity games are positionally determined. See `Game.ZielonkaCorrect`
(`Algorithms/ParityGame/Zielonka.lean`). -/
theorem Game.zielonka_correct (G : Game V) [Finite V] : G.ZielonkaCorrect := sorry

/-- **The fixed-point iteration computes the attractor.** On a finite game with decidable edges,
growing `U` by the control predecessor `cpre_α` inside the subgame `X` until nothing changes
yields exactly the attractor `Game.attr X α U`. See `Game.AttrSymCorrect`
(`Algorithms/ParityGame/ZielonkaSymbolic.lean`). -/
theorem Game.attrSym_correct [Fintype V] [DecidableEq V] (G : Game V)
    [DecidableRel G.edge] : G.AttrSymCorrect := sorry

/-- **Zielonka's algorithm on vertex sets is correct.** The executable, set-based version of the
algorithm returns two regions that partition the vertices, and each player has a positional strategy
that wins from every vertex of its region. See `Game.ZielonkaSymCorrect`
(`Algorithms/ParityGame/ZielonkaSymbolic.lean`). -/
theorem Game.zielonkaSym_correct [Fintype V] [DecidableEq V] (G : Game V)
    [DecidableRel G.edge] : G.ZielonkaSymCorrect := sorry

/-! ## Incomplete parity games ([Laveaux2022]) -/

/-- **Lemma 1 of [Laveaux2022]: dominions in the safe vertices survive exploration.** For an
incomplete parity game `a` (a parity game, possibly with sinks, and a set `I` of vertices that may
still get successors), every `α`-dominion of `a ∩ safe_α(a)` is an `α`-dominion of every extension
`a'` of `a`. Extensions add vertices and edges, but no successors of complete vertices. See
`IncompleteGame.DominionsSurvive` (`Theory/ParityGame/Incomplete.lean`). -/
theorem IncompleteGame.dominionsSurvive (a : IncompleteGame V) : a.DominionsSurvive := sorry

/-- **Theorem 1 of [Laveaux2022]: the safe vertices are optimal.** Let `W_α` be the union of the
`α`-dominions of `a ∩ safe_α(a)` and `W_? = V \ (W_♦ ∪ W_□)`. On a finite vertex type with a vertex
outside `a`, a vertex of `a` is in `W_?` iff one player wins it (lies in one of its dominions) in
some extension of `a` and the opponent wins it in another. See `IncompleteGame.SafeOptimal`
(`Theory/ParityGame/Incomplete.lean`). -/
theorem IncompleteGame.safeOptimal [Finite V] (a : IncompleteGame V) : a.SafeOptimal := sorry

/-- **Lemma 2 of [Laveaux2022]: unsafe vertices can be lost.** If the vertex type has a vertex
outside the incomplete game `a`, there is an extension of `a` (a fresh sink of `α` reachable from
every incomplete vertex) in which the opponent `ᾱ` has a dominion containing every vertex outside
`safe_α(a)`. See `IncompleteGame.UnsafeLost` (`Theory/ParityGame/Incomplete.lean`). -/
theorem IncompleteGame.unsafeLost (a : IncompleteGame V) : a.UnsafeLost := sorry

/-- **Lemma 3 of [Laveaux2022].** For `X ⊆ safe_α(a)`, the control predecessor of `X` in the safe
subgame `a ∩ safe_α(a)` is the safe control predecessor `spre_α(a, X)`. See
`IncompleteGame.SafeCpreEq` (`Theory/ParityGame/Incomplete.lean`). -/
theorem IncompleteGame.safeCpreEq (a : IncompleteGame V) : a.SafeCpreEq := sorry

/-- **Lemma 4 of [Laveaux2022].** For `X ⊆ safe_α(a)`, the attractor of `X` in the safe subgame
`a ∩ safe_α(a)` is the safe attractor `SAttr_α(a, X)`. See `IncompleteGame.SafeAttrEq`
(`Theory/ParityGame/Incomplete.lean`). -/
theorem IncompleteGame.safeAttrEq (a : IncompleteGame V) : a.SafeAttrEq := sorry

/-- **Corollary 2 of [Laveaux2022].** If `X ⊆ safe_α(a)` is an `α`-dominion of the safe subgame
`a ∩ safe_α(a)`, then the safe attractor `SAttr_α(a, X)` is an `α`-dominion of every extension of
`a`. See `IncompleteGame.SAttrDominion` (`Theory/ParityGame/Incomplete.lean`). -/
theorem IncompleteGame.sAttrDominion (a : IncompleteGame V) : a.SAttrDominion := sorry

/-- **Corollary 3 of [Laveaux2022].** The safe `α`-attractor of the opponent's complete sinks,
`SAttr_α(a, sinks_ᾱ(a) \ I)`, is an `α`-dominion of every extension of `a`. See
`IncompleteGame.SinkAttrDominion` (`Theory/ParityGame/Incomplete.lean`). -/
theorem IncompleteGame.sinkAttrDominion (a : IncompleteGame V) : a.SinkAttrDominion := sorry

/-- **The iteration computes the attractor of an incomplete game.** For an incomplete parity game
with decidable vertices, incomplete vertices and edges on a finite type, iterating
`Z ↦ U ∪ cpre_α(a, Z)` from `∅` until nothing changes yields `Attr_α(a, U)`. See
`Incomplete.AttrCorrect` (`Algorithms/ParityGame/Incomplete.lean`). -/
theorem Incomplete.attr_correct [Fintype V] [DecidableEq V] (a : IncompleteGame V)
    [DecidablePred (· ∈ a.vs)] [DecidablePred (· ∈ a.I)] [DecidableRel a.edge] :
    Incomplete.AttrCorrect a := sorry

/-- **The computed safe set is `safe_α(a)`** ([Laveaux2022], Definition 4), the vertices of `a`
outside `Attr_ᾱ(a, V_ᾱ ∩ I)`. See `Incomplete.SafeCorrect`
(`Algorithms/ParityGame/Incomplete.lean`). -/
theorem Incomplete.safe_correct [Fintype V] [DecidableEq V] (a : IncompleteGame V)
    [DecidablePred (· ∈ a.vs)] [DecidablePred (· ∈ a.I)] [DecidableRel a.edge] :
    Incomplete.SafeCorrect a := sorry

/-- **The iteration computes the safe attractor** ([Laveaux2022], Section 4.1): iterating
`Z ↦ U ∪ spre_α(a, Z)` from `∅` until nothing changes yields `SAttr_α(a, U)`. See
`Incomplete.SAttrCorrect` (`Algorithms/ParityGame/Incomplete.lean`). -/
theorem Incomplete.sattr_correct [Fintype V] [DecidableEq V] (a : IncompleteGame V)
    [DecidablePred (· ∈ a.vs)] [DecidablePred (· ∈ a.I)] [DecidableRel a.edge] :
    Incomplete.SAttrCorrect a := sorry

end MercLib.ParityGame

namespace MercLib.HybridSI

open MercLib.ParityGame

/-- **The Vöge–Jurdziński valuation is faithful.** `key G` encodes the value of a play profile as an
integer triple whose lexicographic order is the order `≺` of the paper. See `KeyOrderEmbedding`
(`Theory/ParityGame/Valuation.lean`). -/
theorem keyOrderEmbedding {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) :
    KeyOrderEmbedding G := sorry

end MercLib.HybridSI
