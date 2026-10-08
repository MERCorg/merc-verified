module

public import ParityGame.Defs
public import ParityGame.Attractor
public import ParityGame.Zielonka
public import ParityGame.Scc
public import ParityGame.Transform
public import ParityGame.Special
public import Mathlib.Data.Set.Card

open Cslib (ωSequence)

@[expose] public section Generic

namespace ParityGame

/-!
# The generic solver

Section 3.5 of O. Friedmann and M. Lange, *Solving Parity Games in Practice*, ATVA 2009. The
generic solver takes a *backend* solver `S` and applies it only where the cheaper methods fail:

1. `solveSCC` solves a final SCC `C`: directly if it is a one-player or one-parity game, and
   otherwise by running `S` on `C` after compressing its priorities.
2. `step` first solves a self-cycle node if there is one, and otherwise a final SCC.
3. `genericAux` repeatedly takes a step, adds the attractors (inside the remaining subgame) of
   the winning regions found to the solution, removes them, and continues with what is left.

**Modeling choices**
* The paper eliminates self-cycles once, before the SCC loop. Here a self-cycle node is looked for
  in every iteration (so also after attractor removal); this only makes the solver do more work
  directly and does not affect correctness.
* The paper removes the attractors of both players' regions found in one SCC at once, which is what
  `genericAux` does (`X \ A₀ \ A₁` with `Aᵢ` the `i`-attractor in `X`).
* As in `zielonkaAux` the recursion is guarded by a strict-decrease test that always succeeds.
-/

variable {V : Type*}

/-- A backend solver: it is given a game and a subgame and returns a solution of that subgame. -/
abbrev Backend (V : Type*) := Game V → Set V → Solution V

/-- A backend is sound if it solves every subgame (the paper only requires soundness and progress,
    we require it to be complete, as Zielonka's algorithm is). -/
def Backend.Sound (S : Backend V) : Prop :=
  ∀ (G : Game V) (X : Set V), G.IsSubgame X → G.Solves X (S G X)

/-- Zielonka's algorithm as a backend. -/
noncomputable def zielonkaBackend [Finite V] : Backend V := fun G X => G.zielonkaAux X

open scoped Classical in
/-- Lines 6-13 of the generic solver: solve the final SCC `C`. -/
noncomputable def Game.solveSCC (G : Game V) (S : Backend V) (C : Set V) : Solution V :=
  if h : ∃ i, G.OnePlayer C i then G.onePlayerSolve C h.choose
  else if h : ∃ i, G.OneParity C i then G.oneParitySolve C h.choose
  else S (G.withPrio (compress (G.prio '' C) ∘ G.prio)) C

open scoped Classical in
/-- Solve a self-cycle node of `X` if there is one, and otherwise a final SCC of `X`. -/
noncomputable def Game.step (G : Game V) (S : Backend V) (X : Set V) : Solution V :=
  if h : ∃ v, G.IsSelfCycle X v then G.selfCycleSolve h.choose
  else G.solveSCC S (G.finalSCC X)

/-- What remains of `X` after removing the attractors of both players' regions in `r`
    (`(G \ A₀) \ A₁` in the paper). -/
def Game.remainder (G : Game V) (X : Set V) (r : Solution V) : Set V :=
  (X \ G.attr X Player.zero (r.win Player.zero)) \ G.attr X Player.one (r.win Player.one)

open scoped Classical in
/-- Add the attractors of the regions of `r` (with the attractor strategies) to the solution `r'`
    of what remains of `X`. -/
noncomputable def Game.merge (G : Game V) (X : Set V) (r r' : Solution V) : Solution V where
  win := fun i => G.attr X i (r.win i) ∪ r'.win i
  strat := fun i v =>
    if v ∈ r.win i then r.strat i v
    else if v ∈ G.attr X i (r.win i) then G.attrStrategy X i (r.win i) v
    else r'.strat i v

open scoped Classical in
/-- The main loop of the generic solver on the subgame `X`. -/
noncomputable def Game.genericAux (G : Game V) [Finite V] (S : Backend V) (X : Set V) :
    Solution V :=
  if _hX : X.Nonempty then
    let r := G.step S X
    if _h : G.remainder X r ⊂ X then G.merge X r (G.genericAux S (G.remainder X r))
    else Solution.empty
  else Solution.empty
termination_by Set.ncard X
decreasing_by exact Set.ncard_lt_ncard _h (Set.toFinite X)

/-- The generic solver on the whole game. -/
noncomputable def Game.genericSolve (G : Game V) [Finite V] (S : Backend V) : Solution V :=
  G.genericAux S Set.univ

/-- Contract (Section 3.5): the generic solver with a sound backend solves every finite game. -/
def Game.GenericCorrect (G : Game V) [Finite V] (S : Backend V) : Prop :=
  S.Sound → G.Solves Set.univ (G.genericSolve S)

end ParityGame

end Generic
