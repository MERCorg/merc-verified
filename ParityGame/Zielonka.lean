module

public import ParityGame.Defs
public import ParityGame.Attractor
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat

open Cslib (ωSequence)

@[expose] public section Zielonka

namespace ParityGame

/-!
# Zielonka's recursive algorithm, with winning strategies

Zielonka's recursive algorithm [18 in O. Friedmann and M. Lange, *Solving Parity Games in
Practice*, ATVA 2009], the constructive proof of positional determinacy that the paper uses as one
of its backend solvers. On a (sub)game `X` with greatest priority `m`, owned by player
`i = Player.ofPrio m`:

1. `A := Attrᵢ(U)` for the nodes `U` of priority `m`; solve `X \ A` recursively.
2. If player `1 - i` wins nowhere in `X \ A`, player `i` wins all of `X`: use the attractor
   strategy on `A \ U`, an arbitrary move on `U`, and the recursive strategy on `X \ A`.
3. Otherwise `B := Attr₁₋ᵢ(W'₁₋ᵢ)` is won by `1 - i` (attractor strategy, then the recursive
   strategy); solve `X \ B` recursively, where the recursive results are kept by their owners.

**Modeling choices**
* All set operations go through classical choice (`noncomputable`); the attractor is the
  stage-wise definition of `ParityGame.Attractor`, not a worklist.
* Termination is by the size of `X`. The second recursive call is guarded by `X \ B ⊂ X`; the
  guard is always true (`B` contains the non-empty `W'₁₋ᵢ ⊆ X`), which is part of the correctness
  proof, and the `else` branch only exists to make the definition total.
-/

variable {V : Type*}

/-- The greatest priority of a node of `X`. -/
noncomputable def Game.maxPrio (G : Game V) (X : Set V) : ℕ := sSup (G.prio '' X)

open scoped Classical in
/-- Some successor inside `X` (the node itself if there is none). -/
noncomputable def Game.anyMove (G : Game V) (X : Set V) : Strategy V := fun v =>
  if h : ∃ w ∈ X, G.edge v w then h.choose else v

/-- The empty solution. -/
def Solution.empty : Solution V := ⟨fun _ => ∅, fun _ v => v⟩

open scoped Classical in
/-- Step 2 of the algorithm: player `i` wins all of `X`. Its strategy is the attractor strategy on
    `Attrᵢ(U) \ U`, an arbitrary move on `U`, and the recursive strategy `r₁.strat i` elsewhere. -/
noncomputable def Game.wonAll (G : Game V) (X : Set V) (i : Player) (U : Set V)
    (r₁ : Solution V) : Solution V where
  win := fun p => if p = i then X else ∅
  strat := fun p v =>
    if p = i then
      (if v ∈ G.attr X i U then (if v ∈ U then G.anyMove X v else G.attrStrategy X i U v)
        else r₁.strat i v)
    else v

open scoped Classical in
/-- Step 3 of the algorithm: `1 - i` wins `B := Attr₁₋ᵢ(W'₁₋ᵢ)` as well as its own region of the
    recursive solution `r₂` of `X \ B`; `i` keeps its region of `r₂`. -/
noncomputable def Game.wonSplit (G : Game V) (X : Set V) (i : Player)
    (r₁ r₂ : Solution V) : Solution V where
  win := fun p => if p = i then r₂.win i else r₂.win i.opp ∪ G.attr X i.opp (r₁.win i.opp)
  strat := fun p v =>
    if p = i then r₂.strat i v
    else
      (if v ∈ r₁.win i.opp then r₁.strat i.opp v
        else if v ∈ G.attr X i.opp (r₁.win i.opp) then G.attrStrategy X i.opp (r₁.win i.opp) v
        else r₂.strat i.opp v)

open scoped Classical in
/-- Zielonka's recursive algorithm on the subgame `X`. -/
noncomputable def Game.zielonkaAux (G : Game V) [Finite V] (X : Set V) : Solution V :=
  if _hX : X.Nonempty then
    let m := G.maxPrio X
    let i := Player.ofPrio m
    let U := {v | v ∈ X ∧ G.prio v = m}
    let r₁ := G.zielonkaAux (X \ G.attr X i U)
    if r₁.win i.opp = ∅ then G.wonAll X i U r₁
    else if _hB : X \ G.attr X i.opp (r₁.win i.opp) ⊂ X then
      G.wonSplit X i r₁ (G.zielonkaAux (X \ G.attr X i.opp (r₁.win i.opp)))
    else Solution.empty
  else Solution.empty
termination_by Set.ncard X
decreasing_by
  · refine Set.ncard_lt_ncard ?_ (Set.toFinite X)
    have hmem : G.maxPrio X ∈ G.prio '' X :=
      Nat.sSup_mem (_hX.image _) (Set.toFinite _).bddAbove
    obtain ⟨v, hv, hvm⟩ := hmem
    refine ⟨Set.sdiff_subset, fun hsub => ?_⟩
    exact (hsub hv).2 ⟨0, hv, hvm⟩
  · exact Set.ncard_lt_ncard _hB (Set.toFinite X)

/-- Zielonka's algorithm on the whole game. -/
noncomputable def Game.zielonka (G : Game V) [Finite V] : Solution V :=
  G.zielonkaAux Set.univ

/-- Contract (positional determinacy via Zielonka's algorithm): the winning regions returned for
    the whole game partition it, and each player's returned positional strategy wins from every
    node of that player's region. -/
def Game.ZielonkaCorrect (G : Game V) [Finite V] : Prop :=
  G.Solves Set.univ G.zielonka

end ParityGame

end Zielonka
