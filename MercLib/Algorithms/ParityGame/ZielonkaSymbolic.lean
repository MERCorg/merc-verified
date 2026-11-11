module

public import MercLib.Algorithms.ParityGame.Zielonka
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# Zielonka's algorithm on vertex sets

The symbolic formulation of Zielonka's algorithm, as `merc_vpg` runs it on decision diagrams
(website page *Zielonka's algorithm*): every step is an operation on sets of vertices, and the
attractor is the least fixed point `μZ. U ∪ cpre_α(Z)`, computed by iterating `cpre` until nothing
changes. Sets are modelled by `Finset`, so the algorithm is executable; the decision diagrams of
merc are not modelled.

The recursion is the one of `Game.zielonkaAux`; it returns only the winning regions. Both recursive
calls are guarded by the vertex set getting smaller. The guards always hold (the first because the
vertices of the highest priority are removed, the second because `W'_ᾱ` is non-empty), and the
`else` branches only make the definition total.

## Main definitions

- `Game.cpre`: the control predecessor of `Z` for player `α` inside the subgame `X`.
- `Game.attrSym`: the attractor, as a fixed-point iteration.
- `Game.zielonkaSym`: the winning regions `W₀, W₁`.

## Main claims

- `Game.AttrSymCorrect`: `attrSym` computes the attractor `Game.attr`.
- `Game.ZielonkaSymCorrect`: the regions partition the vertices, and each player has a positional
  strategy that wins from every vertex of its region.
-/

namespace MercLib.ParityGame

variable {V : Type*} [Fintype V] [DecidableEq V] (G : Game V) [DecidableRel G.edge]

/-- The control predecessor `cpre_α(Z)` inside the subgame `X`: the vertices of `X` of player `α`
with a successor in `Z`, and those of the opponent with all successors in `X` inside `Z`. -/
def Game.cpre (X : Finset V) (α : Player) (Z : Finset V) : Finset V :=
  X.filter fun v =>
    (G.owner v = α ∧ ∃ w ∈ Z, G.edge v w) ∨ (G.owner v ≠ α ∧ ∀ w ∈ X, G.edge v w → w ∈ Z)

/-- The attractor `Attr_α(U)` inside the subgame `X`: grow `Z` from `U` by `cpre_α(Z)` until it
is a fixed point. -/
def Game.attrSym (X : Finset V) (α : Player) (U : Finset V) : Finset V := Id.run do
  let mut Z := U
  while Z ∪ G.cpre X α Z ≠ Z do
    Z := Z ∪ G.cpre X α Z
  return Z

/-- Zielonka's algorithm on the subgame `X`: the winning regions of the two players. -/
def Game.zielonkaSymAux (G : Game V) [DecidableRel G.edge] (X : Finset V) : Player → Finset V :=
  if _hX : X.Nonempty then
    let d := X.sup G.prio                               -- the highest priority present
    let α := Player.ofPrio d
    let U := X.filter fun v => G.prio v = d
    let A := G.attrSym X α U
    if _h₁ : (X \ A).card < X.card then
      let W' := G.zielonkaSymAux (X \ A)
      if W' α.opp = ∅ then
        fun p => if p = α then X else ∅                 -- `α` wins all of `X`
      else
        let B := G.attrSym X α.opp (W' α.opp)
        if _h₂ : (X \ B).card < X.card then
          let W'' := G.zielonkaSymAux (X \ B)
          fun p => if p = α then W'' α else W'' α.opp ∪ B
        else fun _ => ∅
    else fun _ => ∅
  else fun _ => ∅
termination_by X.card

/-- Zielonka's algorithm on the whole game. -/
def Game.zielonkaSym : Player → Finset V := G.zielonkaSymAux Finset.univ

/-- **The fixed-point iteration computes the attractor.** -/
def Game.AttrSymCorrect : Prop :=
  ∀ (X : Finset V) (α : Player) (U : Finset V),
    (G.attrSym X α U : Set V) = G.attr (X : Set V) α (U : Set V)

/-- **Zielonka's algorithm on vertex sets is correct**: the regions partition the vertices, and
each player has a positional strategy that wins from every vertex of its region. -/
def Game.ZielonkaSymCorrect : Prop :=
  (G.zielonkaSym .zero : Set V) ∪ G.zielonkaSym .one = Set.univ ∧
    Disjoint (G.zielonkaSym .zero) (G.zielonkaSym .one) ∧
    ∀ i, ∃ σ : Strategy V, ∀ v ∈ G.zielonkaSym i, G.WinsFrom Set.univ i σ v

end MercLib.ParityGame
