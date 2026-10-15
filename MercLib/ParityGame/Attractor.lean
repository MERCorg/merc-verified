module

public import MercLib.ParityGame.Game

open Cslib (ωSequence)

@[expose] public section

namespace MercLib.ParityGame

/-!
# Attractors and attractor strategies

Section 2 of
[O. Friedmann and M. Lange, *Solving Parity Games in Practice*][Friedmann2009], ATVA 2009.

The `i`-attractor of `U` inside the subgame `X` is the limit of the stages
`Attr⁰ = U`, `Attrᵏ⁺¹ = Attrᵏ ∪ {v ∈ Vᵢ | ∃ w ∈ Attrᵏ, vEw} ∪ {v ∈ V₁₋ᵢ | ∀ w, vEw → w ∈ Attrᵏ}`,
with all moves restricted to `X`. The attractor strategy sends a node of `Vᵢ` first reached at
stage `k > 0` to a successor in stage `k - 1`.
-/

variable {V : Type*}

/-- The `k`-th stage `Attrᵏᵢ(U)` of the attractor computation inside `X`. -/
def Game.attrStage (G : Game V) (X : Set V) (i : Player) (U : Set V) : ℕ → Set V
  | 0 => U
  | k + 1 =>
    G.attrStage X i U k ∪
      {v | v ∈ X ∧
        ((G.owner v = i ∧ ∃ w ∈ G.attrStage X i U k, G.edge v w) ∨
         (G.owner v ≠ i ∧ ∀ w ∈ X, G.edge v w → w ∈ G.attrStage X i U k))}

/-- The `i`-attractor `Attrᵢ(U) = ⋃ₖ Attrᵏᵢ(U)` of `U` inside `X`. -/
def Game.attr (G : Game V) (X : Set V) (i : Player) (U : Set V) : Set V :=
  {v | ∃ k, v ∈ G.attrStage X i U k}

open scoped Classical in
/-- The stage at which `v` first enters the attractor (`0` for nodes outside it). -/
noncomputable def Game.attrRank (G : Game V) (X : Set V) (i : Player) (U : Set V) (v : V) : ℕ :=
  if h : ∃ k, v ∈ G.attrStage X i U k then Nat.find h else 0

open scoped Classical in
/-- The attractor strategy `σ^Attr_i` (Section 2): a node first reached at stage `k > 0` moves to a
    successor in stage `k - 1`; everything else (including `U` itself) maps to the node itself. -/
noncomputable def Game.attrStrategy (G : Game V) (X : Set V) (i : Player) (U : Set V) :
    Strategy V := fun v =>
  if h : 0 < G.attrRank X i U v ∧ ∃ w ∈ G.attrStage X i U (G.attrRank X i U v - 1), G.edge v w
  then h.2.choose else v

end MercLib.ParityGame
