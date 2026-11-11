module

public import MercLib.Theory.ParityGame.Game

@[expose] public section

/-!
# Incomplete parity games

Section 3 of [M. Laveaux, W. Wesselink and T. A. C. Willemse, *On-The-Fly Solving for Symbolic
Parity Games*][Laveaux2022], TACAS 2022. A game explored on the fly is only partly known: an
*incomplete parity game* `a = (G, I)` (Definition 2) is a parity game `G` whose vertices in `I` may
still get successors.

**Modelling choices**
* The parity game `G` of the paper (Definition 1) has a finite vertex set and may have *sinks*,
  vertices without successors. `IncompleteGame` holds its fields directly, next to `I`: a vertex set
  `vs` inside the type `V`, and owners and priorities as functions on all of `V`, of which only the
  values on `vs` matter. As in the paper, notions of `G` are written for `a`: `a.pre U` is
  `pre(a, U)`, `a.attr α U` is `Attr_α(a, U)`, and `(G, ∅)` is a parity game. The total games of
  `Game` are not used, since an unexplored vertex has no known successors.
* A player who cannot move loses. Winning is defined through the total game
  `IncompleteGame.toGame` on `V ⊕ Player`, in which a sink of player `p` moves to the vertex
  `inr p.opp`, a self-loop with a priority that favours `p.opp`.
* Definition 3 of the paper restricts the new edges of complete vertices by
  `((V \ I) × V) ∩ E' ⊆ E`. Read literally, a complete vertex may then get an edge to a *new*
  vertex, and Lemma 1 fails: an opponent vertex of a dominion escapes along it. The proof of
  Lemma 1 uses `((V \ I) × V') ∩ E' ⊆ E`, which `Extends` states: a complete vertex gets no new
  successors at all.

## Main definitions

- `IncompleteGame` (Definition 2), `restrict` (`a ∩ U`), `pre`, `sinks`, `cpre`, `attr`.
- `toGame`, `IsDominion`: winning, through the total encoding.
- `Extends` (`a ⊑ a'`, Definition 3), `safe` (Definition 4).
- `spre`, `sattr`: the safe control predecessor and safe attractor (Section 4.1).

## Main claims

- `SafeCpreEq` (Lemma 3) and `SafeAttrEq` (Lemma 4): inside the `α`-safe vertices, the safe
  control predecessor and attractor of `a` are the ordinary ones of `a ∩ safe_α(a)`.
- `DominionsSurvive` (Lemma 1): an `α`-dominion of `a ∩ safe_α(a)` is an `α`-dominion of every
  extension of `a`.
- `UnsafeLost` (Lemma 2): the vertices outside `safe_α(a)` are won by the opponent in some
  extension.
- `SafeOptimal` (Theorem 1): the vertices in no safe dominion are exactly those whose winner
  depends on the extension.
- `SAttrDominion` (Corollary 2) and `SinkAttrDominion` (Corollary 3): safe attractors of safe
  dominions, and of the opponent's complete sinks, are dominions of every extension.
-/

namespace MercLib.ParityGame

open Cslib (ωSequence)

variable {V : Type*}

/-- An incomplete parity game `a = (G, I)` ([Laveaux2022], Definitions 1 and 2): a parity game
with vertices `vs`, owners, edges between vertices of `vs` and priorities, in which sinks are
allowed, and the vertices `I ⊆ vs` that may still get successors. -/
structure IncompleteGame (V : Type*) where
  vs : Set V
  owner : V → Player
  edge : V → V → Prop
  prio : V → ℕ
  edge_mem : ∀ v w, edge v w → v ∈ vs ∧ w ∈ vs
  I : Set V
  I_sub : I ⊆ vs

namespace IncompleteGame

variable (a : IncompleteGame V)

/-- `a ∩ U = (G ∩ U, I ∩ U)`: the subgame on the vertices of `a` in `U`. -/
def restrict (U : Set V) : IncompleteGame V where
  vs := a.vs ∩ U
  owner := a.owner
  edge v w := a.edge v w ∧ v ∈ U ∧ w ∈ U
  prio := a.prio
  edge_mem v w h := ⟨⟨(a.edge_mem v w h.1).1, h.2.1⟩, ⟨(a.edge_mem v w h.1).2, h.2.2⟩⟩
  I := a.I ∩ U
  I_sub _ hv := ⟨a.I_sub hv.1, hv.2⟩

/-- `V_α`: the vertices of player `α`. -/
def own (α : Player) : Set V := {v | v ∈ a.vs ∧ a.owner v = α}

/-- `pre(a, U)`: the vertices with a successor in `U`. -/
def pre (U : Set V) : Set V := {v | v ∈ a.vs ∧ ∃ w ∈ U, a.edge v w}

/-- `sinks(a)`: the vertices without successors. -/
def sinks : Set V := {v | v ∈ a.vs ∧ ∀ w, ¬ a.edge v w}

/-- `cpre_α(a, U)`: the vertices of `α` with a successor in `U`, and those of the opponent that
are not sinks and have all successors in `U`. -/
def cpre (α : Player) (U : Set V) : Set V :=
  (a.own α ∩ a.pre U) ∪ (a.own α.opp \ (a.pre (a.vs \ U) ∪ a.sinks))

/-- The stages `A₀ = ∅`, `Aₖ₊₁ = U ∪ cpre_α(a, Aₖ)` of the attractor. -/
def attrStage (a : IncompleteGame V) (α : Player) (U : Set V) : ℕ → Set V
  | 0 => ∅
  | k + 1 => U ∪ a.cpre α (a.attrStage α U k)

/-- `Attr_α(a, U) = μZ. U ∪ cpre_α(a, Z)`. -/
def attr (α : Player) (U : Set V) : Set V := {v | ∃ k, v ∈ a.attrStage α U k}

open scoped Classical in
/-- The total game encoding `a`: the vertices of `a` with their edges, a sink of `p` moving to
`inr p.opp`, and the self-loops `inr q` with priority `0` for `zero` and `1` for `one`, so that
`inr q` is won by `q`. -/
noncomputable def toGame : Game (V ⊕ Player) where
  owner
    | .inl v => a.owner v
    | .inr q => q
  edge
    | .inl v, .inl w => a.edge v w
    | .inl v, .inr q => v ∈ a.sinks ∧ q = (a.owner v).opp ∨ v ∉ a.vs ∧ q = .zero
    | .inr q, .inr q' => q' = q
    | .inr _, .inl _ => False
  prio
    | .inl v => a.prio v
    | .inr .zero => 0
    | .inr .one => 1
  total
    | .inl v => by
      by_cases hv : v ∈ a.vs
      · by_cases hs : v ∈ a.sinks
        · exact ⟨.inr (a.owner v).opp, Or.inl ⟨hs, rfl⟩⟩
        · have : ∃ w, a.edge v w := by
            by_contra h
            exact hs ⟨hv, fun w hw => h ⟨w, hw⟩⟩
          obtain ⟨w, hw⟩ := this
          exact ⟨.inl w, hw⟩
      · exact ⟨.inr .zero, Or.inr ⟨hv, rfl⟩⟩
    | .inr q => ⟨.inr q, rfl⟩

/-- The vertices of the encoding that belong to the subgame on `U`: those of `U` and the
self-loops that a sink leads to. -/
def embed (U : Set V) : Set (V ⊕ Player) := Sum.inl '' U ∪ Set.range Sum.inr

/-- `D` is an `α`-dominion of `a`: `D` consists of vertices of `a`, the opponent cannot leave
`D`, and `α` has a positional strategy that stays in `D` and wins every play from `D`. -/
def IsDominion (α : Player) (D : Set V) : Prop :=
  D ⊆ a.vs ∧ (∀ v ∈ D, a.owner v ≠ α → ∀ w, a.edge v w → w ∈ D) ∧
    ∃ σ : Strategy (V ⊕ Player), ∀ v ∈ D, a.toGame.WinsFrom (embed D) α σ (.inl v)

/-- `a ⊑ a'` ([Laveaux2022], Definition 3, with the new edges of complete vertices excluded
towards all vertices, see the module documentation): `a'` has more vertices with the same owners
and priorities, more edges, no new successors of complete vertices, and no new incomplete
vertices among the old ones. -/
def Extends (a' : IncompleteGame V) : Prop :=
  a.vs ⊆ a'.vs ∧ (∀ v ∈ a.vs, a'.owner v = a.owner v) ∧
    (∀ v w, a.edge v w → a'.edge v w) ∧
    (∀ v ∈ a.vs \ a.I, ∀ w, a'.edge v w → a.edge v w) ∧
    (∀ v ∈ a.vs, a'.prio v = a.prio v) ∧
    a'.I ∩ a.vs ⊆ a.I

/-- `safe_α(a) = V \ Attr_ᾱ(a, V_ᾱ ∩ I)` ([Laveaux2022], Definition 4). -/
def safe (α : Player) : Set V := a.vs \ a.attr α.opp (a.own α.opp ∩ a.I)

/-- The safe control predecessor `spre_α(a, U)` (Section 4.1): as `cpre`, but an opponent vertex
also must not be incomplete. -/
def spre (α : Player) (U : Set V) : Set V :=
  (a.own α ∩ a.pre U) ∪ (a.own α.opp \ (a.pre (a.vs \ U) ∪ a.sinks ∪ a.I))

/-- The stages of the safe attractor. -/
def sattrStage (a : IncompleteGame V) (α : Player) (U : Set V) : ℕ → Set V
  | 0 => ∅
  | k + 1 => U ∪ a.spre α (a.sattrStage α U k)

/-- The safe attractor `SAttr_α(a, U) = μZ. U ∪ spre_α(a, Z)` (Section 4.1). -/
def sattr (α : Player) (U : Set V) : Set V := {v | ∃ k, v ∈ a.sattrStage α U k}

/-- **Lemma 3 of [Laveaux2022].** For `X ⊆ safe_α(a)`,
`cpre_α(a ∩ safe_α(a), X) = spre_α(a, X)`. -/
def SafeCpreEq : Prop :=
  ∀ α X, X ⊆ a.safe α → (a.restrict (a.safe α)).cpre α X = a.spre α X

/-- **Lemma 4 of [Laveaux2022].** For `X ⊆ safe_α(a)`,
`Attr_α(a ∩ safe_α(a), X) = SAttr_α(a, X)`. -/
def SafeAttrEq : Prop :=
  ∀ α X, X ⊆ a.safe α → (a.restrict (a.safe α)).attr α X = a.sattr α X

/-- **Lemma 1 of [Laveaux2022].** An `α`-dominion of `a ∩ safe_α(a)` is an `α`-dominion of every
extension of `a`. -/
def DominionsSurvive : Prop :=
  ∀ α D (a' : IncompleteGame V), a.Extends a' →
    (a.restrict (a.safe α)).IsDominion α D → a'.IsDominion α D

/-- **Lemma 2 of [Laveaux2022].** If the type `V` has a vertex outside `a`, there is an extension
of `a` in which the opponent `ᾱ` has a dominion containing every vertex outside `safe_α(a)`. The
paper states this for the vertices of an `α`-dominion `W` outside `safe_α(a)`; its proof covers all
of them at once. -/
def UnsafeLost : Prop :=
  (∃ z, z ∉ a.vs) → ∀ α, ∃ a' : IncompleteGame V, a.Extends a' ∧
    ∃ D, a'.IsDominion α.opp D ∧ a.vs \ a.safe α ⊆ D

/-- Player `i` wins `v` in `a`: `v` lies in an `i`-dominion of `a`. -/
def Wins (i : Player) (v : V) : Prop := ∃ D, a.IsDominion i D ∧ v ∈ D

/-- `W_α`: the union of the `α`-dominions of `a ∩ safe_α(a)`. -/
def safeWon (α : Player) : Set V := {v | (a.restrict (a.safe α)).Wins α v}

/-- `W_? = V \ (W_♦ ∪ W_□)`: the vertices that are in no safe dominion. -/
def undecided : Set V := a.vs \ (a.safeWon .zero ∪ a.safeWon .one)

/-- **Theorem 1 of [Laveaux2022].** On a finite vertex type with room for a vertex outside `a`,
`W_?` consists exactly of the vertices of `a` that one player wins in some extension of `a` and the
opponent wins in another. -/
def SafeOptimal [Finite V] : Prop :=
  (∃ z, z ∉ a.vs) → ∀ v ∈ a.vs, v ∈ a.undecided ↔
    ∃ α, ∃ a₁ a₂ : IncompleteGame V, a.Extends a₁ ∧ a.Extends a₂ ∧ a₁.Wins α v ∧
      a₂.Wins α.opp v

/-- **Corollary 2 of [Laveaux2022].** For an `α`-dominion `X ⊆ safe_α(a)` of `a ∩ safe_α(a)`,
`SAttr_α(a, X)` is an `α`-dominion of every extension of `a`. -/
def SAttrDominion : Prop :=
  ∀ α X (a' : IncompleteGame V), a.Extends a' → X ⊆ a.safe α →
    (a.restrict (a.safe α)).IsDominion α X → a'.IsDominion α (a.sattr α X)

/-- **Corollary 3 of [Laveaux2022].** The safe `α`-attractor of the complete sinks of the
opponent, `SAttr_α(a, sinks_ᾱ(a) \ I)`, is an `α`-dominion of every extension of `a`. -/
def SinkAttrDominion : Prop :=
  ∀ α (a' : IncompleteGame V), a.Extends a' →
    a'.IsDominion α (a.sattr α ((a.own α.opp ∩ a.sinks) \ a.I))

end IncompleteGame

end MercLib.ParityGame
