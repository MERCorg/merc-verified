module

public import ParityGame.Defs

open Cslib (ωSequence)

@[expose] public section ProgressMeasure

namespace ParityGame

/-!
# Progress measures over an arbitrary priority-indexed ordered codomain

M. Jurdziński, *Small Progress Measures for Solving Parity Games*, STACS 2000, labels every node
with a tuple of natural numbers (one component per odd priority) such that along every edge
consistent with a strategy of player `0` the label does not increase when compared on the
components for priorities `≥ Ω(v)`, and strictly decreases there when `Ω(v)` is odd. Since the
labels come from a well-founded order, an odd priority cannot be the greatest one occurring
infinitely often, so player `0` wins.

Later work (Jurdziński–Lazić 2017; Czerwiński, Daviaud, Fijalkow, Jurdziński, Lazić, Parys,
*Universal trees grow inside separating automata: Quasi-polynomial lower bounds for parity games*,
SODA 2019) replaces the tuples by the leaves of an ordered *universal tree*, compared after
truncation to a given level. The soundness argument only uses the order structure, which is what
this file abstracts: a `Codomain` is a family of preorders `le p` indexed by priorities, getting
coarser as `p` grows (comparing only the components / tree levels for priorities `≥ p`), whose
strict part is well-founded at every odd level. Tuples, universal trees and arbitrary
instance-specific ordered trees with truncation all fit this interface, and the headline claim
`Game.ProgressMeasureSound` says that *any* progress measure over *any* such codomain certifies
that player `0` wins from every node of its domain — so lifting over a candidate codomain can only
under-approximate player `0`'s winning region, never be wrong.

**Modeling choices**
* MAX-parity convention (as in `ParityGame.Defs`): coarser comparison at higher priorities.
* The "⊤" value of Jurdziński's measures is not modelled; instead the measure comes with an
  explicit domain `D` (the nodes not mapped to ⊤), and the closure conditions on `D` express that
  the measure never progresses into ⊤.
* Well-foundedness is only required at odd levels: only those carry strict decreases.
-/

/-- A priority-indexed ordered codomain. `le p a b` reads "`a ≤ b` when only the components for
    priorities `≥ p` are compared". Each `le p` is a preorder; comparisons get coarser as `p` grows;
    and at every odd level the strict part is well-founded. -/
structure Codomain (M : Type*) where
  le : ℕ → M → M → Prop
  refl : ∀ p a, le p a a
  trans : ∀ p a b c, le p a b → le p b c → le p a c
  mono : ∀ p q a b, p ≤ q → le p a b → le q a b
  wf : ∀ p, p % 2 = 1 → WellFounded (fun a b => le p a b ∧ ¬ le p b a)

variable {V M : Type*}

/-- The progress condition for the edge `v → w` under the labelling `μ`: the label does not
    increase at level `Ω(v)`, and strictly decreases at that level if `Ω(v)` is odd. -/
def Game.Prog (G : Game V) (C : Codomain M) (μ : V → M) (v w : V) : Prop :=
  C.le (G.prio v) (μ w) (μ v) ∧ (G.prio v % 2 = 1 → ¬ C.le (G.prio v) (μ v) (μ w))

/-- `μ` is a progress measure on the domain `D ⊆ X` of the subgame `X`, witnessed by the strategy
    `σ` of player `0`: from a node of `D` owned by `0`, `σ` moves along an edge to `D` and
    progresses; from a node of `D` owned by `1`, every successor in `X` lies in `D` and the move
    progresses. -/
def Game.IsProgressMeasure (G : Game V) (X : Set V) (C : Codomain M) (D : Set V) (μ : V → M)
    (σ : Strategy V) : Prop :=
  D ⊆ X ∧
  (∀ v ∈ D, G.owner v = .zero → σ v ∈ D ∧ G.edge v (σ v) ∧ G.Prog C μ v (σ v)) ∧
  (∀ v ∈ D, G.owner v = .one → ∀ w ∈ X, G.edge v w → w ∈ D ∧ G.Prog C μ v w)

/-- Progress cycles are even: along a cycle `c 0 → c 1 → … → c k = c 0` (`k ≥ 1`) every edge of
    which satisfies the progress condition (for an arbitrary codomain and labelling), the greatest
    priority is even. An odd maximum `P` would make the labels non-increasing at level `P` all the
    way round while strictly decreasing at level `P` on the edge leaving a node of priority `P` —
    a strict cycle in the preorder `C.le P`, impossible even without well-foundedness. -/
def Game.ProgCycleEven (G : Game V) (C : Codomain M) (μ : V → M) : Prop :=
  ∀ (k : ℕ) (c : ℕ → V), 0 < k → c k = c 0 → (∀ i < k, G.Prog C μ (c i) (c (i + 1))) →
    ∀ i < k, (∀ j < k, G.prio (c j) ≤ G.prio (c i)) → G.prio (c i) % 2 = 0

/-- Soundness of progress measures: in a finite game, a progress measure over any codomain
    certifies that its witnessing strategy is winning for player `0` from every node of its
    domain. -/
def Game.ProgressMeasureSound [Finite V] (G : Game V) (X : Set V) (C : Codomain M) (D : Set V)
    (μ : V → M) (σ : Strategy V) : Prop :=
  G.IsSubgame X → G.IsProgressMeasure X C D μ σ → ∀ v ∈ D, G.WinsFrom X .zero σ v

end ParityGame

end ProgressMeasure
