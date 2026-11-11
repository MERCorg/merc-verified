module

public import MercLib.Theory.ParityGame.Incomplete
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# Safe vertices and safe attractors

The set computations of Section 4.1 of [M. Laveaux, W. Wesselink and T. A. C. Willemse,
*On-The-Fly Solving for Symbolic Parity Games*][Laveaux2022]. Every operation is the paper's
formula on sets of vertices, and every least fixed point `μZ. f(Z)` is computed by the iteration
`∅, f(∅), f(f(∅)), …` until nothing changes. Since only set operations are used, the computations
apply to explicit and symbolic representations of the sets alike; here a set is a `Finset`.

The incomplete game is an `IncompleteGame` whose vertex set, incomplete vertices and edge relation
are decidable. The definitions are in the namespace `Incomplete`, next to the set-valued ones of
`IncompleteGame` that they compute.

## Main definitions

- `Incomplete.lfp`: the least fixed point `μZ. f(Z)` by iteration from `∅`.
- `Incomplete.pre`, `sinks`, `cpre`, `spre`: `pre(a, U)`, `sinks(a)`, `cpre_α(a, U)` and
  `spre_α(a, U)`.
- `Incomplete.attr`: `Attr_α(a, U) = μZ. U ∪ cpre_α(a, Z)`.
- `Incomplete.safe`: `safe_α(a) = V \ Attr_ᾱ(a, V_ᾱ ∩ I)` (Definition 4).
- `Incomplete.sattr`: `SAttr_α(a, U) = μZ. U ∪ spre_α(a, Z)`.

## Main claims

- `Incomplete.AttrCorrect`, `SafeCorrect`, `SAttrCorrect`: the computations return
  `IncompleteGame.attr`, `IncompleteGame.safe` and `IncompleteGame.sattr`.
-/

namespace MercLib.ParityGame.Incomplete

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The least fixed point `μZ. f(Z)`: iterate `f` from `∅` until nothing changes. -/
def lfp (f : Finset V → Finset V) : Finset V := Id.run do
  let mut Z := ∅
  while f Z ≠ Z do
    Z := f Z
  return Z

variable (a : IncompleteGame V) [DecidablePred (· ∈ a.vs)] [DecidablePred (· ∈ a.I)]
  [DecidableRel a.edge]

/-- The vertices `V` of `a`. -/
def vs : Finset V := Finset.univ.filter (· ∈ a.vs)

/-- The incomplete vertices `I`. -/
def I : Finset V := Finset.univ.filter (· ∈ a.I)

/-- `V_α`: the vertices of player `α`. -/
def own (α : Player) : Finset V := (vs a).filter fun v => a.owner v = α

/-- `pre(a, U)`: the vertices with a successor in `U`. -/
def pre (U : Finset V) : Finset V := (vs a).filter fun v => ∃ w ∈ U, a.edge v w

/-- `sinks(a)`: the vertices without successors. -/
def sinks : Finset V := (vs a).filter fun v => ∀ w, ¬ a.edge v w

/-- `cpre_α(a, U) = (V_α ∩ pre(a, U)) ∪ (V_ᾱ \ (pre(a, V \ U) ∪ sinks(a)))`. -/
def cpre (α : Player) (U : Finset V) : Finset V :=
  (own a α ∩ pre a U) ∪ (own a α.opp \ (pre a (vs a \ U) ∪ sinks a))

/-- `spre_α(a, U) = (V_α ∩ pre(a, U)) ∪ (V_ᾱ \ (pre(a, V \ U) ∪ sinks(a) ∪ I))`. -/
def spre (α : Player) (U : Finset V) : Finset V :=
  (own a α ∩ pre a U) ∪ (own a α.opp \ (pre a (vs a \ U) ∪ sinks a ∪ I a))

/-- `Attr_α(a, U) = μZ. U ∪ cpre_α(a, Z)`. -/
def attr (α : Player) (U : Finset V) : Finset V := lfp fun Z => U ∪ cpre a α Z

/-- `safe_α(a) = V \ Attr_ᾱ(a, V_ᾱ ∩ I)` ([Laveaux2022], Definition 4). -/
def safe (α : Player) : Finset V := vs a \ attr a α.opp (own a α.opp ∩ I a)

/-- `SAttr_α(a, U) = μZ. U ∪ spre_α(a, Z)` ([Laveaux2022], Section 4.1). -/
def sattr (α : Player) (U : Finset V) : Finset V := lfp fun Z => U ∪ spre a α Z

/-- **The iteration computes the attractor** `Attr_α(a, U)`. -/
def AttrCorrect : Prop := ∀ α U, (attr a α U : Set V) = a.attr α U

/-- **The computed safe set is** `safe_α(a)`. -/
def SafeCorrect : Prop := ∀ α, (safe a α : Set V) = a.safe α

/-- **The iteration computes the safe attractor** `SAttr_α(a, U)`. -/
def SAttrCorrect : Prop := ∀ α U, (sattr a α U : Set V) = a.sattr α U

end MercLib.ParityGame.Incomplete
