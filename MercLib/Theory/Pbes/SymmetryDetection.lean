module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Algebra.Group.End

@[expose] public section

/-!
# Symmetry detection graphs

The symmetry detection graph (SDG) of a PBES ([M. Bartels, M. Laveaux, T. Neele and
T. Willemse, *Symmetry Detection Graphs and Symmetry Reduction for Parameterised Boolean Equation
Systems*][Bartels2026], Section 3), and the theorem that the restriction of an SDG automorphism
to the parameters is a symmetry (Theorem 2 of the paper).

The paper's SDG is undirected and leaves the edges of an update vertex uncoloured. With either,
Theorem 2 is false (`UndirectedUnsound` and `UncolouredUpdatesUnsound`). This file defines the
SDG that merc builds: arcs go from a formula to its direct subformulas, from a PVI to its update
vertices, and from an update vertex to its argument and its parameter, and the arcs of an update
vertex are coloured with their roles.

The model follows the paper's single-sorted presentation: one data domain `D`, function symbols
`F` interpreted by `I`, and Boolean terms interpreted by `T`. Terms and predicate formulas share
one syntax `Expr`, since the SDG has a vertex for both. A function symbol is *commutative*
(`comm f`) when `I f [a, b] = I f [b, a]`; as in merc, the arcs of an application are only
uncoloured when a commutative symbol is applied to two arguments.

See [Symmetry detection graph](https://mercorg.github.io/merc-website/model-checking/symmetry/symmetry-detection-graph/#thm-symmetries-from-automorphisms-blnw).

## Main definitions

- `Expr`: data terms and predicate formulas over parameters `d₀, …, dₙ₋₁`.
- `Expr.act`: the group action `π(φ)` of a parameter permutation (Definition 4).
- `IsSymmetry`: `π(φ_X) ≡ φ_X` for every equation (Definition 5).
- `Arc`, `vertices`, `colour`, `arcColour`: the directed, coloured SDG.
- `IsAut`: an automorphism of a coloured graph (Definition 7).
- `Expr.size`: the vertex size (Definition 8).

## Main statements

- `RhsFixed`: an automorphism maps every right-hand side to itself (Lemma 1).
- `SizePreserved`: an automorphism preserves vertex size (Lemma 2).
- `AgreesWithAct`: an automorphism acts on a vertex as its restriction to the parameters
  (Lemma 3).
- `RestrictionExists`, `SymmetryFromAutomorphism`: the restriction of an automorphism to the
  parameters is a symmetry (Theorem 2).
- `UndirectedUnsound`, `UncolouredUpdatesUnsound`: Theorem 2 fails for the undirected SDG, and
  for the directed SDG with uncoloured update arcs.

## References

- [M. Bartels, M. Laveaux, T. Neele and T. Willemse, *Symmetry Detection Graphs and Symmetry
  Reduction for Parameterised Boolean Equation Systems*][Bartels2026]
-/

namespace MercLib.Symmetry

/-- Data terms and predicate formulas, with parameters `par k` and bound variables `var x`. -/
inductive Expr (F P : Type) (n : ℕ) where
  /-- The parameter `d_k`. -/
  | par (k : Fin n)
  /-- A variable bound by a quantifier. -/
  | var (x : ℕ)
  /-- The data term `f(t₁, …, tₘ)`. -/
  | app (f : F) (ts : List (Expr F P n))
  /-- The predicate variable instantiation (PVI) `X(t₁, …, tₙ)`. -/
  | pvi (X : P) (ts : List (Expr F P n))
  /-- `φ ∧ ψ`. -/
  | and (φ ψ : Expr F P n)
  /-- `φ ∨ ψ`. -/
  | or (φ ψ : Expr F P n)
  /-- `∀ x : D. φ`. -/
  | all (x : ℕ) (φ : Expr F P n)
  /-- `∃ x : D. φ`. -/
  | ex (x : ℕ) (φ : Expr F P n)

namespace Expr

variable {F P : Type} {n : ℕ}

/-- The value of a data term; `default` for a predicate formula. -/
def eval {D : Type} [Inhabited D] (I : F → List D → D) (σ : Fin n → D) (β : ℕ → D) :
    Expr F P n → D
  | par k => σ k
  | var x => β x
  | app f ts => I f (ts.map (eval I σ β))
  | _ => default

/-- `⟦φ⟧ηδ`: whether `φ` holds for the predicate environment `η`, the parameter values `σ` and
the bound variables `β`. A data term holds when its value satisfies `T`. -/
def holds {D : Type} [Inhabited D] (I : F → List D → D) (T : D → Prop) (η : P → Set (List D)) :
    (Fin n → D) → (ℕ → D) → Expr F P n → Prop
  | σ, β, pvi X ts => ts.map (eval I σ β) ∈ η X
  | σ, β, and φ ψ => holds I T η σ β φ ∧ holds I T η σ β ψ
  | σ, β, or φ ψ => holds I T η σ β φ ∨ holds I T η σ β ψ
  | σ, β, all x φ => ∀ d, holds I T η σ (Function.update β x d) φ
  | σ, β, ex x φ => ∃ d, holds I T η σ (Function.update β x d) φ
  | σ, β, t => T (eval I σ β t)

/-- `φ ≡ ψ`: the formulas hold in the same environments. -/
def Equivalent {D : Type} [Inhabited D] (I : F → List D → D) (T : D → Prop)
    (φ ψ : Expr F P n) : Prop :=
  ∀ η σ β, holds I T η σ β φ ↔ holds I T η σ β ψ

/-- `t[π]`: every parameter `d_k` is replaced by `d_{π(k)}`. -/
def subst (π : Equiv.Perm (Fin n)) : Expr F P n → Expr F P n
  | par k => par (π k)
  | var x => var x
  | app f ts => app f (ts.map (subst π))
  | pvi X ts => pvi X (ts.map (subst π))
  | and φ ψ => and (subst π φ) (subst π ψ)
  | or φ ψ => or (subst π φ) (subst π ψ)
  | all x φ => all x (subst π φ)
  | ex x φ => ex x (subst π φ)

/-- The group action `π(φ)` of Definition 4: `π(b) = b[π]` for a data term, and
`π(X(t₁, …, tₙ)) = X(t_{π⁻¹(1)}[π], …, t_{π⁻¹(n)}[π])`. -/
def act (π : Equiv.Perm (Fin n)) : Expr F P n → Expr F P n
  | pvi X ts => pvi X (List.ofFn fun m : Fin n => ((ts[(π.symm m : ℕ)]?).getD (var 0)).subst π)
  | and φ ψ => and (act π φ) (act π ψ)
  | or φ ψ => or (act π φ) (act π ψ)
  | all x φ => all x (act π φ)
  | ex x φ => ex x (act π φ)
  | t => t.subst π

/-- `sub♯(φ)`, the direct subformulas (Definition 6), as a list. -/
def subD : Expr F P n → List (Expr F P n)
  | par _ => []
  | var _ => []
  | app _ ts => ts
  | pvi _ ts => ts
  | and φ ψ => [φ, ψ]
  | or φ ψ => [φ, ψ]
  | all _ φ => [φ]
  | ex _ φ => [φ]

/-- `sub(φ)`, all subformulas (Definition 6), in pre-order. -/
def sub : Expr F P n → List (Expr F P n)
  | par k => [par k]
  | var x => [var x]
  | app f ts => app f ts :: ts.flatMap sub
  | pvi X ts => pvi X ts :: ts.flatMap sub
  | and φ ψ => and φ ψ :: (sub φ ++ sub ψ)
  | or φ ψ => or φ ψ :: (sub φ ++ sub ψ)
  | all x φ => all x φ :: sub φ
  | ex x φ => ex x φ :: sub φ

/-- `ispvi(φ)`. -/
def isPvi : Expr F P n → Bool
  | pvi _ _ => true
  | _ => false

/-- The PVIs of `φ` in pre-order: `PVI(X, i)` is the `i`'th element for `φ = φ_X`. -/
def pvis (φ : Expr F P n) : List (Expr F P n) := (sub φ).filter isPvi

/-- The vertex size `|φ|` (Definition 8). -/
def size : Expr F P n → ℕ
  | par _ => 1
  | var _ => 1
  | app _ ts => 1 + (ts.map size).sum
  | pvi _ ts => 1 + (ts.map size).sum
  | and φ ψ => size φ + size ψ
  | or φ ψ => size φ + size ψ
  | all _ φ => 1 + size φ
  | ex _ φ => 1 + size φ

end Expr

open Expr

/-- An equation `σX(d) = φ`. The fixpoint sign plays no role in symmetry detection. -/
structure Equation (F P : Type) (n : ℕ) where
  /-- Whether the equation is a greatest fixpoint. -/
  nu : Bool
  /-- The bound predicate variable. -/
  X : P
  /-- The right-hand side `φ_X`. -/
  φ : Expr F P n

/-- A PBES whose equations all have the parameters `d₀, …, dₙ₋₁`. -/
abbrev Pbes (F P : Type) (n : ℕ) := List (Equation F P n)

variable {F P : Type} {n : ℕ}

/-- `sub(E)`. -/
def subE (E : Pbes F P n) : List (Expr F P n) := E.flatMap fun e => e.φ.sub

/-- Every predicate variable has one equation, and every PVI has one argument per parameter. -/
def WellFormed (E : Pbes F P n) : Prop :=
  (E.map Equation.X).Nodup ∧ ∀ X ts, Expr.pvi X ts ∈ subE E → ts.length = n

/-- `π` is a symmetry of `E` (Definition 5): `π(φ_X) ≡ φ_X` for every equation. -/
def IsSymmetry {D : Type} [Inhabited D] (I : F → List D → D) (T : D → Prop)
    (E : Pbes F P n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ e ∈ E, Equivalent I T (e.φ.act π) e.φ

/-! ## The symmetry detection graph -/

/-- A vertex of the SDG: a subformula or parameter, or the update vertex `X_{i,k}`. -/
inductive Vertex (F P : Type) (n : ℕ) where
  | expr (φ : Expr F P n)
  | upd (X : P) (i : ℕ) (k : Fin n)

open Vertex

/-- `V = sub(E) ∪ pars(E) ∪ updates(E)`. -/
def vertices (E : Pbes F P n) : Set (Vertex F P n) :=
  {v | (∃ φ ∈ subE E, v = expr φ) ∨ (∃ k, v = expr (par k)) ∨
    ∃ e ∈ E, ∃ i < e.φ.pvis.length, ∃ k, v = upd e.X i k}

/-- `PVI(X, i) = p` for the equation `e` of `X`. -/
def IsPviAt (e : Equation F P n) (i : ℕ) (p : Expr F P n) : Prop := e.φ.pvis[i]? = some p

/-- The directed arcs of the SDG: from a formula that is not a PVI to its direct subformulas,
from `PVI(X, i)` to `X_{i,k}`, and from `X_{i,k}` to `data(X, i, k)` and to `d_k`. -/
def Arc (E : Pbes F P n) (u v : Vertex F P n) : Prop :=
  (∃ φ ∈ subE E, φ.isPvi = false ∧ ∃ ψ ∈ φ.subD, u = expr φ ∧ v = expr ψ) ∨
  ∃ e ∈ E, ∃ i p, IsPviAt e i p ∧ ∃ k : Fin n,
    (u = expr p ∧ v = upd e.X i k) ∨
    (u = upd e.X i k ∧ ∃ t, p.subD[(k : ℕ)]? = some t ∧ v = expr t) ∨
    (u = upd e.X i k ∧ v = expr (par k))

/-- The edges of the undirected SDG of the paper. -/
def Edge (E : Pbes F P n) (u v : Vertex F P n) : Prop := Arc E u v ∨ Arc E v u

/-- `C_Φ`, the colour of a vertex that describes its formula. -/
inductive ShapeColour (F P : Type) where
  | par
  | var (x : ℕ)
  | fn (f : F)
  | pvi (X : P)
  | and
  | or
  | all (x : ℕ)
  | ex (x : ℕ)
  | upd

/-- `C_Φ(v)`. -/
def shapeColour : Vertex F P n → ShapeColour F P
  | expr (par _) => .par
  | expr (var x) => .var x
  | expr (app f _) => .fn f
  | expr (pvi X _) => .pvi X
  | expr (Expr.and _ _) => .and
  | expr (Expr.or _ _) => .or
  | expr (all x _) => .all x
  | expr (ex x _) => .ex x
  | upd _ _ _ => .upd

/-- `C(v) = (C_Φ(v), C_RHS(v))` with `C_RHS(v) = {X | v = φ_X}`. -/
def colour (E : Pbes F P n) (v : Vertex F P n) : ShapeColour F P × Set P :=
  (shapeColour v, {X | ∃ e ∈ E, e.X = X ∧ v = expr e.φ})

/-- The role of an arc of an update vertex. -/
inductive Role where
  | pvi
  | data
  | par

/-- The colour of an arc. -/
inductive ArcColour where
  /-- No colour, `⊥`. -/
  | bot
  /-- The positions `{i | t = tᵢ}` of the argument `t` of `f(t₁, …, tₘ)`. -/
  | pos (s : Set ℕ)
  /-- The roles of an arc of an update vertex. -/
  | roles (s : Set Role)

/-- The colour of the arc of an application `f(t₁, …, tₘ)` to its argument `t`: `⊥` when `f` is
commutative and `m = 2`, and the positions of `t` otherwise. Every other arc is `⊥`. -/
noncomputable def termArcColour (comm : F → Prop) : Vertex F P n → Vertex F P n → ArcColour
  | expr (app f ts), expr t =>
    open Classical in if comm f ∧ ts.length = 2 then .bot else .pos {i | ts[i]? = some t}
  | _, _ => .bot

/-- The arc colouring of merc: the arcs of an update vertex are coloured with their roles,
`{pvi}` for the arc from the PVI, and `{data}`, `{par}` or `{data, par}` for its arcs to
`data(X, i, k)` and `d_k`, which coincide when the argument is `d_k` itself. -/
noncomputable def arcColour (comm : F → Prop) (E : Pbes F P n) : Vertex F P n → Vertex F P n → ArcColour
  | expr _, upd _ _ _ => .roles {.pvi}
  | upd X i k, v => .roles ({r | r = .par ∧ v = expr (par k)} ∪
      {r | r = .data ∧ ∃ e ∈ E, e.X = X ∧ ∃ p, IsPviAt e i p ∧ ∃ t,
        p.subD[(k : ℕ)]? = some t ∧ v = expr t})
  | u, v => termArcColour comm u v

/-- The paper's arc colouring, in which the arcs of an update vertex are uncoloured. -/
noncomputable def paperArcColour (comm : F → Prop) : Vertex F P n → Vertex F P n → ArcColour :=
  termArcColour comm

/-- The colour of an undirected edge `{u, v}`: the colour of the arc between them. -/
noncomputable def edgeColour (E : Pbes F P n) (col : Vertex F P n → Vertex F P n → ArcColour)
    (u v : Vertex F P n) : ArcColour :=
  open Classical in if Arc E u v then col u v else col v u

/-- `h ∈ Aut(G)` (Definition 7) for the graph with vertices `vertices E`, vertex colouring
`colour E`, edge relation `R` and edge colouring `col`: `h` is a bijection on the vertices that
preserves the colour of every vertex, maps every edge to an edge, and preserves its colour. -/
def IsAut (E : Pbes F P n) (R : Vertex F P n → Vertex F P n → Prop)
    (col : Vertex F P n → Vertex F P n → ArcColour) (h : Vertex F P n → Vertex F P n) : Prop :=
  Set.BijOn h (vertices E) (vertices E) ∧
  (∀ v ∈ vertices E, colour E (h v) = colour E v) ∧
  ∀ u v, R u v → R (h u) (h v) ∧ col (h u) (h v) = col u v

/-- `h` is an automorphism of the directed SDG that merc builds. -/
def IsSdgAut (comm : F → Prop) (E : Pbes F P n) (h : Vertex F P n → Vertex F P n) : Prop :=
  IsAut E (Arc E) (arcColour comm E) h

/-- `π = h|pars(E)`. -/
def Restricts (h : Vertex F P n → Vertex F P n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, h (expr (par k)) = expr (par (π k))

/-- The interpretation of every commutative symbol is commutative. -/
def CommSound {D : Type} (I : F → List D → D) (comm : F → Prop) : Prop :=
  ∀ f, comm f → ∀ a b, I f [a, b] = I f [b, a]

/-! ## Claims -/

/-- **Lemma 1.** An automorphism maps every right-hand side to itself. -/
def RhsFixed (comm : F → Prop) (E : Pbes F P n) : Prop :=
  WellFormed E → ∀ h, IsSdgAut comm E h → ∀ e ∈ E, h (expr e.φ) = expr e.φ

/-- **Lemma 2.** An automorphism maps a subformula or parameter to a formula of the same size. -/
def SizePreserved (comm : F → Prop) (E : Pbes F P n) : Prop :=
  WellFormed E → ∀ h, IsSdgAut comm E h → ∀ φ, (φ ∈ subE E ∨ ∃ k, φ = par k) →
    ∃ ψ, h (expr φ) = expr ψ ∧ ψ.size = φ.size

/-- **Lemma 3.** An automorphism `h` maps a subformula or parameter `φ` to a formula with the
same value and semantics as `π(φ)`, for `π = h|pars(E)`. -/
def AgreesWithAct {D : Type} [Inhabited D] (I : F → List D → D) (T : D → Prop)
    (comm : F → Prop) (E : Pbes F P n) : Prop :=
  CommSound I comm → WellFormed E → ∀ h π, IsSdgAut comm E h → Restricts h π →
    ∀ φ, (φ ∈ subE E ∨ ∃ k, φ = par k) → ∃ ψ, h (expr φ) = expr ψ ∧
      ∀ η σ β, ψ.eval I σ β = (φ.act π).eval I σ β ∧
        (ψ.holds I T η σ β ↔ (φ.act π).holds I T η σ β)

/-- **Theorem 2, first part.** Every automorphism restricts to a permutation of the parameters. -/
def RestrictionExists (comm : F → Prop) (E : Pbes F P n) : Prop :=
  ∀ h, IsSdgAut comm E h → ∃ π, Restricts h π

/-- **Theorem 2.** The restriction of an SDG automorphism to the parameters is a symmetry. -/
def SymmetryFromAutomorphism {D : Type} [Inhabited D] (I : F → List D → D) (T : D → Prop)
    (comm : F → Prop) (E : Pbes F P n) : Prop :=
  CommSound I comm → WellFormed E → ∀ h π, IsSdgAut comm E h → Restricts h π →
    IsSymmetry I T E π

/-! ## Counterexamples for the paper's SDG -/

/-- The function symbol `==` on Booleans, the only symbol of the counterexamples. -/
inductive BoolSym where
  | eq
  deriving DecidableEq

/-- `==` is interpreted as equality of Booleans. -/
def boolI : BoolSym → List Bool → Bool
  | .eq, [a, b] => a == b
  | .eq, _ => false

/-- `==` is commutative. -/
def boolComm : BoolSym → Prop := fun _ => True

/-- **The undirected SDG is unsound.** There is a well-formed PBES and an automorphism of its
undirected SDG, with merc's colouring, whose restriction to the parameters is not a symmetry. -/
def UndirectedUnsound : Prop :=
  ∃ (E : Pbes BoolSym ℕ 3) (h : Vertex BoolSym ℕ 3 → Vertex BoolSym ℕ 3) (π : Equiv.Perm (Fin 3)), WellFormed E ∧ IsAut E (Edge E) (edgeColour E (arcColour boolComm E)) h ∧
    Restricts h π ∧ ¬ IsSymmetry boolI (· = true) E π

/-- **Uncoloured update arcs are unsound.** There is a well-formed PBES and an automorphism of
its directed SDG with the paper's uncoloured update arcs, whose restriction to the parameters is
not a symmetry. -/
def UncolouredUpdatesUnsound : Prop :=
  ∃ (E : Pbes BoolSym ℕ 3) (h : Vertex BoolSym ℕ 3 → Vertex BoolSym ℕ 3) (π : Equiv.Perm (Fin 3)), WellFormed E ∧ IsAut E (Arc E) (paperArcColour boolComm) h ∧
    Restricts h π ∧ ¬ IsSymmetry boolI (· = true) E π

end MercLib.Symmetry
