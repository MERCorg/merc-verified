module

public import MercLib.TwoSided.TwoSidedAlgorithm

@[expose] public section Certificate

namespace MercLib.ParityGame

/-!
# A checkable two-sided certificate for the winning regions

A *certificate* for a finite parity game `G` is a pair of progress measures: one for player `0` in
`G` and one for player `1`, i.e. for player `0` in the dual game `G.dual` (priorities `+ 1`,
owners swapped). A node in the domain of the first is won by player `0`, a node in the domain of
the second is won by player `1`; if the two domains cover all nodes, the winning regions of both
players are certified without trusting any solver.

Validity (`Game.CertValid`) consists of *local* conditions only — one comparison of two labels per
edge, plus covering — and does not mention the chain tree: the labels are tuples of numbers
compared lexicographically on the first `Game.chainDepth` coordinates, a function of the
priorities alone. Hence checking a certificate takes time polynomial in the size of the game; the
size of a certificate is polynomial too (`Game.CertComplete`).

## Headlines (proved in `ParityGame.Proofs.Certificate_Proofs`)
* `Game.CertSound`: a valid certificate determines the winning regions of both players.
* `Game.CertComplete`: every finite game has a valid certificate, with at most `2 * height`
  non-zero coordinates per label, each at most `|V|`, and `height ≤ |V|`.

**Not claimed.** Uniqueness of the certificate (that would be a UP statement), and any statement
about how a solver produces a certificate or how fast. The checker's cost is modelled separately.
-/

variable {V : Type*}

/-- The progress condition of the certificate along the edge `v → w`: the labels, compared
    lexicographically on the first `Game.chainDepth` coordinates for the priority of `v`, do not
    increase from `v` to `w`, and strictly decrease if the priority of `v` is odd. -/
def Game.CertProg [Finite V] (G : Game V) (μ : V → ℕ → ℕ) (v w : V) : Prop :=
  LexLE (G.chainDepth Set.univ (G.prio v)) (μ w) (μ v) ∧
    (G.prio v % 2 = 1 → ¬ LexLE (G.chainDepth Set.univ (G.prio v)) (μ v) (μ w))

/-- `μ` is a certificate labelling for player `0` on the domain `D` with witnessing strategy `σ`:
    from a node of `D` owned by player `0`, `σ` moves along an edge to `D` and progresses; from a
    node of `D` owned by player `1`, every successor lies in `D` and the move progresses. -/
def Game.CertPM [Finite V] (G : Game V) (D : Set V) (μ : V → ℕ → ℕ) (σ : Strategy V) : Prop :=
  (∀ v ∈ D, G.owner v = .zero → σ v ∈ D ∧ G.edge v (σ v) ∧ G.CertProg μ v (σ v)) ∧
  (∀ v ∈ D, G.owner v = .one → ∀ w, G.edge v w → w ∈ D ∧ G.CertProg μ v w)

/-- A two-sided certificate: a labelling with strategy and domain for player `0` in `G`
    (`μ₀, σ₀, D₀`), and one for player `0` in `G.dual`, i.e. for player `1` in `G`
    (`μ₁, σ₁, D₁`). -/
structure Game.Cert (V : Type*) where
  μ₀ : V → ℕ → ℕ
  σ₀ : Strategy V
  D₀ : Set V
  μ₁ : V → ℕ → ℕ
  σ₁ : Strategy V
  D₁ : Set V

/-- The certificate `c` is valid for `G`: both labellings are certificate labellings (the second
    in the dual game) and their domains cover all nodes. -/
def Game.CertValid [Finite V] (G : Game V) (c : Game.Cert V) : Prop :=
  G.CertPM c.D₀ c.μ₀ c.σ₀ ∧ G.dual.CertPM c.D₁ c.μ₁ c.σ₁ ∧ c.D₀ ∪ c.D₁ = Set.univ

/-- Contract (soundness): a valid certificate determines both winning regions of the whole game:
    `D₀` is exactly the set of nodes won by player `0` and `D₁` exactly the set won by
    player `1`. -/
def Game.CertSound [Finite V] (G : Game V) (c : Game.Cert V) : Prop :=
  G.CertValid c → ∀ v, (v ∈ c.D₀ ↔ G.Wins Set.univ .zero v) ∧ (v ∈ c.D₁ ↔ G.Wins Set.univ .one v)

/-- Contract (completeness, with small labels): every finite game has a valid certificate whose
    labels have at most `2 * height` non-zero coordinates, each at most the number of nodes, where
    the height (the number of odd priorities) is itself at most the number of nodes. So a
    certificate has polynomially many numbers of logarithmic bit-length. -/
def Game.CertComplete [Finite V] (G : Game V) : Prop :=
  G.height Set.univ ≤ Nat.card V ∧ G.dual.height Set.univ ≤ Nat.card V ∧
  ∃ c : Game.Cert V, G.CertValid c ∧
    (∀ v ∈ c.D₀, ∀ i, c.μ₀ v i ≤ Nat.card V ∧ (2 * G.height Set.univ ≤ i → c.μ₀ v i = 0)) ∧
    (∀ v ∈ c.D₁, ∀ i, c.μ₁ v i ≤ Nat.card V ∧ (2 * G.dual.height Set.univ ≤ i → c.μ₁ v i = 0))

end MercLib.ParityGame

end Certificate
