module

public import MercLib.HybridSI.Potential

@[expose] public section HybridSIBounds

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Structural bounds for H-B runs

Claims about the traces (`RunTrace`, `HybridSI.Potential`) of H-B. The paper proofs are in
`~/parity-polynomial/experiments/hb_bound/README.md` (P2: the sandwich),
`hb_nest/README.md` (O1) and `hb_epochs_count/README.md` (autonomy lemma). Nothing here is
proved; proofs go to `HybridSI/Proofs/Bounds_*.lean`.

**The sandwich (P2).** `Ξ_k = key G (ps k)` is the valuation of Even's strategy `σ_k` (keys of
Odd's best response), `K*_j = key G pstar` with `pstar` Even's best response to `ps j` (the
optimum of the one-player game against Odd's strategy of `ps j`), and `v*` the optimal valuation:
the keys of a *saddle* profile (`Saddle`: no player has a strictly improving move). Saddle
valuations are unique (`SaddleUnique`) and exist on relabelled games (`SaddleExists`), and along
every trace `Ξ_k ≤ v* ≤ K*_j` (`Sandwich`), in particular `Ξ_k ≤ K*_j` (`LowerBelowUpper`, which
needs no saddle).

**Autonomy on closed subgames (hb_epochs_count sec. 3) and O1 (hb_nest sec. 2).** A finite set
`D` is closed (`Closed`) if no edge leaves it; then `subgame G D hD : Game D` is the game
restricted to `D` (with the induced relevance order). `Autonomy`: along every trace of H-B on
`G`, the restrictions to `D` of the profiles and of Odd's best responses form a trace of H-B on
the subgame, up to the iteration `LD` at which the subgame's run is final; from then on the
restriction to `D` is frozen. `ClosedIterations` (O1): with enough fuel for the best responses
the whole run has at most `T(D) + ∏_{v ∉ D} deg v` iterations, `T(D)` the length of the
subgame's run from the restricted initial profile.

**Decisive elements (hb_bound P4, hb_g1 lemma M).** `TruncationMonotone` (M): while the cycle
maximum of `v` stays the same, every truncation `B_k(v) ∩ [x, ∞)` of the set `B` of its play value
is non-decreasing in the signed weight. `DecisiveRounds` (P4): in a stretch of iterations without
a change of any cycle maximum in which no element above `x` enters or leaves any `B` (decisive
element `δ ≤ x`), at most `n` iterations change the membership of `x` in some `B` (`δ = x`); in
fact every vertex contributes at most one such iteration.

**Resets need Odd changes (hb_reset, session 3).** Iteration `k` is *`l`-stable* (`LStable`) if
it changes no cycle maximum, and has *decisive element at most `x`* (`DecisiveLe`) if no element
above `x` enters or leaves any `B`. `EpochDecisive` (EDEC2): if Odd's best responses agree at the
states `a, …, j + 1` (`SameOdd`), the iterations `a, …, j` are `l`-stable and the iterations
`a, …, j - 1` have decisive element at most `x`, then so has iteration `j`. Consequences:
`EpochNoReset` (ESEP: inside an epoch and an `l`-interval the decisive elements never rise above
a bound they once satisfied) and `ResetLocal` (LOC: a first jump of the decisive element above
`x` is adjacent to a change of Odd's best response).
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- `q` is a saddle profile: it follows edges, no Odd vertex has a successor of strictly smaller
    key and no Even vertex a successor of strictly larger key (keys of `q` itself). Its keys are
    the optimal valuation `v*`. -/
def Saddle (G : Game V) (q : V → V) : Prop :=
  (∀ v, G.edge v (q v)) ∧
  (∀ u, G.owner u = .one → ∀ w, G.edge u w → key G q (q u) ≤ key G q w) ∧
  (∀ u, G.owner u = .zero → ∀ w, G.edge u w → key G q w ≤ key G q (q u))

/-- Contract (uniqueness of the optimal valuation): any two saddle profiles have the same keys. -/
def SaddleUnique (G : Game V) : Prop :=
  ∀ q q' : V → V, Saddle G q → Saddle G q' → key G q = key G q'

/-- Contract (existence of the optimal valuation): every relabelled game has a saddle profile
    (the final profile of H-B). -/
def SaddleExists (G : Game V) [DecidableRel G.edge] : Prop :=
  G.Relabelled → ∃ q : V → V, Saddle G q

/-- Contract (`Ξ_k ≤ K*_j`): along a trace, the valuation of every iteration is pointwise at most
    the keys of Even's best response to Odd's best response of any iteration. -/
def LowerBelowUpper (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ k ≤ L, ∀ j ≤ L, ∀ pstar, respond G false bf (ps j) = some pstar →
      ∀ v, key G (ps k) v ≤ key G pstar v

/-- Contract (the sandwich `Ξ_k ≤ v* ≤ K*_j`, P2): along a trace, for every saddle profile `q`,
    the valuation of every iteration is pointwise at most `v* = key G q`, which is pointwise at
    most the keys of Even's best response to Odd's best response of any iteration. -/
def Sandwich (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ q, Saddle G q →
    (∀ k ≤ L, ∀ v, key G (ps k) v ≤ key G q v) ∧
    ∀ j ≤ L, ∀ pstar, respond G false bf (ps j) = some pstar → ∀ v, key G q v ≤ key G pstar v

/-- `D` is closed: no edge leaves `D`. -/
def Closed (G : Game V) (D : Finset V) : Prop := ∀ v ∈ D, ∀ w, G.edge v w → w ∈ D

/-- The subgame of `G` on a closed set `D`: owners, edges and priorities restricted to `D`. -/
def subgame (G : Game V) (D : Finset V) (hD : Closed G D) : Game D where
  owner a := G.owner a.1
  edge a b := G.edge a.1 b.1
  prio a := G.prio a.1
  total a := by
    obtain ⟨w, hw⟩ := G.total a.1
    exact ⟨⟨w, hD a.1 a.2 w hw⟩, hw⟩

instance (G : Game V) [DecidableRel G.edge] (D : Finset V) (hD : Closed G D) :
    DecidableRel (subgame G D hD).edge := fun a b => ‹DecidableRel G.edge› a.1 b.1

/-- Contract (autonomy lemma): on a relabelled game, along a trace of H-B on `G` and for a
    closed `D`, the profiles `pD k` and Odd's best responses `psD k` of the subgame on `D`
    restrict those of `G` (`k ≤ L`) and form a trace of H-B on the subgame of some length
    `LD ≤ L`; if `LD < L` the iteration of the subgame from `pD LD` is final, and the
    restriction to `D` stays `pD LD` up to `L`. -/
def Autonomy (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (D : Finset V) (hD : Closed G D) (L : ℕ) (p ps : ℕ → V → V),
    RunTrace G bf L p ps → ∃ (pD psD : ℕ → D → D) (LD : ℕ), LD ≤ L ∧
      (∀ k ≤ L, ∀ a : D, (pD k a).1 = p k a.1 ∧ (psD k a).1 = ps k a.1) ∧
      RunTrace (subgame G D hD) bf LD pD psD ∧
      (LD < L → ∃ kt, hbStep (subgame G D hD) bf (pD LD) = .done kt) ∧
      ∀ k, LD ≤ k → k ≤ L → pD k = pD LD

/-- Contract (O1, closed subgames add at most the number of profiles outside): on a relabelled
    game, with fuel `hbFuel V` for the best responses, if the run of H-B on the subgame on a
    closed `D`, from the restriction of `p 0`, is final after `LD` iterations, then every trace
    of H-B on `G` from `p 0` has at most `LD + ∏_{v ∉ D} deg v` iterations. -/
def ClosedIterations (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → hbFuel V ≤ bf → ∀ (D : Finset V) (hD : Closed G D) (L : ℕ)
    (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ (LD : ℕ) (pD psD : ℕ → D → D),
      (∀ a : D, (pD 0 a).1 = p 0 a.1) → RunTrace (subgame G D hD) bf LD pD psD →
      (∃ kt, hbStep (subgame G D hD) bf (pD LD) = .done kt) →
      L ≤ LD + ∏ v ∈ Dᶜ, (Finset.univ.filter (G.edge v)).card

/-- Contract (lemma M, truncation monotonicity): along a trace, if the cycle maximum of `v` is the
    same at iterations `k ≤ k'`, then for every threshold `x` the signed weight of the part of `B`
    at or above `x` does not decrease from `k` to `k'`. -/
def TruncationMonotone (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ k k', k ≤ k' → k' ≤ L → ∀ v,
    cycMax (ps k) v = cycMax (ps k') v → ∀ x : V,
      ∑ y ∈ (bSet (ps k) v).filter (x ≤ ·), weight G y ≤
        ∑ y ∈ (bSet (ps k') v).filter (x ≤ ·), weight G y

/-- Contract (P4): along a trace, in a stretch of iterations `j ≤ k < j'` in which no cycle
    maximum changes and no element above `x` enters or leaves the set `B` of any vertex, at most
    `n` iterations change the membership of `x` in the set `B` of some vertex. -/
def DecisiveRounds (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ (j j' : ℕ) (x : V), j' ≤ L →
    (∀ k, j ≤ k → k < j' → ∀ v, cycMax (ps k) v = cycMax (ps (k + 1)) v) →
    (∀ k, j ≤ k → k < j' → ∀ v y, x < y → (y ∈ bSet (ps k) v ↔ y ∈ bSet (ps (k + 1)) v)) →
    ((Finset.Ico j j').filter fun k =>
      ∃ v, ¬ (x ∈ bSet (ps k) v ↔ x ∈ bSet (ps (k + 1)) v)).card ≤ Fintype.card V

/-- Iteration `k` changes no cycle maximum. -/
def LStable (ps : ℕ → V → V) (k : ℕ) : Prop := ∀ v, cycMax (ps k) v = cycMax (ps (k + 1)) v

/-- Iteration `k` has decisive element at most `x`: no element above `x` enters or leaves the set
    `B` of any vertex. -/
def DecisiveLe (ps : ℕ → V → V) (k : ℕ) (x : V) : Prop :=
  ∀ v y, x < y → (y ∈ bSet (ps k) v ↔ y ∈ bSet (ps (k + 1)) v)

/-- Two profiles agree at every Odd vertex. -/
def SameOdd (G : Game V) (f g : V → V) : Prop := ∀ u, G.owner u = .one → f u = g u

/-- Contract (EDEC2): on a relabelled game, along a trace, if Odd's best responses at the states
    `a, …, j + 1` agree, the iterations `a, …, j` are `l`-stable and the iterations `a, …, j - 1`
    (`a < j`) have decisive element at most `x`, then iteration `j` has decisive element at
    most `x`. -/
def EpochDecisive (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ (a j : ℕ) (x : V), a < j → j < L →
      (∀ k, a ≤ k → k ≤ j + 1 → SameOdd G (ps k) (ps a)) →
      (∀ k, a ≤ k → k ≤ j → LStable ps k) →
      (∀ k, a ≤ k → k < j → DecisiveLe ps k x) →
      DecisiveLe ps j x

/-- Contract (ESEP): on a relabelled game, along a trace, if Odd's best responses at the states
    `a, …, b + 1` agree, the iterations `a, …, b` are `l`-stable and iteration `a` has decisive
    element at most `x`, then so has every iteration `a, …, b` (so no pattern `x, y, x` with
    `y > x` of decisive elements occurs inside an epoch and an `l`-interval). -/
def EpochNoReset (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ (a b : ℕ) (x : V), b < L →
      (∀ k, a ≤ k → k ≤ b + 1 → SameOdd G (ps k) (ps a)) →
      (∀ k, a ≤ k → k ≤ b → LStable ps k) →
      DecisiveLe ps a x → ∀ k, a ≤ k → k ≤ b → DecisiveLe ps k x

/-- Contract (LOC): on a relabelled game, along a trace, if the `l`-stable iterations `j - 1` and
    `j` have decisive elements `≤ x` and `> x`, then Odd's best response changes in iteration
    `j - 1` or in iteration `j`. -/
def ResetLocal (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ (j : ℕ) (x : V), 0 < j → j < L → LStable ps (j - 1) → LStable ps j →
      DecisiveLe ps (j - 1) x → ¬ DecisiveLe ps j x →
      ¬ SameOdd G (ps (j - 1)) (ps j) ∨ ¬ SameOdd G (ps j) (ps (j + 1))

end MercLib.HybridSI

end HybridSIBounds
