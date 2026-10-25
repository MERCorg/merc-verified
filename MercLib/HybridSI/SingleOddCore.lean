module

public import MercLib.HybridSI.SingleOddPoly

@[expose] public section HybridSISingleOddCore

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# The core of a run with a single Odd choice vertex

The route of `~/parity-polynomial/experiments/hb_k1proof/STRATEGY.md` (§1, §2.2, §4) to
`SingleOddPoly`, with `u` the only Odd vertex with more than one successor and `c_k = K*_k(u)` the
world value (`worldValue`) at state `k`.

* `UnreachFreeze` (R2): the set `D = unreach G u` of vertices that cannot reach `u` is closed, and
  the run restricted to `D` is an H-B run without Odd choices (`Autonomy`), hence one epoch
  (`EpochBound`): after at most `numEvenIn G D` iterations the profiles are frozen on `D`
  (`FrozenFrom`).
* `UpDownCount` (§2.2, first half): in a stretch without an up move of the world value
  (`upRounds`) every down move (`downRounds`) strictly lowers it, so a trace has at most
  `(#up + 1)(r - 1)` down moves, `r` the number of distinct world values (`worldValues`). Pure
  combinatorics of a sequence; it holds for every game.
* `MonotoneWorlds` (MW, **open**): the keys `K*` are a function of Odd's choice at `u`, and world
  values compare like the keys `K*` (`c_j ≤ c_k ⇒ K*_j ≤ K*_k` pointwise). Then the world values are
  at most `deg u` many (`WorldsBound`) and `K*` changes only at up and down moves (`KStarUpDown`).
  Together (`KStarUpCount`): `#K*-changes + 1 ≤ deg u · (#up + 1)`.
* `UpConjecture` (**open**): at most `n_E` up moves. `UpReduction`: `MonotoneWorlds` and
  `UpConjecture` imply `KChangeConjecture` (`#K*-changes + 1 ≤ n (n_E + 1) ≤ n²`), hence
  `SingleOddPoly` by `KChangeReduction`. (CORE-UP of `STRATEGY.md` §4, a constant bound `3 deg u`
  on the up moves after the R2 freeze, is refuted.)

The headline claims are stated here; proofs go to `HybridSI/Proofs/SingleOddCore_Proofs.lean`.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

open Classical in
/-- The vertices from which `u` is not reachable. -/
noncomputable def unreach (G : Game V) (u : V) : Finset V :=
  Finset.univ.filter fun v => ¬ Relation.ReflTransGen G.edge v u

/-- The number of Even vertices in `D`. -/
def numEvenIn (G : Game V) (D : Finset V) : ℕ := (D.filter fun v => G.owner v = .zero).card

/-- The profiles of a trace are frozen on the vertices that cannot reach `u` from state `t` to `L`. -/
def FrozenFrom (G : Game V) (L : ℕ) (p : ℕ → V → V) (u : V) (t : ℕ) : Prop :=
  ∀ k, t ≤ k → k ≤ L → ∀ v ∈ unreach G u, p k v = p t v

/-- The upward moves: iterations `k` with `k + 1 < L` after which the world value rises. -/
def upRounds (G : Game V) [DecidableRel G.edge] (bf L : ℕ) (ps : ℕ → V → V) (u : V) :
    Finset ℕ :=
  (Finset.range L).filter fun k => k + 1 < L ∧ worldValue G bf ps u k < worldValue G bf ps u (k + 1)

/-- The distinct world values at the states `0, …, L - 1`. -/
def worldValues (G : Game V) [DecidableRel G.edge] (bf L : ℕ) (ps : ℕ → V → V) (u : V) :
    Finset Key :=
  (Finset.range L).image (worldValue G bf ps u)

/-- Contract (R2, the part that cannot reach `u` freezes): on a relabelled game, along a trace, if
    `u` is the only Odd vertex with more than one successor, the profiles are frozen on
    `unreach G u` from some state `t ≤ L` with `t` at most the number of Even vertices that
    cannot reach `u`. -/
def UnreachFreeze (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ u, G.owner u = .one → SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → V → V),
    RunTrace G bf L p ps → ∃ t ≤ L, t ≤ numEvenIn G (unreach G u) ∧ FrozenFrom G L p u t

/-- Contract (§2.2): at most `(#up + 1)(r - 1)` downward moves, `r` the number of distinct world
    values. -/
def UpDownCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (ps : ℕ → V → V) (u : V),
    (downRounds G bf L ps u).card ≤
      ((upRounds G bf L ps u).card + 1) * ((worldValues G bf L ps u).card - 1)

/-- Contract (few worlds): along a trace, if the keys `K*` depend only on Odd's choice at the Odd
    vertex `u`, there are at most `deg u` distinct world values. -/
def WorldsBound (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    (∀ j k, j ≤ L → k ≤ L → ps j u = ps k u → kstarOf G bf ps j = kstarOf G bf ps k) →
    (worldValues G bf L ps u).card ≤ (Finset.univ.filter (G.edge u)).card

/-- Contract (§2.2, second half): if equal world values give equal keys `K*`, then `K*` changes
    only at upward and downward moves. -/
def KStarUpDown (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (ps : ℕ → V → V) (u : V),
    (∀ j k, j ≤ L → k ≤ L → worldValue G bf ps u j = worldValue G bf ps u k →
      kstarOf G bf ps j = kstarOf G bf ps k) →
    (kstarChangeRounds G bf L ps).card ≤ (upRounds G bf L ps u).card + (downRounds G bf L ps u).card

/-- **Contract** (MW of `STRATEGY.md`; proved as `monotoneWorlds`): with a single Odd choice
    vertex `u`, along every trace of H-B the keys `K*` depend only on Odd's choice at `u`, and if
    the world value at state `j` is at most that at state `k`, so are the keys `K*` pointwise. -/
def MonotoneWorlds : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      ∀ j k, j ≤ L → k ≤ L →
        (ps j u = ps k u → kstarOf G (hbFuel (Fin n)) ps j = kstarOf G (hbFuel (Fin n)) ps k) ∧
        (worldValue G (hbFuel (Fin n)) ps u j ≤ worldValue G (hbFuel (Fin n)) ps u k →
          ∀ v, kstarOf G (hbFuel (Fin n)) ps j v ≤ kstarOf G (hbFuel (Fin n)) ps k v)

/-- Contract (§2.2): along a trace, if the keys `K*` depend only on Odd's choice at the Odd vertex
    `u` and equal world values give equal keys `K*`, then `#K*-changes + 1 ≤ deg u · (#up + 1)`
    (so any bound `B` on the upward moves gives at most `deg u · (B + 1) - 1` changes of `K*`). -/
def KStarUpCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    (∀ j k, j ≤ L → k ≤ L → ps j u = ps k u → kstarOf G bf ps j = kstarOf G bf ps k) →
    (∀ j k, j ≤ L → k ≤ L → worldValue G bf ps u j = worldValue G bf ps u k →
      kstarOf G bf ps j = kstarOf G bf ps k) →
    (kstarChangeRounds G bf L ps).card + 1 ≤
      (Finset.univ.filter (G.edge u)).card * ((upRounds G bf L ps u).card + 1)

/-- **Open** (not a contract; tested, not proved): with a single Odd choice vertex `u`, every
    trace of H-B from any profile that follows edges has at most `n_E` upward moves of the world
    value. (A constant bound such as `3 deg u` after the R2 freeze is refuted: `D = ∅` and `n / 12`
    up moves into one world.) -/
def UpConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      (upRounds G (hbFuel (Fin n)) L ps u).card ≤ numEven G

/-- Contract (reduction): `MonotoneWorlds` and `UpConjecture` imply `KChangeConjecture` (hence
    `SingleOddPoly`, by `KChangeReduction`). -/
def UpReduction : Prop := MonotoneWorlds → UpConjecture → KChangeConjecture

/-- Contract (reduction): `UpConjecture` alone implies `SingleOddPoly` (via `MonotoneWorlds`,
    `UpReduction` and `KChangeReduction`). -/
def UpPoly : Prop := UpConjecture → SingleOddPoly

end MercLib.HybridSI

end HybridSISingleOddCore
