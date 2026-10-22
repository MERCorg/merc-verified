module

public import MercLib.HybridSI.Bounds

@[expose] public section HybridSISingleOdd

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Odd's best responses along H-B runs, and runs with a single Odd choice vertex

Claims about the traces (`RunTrace`, `HybridSI.Potential`) of H-B, with `Ξ_k = key G (ps k)` and
`l_k(v) = cycMax (ps k) v`. The paper proofs are in
`~/parity-polynomial/experiments/hb_param/README.md` (sec. 3: K1-K4, sec. 8: MMON). Nothing here
is proved; proofs go to `HybridSI/Proofs/SingleOdd_Proofs.lean`.

* `OddOptimal` (K1): at every state Odd's move is a successor of minimal key.
* `CycMaxSucc` (K2): the cycle maximum of a vertex is that of its successor.
* `StableOddChange` (K3): if Odd switches `u` from `a` to `b` in an iteration that changes neither
  the cycle maximum of `a` nor that of `b`, then `a` and `b` have the same cycle maximum.
* `EscapeMonotone` (MMON): the key of Odd's chosen successor (the *escape value* of `u`) is
  non-decreasing.
* `SingleOddEpochs` (K4 for one Odd choice vertex `u`): the number of epoch changes is at most
  `deg u · (n - 1)` plus the number of epoch changes that change no cycle maximum on `{u} ∪ succ u`
  (`locRounds`); `LocSameTop`: in every such round `u` switches between two successors whose
  cycle maximum is that of `u`.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Contract (K1, Odd optimality): along a trace, at every state `k ≤ L`, the move of Odd's best
    response at an Odd vertex `u` has a key at most that of every successor of `u`. -/
def OddOptimal (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ k ≤ L, ∀ u, G.owner u = .one → ∀ w, G.edge u w → key G (ps k) (ps k u) ≤ key G (ps k) w

/-- Contract (K2): in the functional graph of any profile `f`, a vertex and its successor have the
    same cycle maximum. -/
def CycMaxSucc (V : Type*) [Fintype V] [LinearOrder V] : Prop :=
  ∀ (f : V → V) (v : V), cycMax f v = cycMax f (f v)

/-- Contract (K3): along a trace, if iteration `k < L` changes Odd's move at `u` from `a` to `b`
    and changes neither the cycle maximum of `a` nor that of `b`, then `a` and `b` have the same
    cycle maximum at state `k`. -/
def StableOddChange (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ k < L, ∀ u, G.owner u = .one → ps k u ≠ ps (k + 1) u →
      cycMax (ps k) (ps k u) = cycMax (ps (k + 1)) (ps k u) →
      cycMax (ps k) (ps (k + 1) u) = cycMax (ps (k + 1)) (ps (k + 1) u) →
      cycMax (ps k) (ps k u) = cycMax (ps k) (ps (k + 1) u)

/-- Contract (MMON, the escape value is monotone): along a trace, for every Odd vertex `u` and
    iteration `k < L`, the key of Odd's chosen successor of `u` does not decrease. -/
def EscapeMonotone (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    ∀ k < L, ∀ u, G.owner u = .one → key G (ps k) (ps k u) ≤ key G (ps (k + 1)) (ps (k + 1) u)

/-- The local epoch changes at `u`: epoch changes `k < L` at which no vertex of `{u} ∪ succ u`
    changes its cycle maximum. -/
def locRounds (G : Game V) [DecidableRel G.edge] (L : ℕ) (ps : ℕ → V → V) (u : V) : Finset ℕ :=
  (oddChangeRounds G L ps).filter fun k =>
    ∀ v, (v = u ∨ G.edge u v) → cycMax (ps k) v = cycMax (ps (k + 1)) v

/-- Every Odd vertex other than `u` has at most one successor. -/
def SingleOddChoice (G : Game V) (u : V) : Prop :=
  ∀ u', G.owner u' = .one → u' ≠ u → ∀ w w', G.edge u' w → G.edge u' w' → w = w'

/-- Contract (K4 for one Odd choice vertex): along a trace, if `u` is the only Odd vertex with
    more than one successor, the number of epoch changes is at most `deg u · (n - 1)` plus the
    number of local epoch changes at `u`. -/
def SingleOddEpochs (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    SingleOddChoice G u →
    (oddChangeRounds G L ps).card ≤
      (Finset.univ.filter (G.edge u)).card * (Fintype.card V - 1) + (locRounds G L ps u).card

/-- Contract (local epoch changes keep the cycle top): along a trace, if `u` is the only Odd
    vertex with more than one successor, every local epoch change at `u` switches `u` between two
    successors whose cycle maximum (at state `k`) is that of `u`. -/
def LocSameTop (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ k ∈ locRounds G L ps u,
      ps k u ≠ ps (k + 1) u ∧ G.edge u (ps k u) ∧ G.edge u (ps (k + 1) u) ∧
      cycMax (ps k) (ps k u) = cycMax (ps k) u ∧ cycMax (ps k) (ps (k + 1) u) = cycMax (ps k) u

end MercLib.HybridSI

end HybridSISingleOdd
