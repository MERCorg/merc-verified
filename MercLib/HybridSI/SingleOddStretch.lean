module

public import MercLib.HybridSI.SingleOddPoly

@[expose] public section HybridSISingleOddStretch

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Switches and same-key iterations inside a stretch

Two lemmas of the decisive-element analysis of stretches (maximal intervals of `l`-stable
iterations, `LStable` of `HybridSI.Bounds`) in
`~/parity-polynomial/experiments/hb_k1proof/ST_DEC.md` (sec. 2), with `Ξ_k = key G (ps k)`:

* `NonTopStrict` (Lemma NT, non-top switches are strict): in an `l`-stable iteration `k`, every
  Even vertex `v` that switches (`p (k + 1) v ≠ p k v`) and is not the most relevant vertex of its
  own cycle (`v ≠ cycMax (ps k) v`) strictly raises its key: `Ξ_k(v) < Ξ_{k+1}(v)`. (H-B switches
  `v` from `s` to `w` with `Ξ_k(s) < Ξ_k(w)`; the key of a non-top vertex is that of its successor
  shifted by a constant that only depends on `v` and the cycle maximum, and `Ξ_k(w) ≤ Ξ_{k+1}(w)`
  by P2.) No hypothesis on the number of Odd choice vertices is needed.
* `SameKeysTie` (Lemma SK, same keys give a tie): if an iteration `k` with `k + 1 < L` (that is,
  `k < L − 1`: the next iteration is not final) leaves all keys unchanged (`Ξ_k = Ξ_{k+1}`), then
  for every Odd vertex `u` the iteration is an escape tie of `u` (`escapeTieRounds` of
  `HybridSI.SingleOddPoly`: an epoch change, i.e. some Odd move changes, that keeps the escape value
  of `u`), and if `u` is the only Odd choice vertex (`SingleOddChoice`), `u` itself switches.

Changes with respect to `ST_DEC.md`: in SK the paper assumes a single Odd choice vertex
throughout; here only the conclusion `ps k u ≠ ps (k + 1) u` assumes it, the tie part
(`k ∈ escapeTieRounds G L ps u`: some Odd move changes, and the escape value of `u` is unchanged)
holds for every Odd vertex of any relabelled game. The hypothesis BR-Even of the paper (`K*` are
the optimal keys of the world of `ps k`) is not an assumption: it follows from the optimality of a
returned `respond`. The relabelling hypothesis is needed for `FilterNonempty`. Nothing here is
proved; proofs go to `HybridSI/Proofs/SingleOddStretch_Proofs.lean`.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Contract (Lemma NT): along a trace, in an `l`-stable iteration `k < L`, every switched Even
    vertex that is not the cycle maximum of its own play strictly raises its key. -/
def NonTopStrict (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ k < L, LStable ps k →
    ∀ v, G.owner v = .zero → p (k + 1) v ≠ p k v → v ≠ cycMax (ps k) v →
      key G (ps k) v < key G (ps (k + 1)) v

/-- Contract (Lemma SK): on a relabelled game, along a trace, if iteration `k` with `k + 1 < L`
    changes no key, then for every Odd vertex `u` it is an escape tie of `u`, and if `u` is the
    only Odd choice vertex, Odd's move at `u` changes. -/
def SameKeysTie (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ k, k + 1 < L →
    key G (ps k) = key G (ps (k + 1)) → ∀ u, G.owner u = .one →
      k ∈ escapeTieRounds G L ps u ∧ (SingleOddChoice G u → ps k u ≠ ps (k + 1) u)

/-!
## Theorem DR: stretch length from the rises of the decisive element

The decisive element of iteration `k` (`decisive`, `dec(k)` of `ST_DEC.md` sec. 2) is the most
relevant vertex that enters or leaves the set `B` of some vertex in that iteration, `⊥` ("silent")
if no `B` changes; `decisive ps k ≤ x` is `DecisiveLe ps k x`. A rise in the iterations
`j, …, j' - 1` (`riseRounds`) is an iteration `k` with `j < k < j'` and `dec(k - 1) < dec(k)`.

* `DecisiveStretch` (Theorem DR): on a relabelled game, along a trace, for every Odd vertex `u`,
  a stretch `j, …, j' - 1` (`j' ≤ L`) of `l`-stable iterations has at most
  `(R + 1) · n(2n - 1) + Tie + 1` iterations, `R` its number of rises and `Tie` the number of
  escape ties of `u` in it. (Cut at the rises; on each piece `dec` is non-increasing, so by P4
  each `x ∈ V` is decisive in at most `n` iterations; the silent iterations form a suffix with
  fixed cycle maxima and `B`-sets, so a key changes only in its length component, monotonically
  by P2 and at most `n - 1` times per vertex since the play from `v` reaches its cycle maximum
  within `n - 1` steps; the silent iterations that change no key are escape ties by SK, or the
  last iteration `L - 1`.) `n(2n - 1) = 2n² - n` as in the paper.
* `DecisiveStretchBound`: the uniform form: if every stretch has at most `r` rises
  (`RiseBound`) and `u` has at most `t` escape ties, every stretch has at most
  `(r + 1) · n(2n - 1) + t + 1` iterations (`StretchBound`); `DecisiveIterations` then bounds
  the iterations by `StretchCount`.
* `RiseConjecture` (**open**, tested in `ST_DEC.md` sec. 3 and 7 as `R(S) ≤ deg u ≤ n`, with C2
  of `TIES.md` for the ties): with one Odd choice vertex, at most `n` rises per stretch and `n`
  escape ties. It does not give the `(n + 1)⁴` of `SingleOddPoly` (DR is cubic per stretch, so
  the bound is of degree `5`): `RiseReduction` derives `SingleOddRisePoly`, at most
  `2 (n + 1)⁵` iterations. The stretches of exactly `2 n_E` iterations of family K1B
  (`ST_RT.md`) have no rises and are consistent with DR.

Changes with respect to `ST_DEC.md`: the escape ties are those of an arbitrary Odd vertex `u`
(SK holds for each), and the stretch need not be maximal.
-/

/-- The decisive element of iteration `k`: the most relevant vertex entering or leaving the set
    `B` of some vertex, `⊥` if no `B` changes. -/
def decisive (ps : ℕ → V → V) (k : ℕ) : WithBot V :=
  (Finset.univ.biUnion fun v => symmDiff (bSet (ps k) v) (bSet (ps (k + 1)) v)).max

/-- The rises of the decisive element in the iterations `j, …, j' - 1`: the iterations `k` with
    `j < k < j'` whose decisive element is above that of iteration `k - 1`. -/
def riseRounds (ps : ℕ → V → V) (j j' : ℕ) : Finset ℕ :=
  (Finset.Ioo j j').filter fun k => decisive ps (k - 1) < decisive ps k

/-- Contract (Theorem DR): on a relabelled game, along a trace, for every Odd vertex `u`, a
    stretch of `l`-stable iterations `j ≤ k < j' ≤ L` has at most `(R + 1) · n(2n - 1) + Tie + 1`
    iterations, `R` the number of rises of the decisive element in it and `Tie` the number of
    escape ties of `u` in it. -/
def DecisiveStretch (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    ∀ j j', j' ≤ L → (∀ k, j ≤ k → k < j' → LStable ps k) →
      j' - j ≤ ((riseRounds ps j j').card + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) +
        ((escapeTieRounds G L ps u).filter fun k => j ≤ k ∧ k < j').card + 1

/-- Every stretch of `l`-stable iterations `j ≤ k < j' ≤ L` has at most `r` rises of the
    decisive element. -/
def RiseBound (L : ℕ) (ps : ℕ → V → V) (r : ℕ) : Prop :=
  ∀ j j', j' ≤ L → (∀ k, j ≤ k → k < j' → LStable ps k) → (riseRounds ps j j').card ≤ r

/-- Contract (uniform DR): on a relabelled game, along a trace, if every stretch has at most `r`
    rises and an Odd vertex `u` has at most `t` escape ties, every stretch without a change of a
    cycle maximum has at most `(r + 1) · n(2n - 1) + t + 1` iterations. -/
def DecisiveStretchBound (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    ∀ r t, RiseBound L ps r → (escapeTieRounds G L ps u).card ≤ t →
      StretchBound L ps ((r + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) + t + 1)

/-- Contract (iterations from rises and ties): on a relabelled game, along a trace, if every
    stretch has at most `r` rises and an Odd vertex `u` has at most `t` escape ties, the trace has
    at most `n(n - 1) + c · (n(n - 1) + 1)` iterations, `c = (r + 1) · n(2n - 1) + t + 1`. -/
def DecisiveIterations (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  G.Relabelled → ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    ∀ r t, RiseBound L ps r → (escapeTieRounds G L ps u).card ≤ t →
      L ≤ Fintype.card V * (Fintype.card V - 1) +
        ((r + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) + t + 1) *
          (Fintype.card V * (Fintype.card V - 1) + 1)

/-- **Open** (not a contract; tested, not proved): with a single Odd choice vertex `u`, every
    trace of H-B from any profile that follows edges has at most `n` rises of the decisive element
    per stretch of `l`-stable iterations and at most `n` escape ties of `u`. -/
def RiseConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      RiseBound L ps n ∧ (escapeTieRounds G L ps u).card ≤ n

/-- **Open** (not a contract): with a single Odd choice vertex, every trace of H-B from any
    profile that follows edges has at most `2 (n + 1)⁵` iterations. -/
def SingleOddRisePoly : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      L ≤ 2 * (n + 1) ^ 5

/-- Contract (reduction): `RiseConjecture` implies `SingleOddRisePoly`. -/
def RiseReduction : Prop := RiseConjecture → SingleOddRisePoly

end MercLib.HybridSI

end HybridSISingleOddStretch
