module

public import MercLib.HybridSI.SingleOdd
public import MercLib.HybridSI.Epoch

@[expose] public section HybridSISingleOddPoly

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Towards polynomially many iterations with a single Odd choice vertex

The escape value of an Odd vertex `u` at state `k` of a trace is the key of Odd's chosen successor,
`key G (ps k) (ps k u)`; it is non-decreasing (`EscapeMonotone`). This file reduces the number of
iterations of H-B to the number of distinct escape values:

* `EpochIterations`: a trace has at most `(E + 1) · n_E` iterations, `E` the number of epoch
  changes (`EpochBound` for each of the `E + 1` epochs).
* `EscapeCount`: `E + 1` is at most the number of distinct escape values of any Odd vertex `u` plus
  the number of epoch changes that keep its escape value (`escapeTieRounds`).
* `EscapeClasses`: the distinct escape values split by the cycle maximum of the chosen successor.
* `EscapeClassSplit`: per cycle maximum, at most `2n + 1` escape values have `B`-sum `0`. These
  include every escape value at which Odd closes a cycle through `u` (the chosen successor then
  lies on its own cycle, so `B = ∅`: Lemma B of `PROOF.md`).

A second route avoids escape values: cut the trace at the rounds after which the cycle maximum of
the escape value changes or the next iteration changes some cycle maximum (`escapeCutRounds`, at
most `n² - 1` by P3 and MMON: `EscapeCutCount`). `SegmentCount`: if every cut-free stretch holds at
most `c` epoch changes at non-final escape values (`SegmentBound`, SEG^λ of `LROUNDS.md`), the epoch
changes are at most `(c + 1) · n²` plus those that reach the final escape value.

A third route bounds iterations directly: if every stretch of iterations without a change of any
cycle maximum has at most `c` iterations (`StretchBound`), a trace has at most
`n(n - 1) + c · (n(n - 1) + 1)` iterations (`StretchCount`, by P3), for any game. The open
`StretchConjecture` (ST2 of `ST_RT.md`) asks for `c = 2n` with one Odd choice vertex: `c = n_E`
and `c = n` are false (family K1B: stretches of exactly `2 n_E`, `n = n_E + 5`), and every such
bound fails for general games.

A fourth route uses the world value `c_a = K_a(u)` of Odd's choice `a` (`worldValue`: the key of
`u` under Even's best response): cut the trace at the downward moves, after which the world value
drops (`downRounds`). If every cut-free stretch has at most `c` iterations (`DownBound`), a trace has
at most `D + c (D + 1)` iterations, `D` the number of downward moves (`DownCount`). The open
`DownConjecture` (DOWN and DC of `README.md`) asks for `c = n` and `D ≤ n²` (a template family
reaches `D = n - 7`, `ST_RT.md` §5).

A fifth route uses only the keys `K*` of Even's best response (`kstarOf`): an epoch-bound argument
needs only that `K*` is constant, not Odd's moves, so a stretch with constant `K*` has at most
`n_E` iterations (`KStarBlock`, any game; `hb_k1proof/ST_WORLD.md` §DOWN, Lemma B), and a trace has
at most `C + n_E (C + 1)` iterations, `C` the number of changes of `K*` (`KStarCount`). The open
`KChangeConjecture` asks for `C ≤ n²` with one Odd choice vertex, where `K*` is one of `deg u`
fixed vectors.

What is left open for one Odd choice vertex is `SingleOddEscapeConjecture`: polynomially many
escape values with non-zero `B`-sum per cycle maximum, and polynomially many escape ties
(`~/parity-polynomial/experiments/hb_k1proof/`). `SingleOddReduction` derives `SingleOddPoly`,
polynomially many iterations, from it; `SegmentReduction` and `StretchReduction` derive it
from the open `SegmentConjecture`, `StretchConjecture`, `DownConjecture` and
`KChangeConjecture`. Nothing here is proved; proofs go to
`HybridSI/Proofs/SingleOddPoly_Proofs.lean`.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The escape value of `u` at state `k`: the key of Odd's chosen successor of `u`. -/
def escape (G : Game V) (ps : ℕ → V → V) (u : V) (k : ℕ) : Key := key G (ps k) (ps k u)

/-- The distinct escape values of `u` at the states `0, …, L`. -/
def escapeValues (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u : V) : Finset Key :=
  (Finset.range (L + 1)).image (escape G ps u)

/-- The distinct escape values of `u` at the states `0, …, L` at which Odd's chosen successor of
    `u` has cycle maximum `l`. -/
def escapeClassValues (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u l : V) : Finset Key :=
  ((Finset.range (L + 1)).filter fun k => cycMax (ps k) (ps k u) = l).image (escape G ps u)

/-- The `B`-sum of a key: `Σ_{x ∈ B} sgn x · 2^(r x)`. -/
def keySum (κ : Key) : ℤ := (ofLex (ofLex κ).2).1

/-- The escape values of `u` with cycle maximum `l` and non-zero `B`-sum. -/
def escapeClassValuesX (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u l : V) : Finset Key :=
  (escapeClassValues G L ps u l).filter fun κ => keySum κ ≠ 0

/-- The escape ties of `u`: epoch changes `k < L` that keep the escape value of `u`. -/
def escapeTieRounds (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u : V) : Finset ℕ :=
  (oddChangeRounds G L ps).filter fun k => escape G ps u (k + 1) = escape G ps u k

/-- The cut rounds of the escape of `u`: iterations `k < L` that change the cycle maximum of the
    escape value, or whose next iteration `k + 1 < L` changes some cycle maximum. -/
def escapeCutRounds (L : ℕ) (ps : ℕ → V → V) (u : V) : Finset ℕ :=
  (Finset.range L).filter fun k =>
    cycMax (ps k) (ps k u) ≠ cycMax (ps (k + 1)) (ps (k + 1) u) ∨ k + 1 ∈ cycMaxChangeRounds L ps

/-- The epoch changes at `u` after which the escape value of `u` is not yet final. -/
def nonFinalChanges (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u : V) : Finset ℕ :=
  (Finset.range L).filter fun k => ps k u ≠ ps (k + 1) u ∧ escape G ps u (k + 1) ≠ escape G ps u L

/-- The epoch changes at `u` after which the escape value of `u` is final. -/
def finalChanges (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u : V) : Finset ℕ :=
  (Finset.range L).filter fun k => ps k u ≠ ps (k + 1) u ∧ escape G ps u (k + 1) = escape G ps u L

/-- Every stretch of iterations without a cut holds at most `c` non-final epoch changes at `u`. -/
def SegmentBound (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u : V) (c : ℕ) : Prop :=
  ∀ j j', (∀ k, j ≤ k → k < j' → k ∉ escapeCutRounds L ps u) →
    ((nonFinalChanges G L ps u).filter fun k => j ≤ k ∧ k < j').card ≤ c

/-- Every stretch of iterations `k < L` none of which changes a cycle maximum has at most `c`
    iterations. -/
def StretchBound (L : ℕ) (ps : ℕ → V → V) (c : ℕ) : Prop :=
  ∀ j j', (∀ k, j ≤ k → k < j' → k ∉ cycMaxChangeRounds L ps) →
    ((Finset.range L).filter fun k => j ≤ k ∧ k < j').card ≤ c

/-- The world value at state `k`: the key of `u` under Even's best response to `ps k` (`K_a(u)` for
    Odd's choice `a = ps k u` when `u` is the only Odd choice vertex), or `keyDefault`. -/
def worldValue (G : Game V) [DecidableRel G.edge] (bf : ℕ) (ps : ℕ → V → V) (u : V) (k : ℕ) :
    Key :=
  ((respond G false bf (ps k)).map fun q => key G q u).getD keyDefault

/-- The downward moves: iterations `k` with `k + 1 < L` after which the world value drops. -/
def downRounds (G : Game V) [DecidableRel G.edge] (bf L : ℕ) (ps : ℕ → V → V) (u : V) :
    Finset ℕ :=
  (Finset.range L).filter fun k => k + 1 < L ∧ worldValue G bf ps u (k + 1) < worldValue G bf ps u k

/-- Every stretch of iterations `k < L` without a downward move has at most `c` iterations. -/
def DownBound (G : Game V) [DecidableRel G.edge] (bf L : ℕ) (ps : ℕ → V → V) (u : V) (c : ℕ) :
    Prop :=
  ∀ j j', (∀ k, j ≤ k → k < j' → k ∉ downRounds G bf L ps u) →
    ((Finset.range L).filter fun k => j ≤ k ∧ k < j').card ≤ c

/-- The keys `K*` at state `k`: the keys of Even's best response to `ps k`, or `keyDefault`. -/
def kstarOf (G : Game V) [DecidableRel G.edge] (bf : ℕ) (ps : ℕ → V → V) (k : ℕ) (v : V) : Key :=
  ((respond G false bf (ps k)).map fun q => key G q v).getD keyDefault

/-- The iterations `k` with `k + 1 < L` after which `K*` changes. -/
def kstarChangeRounds (G : Game V) [DecidableRel G.edge] (bf L : ℕ) (ps : ℕ → V → V) :
    Finset ℕ :=
  (Finset.range L).filter fun k => k + 1 < L ∧ kstarOf G bf ps (k + 1) ≠ kstarOf G bf ps k

/-- Contract (iterations per epoch): a trace has at most `E + 1` epochs of at most `n_E`
    iterations each, `E` the number of epoch changes. -/
def EpochIterations (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    L ≤ ((oddChangeRounds G L ps).card + 1) * numEven G

/-- Contract (epoch changes and escape values): along a trace, for every Odd vertex `u`, every
    epoch change either raises the escape value of `u` to a new value or is an escape tie of `u`. -/
def EscapeCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    (oddChangeRounds G L ps).card + 1 ≤
      (escapeValues G L ps u).card + (escapeTieRounds G L ps u).card

/-- Contract (escape classes): the distinct escape values are at most the sum over all cycle
    maxima of the distinct escape values with that cycle maximum. -/
def EscapeClasses (V : Type*) [Fintype V] [LinearOrder V] : Prop :=
  ∀ (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u : V),
    (escapeValues G L ps u).card ≤ ∑ l, (escapeClassValues G L ps u l).card

/-- Contract (escape class split): per cycle maximum, the escape values with `B`-sum `0` are at
    most `2n + 1` (they differ only in the number of steps to the cycle maximum). -/
def EscapeClassSplit (V : Type*) [Fintype V] [LinearOrder V] : Prop :=
  ∀ (G : Game V) (L : ℕ) (ps : ℕ → V → V) (u l : V),
    (escapeClassValues G L ps u l).card ≤
      (escapeClassValuesX G L ps u l).card + (2 * Fintype.card V + 1)

/-- Contract (cuts): along a trace, the escape of an Odd vertex `u` has at most `n² - 1` cut
    rounds (at most `n - 1` changes of the cycle maximum of the escape value, by MMON, and at
    most `n (n - 1)` iterations changing some cycle maximum, by P3). -/
def EscapeCutCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    (escapeCutRounds L ps u).card + 1 ≤ Fintype.card V ^ 2

/-- Contract (segments): along a trace, if `u` is the only Odd vertex with more than one successor
    and every cut-free stretch holds at most `c` non-final epoch changes, then the epoch changes
    are at most `(c + 1) · n²` plus the epoch changes that reach the final escape value. -/
def SegmentCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ c, SegmentBound G L ps u c →
      (oddChangeRounds G L ps).card ≤ (c + 1) * Fintype.card V ^ 2 + (finalChanges G L ps u).card

/-- Contract (stretches): along a trace, if every stretch without a change of a cycle maximum has
    at most `c` iterations, the trace has at most `n(n - 1) + c · (n(n - 1) + 1)` iterations. -/
def StretchCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ c, StretchBound L ps c →
    L ≤ Fintype.card V * (Fintype.card V - 1) + c * (Fintype.card V * (Fintype.card V - 1) + 1)

/-- Contract (downward moves): if every stretch without a downward move has at most `c`
    iterations, a trace has at most `D + c (D + 1)` iterations, `D` the number of downward moves. -/
def DownCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ u c, DownBound G bf L ps u c →
    L ≤ (downRounds G bf L ps u).card + c * ((downRounds G bf L ps u).card + 1)

/-- Contract (blocks of constant `K*`): along a trace, a stretch of iterations `j ≤ k < j' ≤ L`
    with the same keys `K*` has at most `n_E` iterations. -/
def KStarBlock (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps → ∀ j j', j' ≤ L →
    (∀ k, j ≤ k → k < j' → kstarOf G bf ps k = kstarOf G bf ps j) → j' - j ≤ numEven G

/-- Contract (changes of `K*`): a trace has at most `C + n_E (C + 1)` iterations, `C` the number
    of changes of `K*`. -/
def KStarCount (G : Game V) [DecidableRel G.edge] (bf : ℕ) : Prop :=
  ∀ (L : ℕ) (p ps : ℕ → V → V), RunTrace G bf L p ps →
    L ≤ (kstarChangeRounds G bf L ps).card +
      numEven G * ((kstarChangeRounds G bf L ps).card + 1)

/-- **Open** (not a contract; tested, not proved): with a single Odd choice vertex, along every
    trace of H-B from any profile that follows edges the keys `K*` of Even's best response change
    at most `n²` times. -/
def KChangeConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      (kstarChangeRounds G (hbFuel (Fin n)) L ps).card ≤ n ^ 2

/-- **Open** (not a contract; DOWN and DC, tested, not proved): with a single Odd choice vertex
    `u`, every trace of H-B from any profile that follows edges has at most `n` iterations in every
    stretch without a downward move of the world value, and at most `n²` downward moves. -/
def DownConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      DownBound G (hbFuel (Fin n)) L ps u n ∧ (downRounds G (hbFuel (Fin n)) L ps u).card ≤ n ^ 2

/-- **Open** (not a contract; ST2, tested, not proved; false for general games): with a single Odd
    choice vertex, every trace of H-B from any profile that follows edges has at most `2n`
    iterations in every stretch without a change of a cycle maximum. -/
def StretchConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      StretchBound L ps (2 * n)

/-- **Open** (not a contract; SEG^λ of `LROUNDS.md`, tested with `c = deg u`, not proved): with a
    single Odd choice vertex `u`, every trace of H-B from any profile that follows edges has at
    most `n` non-final epoch changes per cut-free stretch and at most `n²` epoch changes that
    reach the final escape value. -/
def SegmentConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      SegmentBound G L ps u n ∧ (finalChanges G L ps u).card ≤ n ^ 2

/-- **Open** (not a contract; tested, not proved): with a single Odd choice vertex `u`, every
    trace of H-B from any profile that follows edges has at most `n²` escape values of `u` with
    non-zero `B`-sum per cycle maximum (C1) and at most `n` escape ties of `u` (C2). -/
def SingleOddEscapeConjecture : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      (∀ l, (escapeClassValuesX G L ps u l).card ≤ n ^ 2) ∧ (escapeTieRounds G L ps u).card ≤ n

/-- **Open** (not a contract): with a single Odd choice vertex, every trace of H-B from any
    profile that follows edges has at most `(n + 1)⁴` iterations. -/
def SingleOddPoly : Prop :=
  ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled → ∀ u, G.owner u = .one →
    SingleOddChoice G u → ∀ (L : ℕ) (p ps : ℕ → Fin n → Fin n), RunTrace G (hbFuel (Fin n)) L p ps →
      L ≤ (n + 1) ^ 4

/-- Contract (reduction): `SingleOddEscapeConjecture` implies `SingleOddPoly`. -/
def SingleOddReduction : Prop := SingleOddEscapeConjecture → SingleOddPoly

/-- Contract (reduction): `SegmentConjecture` implies `SingleOddPoly`. -/
def SegmentReduction : Prop := SegmentConjecture → SingleOddPoly

/-- Contract (reduction): `StretchConjecture` implies `SingleOddPoly`. -/
def StretchReduction : Prop := StretchConjecture → SingleOddPoly

/-- Contract (reduction): `DownConjecture` implies `SingleOddPoly`. -/
def DownReduction : Prop := DownConjecture → SingleOddPoly

/-- Contract (reduction): `KChangeConjecture` implies `SingleOddPoly`. -/
def KChangeReduction : Prop := KChangeConjecture → SingleOddPoly

end MercLib.HybridSI

end HybridSISingleOddPoly
