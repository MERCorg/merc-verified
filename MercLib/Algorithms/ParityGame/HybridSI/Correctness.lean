module

public import MercLib.HybridSI.Algorithm

@[expose] public section HybridSICorrectness

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# Contracts for the hybrid strategy-improvement algorithm H-B

Claims about `hbRun` (`HybridSI.Algorithm`) on a library game `G : Game V` whose vertex order is a
relevance order (`Game.Relabelled`). Winning is the library's: some positional strategy wins every
conforming play (`Game.WinsFrom`). Nothing here is proved; proofs go to `HybridSI/Proofs/`.

* `HBCorrect`: whenever H-B returns, the winners read off the returned valuation are the winners
  of the game.
* `HBTerminates`: with fuel `|V|^|V| + 1` (the number of profiles, plus one) H-B returns.
* `FilterNonempty`: the filter is never empty while `σ` is not optimal (so the fallback to plain
  switch-all never fires).
* `HBPolyIterations` and `RespondPolyRounds`: **open** statements, not contracts. Together with a
  polynomial cost per round they would put parity games in P; they are recorded here so that the
  claim being pursued is fixed precisely. `RespondPolyRounds` (one-player strategy improvement in
  polynomially many rounds) could also be avoided by computing best responses with a different,
  polynomial one-player algorithm.
-/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The fuel bound: the number of profiles, plus one. -/
def hbFuel (V : Type*) [Fintype V] : ℕ := Fintype.card V ^ Fintype.card V + 1

/-- Contract (correctness): if H-B returns the key table `kt`, then player `i` wins from `v` in
    the whole game exactly when `i` is the winner of `v`'s key. -/
def HBCorrect (G : Game V) [DecidableRel G.edge] (bf fuel : ℕ) : Prop :=
  G.Relabelled → ∀ it kt, hbRun G bf fuel 0 (initProfile G) = some (it, kt) →
    ∀ v i, keyWinner (look kt keyDefault v) = i ↔ ∃ σ, G.WinsFrom Set.univ i σ v

/-- Contract (termination): with enough fuel H-B returns. -/
def HBTerminates (G : Game V) [DecidableRel G.edge] (bf fuel : ℕ) : Prop :=
  G.Relabelled → hbFuel V ≤ bf → hbFuel V ≤ fuel → (hbRun G bf fuel 0 (initProfile G)).isSome

/-- Contract (the filter is never empty): from a profile `p` that follows edges, if Odd's best
    response `ps` to `σ` leaves an improving edge, then, with Even's best response `pstar` to
    `ps`, some vertex has a filtered edge. -/
def FilterNonempty (G : Game V) [DecidableRel G.edge] (bf : ℕ) (p : V → V) : Prop :=
  G.Relabelled → (∀ v, G.edge v (p v)) → ∀ ps pstar,
    respond G true bf p = some ps → respond G false bf ps = some pstar →
    let ks : V → Key := fun v => look (keyTable G ps) keyDefault v
    let kstar : V → Key := fun v => look (keyTable G pstar) keyDefault v
    (∃ v, improving G ks p v ≠ []) → ∃ v, filtered G ks kstar p v ≠ []

/-- **Open** (not a contract): H-B needs polynomially many iterations on every relabelled game. -/
def HBPolyIterations : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled →
    ∀ it kt, hbRun G (hbFuel (Fin n)) (hbFuel (Fin n)) 0 (initProfile G) = some (it, kt) →
      it ≤ (n + 1) ^ c

/-- **Open** (not a contract): the one-player best responses inside H-B need polynomially many
    switch-all rounds (equivalently: `respond` with fuel `(n + 1)^c` never runs out). -/
def RespondPolyRounds : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (G : Game (Fin n)) (_ : DecidableRel G.edge), G.Relabelled →
    ∀ (pl : Bool) (p : Fin n → Fin n), (∀ v, G.edge v (p v)) →
      (respond G pl ((n + 1) ^ c) p).isSome

end MercLib.HybridSI

end HybridSICorrectness
