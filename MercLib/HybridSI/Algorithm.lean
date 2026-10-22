module

public import MercLib.HybridSI.Valuation

@[expose] public section HybridSIAlgorithm

namespace MercLib.HybridSI

open MercLib.ParityGame

/-!
# The hybrid strategy-improvement algorithm H-B

A profile `p : V → V` holds Even's strategy `σ` at Even vertices and Odd's strategy `τ` at Odd
vertices. One iteration of H-B:
1. `σ̄ = respond true p`: Odd's best response to `σ` (one-player strategy improvement,
   switch-all, warm start from `τ`); its keys `ks` are the valuation `Ξ_σ` of `σ`.
2. `I(v) = {w ∈ succ v | ks w > ks (σ v)}` for Even vertices `v` (improving edges). If every
   `I(v)` is empty, `σ` is optimal and the winners are read off `ks`.
3. `σ* = respond false σ̄`: Even's best response to `σ̄`, with keys `kstar`.
4. `F(v) = {w ∈ I(v) | kstar w = max_{x ∈ succ v} kstar x}`: improving edges that are optimal
   against `σ̄`. If some `F(v)` is non-empty, exactly the vertices with non-empty `F(v)` switch,
   each to its `ks`-best edge in `F(v)`; otherwise plain switch-all on `I` (this never happens).

This mirrors `experiments/hybrid/scripts/algs.py` (`alg = "HB"`), including tie-breaking (the
first best successor in relevance order; the current move is kept unless a successor is strictly
better), so that iteration counts can be compared.

**Evaluation.** Profiles and keys are passed around as tables (`tabulate`, `look`) computed once
per round; functions are only rebuilt from tables, never composed, so `#eval` stays polynomial.
-/

variable {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]

/-- The successors of `v` in relevance order. -/
def succList (v : V) : List V := (univList V).filter fun w => G.edge v w

/-- A placeholder key (never looked up: tables cover all vertices). -/
def keyDefault : Key := toLex (0, toLex (0, 0))

/-- The keys of profile `p`, tabulated. -/
def keyTable (p : V → V) : List (V × Key) := tabulate (key G p)

/-- The first strictly best successor for the player (`better a b`: `a` strictly better than
    `b`), starting from the current move `cur`. -/
def bestOf (better : Key → Key → Bool) (κ : V → Key) (cur : V) (ws : List V) : V :=
  ws.foldl (fun b x => if better (κ x) (κ b) then x else b) cur

/-- Is `v` owned by the player `pl` (`false` = Even, `true` = Odd)? -/
def ownedBy (pl : Bool) (v : V) : Bool := G.owner v == if pl then .one else .zero

/-- One switch-all round for player `pl` (Even maximises, Odd minimises), as a table. -/
def respondRound (pl : Bool) (p : V → V) : List (V × V) :=
  let kt := keyTable G p
  let κ : V → Key := fun v => look kt keyDefault v
  tabulate fun v => if ownedBy G pl v then
      bestOf (fun a b => if pl then decide (a < b) else decide (b < a)) κ (p v) (succList G v)
    else p v

/-- Player `pl`'s best response to the other player's moves in `p`, by one-player strategy
    improvement with `fuel` rounds; `none` if the fuel runs out. -/
def respond (pl : Bool) : ℕ → (V → V) → Option (V → V)
  | 0, _ => none
  | fuel + 1, p =>
    let qt := respondRound G pl p
    let q : V → V := fun v => look qt v v
    if (univList V).all fun v => q v == p v then some p else respond pl fuel q

/-- The improving edges of Even vertex `v` under the keys `ks` of `σ`. -/
def improving (ks : V → Key) (p : V → V) (v : V) : List V :=
  if ownedBy G true v then [] else (succList G v).filter fun w => decide (ks (p v) < ks w)

/-- The filter: improving edges that are optimal against `σ̄` (keys `kstar` of `σ*`). -/
def filtered (ks kstar : V → Key) (p : V → V) (v : V) : List V :=
  let vals := (succList G v).map kstar
  let mx := vals.foldl max (vals.headD (kstar v))
  (improving G ks p v).filter fun w => kstar w == mx

/-- The `ks`-best element of a list (the first maximum), or `d` for the empty list. -/
def argmaxKey (ks : V → Key) (d : V) : List V → V
  | [] => d
  | w :: ws => ws.foldl (fun b x => if decide (ks b < ks x) then x else b) w

/-- The result of one H-B iteration. -/
inductive Step (V : Type*) where
  /-- `σ` is optimal; the table of keys of its valuation. -/
  | done (ks : List (V × Key))
  /-- The next profile, as a table. -/
  | next (p : List (V × V))
  /-- A best-response computation ran out of fuel. -/
  | stuck

/-- One H-B iteration from profile `p` (best responses with fuel `bf`). -/
def hbStep (bf : ℕ) (p : V → V) : Step V :=
  match respond G true bf p with
  | none => .stuck
  | some ps =>
    let kst := keyTable G ps
    let ks : V → Key := fun v => look kst keyDefault v
    if (univList V).all fun v => (improving G ks p v).isEmpty then .done kst
    else
      match respond G false bf ps with
      | none => .stuck
      | some pstar =>
        let kt := keyTable G pstar
        let kstar : V → Key := fun v => look kt keyDefault v
        let useF := (univList V).any fun v => !(filtered G ks kstar p v).isEmpty
        let src := if useF then filtered G ks kstar p else improving G ks p
        .next (tabulate fun v => if (src v).isEmpty then p v else argmaxKey ks (p v) (src v))

/-- H-B from profile `p` with at most `fuel` iterations, counting iterations from `it`: the
    number of iterations and the key table of the optimal valuation, or `none`. -/
def hbRun (bf : ℕ) : ℕ → ℕ → (V → V) → Option (ℕ × List (V × Key))
  | 0, _, _ => none
  | fuel + 1, it, p =>
    match hbStep G bf p with
    | .done ks => some (it, ks)
    | .next qt => hbRun bf fuel (it + 1) fun v => look qt v v
    | .stuck => none

/-- The initial profile: the first successor of every vertex. -/
def initProfile (v : V) : V := (succList G v).headD v

/-- The H-B solver: the winner of every vertex (as a table in relevance order), from the
    first-successor profile; `none` if some fuel runs out. -/
def hbSolve (bf fuel : ℕ) : Option (List Player) :=
  (hbRun G bf fuel 0 (initProfile G)).map fun r => r.2.map fun e => keyWinner e.2

end MercLib.HybridSI

end HybridSIAlgorithm
