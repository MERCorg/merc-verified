# Overview

A formalisation of standard parity game theory in Lean.

## Incomplete parity games ([Laveaux2022])

`Incomplete.lean` formalises Section 3 and §4.1 of M. Laveaux, W. Wesselink and T. A. C. Willemse,
*On-The-Fly Solving for Symbolic Parity Games*, TACAS 2022 (arXiv 2201.09607, `papers/Laveaux2022.pdf`).
Proved: Lemmas 1 to 4, Corollaries 2 and 3, and Theorem 1 (`Challenges/ParityGame.lean`).

*Notation.* This README writes `a` for an incomplete parity game `(G, I)`. The paper writes it as a
stylised (Fraktur) G, so `a ⊑ a'`, `safe_α(a)` and `a ∩ U` here are the paper's notation with that
symbol. In Lean an incomplete game is an `IncompleteGame`, also called `a` in the claims.

### Where the formalisation differs from the paper

- **Max-parity.** The paper decides infinite plays by the *least* priority that occurs infinitely
  often; `Game` (and merc) use the *greatest*. None of the proved statements depends on the
  priorities themselves, except through the encoding below.
- **Positional strategies.** The paper's strategies may depend on the history (`V* V_α → V`, partial);
  dominions here use positional strategies (`Strategy`, a total function), and "`α` wins `v`" is
  `Wins`: `v` lies in a positional `α`-dominion. Determinacy (`determined`, from Zielonka's
  algorithm) is proved in this positional sense.
- **Sinks.** A play ending in a sink is lost by the sink's owner, as in the paper. Winning is defined
  through the total game `toGame` on `V ⊕ Player`, where a sink of `p` moves to a self-loop won by
  the opponent.
- **Vertex sets.** The vertices are a set `vs` inside a type `V`; owners and priorities are functions
  on all of `V`, and `V_♦ ⊆ V_♦'` in Definition 3 becomes "the owners agree on `vs`".
- **Definition 3 (extension).** Condition (2) is `((V \ I) × V') ∩ E' ⊆ E`, not `((V \ I) × V) ∩ E' ⊆ E`;
  see the issues below.
- **Corollary 2** takes `X` to be an `α`-dominion of `a ∩ safe_α(a)`; the paper says "an `α`-dominion"
  without saying in which game.
- **Theorem 1** assumes a finite vertex type with a vertex outside the game, for the determinacy and
  for Lemma 2.
  
### Issues in the paper and how to fix them

#### Definition 3 is too weak for Lemma 1

Condition (2) of Definition 3, `((V \ I) × V) ∩ E' ⊆ E`, only forbids new edges from a complete
vertex to an *old* vertex. A complete vertex may still get an edge to a vertex of `V' \ V`.

*Example.* Let `a = (G, I)` with `G = (V, E, p, (V♦, V□))`, `V = {v}`, `E = {(v, v)}`, `p(v) = 0`,
`V♦ = ∅`, `V□ = {v}` and `I = ∅`. Let `a' = (G', I')` with `V' = {v, z}`,
`E' = {(v, v), (v, z)}`, `p'(v) = p'(z) = 0`, `V♦' = {z}`, `V□' = {v}` and `I' = ∅`. Then `a ⊑ a'`:
(1) `V ⊆ V'`, `V♦ ⊆ V♦'`, `V□ ⊆ V□'`; (2) `E ⊆ E'` and `((V \ I) × V) ∩ E' = {(v, v)} ⊆ E`;
(3) `p = p'↾V`; (4) `I' ∩ V = ∅ ⊆ I`. Moreover
`safe♦(a) = V \ Attr□(a, V□ ∩ I) = V \ Attr□(a, ∅) = {v}`, and `D = {v}` is a `♦`-dominion of
`a ∩ safe♦(a)`: the only play from `v` is `v v v …`, won by `♦`. In `a'`, the play `v z` ends in the
sink `z` of `♦` and is won by `□`, so `D` is not a `♦`-dominion of `a'`, and Lemma 1 fails.

*Where the proof of Lemma 1 goes wrong.* Take the play `v₀ v₁ = v z` of `G'`, consistent with `σ'`.
The first vertex outside `D` is `v₁ = z`, so `i = 1` and `v_{i−1} = v ∈ V_ᾱ = V□`: the case
"`v_{i−1} ∈ V_ᾱ`". Its first sentence holds: `{v'' ∈ V | (v_{i−1}, v'') ∈ E} = {v} ⊆ D`. Its second
sentence, "since `D ⊆ V ∩ safe_α(a)`, `(I' ∩ V) ⊆ I` and `((V \ I) × V) ∩ E' ⊆ E`, also
`{v'' ∈ V' | (v_{i−1}, v'') ∈ E'} ⊆ D`", does not follow: the three facts only bound the successors
in `V`, and `{v'' ∈ V' | (v, v'') ∈ E'} = {v, z} ⊄ D`.

*Fix.* Condition (2) becomes `E ⊆ E'` and `((V \ I) × V') ∩ E' ⊆ E`: a complete vertex gets no new
successors at all. Then the second sentence follows and Lemma 1 holds (`Extends`,
`dominionsSurvive`).

#### Lemma 2 with the fixed Definition 3

Lemma 2 needs no change. Its extension `a' = (G', ∅)`, with `V' = V ∪ {z}` for a fresh `z ∉ V`,
`E' = E ∪ {(v, z) | v ∈ I}`, `V'_α = V_α ∪ {z}` and `p'(z) = 0`, adds edges only from incomplete
vertices, so it also satisfies the fixed condition (2): `((V \ I) × V') ∩ E' = ((V \ I) × V') ∩ E ⊆ E`.
Its proof shows more than its statement: every vertex of `V \ safe_α(a)` is won by `ᾱ` in this one
`a'`, whether or not it lies in an `α`-dominion `W`. `UnsafeLost` states it in that form.

#### Theorem 1 with the fixed Definition 3

*The statement* holds for the fixed Definition 3 but not for the literal one. Its last part,
"`W_?` cannot be larger", uses Lemma 1: a vertex of `W_α` is won by `α` in every extension. In the
example above `v ∈ W♦` (it lies in the `♦`-dominion `{v}` of `a ∩ safe♦(a)`), yet `□` wins `v` in
the literal extension `a'`, so `v` satisfies the property that Theorem 1 says characterises `W_?`.
With the fixed `⊑`, `a'` is not an extension of `a`.

*The proof* needs one step replaced. For a vertex `v ∈ W_?` won by `α` in `G`, it argues: "Towards a
contradiction, assume that `v ∈ safe_α(a)`. Then there must also be a `α`-dominion containing `v` in
`G ∩ safe_α(a)`, since `ᾱ` cannot escape the set `safe_α(a)`. But then `v ∈ W_α`. Contradiction, so
`v ∉ safe_α(a)`." It then applies Lemma 2 to `v`. The inference "there must also be an `α`-dominion
containing `v` in `G ∩ safe_α(a)`" does not hold: `α` may win `v` in `G` only by moving out of
`safe_α(a)`.

*Example.* `V = {v, u}`, `V♦ = {v}`, `V□ = {u}`, `E = {(v, v), (v, u), (u, u)}`, `p(v) = 1`,
`p(u) = 0`, `I = {u}`. Then `Attr□(a, V□ ∩ I) = Attr□(a, {u}) = {u}` (`v` has the successor
`v ∉ {u}`), so `safe♦(a) = {v}`. In `G`, `♦` wins `v` by moving to `u`: the play `v u u …` has
least priority 0 infinitely often, and `{v, u}` is a `♦`-dominion of `G`. In `G ∩ safe♦(a)` only
the play `v v …` is left, won by `□`. So `v ∈ safe♦(a)` is won by `♦` in `G` but lies in no
`♦`-dominion of `G ∩ safe♦(a)`. Also `safe□(a) = V` (no incomplete vertices of `♦`) and `□` does not
win `v` in `G`, so `v ∈ W_?`. The theorem's conclusion holds for `v` (in the extension of Lemma 2,
`□` moves from `u` to the sink `z` of `♦` and wins `v`), but the paper's argument would conclude
`v ∉ safe♦(a)`, which is false.

*Fix of the proof.* Let `v ∈ W_?` be won by `α` in `G`, and take `a_α = a`. For `a_ᾱ`, take the
extension `a'` of Lemma 2, for every such `v`, whether `v` is safe or not. By determinacy `v` is won
by `α` or by `ᾱ` in `a'`. Suppose `α` wins `v` in `a'`, with an `α`-dominion `D'` of `a'`. Then:
- `D'` contains no vertex of `V \ safe_α(a)` and not `z`, since those lie in an `ᾱ`-dominion of `a'`
  (Lemma 2, and `z` is a sink of `α`), and no vertex lies in dominions of both players. So
  `D' ⊆ safe_α(a)`.
- Inside `D'` the edges of `a'` are those of `a`, since the only new edges go to `z ∉ D'`.
- An `ᾱ`-vertex `w ∈ D'` is complete (`w ∈ I` would give `w ∈ Attr_ᾱ(a, V_ᾱ ∩ I)`), and its
  successors stay in `D'`.

So `D'` is an `α`-dominion of `a ∩ safe_α(a)` containing `v`, hence `v ∈ W_α`, contradicting
`v ∈ W_?`. So `ᾱ` wins `v` in `a'`. `IncompleteOptimal_Proofs.lean` proves the theorem this way
(`safeOptimal`, with `Agree.dominion` for moving `D'` to `a ∩ safe_α(a)`).
