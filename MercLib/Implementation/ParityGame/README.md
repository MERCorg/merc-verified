# Overview

Functional models of the partial parity game solvers of mCRL2's `pbessolve`, proved against the
parity game theory in `MercLib/Theory/ParityGame/`.

| file | mCRL2 function (`libraries/pbes/include/mcrl2/pbes/pbesinst_fatal_attractors.h`) | `pbessolve` strategy | headline theorems |
|---|---|---|---|
| `FatalAttractor.lean` | `fatal_attractors_original` (Figure 3 of [Huth2014]) | 6 | `fatalAttractorOriginalSound` |
| `FatalAttractorsAlt.lean` | `fatal_attractors_generic`, via `fatal_attractors` and `find_loops2` | 5 and 4 | `fatalAttractorsAltSound`, `fatalAttractorsAltBuggyUnsound`, `subgameAttrCorrect` |

The headline theorems are restated in `Challenges/ParityGame.lean`.

**Conventions.** mCRL2 uses min-parity ranks. `Game` uses max-parity priorities, so a rank `r` is
modelled by a priority of the same parity in reverse order, and `compare = >=` on ranks becomes `≤ j`
on priorities. Disjunctive vertices belong to player `0` and conjunctive ones to player `1`. The
decided regions `S[0], S[1]` and strategies `τ[0], τ[1]` are a `Solution`.

## The alternative fatal-attractor solver

For every rank `j`, with `α = j mod 2`, `fatal_attractors_generic` takes the candidates
`U_j = {u | rank(u) = j} \ S[1-α]` and the target `T = U_j ∪ S[α]`. It then refines a pair
`(X, Y)` until `X = Y`, and adds `X` to `S[α]`. `X` is the attractor of `T ∩ Y` through vertices of
rank at least `j` (`attr_min_rank_generic`, modelled by `Game.attrMinRank`). `Y` is a region that
the opponent `1-α` cannot leave. `X = Y` is only a winning region for `α` if `Y` is a *trap* for
`1-α`:

- every vertex of `1-α` in `Y` has all its successors in `Y`;
- every vertex of `α` in `Y` has at least one successor in `Y`.

### The bug

Before the fix, the loop was

```cpp
X = attr_min_rank_generic(G, set_intersection(U, Y), alpha, V, j, compare);
Y = set_minus(Y, attr_default(G, set_minus(Y, X), 1 - alpha));
```

(`Game.fatalAttractorsAltBuggy`). The attractor of `Y \ X` is computed over the whole graph, but
only its part inside `Y` is removed. An `α`-vertex whose successors inside `Y` are all removed, but
which still has a successor outside `Y`, is not attracted. It stays in `Y` without a successor in
`Y`, so `Y` is no longer a trap. The strategy step then calls `find_successor_in(G, v, Y)`, which
returns `undefined_vertex()`, and `v` is still added to `S[α]`.

### Counterexample

| vertex | owner | rank (mCRL2) | priority (`cexGame`) | successors |
|---|---|---|---|---|
| `v` | `0` (∨) | 0 | 2 | `d`, `w` |
| `u` | `1` (∧) | 0 | 2 | `d` |
| `w` | `0` (∨) | 1 | 1 | `u`, `z` |
| `z` | `0` (∨) | 1 | 1 | `w` |
| `d` | `1` (∧) | 1 | 1 | `d` |

Player `1` wins every vertex: every play either ends in the self-loop at `d` or cycles between `w`
and `z`, and both cycles have rank 1 (priority 1). For `j = 0` (priority 2, `α = 0`) and
`S = ∅`:

1. `U = {v, u}` and `X₀ = AttrMinRank({v, u}) = {v, u, w, z}`: `w` moves to `u` and `z` moves to
   `w`.
2. `Attr₁(V \ X₀) = Attr₁({d}) = {d, u}`, so `Y₀ = {v, w, z} ≠ X₀`.
3. `X₁ = AttrMinRank(U ∩ Y₀) = AttrMinRank({v}) = {v}`, since nothing has an edge into `v`.
4. `Attr₁({w, z}) = {w, z}` over the whole graph: `v` is not attracted, because player `0` can
   still move to `d`. So `Y₁ = {v}`.
5. `X₁ = Y₁ = {v}`: the loop ends with `v` in `S[0]`, and neither successor of `v` is in `Y₁`.

`Game.fatalAttractorsAltBuggyUnsound` proves this on `cexGame`. Starting from the empty partial
solution, which is sound, the buggy loop puts `v` in the region of player `0`, and the result is
not a sound partial solution, because `v` has no move that stays in the region. The mCRL2 unit test
`libraries/pbes/test/pbesinst_fatal_attractors_test.cpp` checks the same graph.

### The fix

```cpp
X = attr_min_rank_generic(G, set_intersection(U, Y), alpha, Y, j, compare);
Y = set_minus(V, attr_default(G, set_minus(V, X), 1 - alpha));
```

(`Game.fatalAttractorsAlt`). The fix makes two changes.

1. **`X` is computed inside `Y`.** The restriction argument of `attr_min_rank_generic` is `Y`
   instead of `V`. That function only ever inserts vertices that lie in its restriction set, so
   `X ⊆ Y`. Then the new `Y` is contained in `X`, which is contained in the old `Y`. The test
   `X ≠ Y` means `X ⊊ Y`, so `Y` shrinks strictly and the loop terminates. The termination measure
   in the proof is the size of `Y`.
2. **`Y` is the complement of an attractor in the whole graph.** The complement of a
   `(1-α)`-attractor is always a `(1-α)`-trap (`Game.AttractorCorrect`), so `Y` stays a trap. The
   update still computes the attractor in the whole graph. The difference is the target: it now
   also contains the vertices discarded earlier (`V \ Y`).

`Game.subgameAttrCorrect` shows that this update is the refinement inside the subgame `Y`. If `Y` is
a trap for `i`, then `V \ Attr_i(V \ X) = Y \ Attr_i^Y(Y \ X)` for every `X ⊆ Y`, where `Attr^Y` is
computed in the subgame `Y`. The trap property is used only for the vertices of `i`: a vertex of `i`
with an edge leaving `Y` would be attracted in the whole graph but not in `Y`. An `α`-vertex such as
`v` above *is* attracted, because its successors outside `Y` are part of the target.

`Game.fatalAttractorsAltSound` proves the fixed version sound: on a finite game, a sound partial
solution is mapped to a sound partial solution that extends it, for every order of the priorities.
At the end of the loop, `Y = X = AttrMinRank(T ∩ R)` for the previous `Y`, called `R`. Every play
that stays in `Y \ S[α]` keeps returning to `U_j`, where the priority is `j`, and it only passes
through priorities at most `j`, so `α` wins.

### Modelling choices

- Everything is relative to a subgame `X` of the game, as in `FatalAttractor.lean`; the C++ code
  uses the whole graph `V`.
- `attr_min_rank_generic` attracts an opponent vertex when all its successors *in the graph* are in
  the attractor. `Game.attrMinRank R` only looks at successors in `R`. The two agree whenever `R`
  is a trap for the opponent, which holds in the fixed loop. The buggy loop always uses the whole
  subgame, so it is modelled exactly.
- The strategy that `attr_min_rank_generic` stores for an attracted `α`-vertex is modelled by the
  monotone attractor strategy `Game.mattrStrategy`. For a vertex of `U_j`, `find_successor_in` is
  modelled by an arbitrary successor in `Y`; if there is none, the old strategy is kept, where
  mCRL2 stores `undefined_vertex()`.
- Structure graphs are modelled as parity games: decorations become owners, and the
  `d_true`/`d_false` filtering of `compute_U_j_map` and the case of unranked vertices in
  `attr_min_rank_generic` are not modelled. See [Keiren2012] for structure graphs.

### Not formalised

- The fixed loop computes the *greatest* region `Z ⊆ Y₀` that is a `(1-α)`-trap and satisfies
  `Z = AttrMinRank^Z(T ∩ Z)`, and so does the variant that keeps `V` as the restriction set in
  change 1 but uses `X ∩ Y` in change 2. So change 1 does not lose any vertices, assuming that
  variant terminates. This is argued in the bug report, not proved here.
- That player `1` actually wins `v` in `cexGame` (rather than only that the reported strategy is
  not winning).
