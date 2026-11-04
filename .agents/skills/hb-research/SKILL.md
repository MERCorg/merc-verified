---
name: hb-research
description: Research workflow for the polynomial-bound question of hybrid strategy improvement (H-B) on parity games, grounded in the Lean formalisation and the website pages. Use when working on H-B lemmas, lower-bound gadgets, or the parity-game strategy-improvement documentation.
---

## Where things are

| what | where |
|---|---|
| Lean (the open target) | `MercLib/Algorithms/ParityGame/HybridSI/` (valuation in `MercLib/Theory/ParityGame/Valuation.lean`) in this repository: spec files (`Algorithm.lean`, `Correctness.lean`, `Epoch.lean`, `BestResponse.lean`, `AlgorithmPoly.lean`, `Potential.lean`, `Bounds.lean`, `Counting.lean`), `Proofs/`, challenge `Challenges/HybridSI.lean`. `Counting.lean`'s `KStarCount` states the current reduction: iterations `≤ C + n_E·(C + 1)`, `C` the number of changes of Even's best-response value `K*`; a polynomial bound on `C` (or a family driving it super-polynomial) is the open target. See `MercLib/Algorithms/ParityGame/HybridSI/README.md` for the full map. |
| Rust solver | `~/merc` crate `merc_vpg` (`merc-vpg solve --solver hybrid-si`, classic rule `vj-si`); check out a branch or worktree to experiment, never edit `~/merc`'s checked-out working tree directly for throwaway runs. |
| Website pages (source of truth for the definitions) | `~/merc-website/docs/developer/parity/{strategy-improvement,exponential-constructions,hybrid-strategy-improvement}.md` |
| Experiments and notes (start here) | `scripts/hybrid-si/README.md`: results so far, each marked proved/checked/open, including the exponential family `E_k` (`exp_template.json`, `exp_family.py`). Tools: `hb.py` (Python mirror exposing `σ̄`, `Ξ`, `σ*`, `K*`), `validate.py`, `checks.py`/`potentials.py` (falsifiers), `climb.py`/`climb_gap.py` (game search), `tmpl.py`/`minimise.py` (per-bit template search and shrinking), `games.py` (Friedmann's `G_n`, `p0`, `merc-vpg` wrapper via `MERC_VPG`). Add new results to that README. |

## Rules

- There is no external paper-proof repository to resume from; Lean (`MercLib/Algorithms/ParityGame/HybridSI/`) and the website pages above are the only ground truth. Do not invent or assume prior results, scripts or status notes that aren't in this repository.
- Every claim in notes says whether it is **proved** (in Lean), **checked** (by which script, on what data) or **open**. Tested is not proved.
- Target general games; the one-Odd-vertex (k = 1) case is a different, narrower question — do not conflate results across them.
- Notation clash: the website writes `σ̄` for Odd's best response to `σ`; keep one consistent notation per document and say which you're using.
- The website definitions are the source of truth; the Lean definitions (`Valuation.lean`, `Algorithm.lean`) are checked against them.
- Always replay a claimed counterexample or witness against the Lean definitions (`hbRun`/`hbStep` in `Algorithm.lean`) or the Rust solver before believing it.
- Runs from the relevance-order `p0` (website, Lean) and from merc-vpg's first listed edge differ; the conjecture is about `p0`. Use `games.p0_moves` / `START=p0` for `p0` runs on merc-vpg.
- Score template searches on growth over several `k` of one residue class and confirm champions far beyond the scored window: parity and residue effects easily fake acceleration.

## Website

- Pages are rendered by `zensical` with the `latex-math` plugin: a ` ```math ` block is compiled with the page's `math_preamble` (add `\usepackage{tikz}` there for TikZ) and converted to SVG. Compile TikZ standalone first (`latex` + `dvisvgm`, or `pdflatex` + `pdftoppm` to look at it).
- Build: `cd ~/merc-website && .venv/bin/zensical build`; the navigation is in `zensical.toml`. Do not commit the website unless asked: that repository has unrelated uncommitted changes.
