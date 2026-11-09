---
name: hb-research
description: Research workflow for the polynomial-bound question of hybrid strategy improvement (H-B) on parity games — paper proofs, the Python reference, z3 falsifiers and gadget searches, annealing experiments, and the website pages. Use when working on H-B lemmas, lower-bound gadgets, z3 encodings, or the parity-game strategy-improvement documentation.
---

## Where things are

| what | where |
|---|---|
| State of the problem (start here) | `~/parity-polynomial/proof/status.md` |
| Paper proof (the live document) | `~/parity-polynomial/proof/hb_general.md` (status, lemmas, open items in §6) |
| Terms, gadgets, rules explained | `~/parity-polynomial/proof/explainer.md` |
| Entry point and working rules | `~/parity-polynomial/README.md` |
| Python reference algorithms | `~/parity-polynomial/experiments/hybrid/scripts/algs.py` (`VJ`, `SSI`, `GSSI`, `HB`, `HBv`, `HA`) |
| Reference trace (used by all checks) | `experiments/hb_reset/scripts/reset.py`: `reset.trace(g, p0, "HBr" \| "VJ", cap)`; each state has `sig`, `tau`, `XL`, `XB`, `KL`, `pstar`, `sw` |
| Split-tree and lemma checks | `experiments/hb_split/` (`split.py`, `prefix_mono.py`, `tree.py`, `progress.py --tops`, `lemma33.py`, `autonomy.py`, `resume.py`, `tree_rules.py`, `reopen.py`) |
| Head tree, Strahler number (Lemma 42) | `experiments/hb_split/strahler.py`, `strahler_supp.py`, `strahler_r.py`; searches `METRIC=strahler climb_pass.py` / `tmpl_pass.py`, growth exponent `tmpl_exp.py` (`ALG=VJ` control) |
| Annealing champions | `experiments/hb_split/results/{climb,esc,reb,rep}_*.json` (`{"gen": [owner, prio, succ, init]}`) |
| z3 encoding of one H-B step | `experiments/hb_z3/hbz3.py`; falsifier `lemmas.py`, searches `gadget.py`, `reset.py`; replay `replay_run.py` |
| Friedmann's switch-all family | `experiments/hb_bound/scripts/gen_friedmann.py`; runs in `experiments/friedmann/` |
| Lean | `MercLib/Algorithms/ParityGame/HybridSI/` (valuation in `MercLib/Theory/ParityGame/Valuation.lean`) in this repository (spec, `Proofs/`, `Challenges/HybridSI.lean`) |
| Rust solver | `~/merc-hybrid-si` worktree (`merc-vpg solve --solver hybrid-si`); never edit `~/merc` |
| Website pages | `~/merc-website/docs/developer/parity/{strategy-improvement,exponential-constructions,hybrid-strategy-improvement}.md` (source of truth for the definitions) |

## Rules

- Paper proofs first; tools check designs. Every claim in the notes says whether it is **proved**, **checked** (by which script, on what data) or **open**. Tested is not proved.
- Document every result, explanation and experiment in `~/parity-polynomial` and commit there (`Co-Authored-By` line). New files are linked from its `README.md`. Never write outputs to `/tmp`; the scratchpad is wiped between sessions.
- Target general games; the one-Odd-vertex (k = 1) line is frozen. Do not use arXiv:2511.03752.
- Notation clash: the website and the papers write `σ̄` for Odd's best response to `σ`; `hb_general.md` writes `τ̄` for it and `σ*` for Even's best response to it, with values `K*`.
- The website definitions are the source of truth; the Lean definitions (`Valuation.lean`, `Algorithm.lean`) are checked against them.

## Running the tools

- z3 needs the virtual environment: `~/parity-polynomial/.venv/bin/python` (set `PYTHONWARNINGS=ignore` to silence the `sys.prefix` warning). Run searches with `nohup timeout 7200 … &`, one per configuration, results in `experiments/hb_z3/results/`.
- `gadget.py N T K [M|-] [same]` and `reset.py N T R [M|-] [between]`; `MAXDEG=d` bounds the out-degree (a sat result stays a real witness; unsat only covers that degree).
- Always replay a z3 witness on the reference (`replay_run.py 'JSON'`) before believing it. Two known artifacts:
  - `K*`-ties: the z3 model may choose a different `σ*` among `K*`-tied best responses than the reference. Conditions stated through `σ*`'s cycle are then spurious; use `K*` values (as the `between` option does).
  - A re-opening of a break *inside* a phase is impossible (H-B only switches into `argmax K*`), so resets can only happen between phases.
- Encoding performance: memoising the key order (one Boolean per pair) was measured slower; it is kept in `hbz3_memo.py` only for reference.
- Do not `pkill -f` with a pattern that also matches your own shell command line; kill by PID.
- Before believing a growth exponent, evaluate the template at large `n` (`tmpl_exp.py eval FILE 24 30 … 72`) and check second differences: small-`n` exponents are dominated by lower-order terms and parity effects.
- Confirm a new family with distinct priorities (`hb_split/distinct.py`) and with the Rust solver before recording it.
- Most checks only make sense on (1S) runs: skip a run if any `XL` entry is not the sink (`0`).

## Website

- Pages are rendered by `zensical` with the `latex-math` plugin: a ` ```math ` block is compiled with the page's `math_preamble` (add `\usepackage{tikz}` there for TikZ) and converted to SVG. Compile TikZ standalone first (`latex` + `dvisvgm`, or `pdflatex` + `pdftoppm` to look at it).
- Build: `cd ~/merc-website && .venv/bin/zensical build`; the navigation is in `zensical.toml`. Do not commit the website unless asked: that repository has unrelated uncommitted changes.
