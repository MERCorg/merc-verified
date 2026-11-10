---
name: ci
description: CI workflow descriptions for merc-verified. Use when the user asks about CI, GitHub Actions, lean_action_ci.yml, or update_aeneas.yml workflows.
---

## CI

Three workflows in `.github/workflows/`:

- **`lean_action_ci.yml`** — runs `lake build` (default targets are `MercVerified` and `MercLib`, see `lakefile.toml`) to check the hand-written Lean proofs against the checked-in generated code. It then runs these checks:
  - `lake comparator --config comparator.json` (MercLib) and `lake comparator --config comparator_MercVerified.json` (MercVerified): every headline theorem must be proved with exactly the statement of its `sorry` challenge in `Challenges/`, using only the permitted axioms. This replaced `scripts/check_axioms.py`.
  - `lake env lean --run scripts/CheckExports.lean`: the exported API must match the human-vetted `EXPORTS.md` (see the lean-conventions skill).
  - `lake test`: the concrete-instance tests in `MercLibTest/`.
  - The comparator loads constants at the exported level. A `native_decide` (or any `nativeEqTrue`) in a headline's dependency cone creates an auxiliary axiom `…._native.decide.ax_i_j` that the comparator cannot find, and it panics. Keep native decision procedures out of proofs that headlines depend on.
- **`docs.yml`** — on pushes to `main` (and manual dispatch), builds the doc-gen4 API documentation via the separate `docbuild/` Lake package (`lake build MercVerified:docs MercLib:docs`) and publishes `docbuild/.lake/build/doc` to GitHub Pages.
- **`update_aeneas.yml`** — full regeneration pipeline (OCaml setup → build Charon → build Aeneas → generate LLBC from `verified/` → translate to `MercVerified/Code/` → `scripts/strip_source_paths.py` to normalize `Source:` comment paths). Fails if the regenerated code differs from what's checked in, so commit the regenerated `MercVerified/Code/` after changing Rust sources.