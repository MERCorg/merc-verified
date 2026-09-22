---
name: ci
description: CI workflow descriptions for merc-verified. Use when the user asks about CI, GitHub Actions, lean_action_ci.yml, or update_aeneas.yml workflows.
---

## CI

Two workflows in `.github/workflows/`:

- **`lean_action_ci.yml`** — runs `lake build` (default targets are `MercVerified` and `Signatures`, see `lakefile.toml`) to check the hand-written Lean proofs against the checked-in generated code, then `scripts/check_axioms.py` to fail the build if a headline theorem depends on an axiom beyond the approved kernel/boundary set (see the lean-conventions skill's spec/Proofs/pin section).
- **`update_aeneas.yml`** — full regeneration pipeline (OCaml setup → build Charon → build Aeneas → generate LLBC from `verified/` → translate to `MercVerified/Code/`). Fails if the regenerated code differs from what's checked in, so commit the regenerated `MercVerified/Code/` after changing Rust sources.