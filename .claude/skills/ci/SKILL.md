---
name: ci
description: CI workflow descriptions for merc-verified. Use when the user asks about CI, GitHub Actions, lean_action_ci.yml, or update_aeneas.yml workflows.
---

## CI

Two workflows in `.github/workflows/`:

- **`lean_action_ci.yml`** — runs `lake build Signatures` to check the hand-written Lean proofs against the checked-in generated code.
- **`update_aeneas.yml`** — full regeneration pipeline (OCaml setup → build Charon → build Aeneas → generate LLBC from `verified/` → translate to `MercVerified/Code/`). Fails if the regenerated code differs from what's checked in, so commit the regenerated `MercVerified/Code/` after changing Rust sources.