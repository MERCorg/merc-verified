---
name: rust-conventions
description: Rust coding conventions for Aeneas-compatible code. Use when writing or editing `.rs` files in `verified/`.
---

## Rust Conventions

- Edition 2024. `#![forbid(unsafe_code)]` is enforced.
- Keep code Aeneas-compatible: no `async`, no trait objects, no raw pointers, no features Aeneas cannot translate.
- `snake_case` for functions/variables, `PascalCase` for types.