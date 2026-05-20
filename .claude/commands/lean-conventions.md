## Lean 4 Conventions

- Toolchain: `leanprover/lean4:v4.30.0-rc2` (see `lean-toolchain`).
- `camelCase` for definitions and theorems; `PascalCase` for types and structures.
- Use `theorem` for propositions, `def` for computations. Prefer `structure` over nested `Sigma` types.
- Import from `Cslib` (e.g. `Cslib.Foundations.Semantics.LTS.Basic`) rather than reimplementing standard LTS theory.
- `Signatures/BranchingBisimilarity.lean` uses `public section ... end` and `public import` — follow this pattern.
- Keep proofs self-contained within their modules; avoid circular imports between `MercVerified/` files.
- Prefer automatic tactics (`grind`, `simp`, `omega`, `aesop`, `decide`) over manual term-mode proofs. Try `grind` first for arithmetic/logical goals; fall back to `simp [...]` with targeted lemmas when `grind` is too slow or fails.
