---
name: lean-conventions
description: Lean 4 coding and proof conventions used in this repository. Use when writing or editing `.lean` files, proofs, tactics, or structures in `Signatures/` or `MercVerified/`.
---

## Lean 4 Conventions

- Toolchain: (see `lean-toolchain`).
- `camelCase` for definitions and theorems; `PascalCase` for types and structures.
- Use `theorem` for propositions, `def` for computations. Prefer `structure` over nested `Sigma` types.
- Import from `Cslib` (e.g. `Cslib.Foundations.Semantics.LTS.Basic`) rather than reimplementing standard LTS theory.
- `Signatures/BranchingBisimilarity.lean` uses `public section ... end` and `public import` — follow this pattern.
- Keep proofs self-contained within their modules; avoid circular imports between `MercVerified/` files.
- Prefer automatic tactics (`grind`, `simp`, `omega`, `aesop`, `decide`) over manual term-mode proofs. Try `grind` first for arithmetic/logical goals; fall back to `simp [...]` with targeted lemmas when `grind` is too slow or fails.

## Spec / Proofs / pin split

For a contract theorem (an externally-meaningful claim about translated code, especially one still `sorry`), split it across three roles so a human only ever has to review the *statement*, never the proof:

1. **Spec** — in the human-vetted file (e.g. `Signatures/Signature.lean`, `MercVerified/Signatures/Refinement.lean`), state the claim as a named `def ... : Prop`, not a bare theorem. Naming it (rather than restating the same existential twice) is what prevents the spec and the proof from silently drifting apart. All of the theorem's hypotheses become parameters of the `def`; nothing here is proved.
2. **Proof** — in the matching `Proofs/` file (machine-generated, freely edited or regenerated), prove a `theorem` whose return type is exactly that spec `def` applied to the same parameters. Any private helper lemmas the proof needs live here too.
3. **Pin** — directly below that theorem, in the same `Proofs/` file, add an `example : <the theorem's full closed signature, written out independently> := theoremName`. This is a regression check, not a duplicate: it independently re-states the closed type, so if a regenerated proof grows an extra hypothesis or narrows generality, the pin fails to type-check and `lake build` catches the drift immediately, without a human having to diff two proofs to notice.

See `MercVerified/Signatures/Refinement.lean` / `MercVerified/Signatures/Proofs/Refinement_Proofs.lean` for a worked example (spec + open `sorry`), and `Signatures/Proofs/Signature_Proofs.lean` for pins on already-proved theorems whose conclusion already uses an existing named `Prop` (no new spec `def` needed there — the pin alone is enough).

Only pin the "headline" result(s) a file builds toward, not every intermediate/auxiliary lemma.

`scripts/check_axioms.py` complements the pin: it runs `#print axioms` on the same pinned theorems and fails CI if one depends on an axiom beyond the approved kernel/boundary set (an open contract is expected to show `sorryAx` until proved — list it in that script's `KNOWN_INCOMPLETE`, not as a pass).