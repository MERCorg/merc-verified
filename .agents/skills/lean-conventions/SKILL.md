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
- Cite literature by adding an entry to `docs/references.bib` (key `AuthorYear`, e.g. `Friedmann2009`) and linking it from the doc comment as a Markdown reference link, e.g. `[O. Friedmann and M. Lange, *Solving Parity Games in Practice*][Friedmann2009]` (Mathlib/doc-gen4 convention).
- Prefer automatic tactics (`grind`, `simp`, `omega`, `aesop`, `decide`) over manual term-mode proofs. Try `grind` first for arithmetic/logical goals; fall back to `simp [...]` with targeted lemmas when `grind` is too slow or fails.

## Spec / Proofs / pin split

For a contract theorem (an externally-meaningful claim about translated code, especially one still `sorry`), split it across three roles so a human only ever has to review the *statement*, never the proof:

1. **Spec** — in the human-vetted file (e.g. `Signatures/Signature.lean`, `MercVerified/Refinement/Refinement.lean`), state the claim as a named `def ... : Prop`, not a bare theorem. Naming it (rather than restating the same existential twice) is what prevents the spec and the proof from silently drifting apart. All of the theorem's hypotheses become parameters of the `def`; nothing here is proved.
2. **Proof** — in the matching `Proofs/` file (machine-generated, freely edited or regenerated), prove a `theorem` whose return type is exactly that spec `def` applied to the same parameters. Any private helper lemmas the proof needs live here too.
3. **Challenge** — in the human-vetted comparator challenge file under `Challenges/` (`Challenges/MercVerified.lean` for the `MercVerified` library, `Challenges/<Area>.lean` for `MercLib`), re-state the theorem with the *exact* same name and statement (binder names and kinds included) and proof `sorry`, and add its name to the matching comparator config (`comparator_MercVerified.json` or `comparator.json`). `lake comparator` checks that the solution module proves each challenged theorem with the same statement, using only the permitted axioms, so a regenerated proof that grows a hypothesis, narrows generality or gains an axiom is caught without a human diffing proofs. Keeping the statement out of the machine-generated `Proofs/` file means a regeneration can't silently drop or weaken it.

See `MercVerified/Refinement/Refinement.lean` / `MercVerified/Refinement/Proofs/Refinement_Proofs.lean` / `Challenges/MercVerified.lean` for a worked example.

Only challenge the "headline" result(s) a file builds toward, not every intermediate/auxiliary lemma.
