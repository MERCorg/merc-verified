---
name: lean-conventions
description: Lean 4 coding and proof conventions used in this repository. Use when writing or editing `.lean` files, proofs, tactics, or structures in `Signatures/` or `MercVerified/`.
---

## Lean 4 Conventions

- Toolchain: (see `lean-toolchain`).
- `camelCase` for definitions and theorems; `PascalCase` for types and structures.
- Use `theorem` for propositions, `def` for computations. Prefer `structure` over nested `Sigma` types.
- Import from `Cslib` (e.g. `Cslib.Foundations.Semantics.LTS.Basic`) rather than reimplementing standard LTS theory.
- Every file is a Lean `module` (`module` header, `public import`, `@[expose] public section`), in `MercLib` and in `MercVerified` alike.
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

### Challenge documentation

Every theorem in a `Challenges/` file is the human-readable frontend of the library, so its doc comment says what it proves. Follow the Mathlib/CSLib docstring style (Mathlib's documentation guide; e.g. `Mathlib/Probability/CentralLimitTheorem.lean`, `Cslib/Foundations/Semantics/LTS/Bisimulation.lean`): a bold title for a named result, then the statement as plain prose, with continuation lines not indented. Do not use `* Given:` / `* Then:` bullet lists; neither library does.

```
/-- **Short title.** If <the hypotheses, including those hidden inside the spec `def`>, then
<the conclusion, in words>. <What is not covered, optional.> See `SpecDef` (`Area/File.lean`). -/
```

For example:

```
/-- **Branching bisimilarity is transitive.** In an LTS with a silent action, if
`s1 ≈br[lts] s2` and `s2 ≈br[lts] s3` then `s1 ≈br[lts] s3`. -/
```

Spell out every hypothesis that is not visible in the signature (those inside the spec `def`); hypotheses that are visible there may be summarised. A docstring may use more than one sentence or paragraph, but keep it as prose.

Module docstrings follow the Mathlib layout: `# Title`, an introduction (with references), then `## Main definitions`, `## Main statements`, `## Notation` and `## References` as needed, each item written as `` - `name`: one-line description ``.

### Exports

Proof modules export only their headline theorems:
* every other declaration in a `Proofs/` file is `private`; sibling proof files that need it `import all` the module that declares it;
* notations in proof files are `local`;
* exceptions are forced by Lean: proof-internal `structure`s and `inductive`s stay public (dot notation does not resolve on the fields of a `private structure`), together with definitions and instances their public types mention.

`EXPORTS.md` (human-vetted) lists everything visible to an importer. `lake env lean --run scripts/CheckExports.lean` fails if the actual exports differ from it; `--write` regenerates it, and a human reviews the diff. A new export from a proof module therefore never goes in silently.
