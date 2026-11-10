---
name: prove
description: lean-lsp MCP workflow, key tools, and definitions for interactive Lean proving. Use when writing or fixing Lean proofs, inspecting proof states, searching for lemmas, or verifying/checking a Lean file without a full `lake build`.
---

## AI Agent Workflow (lean-lsp MCP)

The `lean-lsp` MCP server (configured in `.mcp.json`, `opencode.json` and `.vscode/mcp.json`) supports interactive proving. Key tools:

- `lean_goal` — proof state at a cursor position (`status: complete` = done)
- `lean_diagnostic_messages` — compiler errors/warnings for a file
- `lean_multi_attempt` — test a list of tactics at a position without editing
- `lean_local_search` — find local definitions before guessing names
- `lean_leansearch` / `lean_loogle` / `lean_leanfinder` / `lean_hammer_premise` — search Mathlib/cslib (rate-limited; try `lean_local_search` first)
- `lean_verify` — axiom check + source scan for one theorem (see "Verifying a headline theorem" below)
- `lean_hover_info` / `lean_declaration_file` — type signature and source of a symbol
- `lean_file_outline` — token-efficient list of imports/declarations for a file
- `lean_code_actions` — resolved edits for `Try this` suggestions (`simp?`, `exact?`)
- `lean_run_code` — elaborate a standalone snippet (with its own imports), e.g. to test a counterexample
- `lean_build` — full `lake build` + LSP restart; slow (see below), use sparingly

This MCP does not edit files — use your own file-editing tools for that. All line/column numbers are 1-indexed, columns count characters.

With several open goals, or a proof that breaks into independent helper lemmas, split the work across `lean-prover` subagents and opencode instances: see the `delegate-proofs` skill.

## Checking a file — prefer `lean_diagnostic_messages` over `lake build`

`lake build` recompiles through Mathlib/cslib/Aeneas and can take several minutes even for a one-line change several layers downstream; it is not a reasonable way to check a single edit. Reach for `lean_diagnostic_messages` on the target file instead — the LSP has it (and its dependencies) already elaborated. Reserve `lean_build` for when imports or dependencies actually changed (diagnostics look stale, or a file references a name from a module that isn't imported yet). `lake build <Module.Name>` builds one module and its dependencies when you need a command-line check.

1. Run `lean_diagnostic_messages` on the target file (absolute path). No diagnostics means it elaborates cleanly.
2. To check a whole area, run it file-by-file in dependency order (follow the imports; each area's `Basic.lean` is an aggregator that imports everything) — an error upstream usually explains the downstream ones, so fix in that order. Spec files come before their `Proofs/` files.
3. Interpreting results:
   - `declaration uses 'sorry'` (warning) — an incomplete proof. Report it; do not treat the file as verified. Outside `Challenges/` (where every theorem is `sorry` by design) the library currently has no `sorry`, so any new one is worth flagging.
   - `no goals to be solved` — delete the trailing tactics.
   - `unknown identifier`/`unknown constant` — the name is wrong or not in scope. Try `lean_local_search` first (this repo's own lemmas), then `lean_loogle`/`lean_leansearch` for cslib/Mathlib. A `private` name from another module is only visible through `import all`.
   - Errors that only appear after an import edit may be stale — that's the case for `lean_build`.

## Verifying a headline theorem

Per the lean-conventions skill's spec/Proofs/challenge split, headline theorems are re-stated with `sorry` in `Challenges/` and checked in CI by `lake comparator` (statement and axioms). `lean_verify` with the fully qualified name is the interactive-session equivalent — it confirms the theorem depends on no `sorry` or unexpected axiom before you commit to a proof being "done":

```
lean_verify(file_path=".../MercVerified/Refinement/Proofs/Refinement_Proofs.lean", theorem_name="MercVerified.Refinement.Proofs.strong_bisim_sigref_correct")
```

Only scans the given file, not its imports, so run it on the file that actually declares the theorem. Permitted axioms are `propext`, `Classical.choice`, `Quot.sound`, and for `MercVerified` the Aeneas boundary axioms listed in `comparator_MercVerified.json`. Before calling a headline done, run the matching `lake comparator --config ...` (see the `build` skill): it also catches a statement that drifted from its challenge.

## Proof idioms in this repo

- **Translated-code contracts** (theorems about Aeneas-translated Rust, e.g. `MercVerified/Refinement/Proofs/StrongSignature_Proofs.lean`) go through `Aeneas.Std.WP`: `spec_bind`, `spec_imp_exists`, `loop.spec_decr_nat` with explicit `measure`/`inv`/`post`, and `unfold <def>` before stepping through a `do`-block. Look at an existing loop proof before writing a new one — the shape is fairly fixed.
- **`while`/`for` loops in `Id.run do` pseudocode** (`MercLib/Algorithms/`): use `whileInduction` / `forInList_induction` from `MercLib/Util/Proofs/While_Proofs.lean` with an invariant and a decreasing measure.
- **Pure theory** (`MercLib/Theory/*/Proofs/*.lean`) is mostly `rcases`/`obtain` destructuring, `calc` chains through `↔`/`⊆`, and targeted `simp [...]`/`rw [...]`. See lean-conventions for the general tactic-preference order (`grind`/`simp`/`omega`/`aesop`/`decide` before manual term-mode).
- No `native_decide` anywhere a headline depends on: the comparator cannot load its auxiliary axiom (see the `ci` skill).

## Fixing a failing proof

1. `lean_goal` at the failing line (omit `column` to see the state before and after the line).
2. `lean_multi_attempt` to test candidates without editing the file.
3. If automation stalls, the missing ingredient is usually an unfolding or a side condition, not a cleverer tactic: supply the equation (`unfold`, `simp [f]`) or the invariant as a hypothesis and retry.
4. If a supporting lemma might already exist, check `lean_local_search` (this project) before `lean_leansearch`/`lean_loogle`/`lean_hammer_premise` (cslib/Mathlib).
5. If you suspect the goal is false, test a concrete instance with `lean_run_code` before spending more effort.
6. Apply the fix, then re-run `lean_diagnostic_messages` on the file.

**File editing policy:** `MercLib/**/Proofs/` and `MercVerified/{Refinement,Lts}/Proofs/` files are machine-generated and can be freely modified. All other `MercLib/`, `MercVerified/Refinement/` and `MercVerified/Lts/` files, `Challenges/`, the comparator configs and `EXPORTS.md` are human-vetted — make only minimal, necessary changes (e.g. adding a spec `def` or a single helper `def`); do not refactor, reorder, or rewrite existing content. See the lean-conventions skill for the spec/Proofs/challenge split these files follow.

## Rules

- Never close a goal with `sorry` to make diagnostics pass. If a proof cannot be completed, say so and leave the goal open with an explanation.
- When an existing proof is replaced by `sorry` (e.g. a spec change breaks it, or it needs to be reworked later), keep the old proof body as a comment directly above the `sorry` rather than deleting it — it's a hint for whoever reproves it.
- Do not weaken, restate, or add a hypothesis to a headline theorem's signature to make it provable without saying so explicitly — that's a contract change, not a proof detail (see lean-conventions' spec/Proofs/challenge split). If the proof genuinely needs more than the spec grants, the spec itself needs a deliberate, reviewed edit, not a quiet signature change in the Proofs file.
- Helper lemmas in `Proofs/` files are `private` (see lean-conventions, "Exports").
- Only add an import when a lemma genuinely needs it; after changing imports, run `lean_build` once so the LSP picks up the new dependency.
- Report per-file: clean / errors (with line numbers) / sorries.

## Key Definitions

| Symbol | File | Description |
|---|---|---|
| `Cslib.LTS` | cslib (`Cslib.Foundations.Semantics.LTS.Basic`) | Labelled transition system used by the theory |
| `IsBranchingBisimulation` / `BranchingBisimilarity` (`≈br[lts]`) | `MercLib/Theory/LTS/BranchingBisimilarity.lean` | Branching bisimulation and bisimilarity |
| `StrongSignature` / `IsStable` / `FixPoint` | `MercLib/Theory/Signatures/Signature.lean` | Signatures and partition refinement fixpoints |
| `toLTS` / `WellFormed` / `NonEmpty` | `MercVerified/Lts/Lts.lean` | The Rust `LTS` trait as a `Cslib.LTS`, and well-formedness of a translated system |
| `StrongBisimSigrefCorrectSpec` / `BranchingBisimSigrefImplCorrectSpec` / `BranchingBisimSigrefCorrectSpec` | `MercVerified/Refinement/Refinement.lean` | Contracts for the translated signature-refinement algorithms |
| `merc_lts.labelled_transition_system.LabelledTransitionSystem` | `MercVerified/Code/Types.lean` (generated) | The translated Rust LTS structure |
