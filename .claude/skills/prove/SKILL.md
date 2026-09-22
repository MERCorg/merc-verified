---
name: prove
description: lean-lsp MCP workflow, key tools, and definitions for interactive Lean proving. Use when writing or fixing Lean proofs, inspecting proof states, searching for lemmas, or verifying/checking a Lean file without a full `lake build`.
---

## AI Agent Workflow (lean-lsp MCP)

The `.mcp.json` configures a `lean-lsp` MCP server for interactive proving. Key tools:

- `lean_goal` — proof state at a cursor position ("no goals" = done)
- `lean_diagnostic_messages` — compiler errors/warnings for a file
- `lean_multi_attempt` — test a list of tactics at a position without editing
- `lean_local_search` — find local definitions before guessing names
- `lean_leansearch` / `lean_loogle` / `lean_state_search` / `lean_leanfinder` / `lean_hammer_premise` — search mathlib/cslib (rate-limited; try `lean_local_search` first)
- `lean_verify` — axiom check + source scan for one theorem (see "Verifying a headline theorem" below)
- `lean_hover_info` / `lean_declaration_file` — type signature and source of a symbol
- `lean_file_outline` — token-efficient list of imports/declarations for a file
- `lean_code_actions` — resolved edits for `Try this` suggestions (`simp?`, `exact?`)
- `lean_build` — full `lake build` + LSP restart; slow (see below), use sparingly

This MCP does not edit files — use `Edit`/`Write` for that. All line/column numbers are 1-indexed, columns count characters.

## Checking a file — prefer `lean_diagnostic_messages` over `lake build`

`lake build` recompiles through Mathlib/cslib/Aeneas and can take several minutes even for a one-line change several layers downstream; it is not a reasonable way to check a single edit. Reach for `lean_diagnostic_messages` on the target file instead — the LSP has it (and its dependencies) already elaborated. Reserve `lean_build` for when imports or dependencies actually changed (diagnostics look stale, or a file references a name from a module that isn't imported yet).

1. Run `lean_diagnostic_messages` on the target file (absolute path). No diagnostics means it elaborates cleanly.
2. To check a whole area, run it file-by-file in dependency order — an error upstream usually explains the downstream ones, so fix in that order. Two independent chains in this repo:
   - **`Signatures/`**: `BranchingBisimilarity.lean` → `Signature.lean` → `InductiveSignatures.lean`, then `Proofs/BranchingBisimilarity_Transitivity_Proofs.lean` → `Proofs/Signature_Proofs.lean` → `Proofs/InductiveSignatures_Proofs.lean` → `Basic.lean` (aggregator, imports everything).
   - **`MercVerified/`**: `Basic.lean` (imports `MercVerified.Code.*` and the top-level `Signatures/` defs), then `Signatures/StrongSignature.lean` → `Signatures/Refinement.lean`, then `Signatures/Proofs/StrongSignature_Proofs.lean` → `Signatures/Proofs/Refinement_Proofs.lean`.
3. Interpreting results:
   - `declaration uses 'sorry'` (warning) — an incomplete proof. Report it; do not treat the file as verified. If it's one of the theorems listed in `scripts/check_axioms.py`'s `KNOWN_INCOMPLETE`, that's expected and tracked — otherwise it's new and worth flagging.
   - `no goals to be solved` — delete the trailing tactics.
   - `unknown identifier`/`unknown constant` — the name is wrong or not in scope. Try `lean_local_search` first (this repo's own lemmas), then `lean_loogle`/`lean_leansearch` for cslib/Mathlib.
   - Errors that only appear after an import edit may be stale — that's the case for `lean_build`.

## Verifying a headline/pinned theorem

Per the lean-conventions skill's spec/Proofs/pin split, a handful of theorems are "headline" results with a signature-drift pin (an `example := theoremName` right after them) and are checked in CI by `scripts/check_axioms.py`. `lean_verify` with the fully qualified name is the interactive-session equivalent — it confirms the theorem depends on no `sorry` or unexpected axiom before you commit to a proof being "done":

```
lean_verify(file_path=".../Proofs/Refinement_Proofs.lean", theorem_name="MercVerified.Signatures.Proofs.strong_bisim_sigref_correct")
```

Only scans the given file, not its imports, so run it on the file that actually declares the theorem.

## Proof idioms in this repo

- **Translated-code contracts** (theorems about Aeneas-translated Rust, e.g. `MercVerified/Signatures/Proofs/StrongSignature_Proofs.lean`) go through `Aeneas.Std.WP`: `spec_bind`, `spec_imp_exists`, `loop.spec_decr_nat` with explicit `measure`/`inv`/`post`, and `unfold <def>` before stepping through a `do`-block. Look at an existing loop proof before writing a new one — the shape is fairly fixed.
- **Pure LTS/signature math** (`Signatures/Proofs/*.lean`) is mostly `rcases`/`obtain` destructuring, `calc` chains through `↔`/`⊆`, and targeted `simp [...]`/`rw [...]`. See lean-conventions for the general tactic-preference order (`grind`/`simp`/`omega`/`aesop`/`decide` before manual term-mode).

## Fixing a failing proof

1. `lean_goal` at the failing line (omit `column` to see the state before and after the line).
2. `lean_multi_attempt` to test candidates without editing the file.
3. If automation stalls, the missing ingredient is usually an unfolding or a side condition, not a cleverer tactic: supply the equation (`unfold`, `simp [f]`) or the invariant as a hypothesis and retry.
4. If a supporting lemma might already exist, check `lean_local_search` (this project) before `lean_state_search`/`lean_leansearch`/`lean_loogle`/`lean_hammer_premise` (cslib/Mathlib).
5. Apply the fix, then re-run `lean_diagnostic_messages` on the file.

**File editing policy:** `Signatures/Proofs/` and `MercVerified/Signatures/Proofs/` files are machine-generated and can be freely modified. All other `Signatures/` and `MercVerified/Signatures/` files are human-vetted — make only minimal, necessary changes (e.g. adding a spec `def` or a single helper `def`); do not refactor, reorder, or rewrite existing content. See the lean-conventions skill for the spec/Proofs/pin split these files follow.

## Rules

- Never close a goal with `sorry` to make diagnostics pass. If a proof cannot be completed, say so and leave the goal open with an explanation.
- Do not weaken, restate, or add a hypothesis to a pinned/headline theorem's signature to make it provable without saying so explicitly — that's a contract change, not a proof detail (see lean-conventions' spec/Proofs/pin split). If the proof genuinely needs more than the spec grants, the spec itself needs a deliberate, reviewed edit, not a quiet signature change in the Proofs file.
- Only add an import when a lemma genuinely needs it; after changing imports, run `lean_build` once so the LSP picks up the new dependency.
- Report per-file: clean / errors (with line numbers) / sorries.

## Key Definitions

| Symbol | File | Description |
|---|---|---|
| `LabelledTransitionSystem` | `Signatures/Basic.lean` | Core LTS structure |
| `LTS.IsBranchingBisimulation` | `Signatures/BranchingBisimilarity.lean` | Branching bisimulation predicate |
| `BranchingBisimilarity` | `Signatures/BranchingBisimilarity.lean` | Bisimilarity relation (`≈br[lts]`) |
| `StrongSignature` / `Refine` / `IsStable` / `FixPoint` | `Signatures/Signature.lean` | Partition refinement for observational equivalence |
| `StrongBisimSignatureSpec` | `MercVerified/Signatures/StrongSignature.lean` | Contract: translated `strong_bisim_signature` computes `StrongSignature` |
| `StrongBisimSigrefCorrectSpec` | `MercVerified/Signatures/Refinement.lean` | Contract: translated `strong_bisim_sigref` is a strong-bisimulation partition refinement (open, `sorry`) |
