## AI Agent Workflow (lean-lsp MCP)

The `.mcp.json` configures a `lean-lsp` MCP server for interactive proving. Key tools:

- `lean_goal` — proof state at a cursor position ("no goals" = done)
- `lean_diagnostic_messages` — compiler errors/warnings
- `lean_multi_attempt` — test a list of tactics at a position without editing
- `lean_local_search` — find local definitions before guessing names
- `lean_leansearch` / `lean_loogle` / `lean_state_search` — search mathlib/cslib

When writing proofs, use `lean_multi_attempt` to test tactics before committing edits.

**File editing policy:** `Signatures/Proofs/` files are machine-generated and can be freely modified. All other `Signatures/` files are human-vetted — make only minimal, necessary changes (e.g. adding a `theorem` statement or a single helper `def`); do not refactor, reorder, or rewrite existing content.

## Key Definitions

| Symbol | File | Description |
|---|---|---|
| `LabelledTransitionSystem` | `Signatures/Basic.lean` | Core LTS structure |
| `LTS.IsBranchingBisimulation` | `Signatures/BranchingBisimilarity.lean` | Branching bisimulation predicate |
| `BranchingBisimilarity` | `Signatures/BranchingBisimilarity.lean` | Bisimilarity relation (`≈br[lts]`) |
| `StrongSignature` / `Refine` / `IsStable` / `FixPoint` | `Signatures/Signature.lean` | Partition refinement for observational equivalence |
