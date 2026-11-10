---
name: build
description: Build and test commands for the Lean and Rust projects. Use when the user asks to build, check proofs, run tests, or verify the project compiles.
---

## Build Commands

```bash
# Build everything (checks all Lean proofs; default targets are MercVerified and MercLib)
lake build

# Build one module and its dependencies (faster when checking a single file)
lake build MercLib.Theory.Graph.Proofs.Scc_Proofs

# Run the MercLib tests (MercLibTest/)
lake test

# Check headline theorems (statements and axioms) against the human-vetted challenges
lake comparator --config comparator.json                # MercLib
lake comparator --config comparator_MercVerified.json   # MercVerified

# Check the exported API against EXPORTS.md (`--write` regenerates it for review)
lake env lean --run scripts/CheckExports.lean

# Delegate one `sorry` to an opencode instance and check the result (see the delegate-proofs skill)
scripts/delegate_proof.py <Proofs file> <declaration> [hint]

# Build just the Rust crate
cd verified && cargo build

# Run Rust tests
cd verified && cargo test
```