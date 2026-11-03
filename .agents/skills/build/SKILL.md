---
name: build
description: Build and test commands for the Lean and Rust projects. Use when the user asks to build, check proofs, run tests, or verify the project compiles.
---

## Build Commands

```bash
# Build everything (checks all Lean proofs; default targets are MercVerified and Signatures)
lake build

# Check headline theorems (statements and axioms) against the human-vetted challenges
lake comparator --config comparator.json                # MercLib
lake comparator --config comparator_MercVerified.json   # MercVerified

# Check the exported API against EXPORTS.md (`--write` regenerates it for review)
lake env lean --run scripts/CheckExports.lean

# Build just the Rust crate
cd verified && cargo build

# Run Rust tests
cd verified && cargo test
```