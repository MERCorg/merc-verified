---
name: build
description: Build and test commands for the Lean and Rust projects. Use when the user asks to build, check proofs, run tests, or verify the project compiles.
---

## Build Commands

```bash
# Build everything (checks all Lean proofs; default targets are MercVerified and Signatures)
lake build

# Check headline theorems depend on no unapproved axioms (run after `lake build`)
python3 scripts/check_axioms.py

# Build just the Rust crate
cd verified && cargo build

# Run Rust tests
cd verified && cargo test
```