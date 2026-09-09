---
name: regenerate
description: Regenerate Lean code from Rust sources using Charon and Aeneas. Use when the user asks to regenerate `MercVerified/Code/`, rerun Aeneas, or update generated Lean after changing `verified/`.
---

## Regenerating Code from Rust

Run after changing `verified/` source:

```bash
# Step 1: Compile Rust → LLBC (produces verified/verified.llbc)
cd verified
../3rd-party/aeneas/charon/bin/charon cargo --preset=aeneas
cd ..

# Step 2: Translate LLBC → Lean (outputs to MercVerified/Code/)
./3rd-party/aeneas/bin/aeneas -split-files -backend=lean -dest=. -subdir=MercVerified/Code ./verified/verified.llbc
```

Then update `MercVerified/Code/*External.lean` to implement any new external function stubs.