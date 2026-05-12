# merc-verified

Formal verification of labelled transition system (LTS) algorithms. Rust implementations in `crate/` are translated to Lean 4 via [Aeneas](https://github.com/AeneasVerif/aeneas) and verified against formal definitions in `MercVerified/`.

## Prerequisites

- [Rust](https://rustup.rs/) (stable toolchain)
- [Lean 4](https://leanprover-community.github.io/get_started.html) (managed via `elan`)
- [OCaml 5.3](https://ocaml.org/install) (via `opam`, for building Aeneas)

## Getting Started

### 1. Clone the repository (with submodules)

```bash
git clone --recurse-submodules https://github.com/mlaveaux/merc-verified.git
cd merc-verified
```

If you already cloned without submodules:

```bash
git submodule update --init --recursive
```

### 2. Build Charon and Aeneas

Charon compiles Rust to LLBC, and Aeneas translates LLBC to Lean.

```bash
# Build Charon (Rust → LLBC compiler)
cd aeneas
make setup-charon
cd ..

# Install OCaml dependencies
opam install -y ppx_deriving visitors easy_logging zarith yojson \
  core_unix odoc ocamlgraph menhir ocamlformat.0.27.0 unionFind \
  zarith progress domainslib

# Build Aeneas (LLBC → Lean translator)
cd aeneas
eval $(opam env)
make
cd ..
```

### 3. Generate Lean code from Rust

```bash
# Generate LLBC from the Rust crate
cd crate
../aeneas/charon/bin/charon cargo --preset=aeneas
cd ..

# Translate LLBC to Lean
./aeneas/bin/aeneas -split-files -backend=lean -dest=. -subdir=Code ./crate/test.llbc
```

The generated Lean files will appear in `MercVerified/code/`.

### 4. Build the Lean project

```bash
lake build
```

This builds both the formal definitions in `MercVerified/` and the generated code in `MercVerified/code/`, checking all proofs.
