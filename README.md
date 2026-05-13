# merc-verified

Formal verification of labelled transition system (LTS) algorithms. Rust implementations in `crate/` are translated to Lean 4 via [Aeneas](https://github.com/AeneasVerif/aeneas) and verified against formal definitions in `MercVerified/`.

We want to prove the correctness of the `merc` repository. For this we introduce a derived `crate` of (simplified) Rust code that we can translate to Lean and verify. The `MercVerified/` directory contains the formal definitions and proofs, while `Code` contains the generated Lean code from the Rust implementations.

## Prerequisites

- [Rust](https://rustup.rs/) (stable toolchain)
- [Lean 4](https://leanprover-community.github.io/get_started.html) (managed via `elan`)
- [OCaml 5.3](https://ocaml.org/install) (via `opam`, for building Aeneas)

## Getting Started

### 1. Initialize the submodules

Use the following command to initialize the git submodule:

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
opam switch create 5.3.0

opam install ppx_deriving visitors easy_logging zarith yojson core_unix odoc \
  ocamlgraph menhir ocamlformat.0.27.0 unionFind zarith progress domainslib

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

### 5. Proving with AI agents

Install `ripgrep` for searching:

```bash
cargo install --locked ripgrep
```

Install the `uv` Python package manager for the `lean-lsp-mcp`. A `MCP` is a
Model Context Protocol that allows AI agents to connect to external programs, in
this case interacting with lean.

```bash
cargo install uv
```
