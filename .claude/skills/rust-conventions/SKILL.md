---
name: rust-conventions
description: Rust coding conventions for Aeneas-compatible code. Use when writing or editing `.rs` files in `verified/` or in the `3rd-party/merc` submodule that `verified/Cargo.toml` compiles through Charon.
---

## Rust Conventions

- Edition 2024. `#![forbid(unsafe_code)]` is enforced.
- Keep code Aeneas-compatible: no `async`, no trait objects, no raw pointers, no features Aeneas cannot translate.
- `snake_case` for functions/variables, `PascalCase` for types.
- `verified/Cargo.toml` itself has no interesting source - Charon's `[package.metadata.charon]` `include`/`exclude`/`opaque` lists there point at real code in the `3rd-party/merc` git submodule (e.g. `3rd-party/merc/crates/reduction/src/block_partition.rs`), and `merc_lts`/`merc_reduction` are pulled in with `features = ["lean"]`. Editing Rust for this project almost always means editing files under `3rd-party/merc`, not `verified/`.

## Making an `opaque`-listed function transparent (translatable)

Several functions in `3rd-party/merc` are deliberately split into two implementations selected by the `lean` Cargo feature: the original, idiomatic Rust (`#[cfg(not(feature = "lean"))]`) and a rewrite using only patterns Aeneas can translate (`#[cfg(feature = "lean")]`) - see `BlockPartition::new`/`swap_blocks`/`mark_backward_closure` and `IncomingTransitions::new` for worked examples. To turn an `opaque`-listed function transparent:

1. **Never edit the existing definition in place.** Add `#[cfg(not(feature = "lean"))]` to it if it doesn't already have one, so it keeps compiling and running exactly as before for non-`lean` builds (benchmarks, the non-Aeneas test suite). The `lean`-feature rewrite is a new, separate `fn` with the same signature, not a modification of the original.
2. Write the `#[cfg(feature = "lean")]` rewrite avoiding whatever Aeneas can't handle: closures capturing `self` mutably (`.iter_mut().fold(...)`), custom `Iterator` impls (`Block::iter`/`iter_marked`/etc.) and adaptor chains (`.map()`, `.take_while()`, `.all()`), `impl Iterator` return types (return `Vec<T>` and iterate it with a plain `for x in vec` instead - `Vec`'s `IntoIterator`/manual index loops are fine), and `Vec::swap` (swap manually through two element accesses). If a dependency (e.g. `IncomingTransitions::incoming_silent_transitions`) only has an iterator-returning version, add a `Vec`-returning one under its own `#[cfg(feature = "lean")]` the same way.
3. Remove the function from `verified/Cargo.toml`'s `[package.metadata.charon] opaque` list.
4. Run **both** `cargo build` and `cargo test --features lean -p <crate>` from inside `3rd-party/merc` before regenerating - the lean rewrite is new code with no direct test of its own, so the existing test suite (run with the `lean` feature on) is what actually exercises it.
5. Regenerate with the `/regenerate` skill. Watch for translation errors like "Continue to outer loops are not supported yet" - these mean the CFG shape (typically a `while` loop containing a `for` loop, with a `break`/early-exit placed *after* the inner loop) still isn't translatable; restructure so the exit check happens before any nested loop, e.g. turn a `while` + manual index decrement + trailing `if idx == 0 { break }` into a `for idx in (lo..hi).rev()` with the exit condition checked as the first statement in the loop body.
6. Downstream Lean proofs that treated the function as an opaque axiom (e.g. a hand-written boundary axiom in `FunsExternalSpecs.lean`) need to change too: the axiom becomes provable by `unfold`-ing the real generated `def` instead.