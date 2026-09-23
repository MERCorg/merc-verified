//! Thin, fully-generic forwarders into `merc_reduction`'s partition-refinement
//! signature functions.
//!
//! These exist purely so Charon/Aeneas has a real local call site for them.
//! Reaching them only via `--start-from` (see `Cargo.toml`) with no caller
//! in this crate's own call graph causes Aeneas's Lean backend to silently
//! drop the function from the generated `.lean` files, even though Charon
//! extracts a perfectly good body for it. See `/regenerate`.
//!
//! Each wrapper stays fully polymorphic (same `L`/`P` type parameters as the
//! wrapped function) so Charon keeps translating the dictionary-passing,
//! non-monomorphized form - this file changes reachability only, not shape.


use merc_collections::BlockIndex;
use merc_lts::LTS;
use merc_lts::StateIndex;
use merc_reduction::BlockPartition;
use merc_reduction::Partition;
use merc_reduction::SignatureBuilder;
use merc_utilities::Timing;
use rustc_hash::FxHashSet;

pub fn strong_bisim_sigref<L: LTS>(lts: L, timing: &Timing) -> (L, BlockPartition) {
    merc_reduction::strong_bisim_sigref(lts, timing)
}

pub fn strong_bisim_signature<L: LTS, P: Partition>(
    state_index: StateIndex,
    lts: &L,
    partition: &P,
    builder: &mut SignatureBuilder,
) {
    merc_reduction::strong_bisim_signature(state_index, lts, partition, builder)
}

pub fn branching_bisim_signature<L: LTS, P: Partition>(
    state_index: StateIndex,
    lts: &L,
    partition: &P,
    builder: &mut SignatureBuilder,
    visited: &mut FxHashSet<StateIndex>,
    stack: &mut Vec<StateIndex>,
) {
    merc_reduction::branching_bisim_signature(state_index, lts, partition, builder, visited, stack)
}

pub fn branching_bisim_signature_inductive<L: LTS>(
    state_index: StateIndex,
    lts: &L,
    partition: &BlockPartition,
    state_to_key: &[BlockIndex],
    builder: &mut SignatureBuilder,
) {
    merc_reduction::branching_bisim_signature_inductive(state_index, lts, partition, state_to_key, builder)
}
