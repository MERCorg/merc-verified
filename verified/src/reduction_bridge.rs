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
use merc_lts::LabelledTransitionSystem;
use merc_lts::StateIndex;
use merc_lts::TransitionLabel;
use merc_reduction::BlockPartition;
use merc_reduction::Partition;
use merc_reduction::SignatureBuilder;
use merc_utilities::Timing;
use rustc_hash::FxHashSet;

pub fn strong_bisim_sigref<L: LTS>(lts: L, timing: &Timing) -> (L, BlockPartition) {
    merc_reduction::strong_bisim_sigref(lts, timing)
}

pub fn labelled_transition_system_strong_bisim_sigref<Label: TransitionLabel>(
    lts: LabelledTransitionSystem<Label>,
    timing: &Timing,
) -> (LabelledTransitionSystem<Label>, BlockPartition) {
    strong_bisim_sigref(lts, timing)
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

/// Branching bisimulation partitioning of an LTS that is already free of
/// tau-cycles and topologically sorted, see
/// `merc_reduction::signature_refinement::branching_bisim_sigref_impl`.
pub fn branching_bisim_sigref_impl<L: LTS>(preprocessed_lts: &L, timing: &Timing) -> BlockPartition {
    merc_reduction::branching_bisim_sigref_impl(preprocessed_lts, timing)
}

pub fn tau_cycle_elimination_and_reorder<L: LTS>(
    lts: L,
    state: StateIndex,
    eliminate_tau_selfloops: bool,
) -> (LabelledTransitionSystem<L::Label>, StateIndex) {
    merc_reduction::tau_cycle_elimination_and_reorder(lts, state, eliminate_tau_selfloops)
}

pub fn branching_bisim_sigref<L: LTS>(
    lts: L,
    state: StateIndex,
    divergence_preserving: bool,
    timing: &Timing,
) -> (LabelledTransitionSystem<L::Label>, StateIndex, BlockPartition) {
    merc_reduction::branching_bisim_sigref(lts, state, divergence_preserving, timing)
}

pub fn labelled_transition_system_branching_bisim_sigref<Label: TransitionLabel>(
    lts: LabelledTransitionSystem<Label>,
    state: StateIndex,
    divergence_preserving: bool,
    timing: &Timing,
) -> (LabelledTransitionSystem<Label>, StateIndex, BlockPartition) {
    branching_bisim_sigref(lts, state, divergence_preserving, timing)
}
