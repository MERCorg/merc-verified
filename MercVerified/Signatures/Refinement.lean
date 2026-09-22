import MercVerified.Basic
import MercVerified.Signatures.StrongSignature

/-!
# `strong_bisim_sigref` correctness contract

Human-vetted specification of what it means for the Aeneas-translated
`merc_reduction::signature_refinement::strong_bisim_sigref` (reachable via the
`verified/src/reduction_bridge.rs` bridge) to behave as a strong-bisimulation
partition refinement, in the hand-vetted `StrongSignature` / `IsStable`
vocabulary from `Signatures/Signature.lean`.

`strong_bisim_sigref` is the entry point of merc's strong-bisimulation
partition-refinement reduction. Its internals originally relied on
`unsafe`/arena-lifetime-relaxation, FxHashMap/iterator closures, and
`&mut`-borrow threading that Aeneas could not translate at all, so
`strong_bisim_sigref` used to be kept opaque in full (contract stated as a
single spec axiom on the whole function).

`merc_reduction::signature_refinement` (the `3rd-party/merc` submodule) was
since rewritten to be Aeneas-translatable: the `unsafe` arena reuse was
replaced by a fresh per-iteration arena, and the worklist-refinement loop and
its helpers were factored out into a chain of small functions (see
`verified/Cargo.toml` for the history). `strong_bisim_sigref` and
`signature_refinement` are consequently *no longer opaque* - Aeneas produces
real translated bodies for both. The remaining opaque boundary is just
`merc_reduction.signature_refinement.run_worklist_loop` (the core
worklist-refinement fixpoint, operating on a `WorklistContext`), an
externally-declared axiom in `MercVerified/Code/FunsExternal_Template.lean`
with no hand-written contract yet.

This file states the contract only, as `StrongBisimSigrefCorrectSpec` below -
it proves nothing. The proof lives in
`MercVerified/Signatures/Proofs/Refinement_Proofs.lean`, which is
machine-generated and may be freely edited or regenerated (currently `sorry`:
it requires unfolding the newly-translated `do`-blocks of
`strong_bisim_sigref`/`signature_refinement` down to the `run_worklist_loop`
call and a hand-written contract axiom for it, mirroring what the old
whole-function axiom stated). That file also pins the proof's exact closed
signature against this spec right after the theorem, so it can be regenerated
without a human re-reading it for a silently added/dropped hypothesis: any
drift fails `lake build` at the pin, not just at review time.
-/

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition)
open merc_reduction.signature_refinement (strong_bisim_sigref)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)
open verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem (toLTS)

namespace MercVerified.Signatures

/-- The machine-checked form of the `strong_bisim_sigref` contract: it behaves
    as a strong-bisimulation partition refinement. `strong_bisim_sigref` and
    `signature_refinement` are real translated definitions (no longer an
    opaque whole-function axiom - see the module doc comment above), but
    nothing in this file proves this spec - see
    `Proofs.strong_bisim_sigref_correct` in `Proofs/Refinement_Proofs.lean`. -/
def StrongBisimSigrefCorrectSpec
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) : Prop :=
  ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
    strong_bisim_sigref
        (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
        sys timing = ok (sys, partition) ∧
    (∀ s b, (s, b) ∈ List.zip partition.elements.val partition.element_to_block.val →
        blockOf s = b) ∧
    IsStable (fun s => StrongSignature (toLTS TLInst sys) s blockOf) blockOf

end MercVerified.Signatures
