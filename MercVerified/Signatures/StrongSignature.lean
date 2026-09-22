import MercVerified.Basic

/-!
# `strong_bisim_signature` correctness contract

Human-vetted specification of what it means for the Aeneas-translated
`merc_reduction::signatures::strong_bisim_signature` (reachable via the
`verified/src/reduction_bridge.rs` bridge, see
`docs/plans/reduction-signatures-translation.md`) to compute the hand-vetted
mathematical `StrongSignature` from `Signatures/Signature.lean`.

`block_number` (`Partition.block_number`) is fallible in the translation
(a Rust panic on an out-of-range index becomes `Result.fail`), so the
statement is conditioned on it succeeding everywhere via `blockNumber`, the
total function it agrees with. Likewise `outgoing_transitions` is conditioned
on succeeding for `s` via `ts`. `strong_bisim_signature` also sorts and
dedups its accumulator, which is deliberately *not* part of this statement -
we only characterize the returned list by membership, matching
`StrongSignature`'s `Set`.

This file states the contract only, as `StrongBisimSignatureSpec` below - it
proves nothing. The proof (and the private helper lemmas it needs) lives in
`MercVerified/Signatures/Proofs/StrongSignature_Proofs.lean`, which is
machine-generated and may be freely edited or regenerated. That file also
pins the proof's exact closed signature against this spec right after the
theorem, so it can be regenerated without a human re-reading it for a
silently added/dropped hypothesis: any drift fails `lake build` at the pin,
not just at review time.
-/

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel Transition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.partition (Partition)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)
open verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem (toLTS)

namespace MercVerified.Signatures

/-- The machine-checked form of the `strong_bisim_signature` contract: run
    against the `toLTS` view of a `SimpleLabelledTransitionSystem`, it
    computes exactly the mathematical `StrongSignature` - as long as
    `outgoing_transitions s` and every `block_number` lookup it needs
    actually succeed. Nothing in this file proves this spec - see
    `Proofs.strong_bisim_signature_spec` in
    `Proofs/StrongSignature_Proofs.lean`. -/
def StrongBisimSignatureSpec
    {Label P : Type}
    (TLInst : TransitionLabel Label)
    (PInst : Partition P)
    (sys : SimpleLabelledTransitionSystem Label)
    (partition : P)
    (s : TagIndex Std.Usize StateTag)
    (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (hblock : ∀ t, PInst.block_number partition t = ok (blockNumber t))
    (ts : alloc.vec.Vec Transition)
    (houtgoing :
      (verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS
          TLInst).outgoing_transitions sys s = ok ts) : Prop :=
  ∃ result,
    verified.merc_reduction.signatures.strong_bisim_signature
        (verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
        PInst s sys partition builder0 = ok result
    ∧ ∀ μ β, (μ, β) ∈ result.val ↔
        (μ, β) ∈ StrongSignature (toLTS TLInst sys) s blockNumber

end MercVerified.Signatures
