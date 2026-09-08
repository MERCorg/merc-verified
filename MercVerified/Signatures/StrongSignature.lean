import MercVerified.Basic

/-!
# `strong_bisim_signature` vs. `StrongSignature`

Relates the Aeneas-translated `merc_reduction::signatures::strong_bisim_signature`
(reachable via the `verified/src/reduction_bridge.rs` bridge, see
`docs/plans/reduction-signatures-translation.md`) to the hand-vetted
mathematical `StrongSignature` from `Signatures/Signature.lean`.

`block_number` (`Partition.block_number`) is fallible in the translation
(a Rust panic on an out-of-range index becomes `Result.fail`), so the
statement is conditioned on it succeeding everywhere via `blockNumber`, the
total function it agrees with. Likewise `outgoing_transitions` is conditioned
on succeeding for `s` via `ts`. `strong_bisim_signature` also sorts and
dedups its accumulator, which is deliberately *not* part of this statement -
we only characterize the returned list by membership, matching
`StrongSignature`'s `Set`.
-/

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel Transition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.partition (Partition)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)
open verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem (toLTS)

namespace MercVerified.Signatures

/-- The Rust `strong_bisim_signature`, run against the `toLTS` view of a
    `SimpleLabelledTransitionSystem`, computes exactly the mathematical
    `StrongSignature` - as long as `outgoing_transitions s` and every
    `block_number` lookup it needs actually succeed. -/
theorem strong_bisim_signature_spec
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
          TLInst).outgoing_transitions sys s = ok ts) :
    ∃ result,
      verified.merc_reduction.signatures.strong_bisim_signature
          (verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
          PInst s sys partition builder0 = ok result
      ∧ ∀ μ β, (μ, β) ∈ result.val ↔
          (μ, β) ∈ StrongSignature (toLTS TLInst sys) s blockNumber := by
  sorry

end MercVerified.Signatures
