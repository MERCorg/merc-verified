import MercVerified.Signatures.StrongSignature
import MercVerified.Signatures.Proofs.StrongSignature_Proofs

/-!
# Contract pin for `StrongSignature_Proofs.lean`

Human-vetted (see CLAUDE.md): make only minimal, targeted changes here.

The `example` below independently re-states the closed signature of
`strong_bisim_signature_spec`, proved in
`MercVerified/Signatures/Proofs/StrongSignature_Proofs.lean` against the
`StrongBisimSignatureSpec` contract stated in
`MercVerified/Signatures/StrongSignature.lean`. If a regeneration of that proof drifts from the
pinned shape (e.g. gains an unapproved extra hypothesis), the `example` fails to type-check and
`lake build` catches it, without a human having to diff two proofs to notice. See the
lean-conventions skill for the full spec/Proofs/pin pattern.
-/

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel Transition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.partition (Partition)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)
open MercVerified.Signatures (StrongBisimSignatureSpec)

-- Contract pin: fails to compile if `strong_bisim_signature_spec`'s signature drifts.
example :
    ∀ {Label P : Type}
      (TLInst : TransitionLabel Label) (PInst : Partition P)
      (sys : SimpleLabelledTransitionSystem Label) (partition : P)
      (s : TagIndex Std.Usize StateTag)
      (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
      (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
      (hblock : ∀ t, PInst.block_number partition t = ok (blockNumber t))
      (ts : alloc.vec.Vec Transition)
      (houtgoing :
        (verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS
            TLInst).outgoing_transitions sys s = ok ts),
      StrongBisimSignatureSpec TLInst PInst sys partition s builder0 blockNumber hblock ts houtgoing :=
  MercVerified.Signatures.Proofs.strong_bisim_signature_spec
