import MercVerified.Signatures.StrongSignature
import MercVerified.Signatures.Proofs.StrongSignature_Proofs

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.partition (Partition)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)
open MercVerified.Signatures (StrongBisimSignatureSpec)

-- Contract pin: fails to compile if `strong_bisim_signature_spec_general`'s signature drifts.
example :
    ∀ {L Label P : Type}
      (LTSInst : LTS L Label) (PInst : Partition P)
      (sys : L) (partition : P)
      (s : TagIndex Std.Usize StateTag)
      (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
      (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
      (hblock : ∀ t, PInst.block_number partition t = ok (blockNumber t))
      (ts : alloc.vec.Vec Transition)
      (houtgoing : LTSInst.outgoing_transitions sys s = ok ts),
      StrongBisimSignatureSpec LTSInst PInst sys partition s builder0 blockNumber hblock ts houtgoing :=
  MercVerified.Signatures.Proofs.strong_bisim_signature_spec_general

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
      StrongBisimSignatureSpec
        (verified.simple_labelled_transition_system.SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
        PInst sys partition s builder0 blockNumber hblock ts houtgoing :=
  MercVerified.Signatures.Proofs.strong_bisim_signature_spec
