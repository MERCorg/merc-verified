import MercVerified.Basic

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.partition (Partition)
open verified.merc_lts.lts.LTS (toLTS)

namespace MercVerified.Signatures

def StrongBisimSignatureSpec
    {L Label P : Type}
    (LTSInst : LTS L Label)
    (PInst : Partition P)
    (sys : L)
    (partition : P)
    (s : TagIndex Std.Usize StateTag)
    (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (_hblock : ∀ t, PInst.block_number partition t = ok (blockNumber t))
    (ts : alloc.vec.Vec Transition)
    (_houtgoing : LTSInst.outgoing_transitions sys s = ok ts) : Prop :=
  ∃ result,
    verified.merc_reduction.signatures.strong_bisim_signature
        LTSInst PInst s sys partition builder0 = ok result
    ∧ ∀ μ β, (μ, β) ∈ result.val ↔
        (μ, β) ∈ StrongSignature (toLTS LTSInst sys) s blockNumber

end MercVerified.Signatures
