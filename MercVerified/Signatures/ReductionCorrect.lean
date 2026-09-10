import MercVerified.Basic
import MercVerified.Signatures.StrongSignature

/-!
# `strong_bisim_sigref` vs. strong-bisimulation stability

Relates the Aeneas-translated `merc_reduction::signature_refinement::strong_bisim_sigref`
(reachable via the `verified/src/reduction_bridge.rs` bridge) to the
hand-vetted `StrongSignature` / `IsStable` / `FixPoint` vocabulary from
`Signatures/Signature.lean`.

`strong_bisim_sigref` is the entry point of merc's strong-bisimulation
partition-refinement reduction. Its internals (the `signature_refinement`
refinement loop and the `BlockPartition` mutation machinery) rely on
FxHashMap/iterator closures and `&mut`-borrow threading that Aeneas cannot
translate - so, following the exact convention used for the `sort_unstable`,
`clear`, and `dedup` external specs, they are kept *opaque*
(`[package.metadata.charon].opaque` in `verified/Cargo.toml`) and their
contract is stated here as an explicit spec axiom.

`blockOf` is the total `TagIndex Usize StateTag → TagIndex Usize BlockTag` function
determined by the returned partition (mirroring how `strong_bisim_signature_spec`
takes a total `blockNumber`: `TagIndex` is opaque in the translation and
`block_number` is fallible). The axiom's coherence clause pins `blockOf` to agree
with the recorded `element_to_block` data on the states the partition actually
lists.

The contract is precisely the defining property of a strong-bisimulation
partition refinement: the returned partition is *stable* for the strong
signature - same-block states have identical strong signatures
(`IsStable (StrongSignature ...) blockOf`).

From that premise the file proves the mathematical consequences in the
`Signatures/Signature.lean` vocabulary:
- `strong_bisim_sigref_correct` - the machine-checked form of the contract;
- `stable_implies_strong_fixpoint` - a stable partition witnesses the
  strong-bisimulation `FixPoint` semantics: states in the same block are
  related by `StrongFixPoint` (proved from the definitions);
- `strong_bisim_sigref_same_block_strong_fixpoint` - combining the axiom with
  the latter: the partition that `strong_bisim_sigref` returns puts
  `StrongFixPoint`-related states in one block.
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

/-- The opaque `strong_bisim_sigref` (externals, see `verified/Cargo.toml`
    `[package.metadata.charon].opaque`). It returns the `lts` unchanged along
    with a `BlockPartition`, and - via the total `blockOf` that agrees with
    the recorded `element_to_block` data - that partition is *stable*:
    same-block states have identical `StrongSignature`. -/
axiom strong_bisim_sigref_spec
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      strong_bisim_sigref
          (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
          sys timing = ok (sys, partition) ∧
      (∀ s b, (s, b) ∈ List.zip partition.elements.val partition.element_to_block.val →
          blockOf s = b) ∧
      IsStable (fun s => StrongSignature (toLTS TLInst sys) s blockOf) blockOf

/-- The machine-checked form of the `strong_bisim_sigref` contract: it behaves
    as a strong-bisimulation partition refinement. -/
theorem strong_bisim_sigref_correct
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      strong_bisim_sigref
          (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
          sys timing = ok (sys, partition) ∧
      (∀ s b, (s, b) ∈ List.zip partition.elements.val partition.element_to_block.val →
          blockOf s = b) ∧
      IsStable (fun s => StrongSignature (toLTS TLInst sys) s blockOf) blockOf := by
  exact strong_bisim_sigref_spec TLInst sys timing

/-- Any partition that is stable for the strong signature witnesses the
    `StrongFixPoint` semantic: two states that end up in the same block are
    strong-bisimulation fixpoint related (take the stable partition itself as
    the witness). -/
theorem stable_implies_strong_fixpoint
    {State : Type u} {Label : Type v} (lts : Cslib.LTS State Label)
    {Block : Type u} (partition : State → Block)
    (hstable : IsStable (fun s => StrongSignature lts s partition) partition) :
    ∀ s s', partition s = partition s' → StrongFixPoint lts s s' := by
  intro s s' h
  unfold StrongFixPoint FixPoint
  refine ⟨Block, partition, ?_, h⟩
  simpa using hstable

/-- States that the `strong_bisim_sigref` refinement places in the same block
    are related by the strong-bisimulation `StrongFixPoint` semantics. -/
theorem strong_bisim_sigref_same_block_strong_fixpoint
    {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing) :
    ∃ (partition : BlockPartition) (blockOf : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag),
      strong_bisim_sigref
          (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
          sys timing = ok (sys, partition) ∧
      ∀ s s', blockOf s = blockOf s' → StrongFixPoint (toLTS TLInst sys) s s' := by
  rcases strong_bisim_sigref_spec TLInst sys timing with ⟨partition, blockOf, hret, hcoh, hstab⟩
  refine ⟨partition, blockOf, ?_, ?_⟩
  · simpa using hret
  · intro s s' hbb
    exact stable_implies_strong_fixpoint (toLTS TLInst sys) blockOf hstab s s' hbb

end MercVerified.Signatures