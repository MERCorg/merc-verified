import Signatures.BranchingBisimilarity
import Signatures.Signature

-- Import the generated Lean code
import MercVerified.Code.Funs
import MercVerified.Code.FunsExternal_Template
import MercVerified.Code.FunsExternal
import MercVerified.Code.FunsExternalSpecs
import MercVerified.Code.Types
import MercVerified.Code.TypesExternal_Template
import MercVerified.Code.TypesExternal

/-!
# Bridge: an `LTS` trait implementor as a cslib `LTS`

We view any Aeneas-translated implementor `L` of the `merc_lts::lts::LTS` trait (dictionary-passed
as `LTSInst : verified.merc_lts.lts.LTS L Label`) as an `LTS` (in the sense of
`Cslib.Foundations.Semantics.LTS.Basic`). The states are the `TagIndex Usize StateTag` indices
addressed by the implementation, and the labels are the `TagIndex Usize LabelTag` *label indices*
stored in each `Transition`. There is a transition `s →[μ] s'` iff
`LTSInst.outgoing_transitions sys s` succeeds and the resulting vector contains the transition
record `⟨μ, s'⟩`.
-/

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (Transition StateTag LabelTag TransitionLabel LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_lts.labelled_transition_system (LabelledTransitionSystem)

namespace verified.merc_lts.lts.LTS

/-- The transition relation induced by an `LTS` implementor's concrete representation:
    `s →[μ] s'` iff `LTSInst.outgoing_transitions sys s` succeeds with a vector that contains the
    transition `{ label := μ, to := s' }`. -/
def tr {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L)
    (s : TagIndex Std.Usize StateTag)
    (μ : TagIndex Std.Usize LabelTag)
    (s' : TagIndex Std.Usize StateTag) : Prop :=
  ∃ ts : alloc.vec.Vec Transition,
    LTSInst.outgoing_transitions sys s = ok ts
      ∧ ({ label := μ, «to» := s' } : Transition) ∈ ts.val

/-- The cslib `LTS` view of an `LTS` trait implementor. States are state-tagged usize indices;
    labels are label-tagged usize indices. -/
def toLTS {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L) :
    Cslib.LTS (TagIndex Std.Usize StateTag) (TagIndex Std.Usize LabelTag) where
  Tr := tr LTSInst sys

/-- The one semantic requirement on an `LTS` implementor that the strong-bisimulation refinement
    algorithm's correctness needs beyond the trait's type signature: a non-empty state space
    (needed for `BlockPartition::new`'s `assert!(num_of_elements > 0)`). Not derivable from the
    trait interface alone - it is a property of a specific implementor's invariants (see
    `lts_wellFormed`, `MercVerified/Signatures/Proofs/LabelledTransitionSystem_Proofs.lean`,
    for the proof that `LabelledTransitionSystem` satisfies it). -/
def NonEmpty {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  ∃ n : Std.Usize, LTSInst.num_of_states sys = ok n ∧ 0 < n.val

/-- Well-formedness of an `LTS` implementor's concrete representation: a non-empty state space
    of `n` states in which `outgoing_transitions` succeeds on every state `< n` and only yields
    transitions whose target is again `< n`. The trait's type signature does not imply any of
    this (`outgoing_transitions` may `fail`, and its targets are arbitrary indices), so
    algorithms over `LTS` implementors are only trusted under this hypothesis. -/
def WellFormed {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  LTSInst.NonEmpty sys ∧
  ∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
    ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val →
      ∃ ts : alloc.vec.Vec Transition,
        LTSInst.outgoing_transitions sys s = ok ts ∧ ∀ t ∈ ts.val, t.to.index.val < n.val

end verified.merc_lts.lts.LTS

/-- The Rust method `is_hidden_label` declares the hidden (τ) label to be
    the tagged index `TagIndex::new(0)`. -/
def tauLabelIndex : TagIndex Std.Usize LabelTag := { index := 0#usize, marker := () }

noncomputable instance : Cslib.HasTau (TagIndex Std.Usize LabelTag) where
  τ := tauLabelIndex

/-- `BlockPartition::new` succeeds for a positive number of elements (the
    translated `assert!(num_of_elements > 0)` holds exactly when
    `0 < num_of_elements`); stated here (not in `Code/FunsExternal.lean`)
    because the def it characterizes is generated code. -/
axiom BlockPartition.new_spec
  (num_of_elements : Std.Usize) (hpos : 0 < num_of_elements.val) :
  ∃ bp, verified.merc_reduction.block_partition.BlockPartition.new num_of_elements = ok bp

/-- Raw structural validity of a `LabelledTransitionSystem`'s internal representation: exactly
    what Rust's `assert_valid` (`labelled_transition_system.rs:365-447`, run by every safe
    constructor - `from_raw_parts`, `new`, `relabel`, ... - so no reachable instance skips it)
    checks, restricted to the part `LTS.WellFormed` needs: `states` has one entry per state plus
    a sentinel (`statesAt numStates = numTransitions`, `statesAt` monotone), every transition's
    target is `< numStates`, and `initial_state.value() < numStates`.

    Phrased over the boundary `ByteCompressedVec` primitive's `index`/`len` (an existential
    `statesAt : Nat → Nat` stands in for the array read, since `ByteCompressedVec` is a fully
    opaque external type with no `.val` model of its own - see
    `MercVerified/Code/TypesExternal_Template.lean`). `lts_wellFormed`
    (`MercVerified/Signatures/Proofs/LabelledTransitionSystem_Proofs.lean`) derives
    `LTS.WellFormed` from this by real proof rather than by axiom; `lts_valid` just below
    establishes this predicate itself unconditionally, from the two boundary axioms
    `LabelledTransitionSystem.states_offsets_valid`/`.transitions_bounded`. -/
def LabelledTransitionSystemValid {Label : Type}
    (sys : LabelledTransitionSystem Label) : Prop :=
  ∃ (numStates numTransitions : Nat) (statesAt : Nat → Nat),
    (∃ statesLen : Std.Usize,
      merc_collections.compressed_vec.ByteCompressedVec.len
        verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry sys.states = ok statesLen ∧
      statesLen.val = numStates + 1) ∧
    (∀ i : Std.Usize, i.val ≤ numStates →
      ∃ v : Std.Usize, merc_collections.compressed_vec.ByteCompressedVec.index
        verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry sys.states i = ok v ∧
        v.val = statesAt i.val) ∧
    (∀ i, i < numStates → statesAt i ≤ statesAt (i + 1)) ∧
    statesAt numStates = numTransitions ∧
    sys.initial_state.index.val < numStates ∧
    (∀ k : Std.Usize, k.val < numTransitions →
      ∃ vl : TagIndex Std.Usize LabelTag, merc_collections.compressed_vec.ByteCompressedVec.index
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_labels k = ok vl) ∧
    (∀ k : Std.Usize, k.val < numTransitions →
      ∃ vt : TagIndex Std.Usize StateTag, merc_collections.compressed_vec.ByteCompressedVec.index
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          StateTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_to k = ok vt ∧
        vt.index.val < numStates)

/-!
# `ByteCompressedVec` boundary: `LabelledTransitionSystem`'s internal invariant

`ByteCompressedVec` is a fully opaque external type (`MercVerified/Code/TypesExternal_Template.lean`)
with no model of its own connecting `index`/`len` - Charon cannot translate its byte-packing
internals. The two axioms below assert, at that boundary, exactly the structural invariant Rust's
`LabelledTransitionSystem::assert_valid` (`labelled_transition_system.rs:365-447`) checks and every
safe constructor (`from_raw_parts`, `new`, `relabel`, ...) is trusted to establish - Charon does not
translate the constructors themselves, only the `LTS` trait methods these axioms are designed to
drive (see `lts_valid`, `MercVerified/Signatures/Proofs/LabelledTransitionSystem_Proofs.lean`, which
combines them into `LabelledTransitionSystemValid` above, unconditionally, for any `sys`).

They live here (not `MercVerified/Code/FunsExternal.lean`, the usual hand-written-stub home for
boundary axioms) because they must name the `CompressedEntry` dictionary values
(`Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry`, etc.) that `outgoing_transitions`/
`num_of_states` actually call, and those are generated `def`s in `MercVerified/Code/Funs.lean` -
which imports `FunsExternal.lean`, so declaring them there would be a cyclic import. `Basic.lean`
is the other axiom-policy-approved location (see `scripts/check_axioms.py`) and already imports
`Funs.lean`.
-/

/-- The `states` offset table: one entry per state plus a sentinel equal to the transition count
    (`statesAt (statesLen - 1) = transLen`), non-decreasing, and the initial state in bounds. -/
axiom merc_lts.labelled_transition_system.LabelledTransitionSystem.states_offsets_valid
    {Label : Type} (sys : LabelledTransitionSystem Label) :
    ∃ (statesLen transLen : Std.Usize) (statesAt : Nat → Nat),
      merc_collections.compressed_vec.ByteCompressedVec.len
        verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry sys.states = ok statesLen ∧
      merc_collections.compressed_vec.ByteCompressedVec.len
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_labels = ok transLen ∧
      (∀ i : Std.Usize, i.val + 1 ≤ statesLen.val →
        ∃ v : Std.Usize, merc_collections.compressed_vec.ByteCompressedVec.index
          verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry sys.states i = ok v ∧
          v.val = statesAt i.val) ∧
      (∀ i, i + 1 < statesLen.val → statesAt i ≤ statesAt (i + 1)) ∧
      statesAt (statesLen.val - 1) = transLen.val ∧
      sys.initial_state.index.val + 1 < statesLen.val

/-- `transition_labels`/`transition_to` have equal length, and every transition's target state
    index is in bounds (label-index bounds are not asserted - `LTS.WellFormed` does not need
    them). -/
axiom merc_lts.labelled_transition_system.LabelledTransitionSystem.transitions_bounded
    {Label : Type} (sys : LabelledTransitionSystem Label) :
    ∃ (statesLen transLen : Std.Usize),
      merc_collections.compressed_vec.ByteCompressedVec.len
        verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry sys.states = ok statesLen ∧
      merc_collections.compressed_vec.ByteCompressedVec.len
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_labels = ok transLen ∧
      merc_collections.compressed_vec.ByteCompressedVec.len
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          StateTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_to = ok transLen ∧
      (∀ k : Std.Usize, k.val < transLen.val →
        ∃ vl : TagIndex Std.Usize LabelTag,
          merc_collections.compressed_vec.ByteCompressedVec.index
            (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
              LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry
              core.marker.CopyUsize)
            sys.transition_labels k = ok vl) ∧
      (∀ k : Std.Usize, k.val < transLen.val →
        ∃ vt : TagIndex Std.Usize StateTag,
          merc_collections.compressed_vec.ByteCompressedVec.index
            (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
              StateTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry
              core.marker.CopyUsize)
            sys.transition_to k = ok vt ∧ vt.index.val + 1 < statesLen.val)
