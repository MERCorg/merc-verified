import Signatures.BranchingBisimilarity
import Signatures.Signature

-- Import the generated Lean code
import MercVerified.Code.Funs
import MercVerified.Code.FunsExternal_Template
import MercVerified.Code.FunsExternal
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
open merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (Transition StateTag LabelTag TransitionLabel LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)

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

@[simp] theorem toLTS_Tr {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L)
    (s : TagIndex Std.Usize StateTag)
    (μ : TagIndex Std.Usize LabelTag)
    (s' : TagIndex Std.Usize StateTag) :
    (toLTS LTSInst sys).Tr s μ s' ↔ tr LTSInst sys s μ s' := Iff.rfl

/-- The one semantic requirement on an `LTS` implementor that the strong-bisimulation refinement
    algorithm's correctness needs beyond the trait's type signature: a non-empty state space
    (needed for `BlockPartition::new`'s `assert!(num_of_elements > 0)`). Not derivable from the
    trait interface alone - it is a property of a specific implementor's invariants (see
    `slts_num_of_states_pos` below for the witness that `SimpleLabelledTransitionSystem`
    satisfies it). -/
def NonEmpty {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  ∃ n : Std.Usize, LTSInst.num_of_states sys = ok n ∧ 0 < n.val

end verified.merc_lts.lts.LTS

/-- The Rust method `is_hidden_label` declares the hidden (τ) label to be
    the tagged index `TagIndex::new(0)`. Since `TagIndex` is modelled
    axiomatically by Aeneas, we postulate the corresponding element here so
    that the cslib `HasTau` class can be instantiated, making the LTS usable
    with weak/branching bisimilarity. -/
axiom tauLabelIndex : TagIndex Std.Usize LabelTag

noncomputable instance : Cslib.HasTau (TagIndex Std.Usize LabelTag) where
  τ := tauLabelIndex

/-- `BlockPartition::new` succeeds for a positive number of elements (the
    translated `assert!(num_of_elements > 0)` holds exactly when
    `0 < num_of_elements`); stated here (not in `Code/FunsExternal.lean`)
    because the def it characterizes is generated code. -/
axiom BlockPartition.new_spec
  (num_of_elements : Std.Usize) (hpos : 0 < num_of_elements.val) :
  ∃ bp, verified.merc_reduction.block_partition.BlockPartition.new num_of_elements = ok bp

/-- The translated `SimpleLabelledTransitionSystem` is never empty: Rust's type
    invariant keeps the `initial_state` in the `transitions` map (the
    constructor guarantees it), so `num_of_states` (= `transitions.len()`) is
    always at least `1`. Without this, the translated `BlockPartition::new`
    `assert!(num_of_elements > 0)` would fail on the empty system, so the
    `strong_bisim_sigref` contract would hold for no system at all.

    This is the witness that `SimpleLabelledTransitionSystem`'s `LTS` instance satisfies the
    `LTS.NonEmpty` requirement, making `strong_bisim_sigref_correct` (in
    `MercVerified/Signatures/Proofs/Refinement_Proofs.lean`) a corollary of the generic
    `strong_bisim_sigref_correct_general`. -/
axiom slts_num_of_states_pos {Label : Type}
    (TLInst : verified.merc_lts.lts.TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) :
    (SimpleLabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).NonEmpty sys

/-- Contract of `strong_run_worklist_loop` (a real translated `def` in
    `MercVerified/Code/Funs.lean` - not yet proven from its body, so still
    trusted as an axiom here). On the strong-bisimulation specialization (the
    `signature`/`renumber` closures of `strong_bisim_sigref`, now fully
    specialised away into `WorklistContextStrong`), and any initial
    `WorklistContextStrong`, it succeeds and returns a context whose partition
    is *stable* for the strong signature (states in the same block have
    identical `StrongSignature`), its block map agrees with the concrete
    partition (coherence), covers every state index of `sys` (every
    `s < num_of_states sys` appears among `ctx.partition.elements`), and is
    complete w.r.t. `StrongFixPoint` (strongly bisimilar states are placed in
    the same block).

    Stated generically over any `LTS` implementor `L`/`LTSInst`, not just
    `SimpleLabelledTransitionSystem`: the Rust `strong_run_worklist_loop` is itself
    generic over the `LTS` trait and never downcasts to a concrete type (see
    its generic signature in `MercVerified/Code/Funs.lean`), so trusting its
    correctness for any implementor - not just the one Rust type currently in
    the codebase - faithfully reflects what is actually being trusted at this
    boundary. -/
axiom run_worklist_loop_spec
    {L Label : Type} (LTSInst : verified.merc_lts.lts.LTS L Label)
    (sys : L)
    (incoming : merc_lts.incoming_transitions.IncomingTransitions)
    (ctx0 : verified.merc_reduction.signature_refinement.WorklistContextStrong) :
    ∃ (ctx : verified.merc_reduction.signature_refinement.WorklistContextStrong)
      (blockOf : TagIndex Std.Usize verified.merc_lts.lts.StateTag →
        TagIndex Std.Usize verified.merc_collections.indexed_partition.BlockTag),
      verified.merc_reduction.signature_refinement.strong_run_worklist_loop false
        LTSInst
        sys incoming ctx0 = ok ctx ∧
      (∀ s b, (s, b) ∈ List.zip ctx.partition.elements.val ctx.partition.element_to_block.val → blockOf s = b) ∧
      (∀ n, LTSInst.num_of_states sys = ok n →
        ∀ s : TagIndex Std.Usize verified.merc_lts.lts.StateTag, s.val < n.val →
          s ∈ ctx.partition.elements.val) ∧
      IsStable (fun s => StrongSignature
        (verified.merc_lts.lts.LTS.toLTS LTSInst sys) s blockOf) blockOf ∧
      ∀ s s', StrongFixPoint
        (verified.merc_lts.lts.LTS.toLTS LTSInst sys) s s' → blockOf s = blockOf s'

/-!
# `HashMap` boundary semantics

The `std::collections::hash::map::HashMap` type and its operations are opaque
externals (axioms in `MercVerified/Code/FunsExternal_Template.lean`). To prove
value-level specs of the strong interning pipeline (`strong_intern_signature`
uses `get_key_value`/`insert` on the signature→block-index map) the two
*observable* semantics below are added at the boundary, exactly mirroring how
`std::collections::hash::map::HashMap` is used there: keys looked up through the
blanket `Borrow` (`verified.core.borrow.Borrow.Blanket`) and the passed-through
`Eq`/`Hash` instances.
-/

/-- `HashMap::insert` never fails, and immediately afterwards a lookup of the
    freshly inserted key (through the same equality/hash instances) returns
    exactly that `(key, value)` pair - the observable semantics of
    `std::collections::hash::map::HashMap::<K, V>::insert` that the strong
    interning (`strong_intern_signature`) relies on. The previous value
    associated with `k` is returned but left under-specified. -/
axiom std.collections.hash.map.HashMap.insert_spec
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) :
  ∃ old : Option V, ∃ m' : std.collections.hash.map.HashMap K V S A,
    std.collections.hash.map.HashMap.insert corecmpEqInst corehashHashInst
      corehashBuildHasherInst m k v = ok (old, m') ∧
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m' k = ok (some (k, v))

/-- Inserting `k ↦ v` leaves all lookups of keys the map's own equality test
    reports as *different* from `k` untouched - the `HashMap::insert` behaviour
    that lets interning accumulate distinct signatures independently. -/
axiom std.collections.hash.map.HashMap.insert_get_key_value_other
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : verified.core.hash.BuildHasher S Clause2_Hasher)
  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) (q : K)
  (hneq : corecmpEqInst.partialEqInst.eq k q = ok false) :
  ∃ old : Option V, ∃ m' : std.collections.hash.map.HashMap K V S A,
    std.collections.hash.map.HashMap.insert corecmpEqInst corehashHashInst
      corehashBuildHasherInst m k v = ok (old, m') ∧
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m' q =
    std.collections.hash.map.HashMap.get_key_value corecmpEqInst corehashHashInst
      corehashBuildHasherInst (verified.core.borrow.Borrow.Blanket K)
      corehashHashInst corecmpEqInst m q
