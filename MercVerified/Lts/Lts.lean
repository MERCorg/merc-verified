
import MercVerified.Basic

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

namespace MercVerified.Lts

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
    `lts_wellFormed`, `MercVerified/Lts/Proofs/LabelledTransitionSystem_Proofs.lean`,
    for the proof that `LabelledTransitionSystem` satisfies it). -/
def NonEmpty {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  ∃ n : Std.Usize, LTSInst.num_of_states sys = ok n ∧ 0 < n.val

/-- Well-formedness of an `LTS` implementor's concrete representation: a non-empty state space
    of `n` states in which `outgoing_transitions` succeeds on every state `< n` and only yields
    transitions whose target is again `< n`. The trait's type signature does not imply
    any of this (`outgoing_transitions` may `fail`, its targets are arbitrary indices), so
    algorithms over `LTS` implementors are only trusted under this hypothesis.

    Finally `iter_states` enumerates each of the `n` states exactly once, and
    `num_of_transitions` is at least the total number of transitions the states have
    (`IncomingTransitions::new` allocates its flat arrays with that size), which fits in a `usize`
    with room to spare. -/
def WellFormed {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  NonEmpty LTSInst sys ∧
  (∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
    ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val →
      ∃ ts : alloc.vec.Vec Transition,
        LTSInst.outgoing_transitions sys s = ok ts ∧ ∀ t ∈ ts.val, t.to.index.val < n.val) ∧
  (∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
    ∃ (sv : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (m : Std.Usize),
      LTSInst.iter_states sys = ok sv ∧ sv.val.Nodup ∧
      (∀ s : TagIndex Std.Usize StateTag, s ∈ sv.val ↔ s.index.val < n.val) ∧
      LTSInst.num_of_transitions sys = ok m ∧ m.val < Std.Usize.max ∧
      ∀ ts : TagIndex Std.Usize StateTag → alloc.vec.Vec Transition,
        (∀ s ∈ sv.val, LTSInst.outgoing_transitions sys s = ok (ts s)) →
        (sv.val.map (fun s => (ts s).val.length)).sum ≤ m.val)

/-- The Rust method `is_hidden_label` declares the hidden (τ) label to be
    the tagged index `TagIndex::new(0)`. -/
def tauLabelIndex : TagIndex Std.Usize LabelTag := { index := 0#usize, marker := () }

noncomputable instance : Cslib.HasTau (TagIndex Std.Usize LabelTag) where
  τ := tauLabelIndex

end MercVerified.Lts
