import MercVerified.Basic

/-!
# Contract of `IncomingTransitions::new`

`MercVerified/Code/FunsExternalSpecs.lean` currently axiomatizes
`verified.merc_lts.incoming_transitions.IncomingTransitions.new_spec` with *existence only*:
`∃ incoming, IncomingTransitions.new ltsLTSInst lts = ok incoming`. Nothing in the
development says what `incoming` contains, so the `transition_labels` /
`transition_from` / `state2incoming` fields are unconstrained.

That is enough for `strong_run_worklist_loop`'s *termination* (it never inspects
`incoming`), but not for its *partial correctness*: the soundness half of the worklist
invariant - "a block that is not on the worklist is settled" - holds precisely because
`mark_dirty_new_blocks` re-marks exactly those states that have an edge into a freshly
created block, and that is read off `incoming`. The completeness half ("refinement never
separates bisimilar states") needs the same fact. So this is the gating lemma for
`strong_run_worklist_loop_partial_correct`
(`MercVerified/Signatures/Proofs/WorklistLoop_Proofs.lean`).

This file states the contract; `MercVerified/Signatures/Proofs/IncomingTransitions_Proofs.lean`
discharges it from the translated definition (no new axiom).
-/

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag LTS)
open verified.merc_lts.lts.LTS (toLTS tr)

namespace MercVerified.Signatures

/-- `incoming` indexes the incoming transitions of every in-range state exactly: for each
    state `s` with `s.index.val < n`, `IncomingTransitions::incoming_transitions incoming s`
    succeeds and its result contains exactly the `FromTransition`s `{ label := μ, from := s' }`
    for which the LTS has a transition `s' →[μ] s` - i.e. exactly the transitions whose
    *target* is `s`.

    Stated as a membership (`∈`) characterisation rather than an ordered one. The translated
    `incoming_transitions` sorts each state's range by label (`sort_incoming`, an insertion
    sort), but the only consumers - `mark_dirty_new_blocks` / `mark_dirty_states` in
    `signature_refinement.rs` - ask whether *some* predecessor of `s` lies in a given block, so
    the order carries no information they rely on. -/
def IncomingTransitionsCorrect {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions) : Prop :=
  ∀ n : Std.Usize, LTSInst.num_of_states sys = ok n →
    ∀ s : TagIndex Std.Usize StateTag, s.index.val < n.val →
      ∃ res : alloc.vec.Vec verified.merc_lts.incoming_transitions.FromTransition,
        verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions
            incoming s = ok res ∧
        ∀ i : verified.merc_lts.incoming_transitions.FromTransition, i ∈ res.val ↔
          ∃ μ : TagIndex Std.Usize LabelTag, ∃ s' : TagIndex Std.Usize StateTag,
            tr LTSInst sys s' μ s ∧ (i.label, i.«from») = (μ, s')

end MercVerified.Signatures
