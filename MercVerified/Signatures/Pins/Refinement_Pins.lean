import MercVerified.Signatures.Refinement
import MercVerified.Signatures.Proofs.Refinement_Proofs

/-!
# Contract pin for `Refinement_Proofs.lean`

Human-vetted (see CLAUDE.md): make only minimal, targeted changes here.

The `example` below independently re-states the closed signature of
`strong_bisim_sigref_correct`, proved in
`MercVerified/Signatures/Proofs/Refinement_Proofs.lean` against the
`StrongBisimSigrefCorrectSpec` contract stated in
`MercVerified/Signatures/Refinement.lean`. If a regeneration of that proof drifts from the
pinned shape (e.g. gains an unapproved extra hypothesis), the `example` fails to type-check and
`lake build` catches it, without a human having to diff two proofs to notice. See the
lean-conventions skill for the full spec/Proofs/pin pattern.
-/

open Aeneas Aeneas.Std Result
open merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel)
open verified.simple_labelled_transition_system (SimpleLabelledTransitionSystem)

-- Contract pin: fails to compile if `strong_bisim_sigref_correct`'s signature drifts.
example : ∀ {Label : Type} (TLInst : TransitionLabel Label)
    (sys : SimpleLabelledTransitionSystem Label) (timing : Timing),
    StrongBisimSigrefCorrectSpec TLInst sys timing :=
  MercVerified.Signatures.Proofs.strong_bisim_sigref_correct
