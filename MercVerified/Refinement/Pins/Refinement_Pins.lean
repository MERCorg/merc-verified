import MercVerified.Refinement.Refinement
import MercVerified.Refinement.Proofs.Refinement_Proofs

open Aeneas Aeneas.Std Result
open verified.merc_utilities.tagged_index (TagIndex)
open merc_utilities.timing (Timing)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel LTS)
open MercVerified.Refinement (StrongBisimSigrefCorrectSpec)

-- Contract pin: fails to compile if `strong_bisim_sigref_correct`'s signature drifts.
example : ∀ {L Label : Type} (LTSInst : LTS L Label)
    (sys : L) (hwf : MercVerified.Lts.WellFormed LTSInst sys) (timing : Timing),
    StrongBisimSigrefCorrectSpec LTSInst sys hwf timing :=
  MercVerified.Refinement.Proofs.strong_bisim_sigref_correct
