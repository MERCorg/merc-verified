import Sigref.Proofs.Split_Proofs

open Sigref Sigref.RP

-- Contract pin: fails to compile if `splitExists`'s signature drifts.
example : ∀ {n : ℕ} {G : Type} (rp : RP n) (b : ℕ) (grp : Fin n → G),
    rp.WF → b < rp.nb → ∃ rp' : RP n, IsSplit rp rp' b grp :=
  fun rp b grp => splitExists rp b grp
