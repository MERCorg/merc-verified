import Sigref.Proofs.Scc_Proofs

open Cslib Sigref

-- Contract pin: fails to compile if `quotientCrossBisimulation`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] (lts : LTS State Label) (blk : State → ℕ),
    (∀ s t, blk s = blk t → lts.τSTr s t) →
      IsCrossBB lts (quotientTau lts blk) (fun s b => blk s = b) :=
  fun lts blk => quotientCrossBisimulation lts blk

-- Contract pin: fails to compile if `quotientTauAcyclic`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] (lts : LTS State Label) (blk : State → ℕ) (k : ℕ),
    IsTauSccPartition lts blk k →
      ∀ b, ¬ Relation.TransGen (fun b c => (quotientTau lts blk).Tr b HasTau.τ c) b b :=
  fun lts blk k => quotientTauAcyclic lts blk k
