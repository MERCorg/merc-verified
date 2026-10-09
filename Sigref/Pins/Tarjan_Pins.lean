import Sigref.Proofs.TarjanBridge_Proofs

open Sigref.Tarjan

-- Contract pin: fails to compile if `tarjanCorrect`'s signature drifts.
example : ∀ {n : ℕ} (g : Graph n) (c : Ctx n),
    Relation.ReflTransGen (Step g) (init g) c →
      (step g c = Out.stop → IsSccPartition g c.blk c.eq) ∧ step g c ≠ Out.fail :=
  fun g => tarjanCorrect g

-- Contract pin: fails to compile if `tarjanTerminates`'s signature drifts.
example : ∀ {n : ℕ} (g : Graph n) (c : Ctx n),
    Relation.ReflTransGen (Step g) (init g) c → ∀ c' : Ctx n, Step g c c' →
      measure g c' < measure g c :=
  fun g => tarjanTerminates g

-- Contract pin: fails to compile if `isTauSccPartition_of_scc`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [Cslib.HasTau Label] (lts : Cslib.LTS (Fin n) Label) (g : Graph n),
    (∀ u v, Edge g u v ↔ lts.Tr u Cslib.HasTau.τ v) → ∀ {blk : Fin n → ℕ} {k : ℕ},
      IsSccPartition g blk k → Sigref.IsTauSccPartition lts blk k :=
  fun lts g hE => isTauSccPartition_of_scc lts g hE
