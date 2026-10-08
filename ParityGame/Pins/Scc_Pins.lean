import ParityGame.Scc
import ParityGame.Proofs.Scc_Proofs

open ParityGame

-- Contract pin: fails to compile if `finalSCCExists`'s signature drifts (Section 3.1).
example {V : Type*} [Finite V] (G : Game V) (X : Set V) :
    X.Nonempty → ∃ C, G.IsFinalSCC X C :=
  G.finalSCCExists X
