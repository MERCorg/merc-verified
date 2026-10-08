import ParityGame.Defs
import ParityGame.Proofs.Defs_Proofs

open ParityGame Cslib

-- Contract pin: fails to compile if `playHasUniqueWinner`'s signature drifts (every play of a
-- finite parity game has exactly one winner).
example {V : Type*} [Finite V] (G : Game V) :
    ∀ p : ωSequence V, ∃! i, G.PlayWonBy i p :=
  Game.playHasUniqueWinner G
