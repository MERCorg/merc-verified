module

public import MercLib.Algorithms.Rewriting.SetAutomaton
import all MercLib.Algorithms.Rewriting.Proofs.SetAutomatonRun_Aux

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The headline theorems of `construct` and `findMatches`; the proofs are in `SetAutomatonRun_Aux`. -/

namespace MercLib.SetAutomaton

/-- **`construct` computes the reachable part of the automaton.** -/
public theorem constructCorrect {F : Type} [DecidableEq F] [Fintype F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position) : ConstructCorrect ar Ls L :=
  constructCorrect_aux

/-- **`findMatches` is correct and inspects every position exactly once.** -/
public theorem findMatchesCorrect {F : Type} [DecidableEq F] [Fintype F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position)
    (pick : Finset (Config F) → Finset (Config F)) : FindMatchesCorrect ar Ls L pick :=
  findMatchesCorrect_aux

end MercLib.SetAutomaton
