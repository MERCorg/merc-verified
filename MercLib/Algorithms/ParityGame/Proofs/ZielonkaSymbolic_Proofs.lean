module

public import MercLib.Algorithms.ParityGame.ZielonkaSymbolic
import all MercLib.Algorithms.ParityGame.Proofs.ZielonkaSymbolic_Aux
import MercLib.Algorithms.ParityGame.Proofs.Zielonka_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The headline theorems of the symbolic Zielonka algorithm. The fixed-point iteration computes the
attractor, and the symbolic recursion returns the regions of `Game.zielonka`, whose correctness is
`Game.zielonka_correct`. -/

namespace MercLib.ParityGame

/-- **The fixed-point iteration computes the attractor.** -/
public theorem Game.attrSym_correct {V : Type*} [Fintype V] [DecidableEq V] (G : Game V)
    [DecidableRel G.edge] : G.AttrSymCorrect :=
  fun X α U => attrSym_eq X α U

/-- **Zielonka's algorithm on vertex sets is correct.** -/
public theorem Game.zielonkaSym_correct {V : Type*} [Fintype V] [DecidableEq V] (G : Game V)
    [DecidableRel G.edge] : G.ZielonkaSymCorrect := by
  have heq : ∀ p, (G.zielonkaSym p : Set V) = G.zielonka.win p := fun p => by
    rw [Game.zielonkaSym, zielonkaSymAux_eq _ _ le_rfl, Finset.coe_univ]; rfl
  obtain ⟨hcov, hdisj, hwin⟩ := G.zielonka_correct
  refine ⟨?_, ?_, fun i => ⟨G.zielonka.strat i, fun v hv => hwin i v ?_⟩⟩
  · rw [heq, heq]; exact hcov
  · rw [← Finset.disjoint_coe, heq, heq]; exact hdisj
  · rw [← heq]; exact hv

end MercLib.ParityGame
