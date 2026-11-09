module

public import MercLib.Algorithms.Graph.Tarjan
import all MercLib.Algorithms.Graph.Proofs.TarjanRunStep_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The headline theorem for the do-notation `tarjan`; the proof is in `TarjanRunStep_Proofs`. -/

namespace MercLib.Tarjan

/-- **`tarjan` is correct.** -/
public theorem tarjanRunCorrect {n : ℕ} (g : Graph n) : TarjanRunCorrect g := tarjanRun_aux g

end MercLib.Tarjan
