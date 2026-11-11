module

public import MercLib.Algorithms.ParityGame.Incomplete
import all MercLib.Algorithms.ParityGame.Proofs.Incomplete_Aux

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The headline theorems of the safe-set and (safe) attractor computations. -/

namespace MercLib.ParityGame

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The iteration computes the attractor** `Attr_α(a, U)`. -/
public theorem Incomplete.attr_correct (a : IncompleteGame V) [DecidablePred (· ∈ a.vs)]
    [DecidablePred (· ∈ a.I)] [DecidableRel a.edge] : Incomplete.AttrCorrect a :=
  fun α U => Incomplete.attr_eq a α U

/-- **The computed safe set is** `safe_α(a)`. -/
public theorem Incomplete.safe_correct (a : IncompleteGame V) [DecidablePred (· ∈ a.vs)]
    [DecidablePred (· ∈ a.I)] [DecidableRel a.edge] : Incomplete.SafeCorrect a :=
  fun α => Incomplete.safe_eq a α

/-- **The iteration computes the safe attractor** `SAttr_α(a, U)`. -/
public theorem Incomplete.sattr_correct (a : IncompleteGame V) [DecidablePred (· ∈ a.vs)]
    [DecidablePred (· ∈ a.I)] [DecidableRel a.edge] : Incomplete.SAttrCorrect a :=
  fun α U => Incomplete.sattr_eq a α U

end MercLib.ParityGame
