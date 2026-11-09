module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
import MercLib.Theory.LTS.BranchingBisimilarity

@[expose] public section Signature

namespace MercLib.Signatures

/-- The strong signature of `s`: the pairs `(μ, α)` such that `s` has a `μ`-transition into block `α`.
    It captures the behaviour of strong bisimulation. -/
def StrongSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block): Set (Label × Block)
  := { (μ, α) | ∃ s', lts.Tr s μ s' ∧ partition s' = α }

/-- The branching signature of `s`: the triples `(β, μ, α)` such that `s` reaches some `s'` in block
    `β` by τ-steps, and `s'` has a `μ`-transition into block `α` that is not inert, i.e. visible
    (`μ ≠ τ`) or leaving the block (`α ≠ β`). It captures the behaviour of branching bisimulation.
    Excluding inert transitions is what makes a partition that is stable for this signature a
    branching bisimulation (`IsStable.branchingBisimilarity`). -/
def BranchingSignature [Cslib.HasTau Label] (lts : Cslib.LTS State Label) (s : State)
    (partition : State → Block) : Set (Block × Label × Block) :=
  { (β, μ, α) | ∃ s' s'', lts.τSTr s s' ∧ lts.Tr s' μ s'' ∧ partition s' = β ∧ partition s'' = α
                ∧ (μ ≠ Cslib.HasTau.τ ∨ α ≠ β) }

/-- A partition is stable with respect to a signature if states in the same block always have the
    same signature. -/
def IsStable (sig : State → Sig) (partition : State → Block) : Prop :=
  ∀ s s', partition s = partition s' → sig s = sig s'

/-- `s` and `s'` are related iff some stable partition keeps them in the same block. The `Block`
    universe matches `State`'s, so concrete witnesses such as quotients fit. -/
def FixPoint.{u, w} {State : Type u} {Sig : Type u → Type w}
    (sigBuilder : {Block : Type u} → (State → Block) → State → Sig Block) :
    State → State → Prop :=
  fun s s' => ∃ (Block : Type u) (partition : State → Block),
    IsStable (sigBuilder partition) partition ∧ partition s = partition s'

/-- The per-label variant of `StrongSignature`: for each label `μ`, the set of blocks that `s` reaches
    by a `μ`-transition. Equivalent to `StrongSignature`, but indexed by label rather than collecting
    `(label, block)` pairs. -/
def SplitSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block) :
    Label → Set Block :=
  fun μ => { α | ∃ s', lts.Tr s μ s' ∧ partition s' = α }

/-- `FixPoint` for the strong signature. -/
def StrongFixPoint.{u, v} {State : Type u} {Label : Type v} (lts : Cslib.LTS State Label) :
    State → State → Prop :=
  FixPoint (fun {_} partition s => StrongSignature lts s partition)

/-- `FixPoint` for the per-label signature. -/
def SplitFixPoint.{u, v} {State : Type u} {Label : Type v} (lts : Cslib.LTS State Label) :
    State → State → Prop :=
  FixPoint (fun {_} partition s => SplitSignature lts s partition)

/-- `FixPoint` for the branching signature. -/
def BranchingFixPoint.{u, v} {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    (lts : Cslib.LTS State Label) : State → State → Prop :=
  FixPoint (fun {_} partition s => BranchingSignature lts s partition)

end MercLib.Signatures

end Signature
