module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
import Signatures.BranchingBisimilarity

@[expose] public section Signature

-- The Strong signature captures the behaviour of strong bisimulation --
def StrongSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block): Set (Label × Block)
  := { (μ, α) | ∃ s', lts.Tr s μ s' ∧ partition s' = α }

/-
The branching signatures captures the behaviour of branching bisimulation --

Note that the signature only includes non-inert transitions, i.e., those that
are either visible (μ ≠ τ) or lead to a different block (α ≠ β). This is
crucial for the partition refinement result, as it ensures that the signature
of a state.
-/
def BranchingSignature [Cslib.HasTau Label] (lts : Cslib.LTS State Label) (s : State)
    (partition : State → Block) : Set (Block × Label × Block) :=
  { (β, μ, α) | ∃ s' s'', lts.τSTr s s' ∧ lts.Tr s' μ s'' ∧ partition s' = β ∧ partition s'' = α
                ∧ (μ ≠ Cslib.HasTau.τ ∨ α ≠ β) }

-- A partition is stable w.r.t. a signature if same-block states always have the same signature
def IsStable (sig : State → Sig) (partition : State → Block) : Prop :=
  ∀ s s', partition s = partition s' → sig s = sig s'

/-
States s, s' are related iff some stable partition keeps them in the same block. The `Block`
universe matches State's so concrete witnesses like quotients fit.
-/
def FixPoint.{u, w} {State : Type u} {Sig : Type u → Type w}
    (sigBuilder : {Block : Type u} → (State → Block) → State → Sig Block) :
    State → State → Prop :=
  fun s s' => ∃ (Block : Type u) (partition : State → Block),
    IsStable (sigBuilder partition) partition ∧ partition s = partition s'

-- SplitSignature: the per-label variant of StrongSignature.
-- For each label μ, gives the set of target blocks reachable from s via a μ-transition.
-- Equivalent to StrongSignature but indexed by label rather than collecting (label, block) pairs.
def SplitSignature (lts : Cslib.LTS State Label) (s : State) (partition : State → Block) :
    Label → Set Block :=
  fun μ => { α | ∃ s', lts.Tr s μ s' ∧ partition s' = α }

-- Strong-bisim FixPoint: FixPoint instantiated with the StrongSignature builder.
def StrongFixPoint.{u, v} {State : Type u} {Label : Type v} (lts : Cslib.LTS State Label) :
    State → State → Prop :=
  FixPoint (fun {_} partition s => StrongSignature lts s partition)

-- SplitFixPoint: FixPoint instantiated with the per-label SplitSignature builder.
def SplitFixPoint.{u, v} {State : Type u} {Label : Type v} (lts : Cslib.LTS State Label) :
    State → State → Prop :=
  FixPoint (fun {_} partition s => SplitSignature lts s partition)

-- Branching-bisim FixPoint: FixPoint instantiated with the (inert-τ-excluded) BranchingSignature.
def BranchingFixPoint.{u, v} {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    (lts : Cslib.LTS State Label) : State → State → Prop :=
  FixPoint (fun {_} partition s => BranchingSignature lts s partition)

end Signature
