import Sigref.Proofs.Branching_Proofs

open Cslib Sigref

-- Contract pin: fails to compile if `branchingSigrefCorrect`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] (lts : LTS State Label),
    BranchingInv lts (initConfig State) ∧
    (TauLoopFree lts → ∀ c c' : Config State,
      BranchingInv lts c → BranchingStep lts c c' → BranchingInv lts c') ∧
    (∀ c : Config State, BranchingInv lts c → (∀ s, s ∉ c.X) →
      ∀ s t, c.π.r s t ↔ BranchingBisimilarity lts s t) :=
  fun lts => branchingSigrefCorrect lts

-- Contract pin: fails to compile if `branchingSigrefTerminates`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] [Finite State] (lts : LTS State Label),
    WellFounded (fun c' c : Config State => BranchingStep lts c c') :=
  fun lts => branchingSigrefTerminates lts

-- Contract pin: fails to compile if `branchingSigrefProgress`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] (lts : LTS State Label)
    (c : Config State) (s : State), s ∈ c.X → ∃ c', BranchingStep lts c c' :=
  fun lts => branchingSigrefProgress lts

-- Contract pin: fails to compile if `branchingSigrefTotal`'s signature drifts.
example : ∀ {State Label : Type} [HasTau Label] [Finite State] (lts : LTS State Label),
    TauLoopFree lts →
      ∃ c : Config State, Relation.ReflTransGen (BranchingStep lts) (initConfig State) c ∧
        (∀ s, s ∉ c.X) ∧ ∀ s t, c.π.r s t ↔ BranchingBisimilarity lts s t :=
  fun lts => branchingSigrefTotal lts
