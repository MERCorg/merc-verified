import Sigref.Proofs.Iteration_Proofs

open Cslib Sigref Sigref.RP

-- Contract pin: fails to compile if `closureComputesInertClosure`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (preds : Fin n → List (Fin n)) (rp : RP n) (b : ℕ),
    (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) → rp.WF → b < rp.nb →
    ∀ x, rp.blk x = b → ((closure b preds rp).Dirty x ↔
      x ∈ inertClosure lts rp.setoid {d | rp.blk d = b ∧ rp.Dirty d}) :=
  fun lts preds rp b => closureComputesInertClosure lts preds rp b

-- Contract pin: fails to compile if `iterSimulatesBranchingStep`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TauLoopFree lts → ∀ c c' : Ctx n, WLInv c → Iter lts inc preds c c' →
      WLInv c' ∧ BranchingStep lts c.rp.config c'.rp.config :=
  fun lts inc preds => iterSimulatesBranchingStep lts inc preds

-- Contract pin: fails to compile if `rpSigrefCorrect`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)) (hn : 0 < n),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TauLoopFree lts → ∀ c : Ctx n,
      Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c → c.wl = [] →
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y :=
  fun lts inc preds hn => rpSigrefCorrect lts inc preds hn

-- Contract pin: fails to compile if `rpSigrefTerminates`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)) (hn : 0 < n),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TauLoopFree lts → WellFounded (fun c' c : Ctx n =>
      Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c ∧ Iter lts inc preds c c') :=
  fun lts inc preds hn => rpSigrefTerminates lts inc preds hn

-- Contract pin: fails to compile if `rpSigrefProgress`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)),
    (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) → TauLoopFree lts →
    ∀ c : Ctx n, WLInv c → c.wl ≠ [] → ∃ c', Iter lts inc preds c c' :=
  fun lts inc preds => rpSigrefProgress lts inc preds

-- Contract pin: fails to compile if `rpSigrefTotal`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)) (hn : 0 < n),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TauLoopFree lts → ∃ c : Ctx n,
      Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c ∧ c.wl = [] ∧
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y :=
  fun lts inc preds hn => rpSigrefTotal lts inc preds hn
