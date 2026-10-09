import Sigref.Proofs.KeyComp_Proofs
import Sigref.Proofs.IterK_Proofs

open Cslib Sigref Sigref.RP

-- Contract pin: fails to compile if `keyCompCorrect`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label) (rp : BD n) (b : ℕ)
    (key0 : Fin n → ℕ),
    TopoSorted lts → BlockInv lts rp b →
      ∀ x y, rp.blk x = b → rp.blk y = b → rp.Dirty x → rp.Dirty y →
        (keysOf lts rp b key0 x = keysOf lts rp b key0 y ↔ E lts rp.setoid x y) :=
  fun lts rp b key0 => keyCompCorrect lts rp b key0

-- Contract pin: fails to compile if `iterKSimulatesBranchingStep`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → ∀ c c' : Ctx n, WLInv c → BranchingInv lts c.rp.config →
      IterK lts inc preds c c' → WLInv c' ∧ BranchingStep lts c.rp.config c'.rp.config :=
  fun lts inc preds => iterKSimulatesBranchingStep lts inc preds

-- Contract pin: fails to compile if `rpSigrefKCorrect`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)) (hn : 0 < n),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → ∀ c : Ctx n,
      Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c → c.wl = [] →
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y :=
  fun lts inc preds hn => rpSigrefKCorrect lts inc preds hn

-- Contract pin: fails to compile if `rpSigrefKTerminates`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)) (hn : 0 < n),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → WellFounded (fun c' c : Ctx n =>
      Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c ∧ IterK lts inc preds c c') :=
  fun lts inc preds hn => rpSigrefKTerminates lts inc preds hn

-- Contract pin: fails to compile if `rpSigrefKTotal`'s signature drifts.
example : ∀ {n : ℕ} {Label : Type} [HasTau Label] (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)) (hn : 0 < n),
    (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → ∃ c : Ctx n,
      Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c ∧ c.wl = [] ∧
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y :=
  fun lts inc preds hn => rpSigrefKTotal lts inc preds hn
