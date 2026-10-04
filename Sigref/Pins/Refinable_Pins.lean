import Sigref.Proofs.Refinable_Proofs
import Sigref.Proofs.Worklist_Proofs

open Sigref Sigref.RP

-- Contract pin: fails to compile if `markDirtyCorrect`'s signature drifts.
example : ∀ {n : ℕ} (rp : RP n) (s : Fin n), rp.WF →
    (rp.mark s).WF ∧ (rp.mark s).blk = rp.blk ∧
      ∀ x, (rp.mark s).Dirty x ↔ rp.Dirty x ∨ x = s :=
  fun rp s => markDirtyCorrect rp s

-- Contract pin: fails to compile if `closureCorrect`'s signature drifts.
example : ∀ {n : ℕ} (tau : Fin n → Fin n → Prop) (b : ℕ) (preds : Fin n → List (Fin n))
    (rp : RP n), (∀ x y, y ∈ preds x ↔ tau y x) → rp.WF → b < rp.nb →
    (closure b preds rp).WF ∧ (closure b preds rp).blk = rp.blk ∧
    (∀ x, rp.blk x ≠ b → ((closure b preds rp).Dirty x ↔ rp.Dirty x)) ∧
    (∀ x, rp.blk x = b → ((closure b preds rp).Dirty x ↔ DirtyClosure tau rp b x)) ∧
    (closure b preds rp).nb = rp.nb :=
  fun tau b preds rp => closureCorrect tau b preds rp

-- Contract pin: fails to compile if `markAllWCorrect`'s signature drifts.
example : ∀ {n : ℕ} (c : Ctx n) (l : List (Fin n)), WLInv c →
    WLInv (markAllW l c) ∧ ∀ z, (markAllW l c).rp.Dirty z ↔ c.rp.Dirty z ∨ z ∈ l :=
  fun c l => markAllWCorrect c l
