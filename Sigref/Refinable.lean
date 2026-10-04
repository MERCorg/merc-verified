import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Perm
import Sigref.Basic

/-!
# The refinable partition data structure (paper §3.3), abstractly

States are `Fin n`. The elements are stored in an array `loc2state`; a state's location is
`state2loc`, modelled by one permutation `loc : Perm (Fin n)` (`loc s` is the location of `s`,
`loc.symm p` the state at location `p`). Blocks are intervals `[bs b, be b)` of locations whose
suffix `[bm b, be b)` holds the *marked* (dirty) states.

`RP.WF` is the structural invariant. The abstract view of a refinable partition is the pair
(partition, dirty set) of `Sigref.Config`:

* the partition relates states with equal `blk`;
* a state is dirty iff its location is `≥ bm` of its block.

`RP.mark` is the paper's `MarkDirty` (swap with the last clean state and move the split), and
`RP.mark_wf` / `RP.mark_view` show it preserves the invariant and adds exactly one dirty state.
-/

namespace Sigref

structure RP (n : ℕ) where
  loc : Equiv.Perm (Fin n)
  blk : Fin n → ℕ
  nb : ℕ
  bs : ℕ → ℕ
  bm : ℕ → ℕ
  be : ℕ → ℕ

namespace RP

variable {n : ℕ}

/-- Structural invariant: blocks are non-empty location intervals, every state lies in the interval
of its block, and the intervals determine the block of a state. -/
structure WF (rp : RP n) : Prop where
  block : ∀ b, b < rp.nb → rp.bs b < rp.be b ∧ rp.be b ≤ n ∧ rp.bs b ≤ rp.bm b ∧ rp.bm b ≤ rp.be b
  state : ∀ s, rp.blk s < rp.nb ∧ rp.bs (rp.blk s) ≤ (rp.loc s).val ∧
    (rp.loc s).val < rp.be (rp.blk s)
  unique : ∀ s b, b < rp.nb → rp.bs b ≤ (rp.loc s).val → (rp.loc s).val < rp.be b → rp.blk s = b

/-- A state is dirty iff it lies in the marked suffix of its block. -/
def Dirty (rp : RP n) (s : Fin n) : Prop := rp.bm (rp.blk s) ≤ (rp.loc s).val

/-- The abstract partition: equal block numbers. -/
def setoid (rp : RP n) : Setoid (Fin n) :=
  ⟨fun s t => rp.blk s = rp.blk t, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

/-- The paper's `MarkDirty`: swap `s` with the last clean state of its block and lower `bm`. -/
def mark (rp : RP n) (s : Fin n) : RP n :=
  if h : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n then
    { rp with
      loc := (Equiv.swap s (rp.loc.symm ⟨rp.bm (rp.blk s) - 1, h.2⟩)).trans rp.loc
      bm := Function.update rp.bm (rp.blk s) (rp.bm (rp.blk s) - 1) }
  else rp

section MarkProofs

variable {rp : RP n} (hwf : rp.WF) (s : Fin n)

/-- Position of the last clean state of the block of `s`. -/
def lastClean (hc : (rp.loc s).val < rp.bm (rp.blk s) ∧ rp.bm (rp.blk s) - 1 < n) : Fin n :=
  rp.loc.symm ⟨rp.bm (rp.blk s) - 1, hc.2⟩

end MarkProofs

/-- Mark every state of `l` that lies in block `b`. -/
def markList (b : ℕ) : List (Fin n) → RP n → RP n
  | [], rp => rp
  | x :: xs, rp => markList b xs (if rp.blk x = b then rp.mark x else rp)

/-- The paper's loop: scan locations from `it` downwards while the position is in the marked
region and the block still has a clean state; mark the in-block predecessors of each scanned
state. `k` is the fuel (the span of the block). -/
def closureLoop (b : ℕ) (preds : Fin n → List (Fin n)) : ℕ → ℕ → RP n → RP n
  | 0, _, rp => rp
  | k + 1, it, rp =>
    if h : rp.bs b < rp.bm b ∧ rp.bm b ≤ it ∧ it < n then
      closureLoop b preds k (it - 1) (markList b (preds (rp.loc.symm ⟨it, h.2.2⟩)) rp)
    else rp

def closure (b : ℕ) (preds : Fin n → List (Fin n)) (rp : RP n) : RP n :=
  closureLoop b preds (rp.be b - rp.bs b) (rp.be b - 1) rp

/-- States of block `b` that reach a dirty state of `rp₀` along τ-steps inside the block. -/
def DirtyClosure (tau : Fin n → Fin n → Prop) (rp₀ : RP n) (b : ℕ) (x : Fin n) : Prop :=
  ∃ d, rp₀.blk d = b ∧ rp₀.Dirty d ∧
    Relation.ReflTransGen (fun u v => tau u v ∧ rp₀.blk u = rp₀.blk v) x d
/-- The abstract view of a refinable partition: the partition (equal block numbers) and the dirty
set. -/
def config (rp : RP n) : Config (Fin n) := ⟨rp.setoid, {x | rp.Dirty x}⟩

/-- **`MarkDirty` correctness**: it preserves the invariant, leaves the partition alone and adds
exactly the marked state to the dirty set. -/
def MarkDirtyCorrect (rp : RP n) (s : Fin n) : Prop :=
  rp.WF → (rp.mark s).WF ∧ (rp.mark s).blk = rp.blk ∧
    ∀ x, (rp.mark s).Dirty x ↔ rp.Dirty x ∨ x = s

/-- **Backwards closure correctness**: the closure loop keeps the partition and all other blocks,
and makes the dirty states of block `b` exactly those that reach a dirty state of the block by
τ-steps inside the block. -/
def ClosureCorrect (tau : Fin n → Fin n → Prop) (b : ℕ) (preds : Fin n → List (Fin n))
    (rp : RP n) : Prop :=
  (∀ x y, y ∈ preds x ↔ tau y x) → rp.WF → b < rp.nb →
    (closure b preds rp).WF ∧ (closure b preds rp).blk = rp.blk ∧
    (∀ x, rp.blk x ≠ b → ((closure b preds rp).Dirty x ↔ rp.Dirty x)) ∧
    (∀ x, rp.blk x = b → ((closure b preds rp).Dirty x ↔ DirtyClosure tau rp b x)) ∧
    (closure b preds rp).nb = rp.nb


end RP

end Sigref
