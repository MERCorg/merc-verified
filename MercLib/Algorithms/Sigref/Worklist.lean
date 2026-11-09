module

public import MercLib.Sigref.Refinable

@[expose] public section

/-!
# `MarkDirty` with the worklist (paper Algorithm 3)

`markW` is the paper's `MarkDirty`: if the block has no dirty state yet it is pushed on the
worklist, then the state is swapped into the marked suffix. `WLInv` is the worklist invariant of
the algorithm: the worklist has no duplicates, every queued block is valid and contains a dirty
state, and every dirty state's block is queued.
-/

namespace MercLib.Sigref

namespace RP

open Classical

variable {n : ℕ}

/-- A refinable partition together with its worklist of blocks that contain dirty states. -/
structure Ctx (n : ℕ) where
  rp : RP n
  wl : List ℕ

/-- Worklist invariant. -/
structure WLInv (c : Ctx n) : Prop where
  wf : c.rp.WF
  nodup : c.wl.Nodup
  queued : ∀ b ∈ c.wl, b < c.rp.nb ∧ ∃ x, c.rp.blk x = b ∧ c.rp.Dirty x
  dirty : ∀ x, c.rp.Dirty x → c.rp.blk x ∈ c.wl

/-- `MarkDirty`: queue the block if it has no dirty state yet, then mark. -/
noncomputable def markW (c : Ctx n) (x : Fin n) : Ctx n :=
  if c.rp.Dirty x then c
  else ⟨c.rp.mark x, if c.rp.bm (c.rp.blk x) = c.rp.be (c.rp.blk x) then c.rp.blk x :: c.wl else c.wl⟩

noncomputable def markAllW : List (Fin n) → Ctx n → Ctx n
  | [], c => c
  | x :: xs, c => markAllW xs (markW c x)

end RP

end MercLib.Sigref
