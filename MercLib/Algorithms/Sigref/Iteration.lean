module

public import MercLib.Sigref.Worklist
public import MercLib.Sigref.SigData
public import MercLib.Sigref.Branching
public import MercLib.Sigref.Refinable

@[expose] public section

/-!
# One iteration of the paper's algorithm on the refinable partition

`Iter` is one iteration of Algorithm 2 on `Ctx` (refinable partition + worklist): pop a block,
compute the backwards closure, split the block by signature, and mark the predecessors of the new
blocks. `iter_sim` shows that it is a step of the abstract algorithm (`BranchingStep`) on the
abstract view, and preserves the worklist invariant.
-/

namespace MercLib.Sigref

open MercLib.LTS MercLib.Signatures

open Cslib

namespace RP

open Classical

variable {n : ℕ} {Label : Type} [HasTau Label]

/-- Postcondition of the paper's `Split`/`finish_partition_marked` on block `b`: the block is
regrouped by `grp`, the pieces are unmarked, one piece keeps the id `b` and the others get fresh
ids, and all other blocks are untouched. -/
structure IsSplit {G : Type} (rp rp' : RP n) (b : ℕ) (grp : Fin n → G) : Prop where
  wf : rp'.WF
  nb_le : rp.nb ≤ rp'.nb
  out : ∀ x, rp.blk x ≠ b → rp'.blk x = rp.blk x ∧ (rp'.Dirty x ↔ rp.Dirty x)
  part : ∀ x y, rp'.blk x = rp'.blk y ↔
    (rp.blk x = rp.blk y ∧ (rp.blk x ≠ b ∨ grp x = grp y))
  clean : ∀ x, rp.blk x = b → ¬ rp'.Dirty x
  newid : ∀ x, rp.blk x = b → rp'.blk x = b ∨ rp.nb ≤ rp'.blk x
  keep : ∃ x, rp.blk x = b ∧ rp'.blk x = b

/-- The states whose block gets marked after a split: predecessors of states of fresh blocks via a
visible step or from a pre-existing block (paper: `Pred(U)`). -/
noncomputable def markTargets (inc : Fin n → List (Fin n × Label)) (rp2 : RP n) (nbOld : ℕ) :
    List (Fin n) :=
  (List.finRange n).flatMap fun u =>
    if nbOld ≤ rp2.blk u then
      ((inc u).filter fun p => decide (p.2 ≠ HasTau.τ ∨ rp2.blk p.1 < nbOld)).map Prod.fst
    else []

/-- One iteration of the algorithm on the refinable partition. -/
def Iter (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (c c' : Ctx n) : Prop :=
  ∃ (b : ℕ) (wl' : List ℕ) (d : SigData lts c.rp.setoid) (rp2 : RP n),
    c.wl = b :: wl' ∧
    IsSplit (closure b preds c.rp) rp2 b
      (fun x => if (closure b preds c.rp).Dirty x then some (d.sigHash x) else none) ∧
    c' = markAllW (markTargets inc rp2 (closure b preds c.rp).nb) ⟨rp2, wl'⟩

/-- The initial refinable partition: one block holding every state, all of them marked. -/
def init (n : ℕ) (_hn : 0 < n) : RP n where
  loc := Equiv.refl _
  blk := fun _ => 0
  nb := 1
  bs := fun _ => 0
  bm := fun _ => 0
  be := fun _ => n

/-- **Partial correctness of the paper's algorithm on the refinable partition**: whenever the
worklist is empty after a run from the initial partition, the partition is exactly branching
bisimilarity. -/
def RPSigrefCorrect (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : Prop :=
  (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TauLoopFree lts → ∀ c : Ctx n,
      Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c → c.wl = [] →
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y

/-- **Termination of the paper's algorithm on the refinable partition**: every run from the initial
partition is finite. -/
def RPSigrefTerminates (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : Prop :=
  (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TauLoopFree lts → WellFounded (fun c' c : Ctx n =>
      Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c ∧ Iter lts inc preds c c')
/-- **Total correctness of the paper's algorithm on the refinable partition**: from the initial
partition the algorithm always reaches an empty worklist, and the resulting partition is exactly
branching bisimilarity. -/
def RPSigrefTotal (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : Prop :=
  (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TauLoopFree lts → ∃ c : Ctx n,
      Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c ∧ c.wl = [] ∧
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y

end RP

end MercLib.Sigref
