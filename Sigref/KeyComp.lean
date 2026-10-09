import Sigref.Iteration
import Sigref.Branching

/-!
# The key computation of the branching algorithm (paper Algorithm 5, as implemented in merc)

`Iter` (see `Iteration.lean`) splits the closed block by an abstract hash `SigData.sigHash`. This
file models how the implementation actually computes the split key of the dirty states of a
block, and states that it induces the same grouping (`KeyCompCorrect`).

Model, following `signature_refinement.rs` (`branching_process_marked_elements`):

* the dirty states of the block are processed in increasing state index (`sortedDirty`); with
  `TopoSorted` every inert τ-target of a state is processed before the state itself;
* the *flat* signature `flatSig` of a state has *visible* entries `(a, block of target)` and
  *hat* entries, the keys of its inert τ-targets that are dirty (the paper's `(τ̇, h(Sig t))`).
  An inert τ-step into a *clean* target is an ordinary `(τ, block)` entry (the implementation's
  deviation from the paper, justified by clean states of a block being `E π`-equivalent);
* `renumber` returns the largest hat key `k` whose interned signature contains the rest of the
  signature (`is_subset_excluding`), otherwise the signature is interned in `tbl`.

The signature table is per iteration; the key array `state_to_key` persists, but only the keys of
dirty targets processed in the same iteration are ever read.
-/

namespace Sigref

open Cslib

variable {State Label : Type}

/-- The flat signature of a state: visible entries and hat entries. -/
structure KSig (Label : Type) where
  vis : Set (Label × ℕ)
  hat : Set ℕ

/-- The state of the key computation: the `state_to_key` array and the interned signatures
(`key_to_signature`). -/
structure KC (n : ℕ) (Label : Type) where
  key : Fin n → ℕ
  tbl : List (KSig Label)

/-- The block data a key computation reads: the block number and the dirty predicate of every
state (a refinable partition forgets everything else). -/
structure BD (n : ℕ) where
  blk : Fin n → ℕ
  Dirty : Fin n → Prop

/-- The partition of block data: equal block numbers. -/
def BD.setoid {n : ℕ} (bd : BD n) : Setoid (Fin n) :=
  ⟨fun s t => bd.blk s = bd.blk t, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

namespace RP

open Classical

variable {n : ℕ} [HasTau Label]

/-- The block data of a refinable partition. -/
def toBD (rp : RP n) : BD n := ⟨rp.blk, fun x => rp.Dirty x⟩

/-- Every inert τ-step of the LTS goes to a state with a smaller index: the input of the branching
algorithm after `tau_cycle_elimination_and_reorder`. -/
def TopoSorted (lts : LTS (Fin n) Label) : Prop :=
  ∀ s t : Fin n, lts.Tr s HasTau.τ t → t < s

/-- `branching_bisim_signature_inductive`: the flat signature of `s` in the partition with block
numbers `blk`, dirty states `dirty` and current keys `key`. -/
def flatSig (lts : LTS (Fin n) Label) (blk : Fin n → ℕ) (dirty : Fin n → Prop) (key : Fin n → ℕ)
    (s : Fin n) : KSig Label where
  vis := {e | ∃ a t, lts.Tr s a t ∧ ¬ (a = HasTau.τ ∧ blk t = blk s ∧ dirty t) ∧ e = (a, blk t)}
  hat := {k | ∃ t, lts.Tr s HasTau.τ t ∧ blk t = blk s ∧ dirty t ∧ k = key t}

/-- `is_subset_excluding` for the hat entry `k` of `sg` against the interned signature `old`:
everything of `sg` except the hat entry `k` occurs in `old`. -/
def SubsetExcl (old sg : KSig Label) (k : ℕ) : Prop :=
  sg.vis ⊆ old.vis ∧ sg.hat \ {k} ⊆ old.hat

/-- `renumber_branching`: the largest hat key whose interned signature absorbs the rest. -/
noncomputable def renumber (tbl : List (KSig Label)) (sg : KSig Label) : Option ℕ :=
  if h : ∃ k, ∃ hk : k < tbl.length, k ∈ sg.hat ∧ SubsetExcl tbl[k] sg k then
    some (Nat.findGreatest (fun k => ∃ hk : k < tbl.length, k ∈ sg.hat ∧ SubsetExcl tbl[k] sg k)
      tbl.length)
  else none

/-- `strong_intern_signature`: the key of `sg` in `tbl`, appending it if it is new. -/
noncomputable def intern (tbl : List (KSig Label)) (sg : KSig Label) : ℕ × List (KSig Label) :=
  if h : ∃ k, ∃ hk : k < tbl.length, tbl[k] = sg then (h.choose, tbl) else (tbl.length, tbl ++ [sg])

/-- `branching_signature_index` followed by writing `state_to_key[s]`. -/
noncomputable def kcStep (lts : LTS (Fin n) Label) (blk : Fin n → ℕ) (dirty : Fin n → Prop)
    (st : KC n Label) (s : Fin n) : KC n Label :=
  let sg := flatSig lts blk dirty st.key s
  match renumber st.tbl sg with
  | some k => { st with key := Function.update st.key s k }
  | none =>
    let r := intern st.tbl sg
    { key := Function.update st.key s r.1, tbl := r.2 }

/-- `branching_process_marked_elements`: process the states in the given order. -/
noncomputable def kcRun (lts : LTS (Fin n) Label) (blk : Fin n → ℕ) (dirty : Fin n → Prop)
    (order : List (Fin n)) (st : KC n Label) : KC n Label :=
  order.foldl (kcStep lts blk dirty) st

/-- The dirty states of block `b` in increasing order (`marked_elements_sorted`). -/
noncomputable def sortedDirty (rp : BD n) (b : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun x => decide (rp.blk x = b ∧ rp.Dirty x)

/-- The keys computed for block `b` (after the backwards closure) from an arbitrary initial
`state_to_key` array. -/
noncomputable def keysOf (lts : LTS (Fin n) Label) (rp : BD n) (b : ℕ) (key0 : Fin n → ℕ) :
    Fin n → ℕ :=
  (kcRun lts rp.blk (fun x => rp.Dirty x) (sortedDirty rp b) ⟨key0, []⟩).key

/-- What the key computation of block `b` needs from the algorithm's invariant, after the backwards
closure: the dirty set is closed under inert τ-predecessors inside `b`, clean states of `b` are
`E π`-related to each other (`U`), and a clean state of `b` is never `E π`-related to a dirty one
(`S`). -/
structure BlockInv (lts : LTS (Fin n) Label) (rp : BD n) (b : ℕ) : Prop where
  closed : ∀ s t, lts.Tr s HasTau.τ t → rp.blk s = b → rp.blk t = b → rp.Dirty t → rp.Dirty s
  U : ∀ s t, rp.blk s = b → rp.blk t = b → ¬ rp.Dirty s → ¬ rp.Dirty t → E lts rp.setoid s t
  S : ∀ s t, rp.blk s = b → rp.blk t = b → ¬ rp.Dirty s → rp.Dirty t → ¬ E lts rp.setoid s t

/-- **Key computation correctness** (paper Algorithm 5 as implemented): on a topologically sorted
τ-loop-free LTS, for a block satisfying `BlockInv`, two dirty states of the block get the same key
exactly when they are related by branching bisimilarity relative to the partition. -/
def KeyCompCorrect (lts : LTS (Fin n) Label) (rp : BD n) (b : ℕ) (key0 : Fin n → ℕ) : Prop :=
  TopoSorted lts → BlockInv lts rp b →
    ∀ x y, rp.blk x = b → rp.blk y = b → rp.Dirty x → rp.Dirty y →
      (keysOf lts rp b key0 x = keysOf lts rp b key0 y ↔ E lts rp.setoid x y)

/-- One iteration of the algorithm with the split key computed as the implementation does
(`keysOf`, for an arbitrary initial `state_to_key` array) instead of an abstract signature hash. -/
def IterK (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (c c' : Ctx n) : Prop :=
  ∃ (b : ℕ) (wl' : List ℕ) (key0 : Fin n → ℕ) (rp2 : RP n),
    c.wl = b :: wl' ∧
    IsSplit (closure b preds c.rp) rp2 b
      (fun x => if (closure b preds c.rp).Dirty x then
        some (keysOf lts (closure b preds c.rp).toBD b key0 x) else none) ∧
    c' = markAllW (markTargets inc rp2 (closure b preds c.rp).nb) ⟨rp2, wl'⟩

/-- **One implementation-keyed iteration is a step of the abstract algorithm**, and preserves the
worklist invariant. -/
def IterKSimulatesBranchingStep (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) : Prop :=
  (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → ∀ c c' : Ctx n, WLInv c → BranchingInv lts c.rp.config →
      IterK lts inc preds c c' → WLInv c' ∧ BranchingStep lts c.rp.config c'.rp.config

/-- **Partial correctness of the algorithm with implementation keys**: whenever the worklist is
empty after a run from the initial partition, the partition is exactly branching bisimilarity. -/
def RPSigrefKCorrect (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : Prop :=
  (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → ∀ c : Ctx n,
      Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c → c.wl = [] →
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y

/-- **Termination of the algorithm with implementation keys.** -/
def RPSigrefKTerminates (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : Prop :=
  (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → WellFounded (fun c' c : Ctx n =>
      Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c ∧ IterK lts inc preds c c')

/-- **Progress with implementation keys**: a context with a non-empty worklist can always take an
iteration. -/
def RPSigrefKProgress (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) : Prop :=
  (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    ∀ c : Ctx n, WLInv c → c.wl ≠ [] → ∃ c', IterK lts inc preds c c'

/-- **Total correctness with implementation keys**: from the initial partition the algorithm
reaches an empty worklist, and the partition is exactly branching bisimilarity. -/
def RPSigrefKTotal (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : Prop :=
  (∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) → (∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) →
    TopoSorted lts → ∃ c : Ctx n,
      Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c ∧ c.wl = [] ∧
        ∀ x y, c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y

end RP

end Sigref
