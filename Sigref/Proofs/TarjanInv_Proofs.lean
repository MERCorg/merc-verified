import Sigref.Proofs.TarjanScan_Proofs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Proofs: the invariant of the Tarjan model

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

Terminology: a state is *initialised* when `low ≠ unv`; the *active* states are the initialised
entries of the work stack (the current DFS path); the *done* states are the initialised states that
are no longer on the SCC stack `stk`.
-/

namespace Sigref.Tarjan

open Relation

variable {n : ℕ}

/-- Reachability along hidden transitions. -/
abbrev Reach (g : Graph n) := ReflTransGen (Edge g)

/-- The state has been initialised (its discovery time and lowlink are set). -/
def Init (g : Graph n) (c : Ctx n) (v : Fin n) : Prop := c.low v ≠ g.unv

/-- The state is initialised and has been assigned to a block. -/
def Done (g : Graph n) (c : Ctx n) (v : Fin n) : Prop := Init g c v ∧ v ∉ c.stk

/-- The hidden edge `x → w` has been examined by the search: for a state in the work stack, the
transitions before its resume offset. -/
def Examined (g : Graph n) (W : List (Fin n × ℕ)) (x w : Fin n) : Prop :=
  Edge g x w ∧ ∀ off, (x, off) ∈ W → ∃ i, i < off ∧ (g.adj x)[i]? = some (true, w)

/-- The invariant of the search. -/
structure Inv (g : Graph n) (c : Ctx n) : Prop where
  -- discovery times
  time_card : c.time = (Finset.univ.filter (fun v => c.low v ≠ g.unv)).card
  disc_lt : ∀ v, Init g c v → c.disc v < c.time
  low_le : ∀ v, Init g c v → c.low v ≤ c.disc v
  disc_inj : ∀ u v, Init g c u → Init g c v → c.disc u = c.disc v → u = v
  unv_disc : ∀ v, ¬ Init g c v →
    c.disc v = g.unv ∨ (c.disc v = 0 ∧ ∃ rest, c.work = (v, 0) :: rest)
  -- the SCC stack
  onSt_iff : ∀ v, c.onSt v = true ↔ v ∈ c.stk
  stk_nodup : c.stk.Nodup
  stk_init : ∀ v ∈ c.stk, Init g c v
  stk_sorted : c.stk.Pairwise (fun a b => c.disc b < c.disc a)
  -- the work stack
  work_nodup : (c.work.map Prod.fst).Nodup
  work_off : ∀ p off, (p, off) ∈ c.work → off ≤ (g.adj p).length
  work_fresh : ∀ p off, (p, off) ∈ c.work → Init g c p ∨ (c.work.head? = some (p, off) ∧ off = 0)
  work_disc : c.work.Pairwise (fun a b => Init g c a.1 → c.disc b.1 < c.disc a.1)
  work_reach : c.work.Pairwise (fun a b => Reach g b.1 a.1)
  work_stk : ∀ p off, (p, off) ∈ c.work → Init g c p → p ∈ c.stk
  -- examined edges
  exam_vis : ∀ x w, Init g c x → Examined g c.work x w → c.disc w ≠ g.unv
  K : ∀ W1 p off W2, c.work = W1 ++ (p, off) :: W2 → Init g c p →
    ∀ x ∈ c.stk, c.disc p ≤ c.disc x → ∀ w ∈ c.stk, Examined g c.work x w →
      ∃ q ∈ W1.map Prod.fst ++ [p], c.low q ≤ c.disc w
  G : ∀ p off, (p, off) ∈ c.work → Init g c p →
    ∀ x ∈ c.stk, c.disc p ≤ c.disc x → Reach g p x
  -- the finished blocks
  E1 : ∀ v, Done g c v → c.blk v < c.eq
  E2 : ∀ v w, Done g c v → Edge g v w → Done g c w
  E3 : ∀ v w, Done g c v → Done g c w → (c.blk v = c.blk w ↔ Reach g v w ∧ Reach g w v)
  E4 : ∀ b, b < c.eq → ∃ v, Done g c v ∧ c.blk v = b
  -- lowlinks
  F : ∀ v ∈ c.stk, ∃ w ∈ c.stk, c.disc w = c.low v ∧ Reach g v w
  L : ∀ v ∈ c.stk, v ∉ c.work.map Prod.fst → c.low v < c.disc v
  SE : ∀ x ∈ c.stk, ∃ p off, (p, off) ∈ c.work ∧ Init g c p ∧ c.disc p ≤ c.disc x
  -- the roots
  R : ∀ v : Fin n, v.val < c.ri → Init g c v ∨ (v, 0) ∈ c.work
  ri_le : c.ri ≤ n

theorem inv_init (g : Graph n) : Inv g (init g) := by
  have hI : ∀ v, ¬ Init g (init g) v := fun v h => h rfl
  refine
    { time_card := by simp [init]
      disc_lt := fun v h => absurd h (hI v)
      low_le := fun v h => absurd h (hI v)
      disc_inj := fun u v h => absurd h (hI u)
      unv_disc := fun v _ => Or.inl rfl
      onSt_iff := by intro v; simp [init]
      stk_nodup := by simp [init]
      stk_init := by simp [init]
      stk_sorted := by simp [init]
      work_nodup := by simp [init]
      work_off := by simp [init]
      work_fresh := by simp [init]
      work_disc := by simp [init]
      work_reach := by simp [init]
      work_stk := by simp [init]
      exam_vis := fun x w h => absurd h (hI x)
      K := by simp [init]
      G := by simp [init]
      E1 := fun v h => absurd h.1 (hI v)
      E2 := fun v w h => absurd h.1 (hI v)
      E3 := fun v w h => absurd h.1 (hI v)
      E4 := by simp [init]
      F := by simp [init]
      L := by simp [init]
      SE := by simp [init]
      R := by simp [init]
      ri_le := by simp [init] }

namespace Inv

variable {g : Graph n} {c : Ctx n}

theorem time_le (h : Inv g c) : c.time ≤ n := by
  rw [h.time_card]
  calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
    _ = n := by simp

theorem disc_ne_unv (h : Inv g c) {v : Fin n} (hv : Init g c v) : c.disc v ≠ g.unv := by
  have := h.disc_lt v hv
  have := h.time_le
  have := g.unv_gt
  omega

theorem time_ne_unv (h : Inv g c) : c.time ≠ g.unv := by
  have := h.time_le
  have := g.unv_gt
  omega

/-- A queued (non-initialised, but not unvisited) state is the fresh head of the work stack. -/
theorem head_unique {s : Fin n} {off : ℕ} {W : List (Fin n × ℕ)} (h : Inv g c)
    (hw : c.work = (s, off) :: W) : ∀ off', (s, off') ∉ W := by
  intro off' hoff
  have := h.work_nodup
  rw [hw] at this
  simp only [List.map_cons, List.nodup_cons] at this
  exact this.1 (List.mem_map.mpr ⟨(s, off'), hoff, rfl⟩)

end Inv

end Sigref.Tarjan
