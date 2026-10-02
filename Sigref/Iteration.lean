import Sigref.RPStep
import Sigref.Worklist
import Sigref.SigE

/-!
# One iteration of the paper's algorithm on the refinable partition

`Iter` is one iteration of Algorithm 2 on `Ctx` (refinable partition + worklist): pop a block,
compute the backwards closure, split the block by signature, and mark the predecessors of the new
blocks. `iter_sim` shows that it is a step of the abstract algorithm (`BranchingStep`) on the
abstract view, and preserves the worklist invariant.
-/

namespace Sigref

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

theorem mem_markTargets {lts : LTS (Fin n) Label} {inc : Fin n → List (Fin n × Label)}
    (hinc : ∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u) (rp2 : RP n) (nbOld : ℕ) (y : Fin n) :
    y ∈ markTargets inc rp2 nbOld ↔
      ∃ a u, nbOld ≤ rp2.blk u ∧ lts.Tr y a u ∧ (a ≠ HasTau.τ ∨ rp2.blk y < nbOld) := by
  unfold markTargets
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨u, _, hu⟩
    by_cases h : nbOld ≤ rp2.blk u
    · rw [if_pos h, List.mem_map] at hu
      obtain ⟨⟨y', a⟩, hp, rfl⟩ := hu
      rw [List.mem_filter, decide_eq_true_eq] at hp
      exact ⟨a, u, h, (hinc u y' a).1 hp.1, hp.2⟩
    · rw [if_neg h] at hu; exact absurd hu (List.not_mem_nil)
  · rintro ⟨a, u, h, hTr, hc⟩
    refine ⟨u, List.mem_finRange u, ?_⟩
    rw [if_pos h, List.mem_map]
    exact ⟨(y, a), by rw [List.mem_filter, decide_eq_true_eq]; exact ⟨(hinc u y a).2 hTr, hc⟩, rfl⟩

/-- One iteration of the algorithm on the refinable partition. -/
def Iter (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (c c' : Ctx n) : Prop :=
  ∃ (b : ℕ) (wl' : List ℕ) (d : SigData lts c.rp.setoid) (rp2 : RP n),
    c.wl = b :: wl' ∧
    IsSplit (closure b preds c.rp) rp2 b
      (fun x => if (closure b preds c.rp).Dirty x then some (d.sigHash x) else none) ∧
    c' = markAllW (markTargets inc rp2 (closure b preds c.rp).nb) ⟨rp2, wl'⟩

section Sim

variable {lts : LTS (Fin n) Label} {inc : Fin n → List (Fin n × Label)}
  {preds : Fin n → List (Fin n)}

/-- **One iteration on the refinable partition is a step of the abstract algorithm.** -/
theorem iter_sim (hinc : ∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u)
    (hpreds : ∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) (hWF : TauLoopFree lts)
    {c c' : Ctx n} (hwl : WLInv c) (hit : Iter lts inc preds c c') :
    WLInv c' ∧ BranchingStep lts c.rp.config c'.rp.config := by
  obtain ⟨b, wl', d, rp2, hwleq, hsplit, rfl⟩ := hit
  have hbmem : b ∈ c.wl := by rw [hwleq]; exact List.mem_cons_self
  obtain ⟨hb, x0, hx0b, hx0d⟩ := hwl.queued b hbmem
  obtain ⟨hcwf, hcblk, hcout, hcin, hcnb⟩ := closure_spec hpreds hwl.wf hb
  have hblk1 : ∀ x, (closure b preds c.rp).blk x = c.rp.blk x := fun x => congrFun hcblk x
  have hnodup : (b :: wl').Nodup := hwleq ▸ hwl.nodup
  have hbnot : b ∉ wl' := (List.nodup_cons.1 hnodup).1
  -- the worklist invariant after the split
  have hwl2 : WLInv (⟨rp2, wl'⟩ : Ctx n) := by
    refine ⟨hsplit.wf, (List.nodup_cons.1 hnodup).2, ?_, ?_⟩
    · intro b' hb'
      have hb'c : b' ∈ c.wl := by rw [hwleq]; exact List.mem_cons_of_mem _ hb'
      obtain ⟨hlt, x, hxb, hxd⟩ := hwl.queued b' hb'c
      have hne : b' ≠ b := fun h => hbnot (h ▸ hb')
      have hxne : c.rp.blk x ≠ b := hxb ▸ hne
      have h1 := (hcout x hxne).2 hxd
      have h2 := hsplit.out x (by rw [hblk1]; exact hxne)
      refine ⟨lt_of_lt_of_le hlt (hcnb ▸ hsplit.nb_le), x, ?_, h2.2.2 h1⟩
      rw [h2.1, hblk1]; exact hxb
    · intro x hx
      by_cases hxb : (closure b preds c.rp).blk x = b
      · exact absurd hx (hsplit.clean x hxb)
      · have h2 := hsplit.out x hxb
        have hxne : c.rp.blk x ≠ b := by rw [← hblk1]; exact hxb
        have h3 := (hcout x hxne).1 (h2.2.1 hx)
        have h4 := hwl.dirty x h3
        rw [hwleq] at h4
        rcases List.mem_cons.1 h4 with h5 | h5
        · exact absurd h5 hxne
        · rw [h2.1, hblk1]; exact h5
  refine ⟨markAllW_inv _ hwl2, ?_⟩
  -- the abstract step
  obtain ⟨x1, hx1a, hx1b⟩ := hsplit.keep
  have hblk3 := markAllW_blk (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)
  have hD3 := markAllW_dirty hwl2 (markTargets inc rp2 (closure b preds c.rp).nb)
  have hset : cls c.rp.setoid x0 ∩ {z | c.rp.Dirty z} = {z | c.rp.blk z = b ∧ c.rp.Dirty z} := by
    ext z
    simp only [cls, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact and_congr_left' (by show c.rp.blk x0 = c.rp.blk z ↔ _; rw [hx0b]; exact eq_comm)
  have hDmem : ∀ x, x ∈ inertClosure lts c.rp.setoid (cls c.rp.setoid x0 ∩ {z | c.rp.Dirty z}) ↔
      c.rp.blk x = b ∧ (closure b preds c.rp).Dirty x := by
    intro x
    rw [hset]
    constructor
    · intro hx
      obtain ⟨d', hd', hp⟩ := hx
      have hxb : c.rp.blk x = b := by
        have := InertReach.rel lts c.rp.setoid hp
        exact this.trans hd'.1
      exact ⟨hxb, (closure_view lts hpreds hwl.wf hb x hxb).2 ⟨d', hd', hp⟩⟩
    · rintro ⟨hxb, hxd⟩
      exact (closure_view lts hpreds hwl.wf hb x hxb).1 hxd
  have hU : ∀ u, u ∈ cls c.rp.setoid x0 \ cls (markAllW (markTargets inc rp2 (closure b preds c.rp).nb)
      (⟨rp2, wl'⟩ : Ctx n)).rp.setoid x1 ↔ (closure b preds c.rp).nb ≤ rp2.blk u := by
    intro u
    simp only [Set.mem_sdiff, cls, Set.mem_setOf_eq]
    show (c.rp.blk x0 = c.rp.blk u ∧ ¬ ((markAllW (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)).rp.blk x1 =
      (markAllW (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)).rp.blk u)) ↔ _
    rw [hblk3]
    constructor
    · rintro ⟨h1, h2⟩
      have hub : (closure b preds c.rp).blk u = b := by rw [hblk1, ← h1, hx0b]
      rcases hsplit.newid u hub with h | h
      · exact absurd (hx1b.trans h.symm) h2
      · exact h
    · intro h
      have hub : c.rp.blk u = b := by
        by_contra hne
        have := (hsplit.out u (by rw [hblk1]; exact hne)).1
        have hlt := (hwl.wf.state u).1
        rw [hblk1] at this
        omega
      refine ⟨by rw [hx0b, hub], fun h2 => ?_⟩
      have hbn : b < (closure b preds c.rp).nb := by rw [hcnb]; exact hb
      have : rp2.blk x1 = rp2.blk u := h2
      omega
  have hπ : ∀ x y, c.rp.setoid.r x y ↔ c.rp.blk x = c.rp.blk y := fun _ _ => Iff.rfl
  have hcls : ∀ x, x ∈ cls c.rp.setoid x0 ↔ c.rp.blk x = b := by
    intro x
    show c.rp.blk x0 = c.rp.blk x ↔ _
    rw [hx0b]; exact eq_comm
  have key : ∀ x y, rp2.blk x = rp2.blk y ↔
      branchRel lts c.rp.setoid {z | c.rp.Dirty z} x0 x y := by
    intro x y
    rw [hsplit.part x y]
    unfold branchRel
    simp only [hblk1, hπ, hcls]
    by_cases hxb : c.rp.blk x = b
    · constructor
      · rintro ⟨h1, h2⟩
        have h2' := h2.resolve_left (fun h => h hxb)
        have hyb : c.rp.blk y = b := h1 ▸ hxb
        have hg : ((closure b preds c.rp).Dirty x ↔ (closure b preds c.rp).Dirty y) ∧
            ((closure b preds c.rp).Dirty x → d.sigHash x = d.sigHash y) := by
          by_cases hx : (closure b preds c.rp).Dirty x <;>
            by_cases hy : (closure b preds c.rp).Dirty y <;> simp [hx, hy] at h2' <;> simp [hx, hy, h2']
        refine ⟨h1, fun _ => ⟨?_, fun hxD => ?_⟩⟩
        · rw [hDmem, hDmem]
          exact ⟨fun h => ⟨hyb, hg.1.1 h.2⟩, fun h => ⟨hxb, hg.1.2 h.2⟩⟩
        · rw [hDmem] at hxD
          exact (SigData.sig_iff_E d hWF ((hπ x y).2 h1)).1 ((d.hCoh x y).1 (hg.2 hxD.2))
      · rintro ⟨h1, h2⟩
        obtain ⟨h3, h4⟩ := h2 hxb
        have hyb : c.rp.blk y = b := h1 ▸ hxb
        refine ⟨h1, Or.inr ?_⟩
        rw [hDmem, hDmem] at h3
        have hE : (closure b preds c.rp).Dirty x → d.sigHash x = d.sigHash y := fun hxd =>
          (d.hCoh x y).2 ((SigData.sig_iff_E d hWF ((hπ x y).2 h1)).2
            (h4 ((hDmem x).2 ⟨hxb, hxd⟩)))
        by_cases hx : (closure b preds c.rp).Dirty x
        · have hy : (closure b preds c.rp).Dirty y := (h3.1 ⟨hxb, hx⟩).2
          simp [hx, hy, hE hx]
        · have hy : ¬ (closure b preds c.rp).Dirty y := fun hy => hx ((h3.2 ⟨hyb, hy⟩).2)
          simp [hx, hy]
    · constructor
      · rintro ⟨h1, _⟩; exact ⟨h1, fun h => absurd h hxb⟩
      · rintro ⟨h1, _⟩; exact ⟨h1, Or.inl hxb⟩
  refine ⟨x0, x1, ⟨⟨x0, c.rp.setoid.refl x0, hx0d⟩, ?_, ?_, ?_⟩⟩
  · show c.rp.blk x0 = c.rp.blk x1
    rw [hx0b, ← hblk1]; exact hx1a.symm
  · intro x y
    show (markAllW (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)).rp.blk x = (markAllW (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)).rp.blk y ↔ _
    rw [hblk3]; exact key x y
  · ext z
    show (markAllW (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)).rp.Dirty z ↔
      (z ∈ {w | c.rp.Dirty w} \ inertClosure lts c.rp.setoid (cls c.rp.setoid x0 ∩ {w | c.rp.Dirty w})) ∨
      z ∈ predB lts (cls c.rp.setoid x0 \ cls (markAllW (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)).rp.setoid x1)
    rw [hD3 z, mem_markTargets hinc]
    have hr2 : rp2.Dirty z ↔ (c.rp.blk z ≠ b ∧ c.rp.Dirty z) := by
      by_cases hzb : c.rp.blk z = b
      · exact ⟨fun h => absurd h (hsplit.clean z (by rw [hblk1]; exact hzb)),
          fun h => absurd hzb h.1⟩
      · have h2 := hsplit.out z (by rw [hblk1]; exact hzb)
        rw [h2.2, hcout z hzb]
        exact ⟨fun h => ⟨hzb, h⟩, fun h => h.2⟩
    have hXD : (z ∈ {w | c.rp.Dirty w} \ inertClosure lts c.rp.setoid
        (cls c.rp.setoid x0 ∩ {w | c.rp.Dirty w})) ↔ (c.rp.blk z ≠ b ∧ c.rp.Dirty z) := by
      simp only [Set.mem_sdiff, Set.mem_setOf_eq, hDmem]
      by_cases hzb : c.rp.blk z = b
      · constructor
        · rintro ⟨hd, hn⟩
          exact absurd ⟨hzb, (hcin z hzb).2 ⟨z, hzb, hd, Relation.ReflTransGen.refl⟩⟩ hn
        · rintro ⟨h, _⟩; exact absurd hzb h
      · exact ⟨fun h => ⟨hzb, h.1⟩, fun h => ⟨h.2, fun h' => hzb h'.1⟩⟩
    have hpred : z ∈ predB lts (cls c.rp.setoid x0 \ cls (markAllW (markTargets inc rp2 (closure b preds c.rp).nb) (⟨rp2, wl'⟩ : Ctx n)).rp.setoid x1) ↔
        ∃ a u, (closure b preds c.rp).nb ≤ rp2.blk u ∧ lts.Tr z a u ∧
          (a ≠ HasTau.τ ∨ rp2.blk z < (closure b preds c.rp).nb) := by
      simp only [predB, Set.mem_setOf_eq, hU]
      constructor
      · rintro ⟨μ, u, h1, h2, h3⟩
        refine ⟨μ, u, h1, h2, ?_⟩
        by_cases hμ : μ = HasTau.τ
        · exact Or.inr (not_le.1 (h3 hμ))
        · exact Or.inl hμ
      · rintro ⟨μ, u, h1, h2, h3⟩
        refine ⟨μ, u, h1, h2, fun hμ => ?_⟩
        rcases h3 with h | h
        · exact absurd hμ h
        · exact not_le.2 h
    rw [hr2, hpred]
    exact or_congr_left hXD.symm

/-- The initial refinable partition: one block holding every state, all of them marked. -/
def init (n : ℕ) (_hn : 0 < n) : RP n where
  loc := Equiv.refl _
  blk := fun _ => 0
  nb := 1
  bs := fun _ => 0
  bm := fun _ => 0
  be := fun _ => n

theorem init_wf (n : ℕ) (hn : 0 < n) : (init n hn).WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb; simp [init] at *; omega
  · intro s; simp [init]
  · intro s b hb _ _; simp [init] at *; omega

theorem init_config (n : ℕ) (hn : 0 < n) : (init n hn).config = initConfig (Fin n) := by
  unfold RP.config initConfig
  congr 1
  · exact Setoid.ext fun x y => ⟨fun _ => trivial, fun _ => rfl⟩
  · ext x; simp [RP.Dirty, init]

theorem init_inv (n : ℕ) (hn : 0 < n) : WLInv (⟨init n hn, [0]⟩ : Ctx n) := by
  refine ⟨init_wf n hn, by simp, ?_, ?_⟩
  · intro b hb
    simp at hb; subst hb
    exact ⟨by simp [init], ⟨0, hn⟩, rfl, by simp [RP.Dirty, init]⟩
  · intro x _; simp [init]

/-- Reachable contexts satisfy the worklist invariant and are abstract runs. -/
theorem reach_sim (hinc : ∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u)
    (hpreds : ∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) (hWF : TauLoopFree lts)
    (hn : 0 < n) {c : Ctx n}
    (h : Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c) :
    WLInv c ∧ Relation.ReflTransGen (BranchingStep lts) (initConfig (Fin n)) c.rp.config := by
  induction h with
  | refl => exact ⟨init_inv n hn, by rw [init_config]⟩
  | tail _ hstep ih =>
    obtain ⟨hwl, hrun⟩ := ih
    obtain ⟨hwl', hbs⟩ := iter_sim hinc hpreds hWF hwl hstep
    exact ⟨hwl', hrun.tail hbs⟩

/-- **Correctness of the paper's algorithm on the refinable partition (partial)**: whenever the
worklist is empty after a run from the initial partition, the partition is exactly branching
bisimilarity. -/
theorem rp_run_correct {n : ℕ} (hn : 0 < n) {lts : LTS (Fin n) Label}
    {inc : Fin n → List (Fin n × Label)} {preds : Fin n → List (Fin n)}
    (hinc : ∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u)
    (hpreds : ∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) (hWF : TauLoopFree lts)
    {c : Ctx n} (h : Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c)
    (hempty : c.wl = []) (x y : Fin n) :
    c.rp.setoid.r x y ↔ BranchingBisimilarity lts x y := by
  obtain ⟨hwl, hrun⟩ := reach_sim hinc hpreds hWF hn h
  have hinv := branchingInv_reach lts hWF hrun
  refine branchingInv_final lts hinv (fun s hs => ?_) x y
  have := hwl.dirty s hs
  rw [hempty] at this
  exact absurd this List.not_mem_nil

/-- **Termination**: every run of the algorithm on the refinable partition is finite. -/
theorem rp_wf {n : ℕ} (hn : 0 < n) {lts : LTS (Fin n) Label}
    {inc : Fin n → List (Fin n × Label)} {preds : Fin n → List (Fin n)}
    (hinc : ∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u)
    (hpreds : ∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) (hWF : TauLoopFree lts) :
    WellFounded (fun c' c : Ctx n =>
      Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c ∧ Iter lts inc preds c c') := by
  refine Subrelation.wf (r := fun c' c : Ctx n => measure c'.rp.config < measure c.rp.config)
    (fun {c' c} h => ?_) (InvImage.wf (fun c : Ctx n => measure c.rp.config) wellFounded_lt)
  obtain ⟨hr, hit⟩ := h
  obtain ⟨hwl, _⟩ := reach_sim hinc hpreds hWF hn hr
  exact branchingStep_measure_lt lts (iter_sim hinc hpreds hWF hwl hit).2

end Sim

end RP

end Sigref
