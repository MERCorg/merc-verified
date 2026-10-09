import Sigref.KeyComp
import Sigref.Proofs.KeyComp_Proofs
import Sigref.Proofs.Iteration_Proofs

/-!
# Proofs: the algorithm with implementation keys

An iteration whose split key is the implementation's `keysOf` is an iteration of the abstract
algorithm (`Iter`), so partial correctness, termination, progress and totality transfer.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/KeyComp_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

namespace RP

open Classical

variable {n : ℕ} {Label : Type} [HasTau Label]
variable {lts : LTS (Fin n) Label} {inc : Fin n → List (Fin n × Label)}
  {preds : Fin n → List (Fin n)}

/-- An implementation-keyed iteration from a state satisfying the invariant is an `Iter`. -/
theorem iterK_iter (hpreds : ∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) (hTopo : TopoSorted lts)
    {c c' : Ctx n} (hwl : WLInv c) (hinv : BranchingInv lts c.rp.config)
    (h : IterK lts inc preds c c') : Iter lts inc preds c c' := by
  obtain ⟨b, wl', key0, rp2, hwleq, hsplit, rfl⟩ := h
  have hWF := tauLoopFree_of_topo lts hTopo
  have hbmem : b ∈ c.wl := by rw [hwleq]; exact List.mem_cons_self
  obtain ⟨hb, _⟩ := hwl.queued b hbmem
  obtain ⟨hcwf, hcblk, hcout, hcin, hcnb⟩ := closure_spec hpreds hwl.wf hb
  obtain ⟨d⟩ := sigDataExists lts c.rp.setoid hWF
  have hblk1 : ∀ x, (closure b preds c.rp).blk x = c.rp.blk x := fun x => congrFun hcblk x
  have hset : (closure b preds c.rp).setoid = c.rp.setoid :=
    Setoid.ext fun x y => by
      show (closure b preds c.rp).blk x = (closure b preds c.rp).blk y ↔ c.rp.blk x = c.rp.blk y
      rw [hblk1, hblk1]
  have hIC : ∀ x, c.rp.blk x = b → ((closure b preds c.rp).Dirty x ↔
      x ∈ inertClosure lts c.rp.setoid {z | c.rp.Dirty z}) := by
    intro x hx
    rw [closure_view lts hpreds hwl.wf hb x hx]
    constructor
    · rintro ⟨d', hd', hp⟩; exact ⟨d', hd'.2, hp⟩
    · rintro ⟨d', hd', hp⟩
      have := InertReach.rel lts c.rp.setoid hp
      exact ⟨d', ⟨(show c.rp.blk x = c.rp.blk d' from this).symm.trans hx, hd'⟩, hp⟩
  have hbi : BlockInv lts (closure b preds c.rp).toBD b := by
    refine ⟨?_, ?_, ?_⟩
    · intro s t hTr hs ht hdt
      replace hs : (closure b preds c.rp).blk s = b := hs
      replace ht : (closure b preds c.rp).blk t = b := ht
      rw [hblk1] at hs ht
      obtain ⟨d', hd', hp⟩ := (hIC t ht).1 hdt
      exact (hIC s hs).2 ⟨d', hd', Relation.ReflTransGen.head
        ⟨hTr, (show c.rp.blk s = c.rp.blk t by rw [hs, ht])⟩ hp⟩
    · intro s t hs ht hds hdt
      replace hs : (closure b preds c.rp).blk s = b := hs
      replace ht : (closure b preds c.rp).blk t = b := ht
      rw [hblk1] at hs ht
      show E lts (closure b preds c.rp).setoid s t
      rw [hset]
      exact hinv.U s t (show c.rp.blk s = c.rp.blk t by rw [hs, ht])
        (fun h => hds ((hIC s hs).2 h)) (fun h => hdt ((hIC t ht).2 h))
    · intro s t hs ht hds hdt
      replace hs : (closure b preds c.rp).blk s = b := hs
      replace ht : (closure b preds c.rp).blk t = b := ht
      rw [hblk1] at hs ht
      show ¬ E lts (closure b preds c.rp).setoid s t
      rw [hset]
      exact hinv.S s t (show c.rp.blk s = c.rp.blk t by rw [hs, ht])
        (fun h => hds ((hIC s hs).2 h)) ((hIC t ht).1 hdt)
  have hkey := keyCompCorrect lts (closure b preds c.rp).toBD b key0 hTopo hbi
  have hgrp : ∀ x y, (closure b preds c.rp).blk x = b → (closure b preds c.rp).blk y = b →
      (((if (closure b preds c.rp).Dirty x then
          some (keysOf lts (closure b preds c.rp).toBD b key0 x) else none) =
        (if (closure b preds c.rp).Dirty y then
          some (keysOf lts (closure b preds c.rp).toBD b key0 y) else none)) ↔
       ((if (closure b preds c.rp).Dirty x then some (d.sigHash x) else none) =
        (if (closure b preds c.rp).Dirty y then some (d.sigHash y) else none))) := by
    intro x y hx hy
    by_cases hdx : (closure b preds c.rp).Dirty x <;> by_cases hdy : (closure b preds c.rp).Dirty y
    · simp only [hdx, hdy, if_true, Option.some.injEq]
      rw [hkey x y hx hy hdx hdy]
      rw [show (closure b preds c.rp).toBD.setoid = c.rp.setoid from hset, d.hCoh,
        d.sig_iff_E hWF (show c.rp.blk x = c.rp.blk y by rw [← hblk1, ← hblk1 y, hx, hy])]
    · simp [hdx, hdy]
    · simp [hdx, hdy]
    · simp [hdx, hdy]
  refine ⟨b, wl', d, rp2, hwleq, ⟨hsplit.wf, hsplit.nb_le, hsplit.out, ?_, hsplit.clean,
    hsplit.newid, hsplit.keep⟩, rfl⟩
  intro x y
  rw [hsplit.part x y]
  refine and_congr_right fun hxy => ?_
  by_cases hxb : (closure b preds c.rp).blk x = b
  · have hyb : (closure b preds c.rp).blk y = b := hxy ▸ hxb
    exact ⟨fun h => h.imp_right (hgrp x y hxb hyb).1, fun h => h.imp_right (hgrp x y hxb hyb).2⟩
  · exact ⟨fun _ => Or.inl hxb, fun _ => Or.inl hxb⟩

/-- Runs of `IterK` are runs of `Iter`. -/
theorem reachK (hinc : ∀ u y a, (y, a) ∈ inc u ↔ lts.Tr y a u)
    (hpreds : ∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) (hTopo : TopoSorted lts)
    (hn : 0 < n) {c : Ctx n}
    (h : Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c) :
    Relation.ReflTransGen (Iter lts inc preds) ⟨init n hn, [0]⟩ c := by
  have hWF := tauLoopFree_of_topo lts hTopo
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨hwl, hrun⟩ := reach_sim hinc hpreds hWF hn ih
    exact ih.tail (iterK_iter hpreds hTopo hwl (branchingInv_reach lts hWF hrun) hstep)

theorem iterKSimulatesBranchingStep (lts : LTS (Fin n) Label)
    (inc : Fin n → List (Fin n × Label)) (preds : Fin n → List (Fin n)) :
    IterKSimulatesBranchingStep lts inc preds :=
  fun hinc hpreds hTopo _ _ hwl hinv hit =>
    iter_sim hinc hpreds (tauLoopFree_of_topo lts hTopo) hwl (iterK_iter hpreds hTopo hwl hinv hit)

theorem rpSigrefKCorrect (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKCorrect lts inc preds hn :=
  fun hinc hpreds hTopo _ h he x y =>
    rp_run_correct hn hinc hpreds (tauLoopFree_of_topo lts hTopo) (reachK hinc hpreds hTopo hn h)
      he x y

theorem rpSigrefKTerminates (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKTerminates lts inc preds hn := by
  intro hinc hpreds hTopo
  have hWF := tauLoopFree_of_topo lts hTopo
  refine Subrelation.wf (fun {c' c} hh => ?_) (rp_wf hn hinc hpreds hWF)
  obtain ⟨hr, hit⟩ := hh
  have hr' := reachK hinc hpreds hTopo hn hr
  obtain ⟨hwl, hrun⟩ := reach_sim hinc hpreds hWF hn hr'
  exact ⟨hr', iterK_iter hpreds hTopo hwl (branchingInv_reach lts hWF hrun) hit⟩

theorem rpSigrefKProgress (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) : RPSigrefKProgress lts inc preds := by
  intro hpreds c hwl hne
  obtain ⟨rp, wl⟩ := c
  cases wl with
  | nil => exact absurd rfl hne
  | cons b wl' =>
    have hb : b < rp.nb := (hwl.queued b List.mem_cons_self).1
    obtain ⟨hcwf, hcblk, hcout, hcin, hcnb⟩ := closure_spec hpreds hwl.wf hb
    obtain ⟨rp2, hsplit⟩ := splitExists (closure b preds rp) b
      (fun x => if (closure b preds rp).Dirty x then
        some (keysOf lts (closure b preds rp).toBD b (fun _ => 0) x) else none)
      hcwf (by rw [hcnb]; exact hb)
    exact ⟨_, b, wl', fun _ => 0, rp2, rfl, hsplit, rfl⟩

theorem rpSigrefKTotal (lts : LTS (Fin n) Label) (inc : Fin n → List (Fin n × Label))
    (preds : Fin n → List (Fin n)) (hn : 0 < n) : RPSigrefKTotal lts inc preds hn := by
  intro hinc hpreds hTopo
  have hWF := tauLoopFree_of_topo lts hTopo
  have key : ∀ c : Ctx n,
      Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c →
      ∃ c', Relation.ReflTransGen (IterK lts inc preds) ⟨init n hn, [0]⟩ c' ∧ c'.wl = [] := by
    intro c
    induction c using (rpSigrefKTerminates lts inc preds hn hinc hpreds hTopo).induction with
    | _ c ih =>
      intro hc
      by_cases hw : c.wl = []
      · exact ⟨c, hc, hw⟩
      · obtain ⟨hwl, _⟩ := reach_sim hinc hpreds hWF hn (reachK hinc hpreds hTopo hn hc)
        obtain ⟨c1, h1⟩ := rpSigrefKProgress lts inc preds hpreds c hwl hw
        exact ih c1 ⟨hc, h1⟩ (hc.tail h1)
  obtain ⟨c, hc, hw⟩ := key _ Relation.ReflTransGen.refl
  exact ⟨c, hc, hw, fun x y => rp_run_correct hn hinc hpreds hWF (reachK hinc hpreds hTopo hn hc) hw x y⟩

end RP

end Sigref
