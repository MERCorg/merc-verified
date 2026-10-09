import MercVerified.Refinement.Proofs.RustTools_Proofs
import MercVerified.Refinement.Proofs.MarkDirty_Proofs
import MercVerified.Refinement.Proofs.BranchingClosure_Proofs
import MercVerified.Lts.Proofs.IncomingTransitions_Proofs
import Sigref.Proofs.TopoSort_Proofs

/-!
# `sort_topological_hidden` is the abstract topological sort

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open MercVerified.Lts.Proofs MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

open Sigref.Topo

abbrev RMark := verified.merc_reduction.sort_topological.Mark

/-- The Rust mark `Temporary`. -/
abbrev rTemp : RMark := verified.merc_reduction.sort_topological.Mark.Temporary

/-- The Rust mark `Permanent`. -/
abbrev rPerm : RMark := verified.merc_reduction.sort_topological.Mark.Permanent

/-- The model mark of a Rust mark. -/
def mOf : Option RMark → Option Sigref.Topo.Mark
  | none => none
  | some .Temporary => some .temp
  | some .Permanent => some .perm

/-- The model marks of the Rust marks vector. -/
def mkOf {n : Nat} (ms : List (Option RMark)) : Fin n → Option Sigref.Topo.Mark :=
  fun i => mOf (ms.getD i.val none)

/-- The targets of the hidden transitions that are not self-loops, in order. -/
def hsucc {n : Nat} (hn0 : 0 < n) (s : Nat) (l : List Transition) : List (Fin n) :=
  l.filterMap fun t =>
    if t.to.index.val ≠ s ∧ t.label.index.val = 0 then some (toFin hn0 t.to) else none

theorem hsucc_cons {n : Nat} (hn0 : 0 < n) (s : Nat) (t : Transition) (l : List Transition) :
    hsucc hn0 s (t :: l) =
      if t.to.index.val ≠ s ∧ t.label.index.val = 0 then toFin hn0 t.to :: hsucc hn0 s l
      else hsucc hn0 s l := by
  unfold hsucc
  simp only [List.filterMap_cons]
  split_ifs <;> rfl

theorem toFin_val {n : Nat} (hn0 : 0 < n) (t : ST) (h : t.index.val < n) :
    (toFin hn0 t).val = t.index.val := Nat.mod_eq_of_lt h

open verified.merc_reduction.sort_topological in
theorem psl_unfold {L Label : Type} (LTSInst : LTS L Label) (sys : L) (state : ST)
    (marks : Slice (Option RMark)) (iter : alloc.vec.into_iter.IntoIter Transition)
    (D : alloc.vec.Vec ST) (a : Bool) :
    push_unvisited_successors_loop LTSInst iter sys state marks D a =
      (do
        let r ← push_unvisited_successors_loop.body LTSInst sys state marks iter D a
        match r with
        | cont x => push_unvisited_successors_loop LTSInst x.1 sys state marks x.2.1 x.2.2
        | done y => ok y) := by
  show loop _ (iter, D, a) = _
  rw [loop]
  simp only []
  congr 1
  funext r
  cases r with
  | cont x => obtain ⟨i, d, b⟩ := x; rfl
  | done y => rfl

open verified.merc_reduction.sort_topological in
theorem push_succ_loop {L Label : Type} (LTSInst : LTS L Label) (sys : L) {n : Nat} (hn0 : 0 < n)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (state : ST) (marks : Slice (Option RMark)) (hm : marks.val.length = n) :
    ∀ (l : List Transition), (∀ t ∈ l, t.to.index.val < n) →
      ∀ (iter : alloc.vec.into_iter.IntoIter Transition) (D : alloc.vec.Vec ST) (a : Bool)
        (DL : List (Fin n)), iter.val = l →
        D.val.map (fun t => t.index.val) = DL.reverse.map Fin.val →
        D.val.length + l.length ≤ Usize.max →
        ∃ D' b, push_unvisited_successors_loop LTSInst iter sys state marks D a = ok (b, D') ∧
          D'.val.map (fun t => t.index.val) =
            (pushSuccs (mkOf marks.val) (hsucc hn0 state.index.val l) DL a).1.reverse.map Fin.val ∧
          b = (pushSuccs (mkOf marks.val) (hsucc hn0 state.index.val l) DL a).2 := by
  intro l
  induction l with
  | nil =>
    intro _ iter D a DL hit hD _
    refine ⟨D, a, ?_, ?_, ?_⟩
    · rw [psl_unfold]
      unfold push_unvisited_successors_loop.body
      rw [into_iter_next_none' _ hit]
      simp
    · simp [hsucc, pushSuccs, hD]
    · simp [hsucc, pushSuccs]
  | cons t l' ih =>
    intro htg iter D a DL hit hD hroom
    obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' iter t l' hit
    have htn : t.to.index.val < n := htg t (by simp)
    have htg' : ∀ t' ∈ l', t'.to.index.val < n := fun t' h => htg t' (List.mem_cons_of_mem _ h)
    have hroom' : D.val.length + l'.length ≤ Usize.max := by simp at hroom; omega
    have hroom0 : D.val.length + l'.length + 1 ≤ Usize.max := by simp at hroom; omega
    by_cases hself : state.index.val ≠ t.to.index.val
    · by_cases hh : t.label.index.val = 0
      · -- a hidden, non-self transition
        have hsc : t.to.index.val ≠ state.index.val := fun e => hself e.symm
        have hmark : marks.val.getD (toFin hn0 t.to).val none = marks.val[t.to.index.val]'(by omega) := by
          rw [toFin_val hn0 t.to htn]
          exact List.getD_eq_getElem _ _ _
        have hidx := slice_tagged_index_ok marks t.to (by omega)
        cases hmk : marks.val[t.to.index.val]'(by omega) with
        | none =>
          obtain ⟨D1, hD1, hD1v⟩ := vec_push_val D t.to (by omega)
          have hbody : push_unvisited_successors_loop.body LTSInst sys state marks iter D a =
              ok (cont (it1, D1, a)) := by
            unfold push_unvisited_successors_loop.body
            rw [hnext]
            simp [tag_ne_ok, hid, hidx, hmk, hD1, hself, hh]
          rw [psl_unfold, hbody]; simp only [bind_ok]
          have := ih htg' it1 D1 a (toFin hn0 t.to :: DL) hit1 (by
            rw [hD1v]; simp [hD, toFin_val hn0 t.to htn]) (by rw [hD1v]; simp; omega)
          obtain ⟨D', b, hl, hv, hb⟩ := this
          refine ⟨D', b, hl, ?_, ?_⟩
          · rw [hv, hsucc_cons, if_pos ⟨hsc, hh⟩]
            have hm' : mkOf marks.val (toFin hn0 t.to) = none := by
              unfold mkOf mOf; rw [hmark, hmk]
            simp [pushSuccs, hm']
          · rw [hb, hsucc_cons, if_pos ⟨hsc, hh⟩]
            have hm' : mkOf marks.val (toFin hn0 t.to) = none := by
              unfold mkOf mOf; rw [hmark, hmk]
            simp [pushSuccs, hm']
        | some mk =>
          cases mk with
          | Temporary =>
            have hbody : push_unvisited_successors_loop.body LTSInst sys state marks iter D a =
                ok (cont (it1, D, false)) := by
              unfold push_unvisited_successors_loop.body
              rw [hnext]
              simp [tag_ne_ok, hid, hidx, hmk, hself, hh]
            rw [psl_unfold, hbody]; simp only [bind_ok]
            obtain ⟨D', b, hl, hv, hb⟩ := ih htg' it1 D false DL hit1 hD hroom'
            have hm' : mkOf marks.val (toFin hn0 t.to) = some Sigref.Topo.Mark.temp := by
              unfold mkOf mOf; rw [hmark, hmk]
            refine ⟨D', b, hl, ?_, ?_⟩
            · rw [hv, hsucc_cons, if_pos ⟨hsc, hh⟩]; simp [pushSuccs, hm']
            · rw [hb, hsucc_cons, if_pos ⟨hsc, hh⟩]; simp [pushSuccs, hm']
          | Permanent =>
            have hbody : push_unvisited_successors_loop.body LTSInst sys state marks iter D a =
                ok (cont (it1, D, a)) := by
              unfold push_unvisited_successors_loop.body
              rw [hnext]
              simp [tag_ne_ok, hid, hidx, hmk, hself, hh]
            rw [psl_unfold, hbody]; simp only [bind_ok]
            obtain ⟨D', b, hl, hv, hb⟩ := ih htg' it1 D a DL hit1 hD hroom'
            have hm' : mkOf marks.val (toFin hn0 t.to) = some Sigref.Topo.Mark.perm := by
              unfold mkOf mOf; rw [hmark, hmk]
            refine ⟨D', b, hl, ?_, ?_⟩
            · rw [hv, hsucc_cons, if_pos ⟨hsc, hh⟩]; simp [pushSuccs, hm']
            · rw [hb, hsucc_cons, if_pos ⟨hsc, hh⟩]; simp [pushSuccs, hm']
      · -- not hidden
        have hbody : push_unvisited_successors_loop.body LTSInst sys state marks iter D a =
            ok (cont (it1, D, a)) := by
          unfold push_unvisited_successors_loop.body
          rw [hnext]
          simp [tag_ne_ok, hid, hself, hh]
        rw [psl_unfold, hbody]; simp only [bind_ok]
        obtain ⟨D', b, hl, hv, hb⟩ := ih htg' it1 D a DL hit1 hD hroom'
        refine ⟨D', b, hl, ?_, ?_⟩
        · rw [hv, hsucc_cons, if_neg (fun h => hh h.2)]
        · rw [hb, hsucc_cons, if_neg (fun h => hh h.2)]
    · -- a self-loop
      have hbody : push_unvisited_successors_loop.body LTSInst sys state marks iter D a =
          ok (cont (it1, D, a)) := by
        unfold push_unvisited_successors_loop.body
        rw [hnext]
        simp [tag_ne_ok, hself]
      rw [psl_unfold, hbody]; simp only [bind_ok]
      obtain ⟨D', b, hl, hv, hb⟩ := ih htg' it1 D a DL hit1 hD hroom'
      have hsc : ¬ (t.to.index.val ≠ state.index.val ∧ t.label.index.val = 0) := by
        intro h; exact hself (fun e => h.1 e.symm)
      refine ⟨D', b, hl, ?_, ?_⟩
      · rw [hv, hsucc_cons, if_neg hsc]
      · rw [hb, hsucc_cons, if_neg hsc]

/-- The model graph of the LTS: the hidden non-self targets of a state. -/
noncomputable def tsucc {L Label : Type} (LTSInst : LTS L Label) (sys : L) {n : Nat} (hn0 : 0 < n)
    (s : Fin n) : List (Fin n) :=
  hsucc hn0 s.val (outVec LTSInst sys (stOf s)).val

theorem mkOf_set {n : Nat} (ms : List (Option RMark)) (hlen : ms.length = n) (x : Fin n)
    (v : Option RMark) :
    (mkOf (n := n) (ms.set x.val v)) = Function.update (mkOf (n := n) ms) x (mOf v) := by
  funext i
  unfold mkOf
  by_cases hi : i = x
  · subst hi
    have hi' : i.val < ms.length := by rw [hlen]; exact i.2
    simp [List.getD_eq_getElem?_getD, hi']
  · have hne : x.val ≠ i.val := fun e => hi (Fin.ext e.symm)
    simp [Function.update_of_ne hi, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

open verified.merc_reduction.sort_topological in
/-- `push_unvisited_successors` is the model's `pushSuccs` along the hidden non-self transitions. -/
theorem push_succ_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (x : Fin n0.val) (marks : Slice (Option RMark)) (hm : marks.val.length = n0.val)
    (D : alloc.vec.Vec ST) (DL : List (Fin n0.val))
    (hD : D.val.map (fun t => t.index.val) = DL.reverse.map Fin.val)
    (hroom : D.val.length + (outVec LTSInst sys (stOf x)).val.length ≤ Usize.max)
    (hnmax : n0.val ≤ Usize.max) :
    ∃ D' b, push_unvisited_successors LTSInst sys (stOf x) marks D = ok (b, D') ∧
      D'.val.map (fun t => t.index.val) =
        (pushSuccs (mkOf marks.val) (tsucc LTSInst sys hn0 x) DL true).1.reverse.map Fin.val ∧
      b = (pushSuccs (mkOf marks.val) (tsucc LTSInst sys hn0 x) DL true).2 := by
  have hxlt : (stOf x).index.val < n0.val := stOf_lt x hnmax
  obtain ⟨ts, hts, htg⟩ := hwf.2.1 n0 hns (stOf x) hxlt
  have hout := outVec_eq_ok LTSInst sys (stOf x) ts hts
  have hov := outVec_of_ok LTSInst sys (stOf x) ts hts
  unfold push_unvisited_successors
  rw [hout]
  simp only [bind_ok]
  have hiter : ∃ iter : alloc.vec.into_iter.IntoIter Transition,
      alloc.vec.IntoIteratorVec.into_iter (outVec LTSInst sys (stOf x)) = ok iter ∧
      iter.val = (outVec LTSInst sys (stOf x)).val := by
    exact ⟨_, rfl, rfl⟩
  obtain ⟨iter, hit, hitv⟩ := hiter
  rw [hit]
  simp only [bind_ok]
  have := push_succ_loop LTSInst sys hn0 hid (stOf x) marks hm (outVec LTSInst sys (stOf x)).val
    (by rw [hov]; exact htg) iter D true DL hitv hD hroom
  obtain ⟨D', b, hl, hv, hb⟩ := this
  have hsx : (stOf x).index.val = x.val := stOf_index x hnmax
  exact ⟨D', b, hl, by rw [hv, hsx]; rfl, by rw [hb, hsx]; rfl⟩

theorem pushSuccs_fst_acyc {n : Nat} (m : Fin n → Option Sigref.Topo.Mark) :
    ∀ (ts D : List (Fin n)) (a : Bool),
      (pushSuccs m ts D a).1 = (pushSuccs m ts D true).1 ∧
      (pushSuccs m ts D a).2 = (a && (pushSuccs m ts D true).2) := by
  intro ts
  induction ts with
  | nil => intro D a; simp [pushSuccs]
  | cons w ts ih =>
    intro D a
    cases hw : m w with
    | none => simp only [pushSuccs, hw]; exact ih _ _
    | some mk =>
      cases mk with
      | temp =>
        have h1 := ih D false
        simp only [pushSuccs, hw, true_and]
        rw [h1.2]; simp
      | perm => simp only [pushSuccs, hw]; exact ih _ _

section Visit

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

/-- The number of transitions of a state. -/
noncomputable def outLen {n : Nat} (u : Fin n) : Nat := (outVec LTSInst sys (stOf u)).val.length

/-- The total number of transitions of the `n` states. -/
noncomputable def Eout (n : Nat) : Nat := ∑ u : Fin n, outLen LTSInst sys u

/-- The transitions of the states that are not yet marked. -/
noncomputable def potSum {n : Nat} (m : Fin n → Option Sigref.Topo.Mark) : Nat :=
  ∑ u : Fin n, if m u = none then outLen LTSInst sys u else 0

theorem potSum_le {n : Nat} (m : Fin n → Option Sigref.Topo.Mark) :
    potSum LTSInst sys m ≤ Eout LTSInst sys n := by
  unfold potSum Eout
  apply Finset.sum_le_sum
  intro u _
  split_ifs <;> omega

theorem potSum_update_none {n : Nat} (m : Fin n → Option Sigref.Topo.Mark) (x : Fin n)
    (hx : m x = none) (mk : Sigref.Topo.Mark) :
    potSum LTSInst sys (Function.update m x (some mk)) + outLen LTSInst sys x =
      potSum LTSInst sys m := by
  unfold potSum
  have h1 : ∀ u ∈ Finset.univ.erase x,
      (if Function.update m x (some mk) u = none then outLen LTSInst sys u else 0) =
        (if m u = none then outLen LTSInst sys u else 0) := by
    intro u hu
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x),
    ← Finset.add_sum_erase _ (fun u => if m u = none then outLen LTSInst sys u else 0)
      (Finset.mem_univ x), Finset.sum_congr rfl h1]
  simp [hx]
  omega

theorem potSum_update_ne {n : Nat} (m : Fin n → Option Sigref.Topo.Mark) (x : Fin n)
    (hx : m x ≠ none) (mk : Sigref.Topo.Mark) :
    potSum LTSInst sys (Function.update m x (some mk)) = potSum LTSInst sys m := by
  unfold potSum
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u = x
  · subst hu; simp [hx]
  · rw [Function.update_of_ne hu]

end Visit

theorem fin_list_eq {n : Nat} (hn0 : 0 < n) :
    ∀ (D : List ST) (L : List (Fin n)), D.map (fun t => t.index.val) = L.map Fin.val →
      D.map (toFin hn0) = L := by
  intro D
  induction D with
  | nil => intro L h; cases L <;> simp_all
  | cons t D ih =>
    intro L h
    cases L with
    | nil => simp at h
    | cons w L =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨Fin.ext ?_, ih L h.2⟩
      have hw := w.2
      rw [← h.1] at hw
      rw [toFin_val hn0 t hw, h.1]

section Visit2

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

/-- The model configuration of the Rust state. -/
noncomputable def toCfg {n : Nat} (hn0 : 0 < n) (D : alloc.vec.Vec ST)
    (marks : alloc.vec.Vec (Option RMark)) (stack : alloc.vec.Vec ST) (acyc : Bool) (idx : Nat) :
    Cfg n where
  marks := mkOf marks.val
  depth := (D.val.map (toFin hn0)).reverse
  order := stack.val.map (toFin hn0)
  acyc := acyc
  idx := idx

/-- Well-formedness of the Rust state of the topological sort. -/
structure RI {n : Nat} (D : alloc.vec.Vec ST) (marks : alloc.vec.Vec (Option RMark))
    (stack : alloc.vec.Vec ST) : Prop where
  mlen : marks.val.length = n
  dlt : ∀ t ∈ D.val, t.index.val < n
  slt : ∀ t ∈ stack.val, t.index.val < n
  scount : stack.val.length =
    (Finset.univ.filter (fun u : Fin n => mkOf (n := n) marks.val u = some Sigref.Topo.Mark.perm)).card
  pot : D.val.length + potSum LTSInst sys (mkOf (n := n) marks.val) ≤ Eout LTSInst sys n + 1


open verified.merc_reduction.sort_topological in
theorem visit_body_done {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (D : alloc.vec.Vec ST) (marks : alloc.vec.Vec (Option RMark)) (stack : alloc.vec.Vec ST)
    (acyclic : Bool) (hD : D.val = []) :
    sort_topological_visit_hidden_loop.body LTSInst sys D marks stack acyclic =
      ok (done (acyclic, D, marks, stack)) := by
  unfold sort_topological_visit_hidden_loop.body
  rw [alloc.vec.Vec.pop_nil_spec Global D hD]
  simp

open verified.merc_reduction.sort_topological in
theorem visit_body_cont {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max) (hEout : Eout LTSInst sys n0.val + 1 ≤ Usize.max)
    (D : alloc.vec.Vec ST) (marks : alloc.vec.Vec (Option RMark)) (stack : alloc.vec.Vec ST)
    (acyclic : Bool) (idx : Nat) (hri : RI LTSInst sys (n := n0.val) D marks stack)
    (hD : D.val ≠ []) :
    ∃ D' marks' stack' acyc',
      sort_topological_visit_hidden_loop.body LTSInst sys D marks stack acyclic =
        ok (cont (D', marks', stack', acyc')) ∧
      RI LTSInst sys (n := n0.val) D' marks' stack' ∧
      Sigref.Topo.step (tsucc LTSInst sys hn0) (toCfg hn0 D marks stack acyclic idx) =
        some (toCfg hn0 D' marks' stack' acyc' idx) := by
  have hnmax : n0.val ≤ Usize.max := hnlt.le
  rcases List.eq_nil_or_concat D.val with hnil | ⟨rest, x, hrest⟩
  · exact absurd hnil hD
  rw [List.concat_eq_append] at hrest
  obtain ⟨D1, hpop, hD1v⟩ := alloc.vec.Vec.pop_cons_spec Global D x rest hrest
  have hxlt : x.index.val < n0.val := hri.dlt x (by rw [hrest]; simp)
  have hmx : x.index.val < marks.val.length := by rw [hri.mlen]; exact hxlt
  have hrestlt : ∀ t ∈ rest, t.index.val < n0.val := fun t ht =>
    hri.dlt t (by rw [hrest]; exact List.mem_append_left _ ht)
  set xf : Fin n0.val := toFin hn0 x with hxf
  have hxfv : xf.val = x.index.val := toFin_val hn0 x hxlt
  have hdepth : (D.val.map (toFin hn0)).reverse = xf :: (rest.map (toFin hn0)).reverse := by
    rw [hrest]; simp [xf]
  have hDlen : D.val.length = rest.length + 1 := by rw [hrest]; simp
  have hmark_xf : mkOf (n := n0.val) marks.val xf = mOf (marks.val[x.index.val]'hmx) := by
    unfold mkOf
    rw [hxfv]
    exact congrArg mOf (List.getD_eq_getElem _ _ _)
  have hread : verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice (Option RMark)) marks x =
      ok (marks.val[x.index.val]'hmx) :=
    vec_tagged_index_val marks x (by simpa [alloc.vec.Vec.length] using hmx)
  have hmut := vec_tagged_index_mut_ok marks x (by simpa using hmx)
  have hstx : stOf xf = x := by
    apply merc_utilities.tagged_index.TagIndex.ext
    apply UScalar.eq_of_val_eq
    rw [stOf_index xf hnmax, hxfv]
  set c0 := toCfg hn0 D marks stack acyclic idx with hc0
  have hc0d : c0.depth = xf :: (rest.map (toFin hn0)).reverse := hdepth
  rcases hmk : marks.val[x.index.val]'hmx with _ | mk
  · -- an unmarked state: expand it
    have hmod : c0.marks xf = none := by
      show mkOf marks.val xf = none
      rw [hmark_xf, hmk]; rfl
    have hstep := Sigref.Topo.step_none (tsucc LTSInst sys hn0) c0 xf _ hc0d hmod
    set marks1 : alloc.vec.Vec (Option RMark) :=
      ({ slice := marks.slice.set x.index (some rTemp) } : alloc.vec.Vec (Option RMark))
      with hm1
    have hm1v : marks1.val = marks.val.set x.index.val (some rTemp) := by
      simp [hm1, alloc.vec.Vec.val, Slice.set_val_eq]
    have hm1len : marks1.val.length = n0.val := by rw [hm1v]; simp [hri.mlen]
    have hD1len : D1.val.length = rest.length := by rw [hD1v]
    have hroom1 : D1.val.length < Usize.max := by
      have := hri.pot; omega
    obtain ⟨D2, hD2, hD2v⟩ := vec_push_val D1 x hroom1
    have hD2map : D2.val.map (fun t => t.index.val) =
        (xf :: (rest.map (toFin hn0)).reverse).reverse.map Fin.val := by
      rw [hD2v, hD1v]
      simp only [List.reverse_cons, List.reverse_reverse, List.map_append, List.map_cons,
        List.map_nil, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro t ht
        simp [toFin_val hn0 t (hrestlt t ht)]
      · simp [hxfv]
    have hD2len : D2.val.length = D.val.length := by rw [hD2v, hD1v, hrest]
    have hm0 : mkOf (n := n0.val) marks.val xf = none := by rw [hmark_xf, hmk]; rfl
    have hpot0 := potSum_update_none LTSInst sys (mkOf (n := n0.val) marks.val) xf hm0 Sigref.Topo.Mark.temp
    have hm1eq : mkOf (n := n0.val) marks1.val =
        Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.temp) := by
      rw [hm1v, ← hxfv, mkOf_set marks.val hri.mlen xf]
      rfl
    have hroom : D2.val.length + (outVec LTSInst sys (stOf xf)).val.length ≤ Usize.max := by
      have := hri.pot
      have h2 : outLen LTSInst sys xf = (outVec LTSInst sys (stOf xf)).val.length := rfl
      omega
    obtain ⟨D3, b, hp, hp1, hp2⟩ := push_succ_spec LTSInst sys hwf n0 hns hn0 hid xf
      (alloc.vec.Vec.deref marks1) (by simpa [alloc.vec.Vec.deref] using hm1len) D2 (xf :: (rest.map (toFin hn0)).reverse) hD2map hroom hnmax
    rw [hstx] at hp
    rw [vec_deref_val] at hp1 hp2
    have hp1' : D3.val.map (fun t => t.index.val) =
        (pushSuccs (mkOf (n := n0.val) marks1.val) (tsucc LTSInst sys hn0 xf)
          (xf :: (rest.map (toFin hn0)).reverse) true).1.reverse.map Fin.val := hp1
    have hp2' : b = (pushSuccs (mkOf (n := n0.val) marks1.val) (tsucc LTSInst sys hn0 xf)
          (xf :: (rest.map (toFin hn0)).reverse) true).2 := hp2
    rw [hm1eq] at hp1' hp2'
    have hbody : sort_topological_visit_hidden_loop.body LTSInst sys D marks stack acyclic =
        ok (cont (D3, marks1, stack, if b = true then acyclic else false)) := by
      unfold sort_topological_visit_hidden_loop.body
      rw [hpop]
      simp [hread, hmk, hmut, hD2]
      have hp' : push_unvisited_successors LTSInst sys x
          ({ slice := marks.slice.set x.index (some verified.merc_reduction.sort_topological.Mark.Temporary) }
            : alloc.vec.Vec (Option RMark)).deref D2 = ok (b, D3) := hp
      rw [hp']
      cases b <;> simp [hm1]
    have hlen3 : D3.val.length ≤ D.val.length + outLen LTSInst sys xf := by
      have h1 := congrArg List.length hp1'
      simp only [List.length_map, List.length_reverse] at h1
      have h2 := (pushSuccs_spec (Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.temp)) (tsucc LTSInst sys hn0 xf)
        (xf :: (rest.map (toFin hn0)).reverse) true).1
      have h3 : (tsucc LTSInst sys hn0 xf).length ≤ outLen LTSInst sys xf := by
        unfold tsucc hsucc outLen
        exact List.length_filterMap_le _ _
      rw [h2] at h1
      simp only [List.length_append, List.length_reverse, List.length_cons, List.length_map] at h1
      have h4 := List.length_filter_le (fun w => decide (Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.temp) w = none))
        (tsucc LTSInst sys hn0 xf)
      omega
    refine ⟨D3, marks1, stack, if b = true then acyclic else false, hbody, ?_, ?_⟩
    · refine ⟨hm1len, ?_, hri.slt, ?_, ?_⟩
      · intro t ht
        have h1 : t.index.val ∈ D3.val.map (fun t => t.index.val) := List.mem_map.mpr ⟨t, ht, rfl⟩
        rw [hp1'] at h1
        obtain ⟨w, _, hw⟩ := List.mem_map.mp h1
        rw [← hw]; exact w.2
      · rw [hm1eq]
        have hset : Finset.univ.filter (fun u : Fin n0.val =>
            Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.temp) u =
              some Sigref.Topo.Mark.perm) =
            Finset.univ.filter (fun u : Fin n0.val => mkOf (n := n0.val) marks.val u =
              some Sigref.Topo.Mark.perm) := by
          ext u
          by_cases hu : u = xf
          · subst hu; simp [hm0]
          · simp [Function.update_of_ne hu]
        rw [hset]; exact hri.scount
      · rw [hm1eq]
        have := hri.pot
        omega
    · rw [hstep]
      have hdepth3 : D3.val.map (toFin hn0) =
          (pushSuccs (Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.temp)) (tsucc LTSInst sys hn0 xf)
            (xf :: (rest.map (toFin hn0)).reverse) true).1.reverse := fin_list_eq hn0 _ _ hp1'
      have hfst := pushSuccs_fst_acyc
        (Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.temp))
        (tsucc LTSInst sys hn0 xf) (xf :: (rest.map (toFin hn0)).reverse) acyclic
      simp only [hc0, toCfg, Option.some.injEq, Sigref.Topo.Cfg.mk.injEq]
      refine ⟨hm1eq.symm, ?_, trivial, ?_, trivial⟩
      · rw [hdepth3, List.reverse_reverse]
        exact hfst.1
      · rw [hfst.2, hp2']
        cases hh : (pushSuccs (Function.update (mkOf (n := n0.val) marks.val) xf
          (some Sigref.Topo.Mark.temp)) (tsucc LTSInst sys hn0 xf)
          (xf :: (rest.map (toFin hn0)).reverse) true).2 <;> simp
  · have hD1len : D1.val.length = rest.length := by rw [hD1v]
    have hDsub : ∀ t ∈ D1.val, t.index.val < n0.val := fun t ht => hrestlt t (by rwa [hD1v] at ht)
    cases mk with
    | Temporary =>
      have hmod : c0.marks xf = some Sigref.Topo.Mark.temp := by
        show mkOf marks.val xf = _
        rw [hmark_xf, hmk]; rfl
      have hstep := Sigref.Topo.step_temp (tsucc LTSInst sys hn0) c0 xf _ hc0d hmod
      set marks1 : alloc.vec.Vec (Option RMark) :=
        ({ slice := marks.slice.set x.index (some rPerm) } : alloc.vec.Vec (Option RMark))
        with hm1
      have hm1v : marks1.val = marks.val.set x.index.val (some rPerm) := by
        simp [hm1, alloc.vec.Vec.val, Slice.set_val_eq]
      have hm1len : marks1.val.length = n0.val := by rw [hm1v]; simp [hri.mlen]
      have hscount_lt : stack.val.length < Usize.max := by
        have h1 : stack.val.length ≤ n0.val := by
          rw [hri.scount]
          calc _ ≤ (Finset.univ : Finset (Fin n0.val)).card := Finset.card_le_univ _
            _ = n0.val := by simp
        omega
      obtain ⟨stack1, hstk1, hstk1v⟩ := vec_push_val stack x hscount_lt
      have hm1eq : mkOf (n := n0.val) marks1.val =
          Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.perm) := by
        rw [hm1v, ← hxfv, mkOf_set marks.val hri.mlen xf]
        rfl
      have hbody : sort_topological_visit_hidden_loop.body LTSInst sys D marks stack acyclic =
          ok (cont (D1, marks1, stack1, acyclic)) := by
        unfold sort_topological_visit_hidden_loop.body
        rw [hpop]
        simp [hread, hmk, hmut, hstk1, hm1]
      refine ⟨D1, marks1, stack1, acyclic, hbody, ?_, ?_⟩
      · refine ⟨hm1len, hDsub, ?_, ?_, ?_⟩
        · intro t ht
          rw [hstk1v] at ht
          rcases List.mem_append.mp ht with h | h
          · exact hri.slt t h
          · simp at h; rw [h]; exact hxlt
        · rw [hm1eq, hstk1v]
          have hset : Finset.univ.filter (fun u : Fin n0.val =>
              Function.update (mkOf (n := n0.val) marks.val) xf (some Sigref.Topo.Mark.perm) u =
                some Sigref.Topo.Mark.perm) =
              insert xf (Finset.univ.filter (fun u : Fin n0.val => mkOf (n := n0.val) marks.val u =
                some Sigref.Topo.Mark.perm)) := by
            ext u
            by_cases hu : u = xf
            · subst hu; simp
            · simp [hu]
          have hmod' : mkOf (n := n0.val) marks.val xf = some Sigref.Topo.Mark.temp := hmod
          rw [hset, Finset.card_insert_of_notMem (by simp [hmod'])]
          simp [hri.scount]
        · rw [hm1eq, potSum_update_ne LTSInst sys _ xf (by rw [show mkOf (n := n0.val) marks.val xf = _ from hmod]; simp) Sigref.Topo.Mark.perm]
          have := hri.pot
          omega
      · rw [hstep]
        simp only [hc0, toCfg, Option.some.injEq, Sigref.Topo.Cfg.mk.injEq]
        refine ⟨hm1eq.symm, ?_, ?_, trivial, trivial⟩
        · rw [hD1v]
        · rw [hstk1v]; simp [hxf]
    | Permanent =>
      have hmod : c0.marks xf = some Sigref.Topo.Mark.perm := by
        show mkOf marks.val xf = _
        rw [hmark_xf, hmk]; rfl
      have hstep := Sigref.Topo.step_perm (tsucc LTSInst sys hn0) c0 xf _ hc0d hmod
      have hbody : sort_topological_visit_hidden_loop.body LTSInst sys D marks stack acyclic =
          ok (cont (D1, marks, stack, acyclic)) := by
        unfold sort_topological_visit_hidden_loop.body
        rw [hpop]
        simp [hread, hmk]
      refine ⟨D1, marks, stack, acyclic, hbody, ?_, ?_⟩
      · refine ⟨hri.mlen, hDsub, hri.slt, hri.scount, ?_⟩
        have := hri.pot
        omega
      · rw [hstep]
        simp only [hc0, toCfg, Option.some.injEq, Sigref.Topo.Cfg.mk.injEq]
        refine ⟨trivial, ?_, trivial, trivial, trivial⟩
        rw [hD1v]



open verified.merc_reduction.sort_topological in
theorem visit_loop_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max) (hEout : Eout LTSInst sys n0.val + 1 ≤ Usize.max)
    (D : alloc.vec.Vec ST) (marks : alloc.vec.Vec (Option RMark)) (stack : alloc.vec.Vec ST)
    (acyclic : Bool) (idx : Nat) (hri : RI LTSInst sys (n := n0.val) D marks stack) :
    ∃ D' marks' stack' acyc',
      sort_topological_visit_hidden_loop LTSInst D sys marks stack acyclic =
        ok (acyc', D', marks', stack') ∧
      RI LTSInst sys (n := n0.val) D' marks' stack' ∧ D'.val = [] ∧
      Sigref.Topo.Runs (tsucc LTSInst sys hn0) (toCfg hn0 D marks stack acyclic idx)
        (toCfg hn0 D' marks' stack' acyc' idx) := by
  unfold sort_topological_visit_hidden_loop
  have hspec : loop (fun x : alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST × Bool =>
        sort_topological_visit_hidden_loop.body LTSInst sys x.1 x.2.1 x.2.2.1 x.2.2.2)
      (D, marks, stack, acyclic)
      ⦃ fun r : Bool × alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST =>
        RI LTSInst sys (n := n0.val) r.2.1 r.2.2.1 r.2.2.2 ∧ r.2.1.val = [] ∧
        Sigref.Topo.Runs (tsucc LTSInst sys hn0) (toCfg hn0 D marks stack acyclic idx)
          (toCfg hn0 r.2.1 r.2.2.1 r.2.2.2 r.1 idx) ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST × Bool =>
        Sigref.Topo.measure (tsucc LTSInst sys hn0) (toCfg hn0 x.1 x.2.1 x.2.2.1 x.2.2.2 idx))
      (inv := fun x : alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST × Bool =>
        RI LTSInst sys (n := n0.val) x.1 x.2.1 x.2.2.1 ∧
        Sigref.Topo.Runs (tsucc LTSInst sys hn0) (toCfg hn0 D marks stack acyclic idx)
          (toCfg hn0 x.1 x.2.1 x.2.2.1 x.2.2.2 idx))
      (post := fun r : Bool × alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST =>
        RI LTSInst sys (n := n0.val) r.2.1 r.2.2.1 r.2.2.2 ∧ r.2.1.val = [] ∧
        Sigref.Topo.Runs (tsucc LTSInst sys hn0) (toCfg hn0 D marks stack acyclic idx)
          (toCfg hn0 r.2.1 r.2.2.1 r.2.2.2 r.1 idx))
      (body := fun x : alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST × Bool =>
        sort_topological_visit_hidden_loop.body LTSInst sys x.1 x.2.1 x.2.2.1 x.2.2.2)
      (x := (D, marks, stack, acyclic))
    · rintro ⟨D1, m1, s1, a1⟩ ⟨hri1, hr1⟩
      by_cases hD1 : D1.val = []
      · exact Std.WP.exists_imp_spec ⟨done (a1, D1, m1, s1), visit_body_done LTSInst sys D1 m1 s1 a1 hD1,
          hri1, hD1, hr1⟩
      · obtain ⟨D', m', s', a', hb, hri', hstep⟩ := visit_body_cont LTSInst sys hwf n0 hns hn0 hid hnlt
          hEout D1 m1 s1 a1 idx hri1 hD1
        refine Std.WP.exists_imp_spec ⟨cont (D', m', s', a'), hb, ⟨hri', ?_⟩, ?_⟩
        · exact hr1.tail hstep
        · exact Sigref.Topo.topoSortTerminates _ _ _ hstep
    · exact ⟨hri, Relation.ReflTransGen.refl⟩
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists hspec
  obtain ⟨a', D', m', s'⟩ := r
  exact ⟨D', m', s', a', hr, hpost⟩


open verified.merc_reduction.sort_topological in
theorem visit_hidden_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max) (hEout : Eout LTSInst sys n0.val + 1 ≤ Usize.max)
    (state : ST) (hst : state.index.val < n0.val)
    (D : alloc.vec.Vec ST) (hD : D.val = []) (marks : alloc.vec.Vec (Option RMark))
    (stack : alloc.vec.Vec ST) (idx : Nat) (hri : RI LTSInst sys (n := n0.val) D marks stack) :
    ∃ D1 b D' marks' stack',
      D1.val = [state] ∧
      sort_topological_visit_hidden LTSInst sys state D marks stack = ok (b, D', marks', stack') ∧
      RI LTSInst sys (n := n0.val) D' marks' stack' ∧ D'.val = [] ∧
      Sigref.Topo.Runs (tsucc LTSInst sys hn0) (toCfg hn0 D1 marks stack true idx)
        (toCfg hn0 D' marks' stack' b idx) := by
  unfold sort_topological_visit_hidden
  obtain ⟨D1, hD1, hD1v⟩ := vec_push_val D state (by rw [hD]; simp; omega)
  have hD1v' : D1.val = [state] := by rw [hD1v, hD]; rfl
  have hri1 : RI LTSInst sys (n := n0.val) D1 marks stack := by
    refine ⟨hri.mlen, ?_, hri.slt, hri.scount, ?_⟩
    · intro t ht; rw [hD1v'] at ht; simp at ht; rw [ht]; exact hst
    · rw [hD1v']
      have := potSum_le LTSInst sys (mkOf (n := n0.val) marks.val)
      simp only [List.length_singleton]
      omega
  obtain ⟨D', m', s', a', hl, hri', hD', hruns⟩ := visit_loop_spec LTSInst sys hwf n0 hns hn0 hid hnlt
    hEout D1 marks stack true idx hri1
  refine ⟨D1, a', D', m', s', hD1v', ?_, hri', hD', hruns⟩
  rw [hD1]
  simp only [bind_ok]
  rw [hl]


open verified.merc_reduction.sort_topological in
theorem visit_all_loop_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max) (hEout : Eout LTSInst sys n0.val + 1 ≤ Usize.max)
    (hA : Sigref.Topo.Acyclic (tsucc LTSInst sys hn0))
    (D : alloc.vec.Vec ST) (hD : D.val = []) (marks : alloc.vec.Vec (Option RMark))
    (stack : alloc.vec.Vec ST) (hri : RI LTSInst sys (n := n0.val) D marks stack)
    (hinit : toCfg hn0 D marks stack true 0 = Sigref.Topo.init n0.val) :
    ∃ b D' marks' stack' c,
      sort_topological_visit_all_loop LTSInst { start := 0#usize, «end» := n0 } sys D marks stack true =
        ok (b, D', marks', stack') ∧
      RI LTSInst sys (n := n0.val) D' marks' stack' ∧ D'.val = [] ∧
      Sigref.Topo.Root (tsucc LTSInst sys hn0) c ∧ c.idx = n0.val ∧
      Sigref.Topo.Runs (tsucc LTSInst sys hn0) (Sigref.Topo.init n0.val) c ∧
      toCfg hn0 D' marks' stack' b n0.val = c := by
  unfold sort_topological_visit_all_loop
  have hspec := range_loop_spec
    (σ := alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST × Bool)
    (ρ := Bool × alloc.vec.Vec ST × alloc.vec.Vec (Option RMark) × alloc.vec.Vec ST)
    (fun x => sort_topological_visit_all_loop.body LTSInst sys x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun i s => ∃ c, Sigref.Topo.Root (tsucc LTSInst sys hn0) c ∧ c.idx = i ∧
      Sigref.Topo.Runs (tsucc LTSInst sys hn0) (Sigref.Topo.init n0.val) c ∧
      RI LTSInst sys (n := n0.val) s.1 s.2.1 s.2.2.1 ∧ s.1.val = [] ∧
      toCfg hn0 s.1 s.2.1 s.2.2.1 s.2.2.2 i = c)
    (fun r => ∃ c, Sigref.Topo.Root (tsucc LTSInst sys hn0) c ∧ c.idx = n0.val ∧
      Sigref.Topo.Runs (tsucc LTSInst sys hn0) (Sigref.Topo.init n0.val) c ∧
      RI LTSInst sys (n := n0.val) r.2.1 r.2.2.1 r.2.2.2 ∧ r.2.1.val = [] ∧
      toCfg hn0 r.2.1 r.2.2.1 r.2.2.2 r.1 n0.val = c)
    n0 ?hsome ?hnone 0#usize (D, marks, stack, true) (by simp) ?h0
  case h0 =>
    exact ⟨Sigref.Topo.init n0.val, Sigref.Topo.root_init _, rfl, Relation.ReflTransGen.refl, hri,
      hD, hinit⟩
  case hnone =>
    intro i s hi hinv
    obtain ⟨c, hroot, hci, hruns, hri', hD', hc⟩ := hinv
    obtain ⟨Ds, ms, ss, ac⟩ := s
    refine ⟨(ac, Ds, ms, ss), ?_, ?_⟩
    · -- the iterator is exhausted
      obtain ⟨o, it1, hnext, hone, hident⟩ := MercVerified.Lts.Proofs.next_range_none
        ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) (by simpa using hi.ge)
      unfold sort_topological_visit_all_loop.body
      rw [hnext, hone]
      simp
    · refine ⟨c, hroot, ?_, hruns, hri', hD', ?_⟩
      · rw [hci, hi]
      · rw [← hc, hi]
  case hsome =>
    intro i s hi hinv
    obtain ⟨c, hroot, hci, hruns, hri', hD', hc⟩ := hinv
    obtain ⟨Ds, ms, ss, ac⟩ := s
    simp only at hri' hD' hc
    have hi' : i.val < n0.val := hi
    have hsucc_eq := Sigref.Topo.root_step hA hroot (by rw [hci]; exact hi')
    obtain ⟨c2, hrc2, hroot2, hidx2⟩ := hsucc_eq
    obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some
      ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) (by simpa using hi)
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := n0 } := by rw [he1]
    rw [hit1] at hnext
    have hacyc : ac = true := by
      have h1 : c.acyc = ac := by rw [← hc]; rfl
      rw [← h1]; exact hroot.acyc
    have hcd : c.depth = [] := hroot.depth
    have hmlen : ms.val.length = n0.val := hri'.mlen
    have hmi : i.val < ms.val.length := by rw [hmlen]; exact hi'
    set st : ST := ({ index := i, marker := () } : TagIndex Std.Usize StateTag) with hst
    have hnew : verified.merc_utilities.tagged_index.TagIndex.new StateTag i = ok st := by simp [hst]
    have hstidx : st.index = i := by rw [hst]
    clear_value st
    have hread : verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
        (core.slice.index.SliceIndexUsizeSlice (Option RMark)) ms st =
        ok (ms.val[i.val]'hmi) := by
      rw [vec_tagged_index_val ms st (by rw [hstidx]; simpa [alloc.vec.Vec.length] using hmi)]
      congr 1
      simp [hstidx, alloc.vec.Vec.val]
    have hcmarks : c.marks ⟨i.val, hi'⟩ = mOf (ms.val[i.val]'hmi) := by
      rw [← hc]
      show mkOf ms.val ⟨i.val, hi'⟩ = _
      unfold mkOf
      exact congrArg mOf (List.getD_eq_getElem _ _ _)
    have hcidx : c.idx = i.val := hci
    subst hacyc
    have hcm : c.marks = mkOf ms.val := by rw [← hc]; rfl
    have hcord : c.order = ss.val.map (toFin hn0) := by rw [← hc]; rfl
    have hcN : c.idx < n0.val := by rw [hcidx]; exact hi'
    have hfin : (⟨c.idx, hcN⟩ : Fin n0.val) = ⟨i.val, hi'⟩ := Fin.ext hcidx
    have hstfin : toFin hn0 st = ⟨i.val, hi'⟩ := by
      apply Fin.ext
      show st.index.val % n0.val = i.val
      rw [hstidx]; exact Nat.mod_eq_of_lt hi'
    rcases hmk : ms.val[i.val]'hmi with _ | mk
    · -- an unvisited state: visit it
      have hmod : c.marks ⟨c.idx, hcN⟩ = none := by rw [hfin, hcmarks, hmk]; rfl
      have hc1 := Sigref.Topo.step_root (tsucc LTSInst sys hn0) c hcd hcN hmod
      have hstlt : st.index.val < n0.val := by rw [hstidx]; exact hi'
      obtain ⟨D1, b, D', m', s', hD1v, hvis, hri'', hD'', hruns''⟩ := visit_hidden_spec LTSInst sys hwf
        n0 hns hn0 hid hnlt hEout st hstlt Ds hD' ms ss (i.val + 1) hri'
      have hc1eq : toCfg hn0 D1 ms ss true (i.val + 1) =
          { c with depth := [⟨c.idx, hcN⟩], idx := c.idx + 1 } := by
        simp only [toCfg, hD1v, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
          List.nil_append, hstfin, Sigref.Topo.Cfg.mk.injEq]
        refine ⟨hcm.symm, ?_, hcord.symm, hroot.acyc.symm, by rw [hcidx]⟩
        rw [hfin]
      have hr3 : Sigref.Topo.Runs (tsucc LTSInst sys hn0) c (toCfg hn0 D' m' s' b (i.val + 1)) := by
        rw [hc1eq] at hruns''
        exact Relation.ReflTransGen.head hc1 hruns''
      have hdeq : c2 = toCfg hn0 D' m' s' b (i.val + 1) := by
        apply Sigref.Topo.unique_empty hrc2 hr3 hroot2.depth
        · simp [toCfg, hD'']
        · simp [toCfg, hidx2, hcidx]
      have hb : b = true := by
        have := hroot2.acyc
        rw [hdeq] at this
        exact this
      have hbody : sort_topological_visit_all_loop.body LTSInst sys
          ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) Ds ms ss true =
          ok (cont ({ start := st1, «end» := n0 }, D', m', s', true)) := by
        unfold sort_topological_visit_all_loop.body
        rw [hnext, hsome]
        subst hst
        simp [hread, hmk, hvis, hb]
      refine ⟨st1, (D', m', s', true), hs1, hbody, c2, hroot2, hidx2.trans (by rw [hcidx]), ?_, hri'', hD'', ?_⟩
      · exact hruns.trans hrc2
      · rw [hdeq, ← hb]
    · -- an already visited state
      have hmod : c.marks ⟨c.idx, hcN⟩ ≠ none := by
        rw [hfin, hcmarks, hmk]; cases mk <;> simp [mOf]
      have hc1 := Sigref.Topo.step_root_marked (tsucc LTSInst sys hn0) c hcd hcN hmod
      have hdeq : c2 = { c with idx := c.idx + 1 } := by
        apply Sigref.Topo.unique_empty hrc2 (Relation.ReflTransGen.head hc1 Relation.ReflTransGen.refl)
          hroot2.depth hcd
        simp [hidx2]
      have hbody : sort_topological_visit_all_loop.body LTSInst sys
          ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) Ds ms ss true =
          ok (cont ({ start := st1, «end» := n0 }, Ds, ms, ss, true)) := by
        unfold sort_topological_visit_all_loop.body
        rw [hnext, hsome]
        subst hst
        simp [hread, hmk]
      refine ⟨st1, (Ds, ms, ss, true), hs1, hbody, c2, hroot2, hidx2.trans (by rw [hcidx]), ?_, hri', hD', ?_⟩
      · exact hruns.trans hrc2
      · rw [hdeq]
        simp only [toCfg, Sigref.Topo.Cfg.mk.injEq]
        refine ⟨hcm.symm, ?_, hcord.symm, hroot.acyc.symm, by rw [hcidx]⟩
        rw [← hc]; rfl
  obtain ⟨r, hr, c, hroot, hidx, hruns, hri', hD', htc⟩ := hspec
  obtain ⟨b, D', m', s'⟩ := r
  exact ⟨b, D', m', s', c, hr, hri', hD', hroot, hidx, hruns, htc⟩


open verified.merc_reduction.sort_topological in
theorem marks_init_spec (n0 : Std.Usize) (hnlt : n0.val < Usize.max) :
    ∃ marks, sort_topological_hidden_loop { start := 0#usize, «end» := n0 }
        (alloc.vec.Vec.new (Option RMark)) = ok marks ∧
      marks.val = List.replicate n0.val none := by
  unfold sort_topological_hidden_loop
  have := range_loop_spec
    (σ := alloc.vec.Vec (Option RMark)) (ρ := alloc.vec.Vec (Option RMark))
    (fun x => sort_topological_hidden_loop.body x.1 x.2) (fun i m => m.val = List.replicate i none)
    (fun r => r.val = List.replicate n0.val none) n0 ?hsome ?hnone 0#usize
    (alloc.vec.Vec.new (Option RMark)) (by simp) (by simp [alloc.vec.Vec.new])
  case hsome =>
    intro i m hi hm
    obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some
      ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) (by simpa using hi)
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := n0 } := by rw [he1]
    rw [hit1] at hnext
    obtain ⟨m1, hm1, hm1v⟩ := vec_push_val m none (by rw [hm]; simp; omega)
    refine ⟨st1, m1, hs1, ?_, ?_⟩
    · unfold sort_topological_hidden_loop.body
      rw [hnext, hsome]
      simp [hm1]
    · rw [hm1v, hm]
      simp [List.replicate_succ']
  case hnone =>
    intro i m hi hm
    obtain ⟨o, it1, hnext, hone, hident⟩ := MercVerified.Lts.Proofs.next_range_none
      ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) (by simp [hi])
    refine ⟨m, ?_, ?_⟩
    · unfold sort_topological_hidden_loop.body
      rw [hnext, hone]
      simp
    · rw [hm, hi]
  obtain ⟨r, hr, hp⟩ := this
  exact ⟨r, hr, hp⟩


open verified.merc_reduction.sort_topological in
theorem order_to_permutation_spec (order : Slice ST) (n : Nat) (hlen : order.val.length = n)
    (_hnlt : n < Usize.max) (hlt : ∀ t ∈ order.val, t.index.val < n)
    (hnd : (order.val.map (fun t => t.index.val)).Nodup) :
    ∃ perm : alloc.vec.Vec ST, order_to_permutation order = ok perm ∧ perm.val.length = n ∧
      ∀ p (hp : p < n), ∃ h : (order.val[p]'(by omega)).index.val < perm.val.length,
        (perm.val[(order.val[p]'(by omega)).index.val]'h).index.val = p := by
  unfold order_to_permutation
  have hcl : ∀ x : ST, (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone StateTag
      core.clone.CloneUsize).clone x = ok x := by
    intro x
    simp [verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone.clone]
  have hnew0 : verified.merc_utilities.tagged_index.TagIndex.new StateTag 0#usize =
      ok ({ index := 0#usize, marker := () } : ST) := by simp
  obtain ⟨reorder, hre, hrev, hrel⟩ := spec_imp_exists (alloc.vec.from_elem_spec
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone StateTag core.clone.CloneUsize)
    ({ index := 0#usize, marker := () } : ST) (Slice.len order) (hcl _))
  have hSlen : (Slice.len order).val = n := by simpa [Slice.len] using hlen
  rw [hnew0]
  simp only [bind_ok]
  rw [hre]
  simp only [bind_ok]
  have hrelen : reorder.val.length = n := by rw [hrev]; simp [hSlen]
  unfold order_to_permutation_loop
  have key := range_loop_spec
    (σ := alloc.vec.Vec ST) (ρ := alloc.vec.Vec ST)
    (fun x => order_to_permutation_loop.body order x.1 x.2)
    (fun m r => r.val.length = n ∧ ∀ q (hq : q < m) (hqn : q < n),
      ∃ h : (order.val[q]'(by omega)).index.val < r.val.length,
        (r.val[(order.val[q]'(by omega)).index.val]'h).index.val = q)
    (fun r => r.val.length = n ∧ ∀ q (hq : q < n),
      ∃ h : (order.val[q]'(by omega)).index.val < r.val.length,
        (r.val[(order.val[q]'(by omega)).index.val]'h).index.val = q)
    (Slice.len order) ?hsome ?hnone 0#usize reorder (by simp) ⟨hrelen, by intro q hq hqn; simp at hq⟩
  case hsome =>
    intro i m hi hm
    have hiN : i.val < n := by omega
    obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some
      ({ start := i, «end» := Slice.len order } : core.ops.range.Range Std.Usize) (by simpa using hi)
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := Slice.len order } := by rw [he1]
    rw [hit1] at hnext
    have hiO : i.val < order.val.length := by omega
    obtain ⟨ti1, hti1e, hti1'⟩ := spec_imp_exists (Slice.index_usize_spec order i hiO)
    have hj : (order.val[i.val]'hiO).index.val < m.val.length := by
      rw [hm.1]; exact hlt _ (List.getElem_mem hiO)
    have hmut := vec_index_mut_ok m (order.val[i.val]'hiO).index hj
    set m1 : alloc.vec.Vec ST :=
      ({ slice := m.slice.set (order.val[i.val]'hiO).index ({ index := i, marker := () } : ST) } :
        alloc.vec.Vec ST) with hm1
    have hm1v : m1.val = m.val.set (order.val[i.val]'hiO).index.val ({ index := i, marker := () } : ST) := by
      simp [hm1, alloc.vec.Vec.val, Slice.set_val_eq]
    have hm1len : m1.val.length = n := by rw [hm1v]; simp [hm.1]
    refine ⟨st1, m1, hs1, ?_, hm1len, ?_⟩
    · unfold order_to_permutation_loop.body
      rw [hnext, hsome]
      have hnewi : verified.merc_utilities.tagged_index.TagIndex.new StateTag i =
          ok ({ index := i, marker := () } : ST) := by simp
      simp only [bind_ok]
      show (do
        let ti ← verified.merc_utilities.tagged_index.TagIndex.new StateTag i
        let ti1 ← order.index_usize i
        let i' ← verified.merc_utilities.tagged_index.TagIndex.value core.marker.CopyUsize ti1
        let (_, index_mut_back) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice ST) m i'
        ok (cont (({ start := st1, «end» := Slice.len order } : core.ops.range.Range Std.Usize),
          index_mut_back ti))) = _
      rw [hnewi]
      simp only
      rw [hti1e]
      simp only [verified.merc_utilities.tagged_index.TagIndex.value]
      subst hti1'
      simp only [bind_tc_ok]
      rw [hmut]
      simp [hm1]
    · intro q hq hqn
      have hqO : q < order.val.length := by omega
      have hjm : (order.val[q]'hqO).index.val < m1.val.length := by
        rw [hm1len]; exact hlt _ (List.getElem_mem hqO)
      refine ⟨hjm, ?_⟩
      by_cases hqi : q = i.val
      · subst hqi
        simp only [hm1v]
        rw [List.getElem_set_self]
      · have hlt' : q < i.val := by omega
        have hne : (order.val[q]'hqO).index.val ≠ (order.val[i.val]'hiO).index.val := by
          intro h
          have hmq : q < (order.val.map (fun t => t.index.val)).length := by simpa using hqO
          have hmi : i.val < (order.val.map (fun t => t.index.val)).length := by simpa using hiO
          have := (List.Nodup.getElem_inj_iff hnd (hi := hmq) (hj := hmi)).1 (by simpa using h)
          exact hqi this
        obtain ⟨h0, h1⟩ := hm.2 q hlt' hqn
        simp only [hm1v]
        rw [List.getElem_set_ne (Ne.symm hne)]
        exact h1
  case hnone =>
    intro i m hi hm
    obtain ⟨o, it1, hnext, hone, hident⟩ := MercVerified.Lts.Proofs.next_range_none
      ({ start := i, «end» := Slice.len order } : core.ops.range.Range Std.Usize) (by simp [hi])
    refine ⟨m, ?_, hm.1, ?_⟩
    · unfold order_to_permutation_loop.body
      rw [hnext, hone]
      simp
    · intro q hq
      exact hm.2 q (by rw [hSlen] at hi; omega) hq
  obtain ⟨r, hr, hp⟩ := key
  exact ⟨r, hr, hp.1, hp.2⟩


open verified.merc_reduction.sort_topological in
/-- **`sort_topological_hidden` returns a reverse topological permutation** of the states along the
hidden transitions, when these have no cycle (self-loops are ignored). -/
theorem sort_topological_hidden_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max) (hEout : Eout LTSInst sys n0.val + 1 ≤ Usize.max)
    (hA : Sigref.Topo.Acyclic (tsucc LTSInst sys hn0)) :
    ∃ perm : alloc.vec.Vec ST, sort_topological_hidden LTSInst sys = ok (some perm) ∧
      perm.val.length = n0.val ∧
      (∀ s (hs : s < perm.val.length), (perm.val[s]'hs).index.val < n0.val) ∧
      (∀ s t (hs : s < perm.val.length) (ht : t < perm.val.length),
        (perm.val[s]'hs).index.val = (perm.val[t]'ht).index.val → s = t) ∧
      (∀ (a b : Fin n0.val), b ∈ tsucc LTSInst sys hn0 a →
        ∃ (ha : a.val < perm.val.length) (hb : b.val < perm.val.length),
          (perm.val[b.val]'hb).index.val < (perm.val[a.val]'ha).index.val) := by
  unfold sort_topological_hidden
  rw [hns]
  simp only [bind_ok]
  obtain ⟨marks, hmarks, hmv⟩ := marks_init_spec n0 hnlt
  rw [hmarks]
  simp only [bind_ok]
  unfold sort_topological_visit_all
  rw [hns]
  simp only [bind_ok]
  have hnone : ∀ u : Fin n0.val, mkOf (n := n0.val) marks.val u = none := by
    intro u; unfold mkOf; rw [hmv]; simp [mOf]
  have hri0 : RI LTSInst sys (n := n0.val) (alloc.vec.Vec.new ST) marks (alloc.vec.Vec.new ST) := by
    refine ⟨by rw [hmv]; simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new], ?_, ?_⟩
    · simp [alloc.vec.Vec.new, hnone]
    · have := potSum_le LTSInst sys (mkOf (n := n0.val) marks.val)
      simp [alloc.vec.Vec.new]
      omega
  have hinit0 : toCfg hn0 (alloc.vec.Vec.new ST) marks (alloc.vec.Vec.new ST) true 0 =
      Sigref.Topo.init n0.val := by
    have hnv : (alloc.vec.Vec.new ST).val = [] := rfl
    unfold toCfg Sigref.Topo.init
    rw [hnv]
    simp only [List.map_nil, List.reverse_nil, Sigref.Topo.Cfg.mk.injEq]
    refine ⟨?_, trivial, trivial, trivial, trivial⟩
    funext u; exact hnone u
  obtain ⟨b, D', m', s', c, hl, hri', hD', hroot, hidx, hruns, htc⟩ := visit_all_loop_spec LTSInst sys
    hwf n0 hns hn0 hid hnlt hEout hA (alloc.vec.Vec.new ST) rfl marks (alloc.vec.Vec.new ST) hri0 hinit0
  rw [hl]
  simp only [bind_ok]
  have hbtrue : b = true := by
    have := hroot.acyc
    rw [← htc] at this
    exact this
  subst hbtrue
  have hstep : Sigref.Topo.step (tsucc LTSInst sys hn0) c = none :=
    Sigref.Topo.step_end _ c hroot.depth (by omega)
  obtain ⟨_, hnd, hall, hclosed⟩ := Sigref.Topo.topoSortCorrect (tsucc LTSInst sys hn0) hA c hruns hstep
  have hord : c.order = s'.val.map (toFin hn0) := by rw [← htc]; rfl
  have hslt := hri'.slt
  have hvals : ∀ t ∈ s'.val, (toFin hn0 t).val = t.index.val := fun t ht => toFin_val hn0 t (hslt t ht)
  have hndv : (s'.val.map (fun t => t.index.val)).Nodup := by
    have h1 : (c.order.map Fin.val).Nodup := hnd.map Fin.val_injective
    rw [hord, List.map_map] at h1
    have : s'.val.map (Fin.val ∘ toFin hn0) = s'.val.map (fun t => t.index.val) :=
      List.map_congr_left (fun t ht => hvals t ht)
    rw [this] at h1
    exact h1
  have hlen : s'.val.length = n0.val := by
    have h2 : c.order.length = n0.val := by
      have := List.toFinset_card_of_nodup hnd
      have hu : c.order.toFinset = Finset.univ := by
        ext v; simp [hall v]
      rw [hu] at this
      simpa using this.symm
    rw [hord] at h2; simpa using h2
  obtain ⟨perm, hperm, hplen, hp⟩ := order_to_permutation_spec (alloc.vec.Vec.deref s') n0.val
    (by simpa [alloc.vec.Vec.deref] using hlen) hnlt (fun t ht => hslt t (by simpa [vec_deref_val] using ht)) (by simpa [alloc.vec.Vec.deref] using hndv)
  have hp' : ∀ p (hpl : p < s'.val.length), ∃ h : (s'.val[p]'hpl).index.val < perm.val.length,
      (perm.val[(s'.val[p]'hpl).index.val]'h).index.val = p := by
    intro p hpl
    have := hp p (by omega)
    simpa [vec_deref_val] using this
  have hclen : c.order.length = n0.val := by rw [hord]; simpa using hlen
  have hget : ∀ p (hpc : p < c.order.length) (hps : p < s'.val.length),
      (c.order[p]'hpc).val = (s'.val[p]'hps).index.val := by
    intro p hpc hps
    simp only [hord, List.getElem_map]
    exact toFin_val hn0 _ (hslt _ (List.getElem_mem _))
  have hpos : ∀ s (hs : s < n0.val), ∃ p, ∃ hpc : p < c.order.length, ∃ hps : p < s'.val.length,
      (s'.val[p]'hps).index.val = s := by
    intro s hs
    obtain ⟨p, hpc, hpe⟩ := List.mem_iff_getElem.mp (hall ⟨s, hs⟩)
    have hps : p < s'.val.length := by omega
    exact ⟨p, hpc, hps, by rw [← hget p hpc hps, hpe]⟩
  have hval : ∀ s (hs : s < perm.val.length), ∃ p, ∃ hps : p < s'.val.length,
      (s'.val[p]'hps).index.val = s ∧ (perm.val[s]'hs).index.val = p := by
    intro s hs
    obtain ⟨p, hpc, hps, hpe⟩ := hpos s (by omega)
    obtain ⟨h, hh⟩ := hp' p hps
    refine ⟨p, hps, hpe, ?_⟩
    simpa [hpe] using hh
  refine ⟨perm, ?_, hplen, ?_, ?_, ?_⟩
  · simp [hperm]
  · intro s hs
    obtain ⟨p, hps, _, hq⟩ := hval s hs
    rw [hq]; omega
  · intro s t hs ht heq
    obtain ⟨p, hps, hpe, hq⟩ := hval s hs
    obtain ⟨p', hps', hpe', hq'⟩ := hval t ht
    have : p = p' := by rw [← hq, ← hq', heq]
    subst this
    omega
  · intro a b hb
    have hamem := hall a
    obtain ⟨pa, hpa, hpae⟩ := List.mem_iff_getElem.mp hamem
    have hsplit : c.order = c.order.take pa ++ a :: c.order.drop (pa + 1) := by
      conv_lhs => rw [← List.take_append_drop pa c.order]
      rw [List.drop_eq_getElem_cons hpa, hpae]
    have hbm := hclosed _ a _ hsplit b hb
    obtain ⟨qb, hqb, hqbe⟩ := List.mem_iff_getElem.mp hbm
    simp only [List.length_take, List.getElem_take] at hqbe hqb
    have hqb' : qb < pa := by omega
    have hpas : pa < s'.val.length := by omega
    have hqbs : qb < s'.val.length := by omega
    have hbval : (s'.val[qb]'hqbs).index.val = b.val := by
      rw [← hget qb (by omega) hqbs]; simp [hqbe]
    have haval : (s'.val[pa]'hpas).index.val = a.val := by
      rw [← hget pa hpa hpas, hpae]
    obtain ⟨hlb, hb2⟩ := hp' qb hqbs
    obtain ⟨hla, ha2⟩ := hp' pa hpas
    refine ⟨by omega, by omega, ?_⟩
    simp only [hbval] at hb2
    simp only [haval] at ha2
    rw [hb2, ha2]
    exact hqb'

end Visit2

end MercVerified.Refinement.Proofs
