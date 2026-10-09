import MercVerified.Refinement.Proofs.TopoSortRust_Proofs
import Sigref.Proofs.TarjanBounds_Proofs

/-!
# `tau_scc_decomposition_iterative` is the abstract Tarjan search

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open MercVerified.Lts.Proofs MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

abbrev SC := verified.merc_reduction.scc_decomposition.SccContext

/-- The function on `Fin n` that a vector represents. -/
def view {α β : Type} (n : Nat) (f : α → β) (d : β) (l : List α) : Fin n → β :=
  fun i => (l[i.val]?.map f).getD d

theorem view_set {α β : Type} {n : Nat} (f : α → β) (d : β) (l : List α) (i : Fin n)
    (hi : i.val < l.length) (x : α) :
    view n f d (l.set i.val x) = Function.update (view n f d l) i (f x) := by
  funext j
  unfold view
  by_cases hj : j = i
  · subst hj; simp [hi]
  · have : j.val ≠ i.val := fun e => hj (Fin.ext e)
    rw [Function.update_of_ne hj]
    simp [this]

theorem view_get {α β : Type} {n : Nat} (f : α → β) (d : β) (l : List α) (i : Fin n)
    (hi : i.val < l.length) : view n f d l i = f (l[i.val]'hi) := by
  simp [view, hi]

/-- The Rust context represents the model context. -/
structure SR (n : Nat) (ctx : SC) (c : Sigref.Tarjan.Ctx n) : Prop where
  llen : ctx.low.val.length = n
  dlen : ctx.disc.val.length = n
  olen : ctx.on_scc_stack.val.length = n
  plen : ctx.partition.partition.val.length = n
  low : view n (fun u : Std.Usize => u.val) 0 ctx.low.val = c.low
  disc : view n (fun u : Std.Usize => u.val) 0 ctx.disc.val = c.disc
  onSt : view n (fun b : Bool => b) false ctx.on_scc_stack.val = c.onSt
  blk : view n (fun t : TagIndex Std.Usize verified.merc_collections.indexed_partition.BlockTag =>
    t.index.val) 0 ctx.partition.partition.val = c.blk
  nb : ctx.partition.num_of_blocks.val = max 1 c.eq
  stk : ctx.scc_stack.val.map (fun u : Std.Usize => u.val) = (c.stk.map Fin.val).reverse
  work : ctx.work.val.map (fun p : TagIndex Std.Usize StateTag × Std.Usize =>
    (p.1.index.val, p.2.val)) = (c.work.map fun p => (p.1.val, p.2)).reverse
  time : ctx.discovery_time.val = c.time
  eq : ctx.eq_class.val = c.eq

/-- Writing a vector slot. -/
def vset {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) (x : α) : alloc.vec.Vec α :=
  { slice := v.slice.set i x }

theorem vset_val {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) (x : α) :
    (vset v i x).val = v.val.set i.val x := by
  show (v.slice.set i x).val = _
  rw [Slice.set_val_eq]; rfl

namespace SR

variable {n : Nat} {ctx : SC} {c : Sigref.Tarjan.Ctx n}

theorem set_disc (h : SR n ctx c) (iu : Std.Usize) (i : Fin n) (hiu : iu.val = i.val) (x : Std.Usize) :
    SR n { ctx with disc := vset ctx.disc iu x } { c with disc := Function.update c.disc i x.val } := by
  have hi : i.val < ctx.disc.val.length := by rw [h.dlen]; exact i.2
  refine ⟨h.llen, ?_, h.olen, h.plen, h.low, ?_, h.onSt, h.blk, h.nb, h.stk, h.work, h.time, h.eq⟩
  · simp [vset_val, h.dlen]
  · show view n _ 0 (vset ctx.disc iu x).val = _
    rw [vset_val, hiu, view_set _ _ _ i hi, h.disc]

theorem set_low (h : SR n ctx c) (iu : Std.Usize) (i : Fin n) (hiu : iu.val = i.val) (x : Std.Usize) :
    SR n { ctx with low := vset ctx.low iu x } { c with low := Function.update c.low i x.val } := by
  have hi : i.val < ctx.low.val.length := by rw [h.llen]; exact i.2
  refine ⟨?_, h.dlen, h.olen, h.plen, ?_, h.disc, h.onSt, h.blk, h.nb, h.stk, h.work, h.time, h.eq⟩
  · simp [vset_val, h.llen]
  · show view n _ 0 (vset ctx.low iu x).val = _
    rw [vset_val, hiu, view_set _ _ _ i hi, h.low]

end SR

theorem unvisited_val : verified.merc_reduction.scc_decomposition.SCC_UNVISITED.val = Usize.max := by
  simp [verified.merc_reduction.scc_decomposition.SCC_UNVISITED, core.num.Usize.MAX]

theorem usize_add_one (a : Std.Usize) (h : a.val < Usize.max) :
    ∃ r : Std.Usize, a + 1#usize = ok r ∧ r.val = a.val + 1 := by
  obtain ⟨r, hr, hv⟩ := spec_imp_exists (Usize.add_spec (x := a) (y := 1#usize) (by simp; omega))
  exact ⟨r, hr, by simpa using hv⟩

theorem ordusize_max_val (a b : Std.Usize) :
    (core.cmp.impls.OrdUsize.max a b).val = max a.val b.val := by
  unfold core.cmp.impls.OrdUsize.max
  split_ifs with h
  · have h' : b.val < a.val := h
    omega
  · have h' : ¬ b.val < a.val := h
    omega

theorem usize_sub_one (a : Std.Usize) (h : 0 < a.val) :
    ∃ r : Std.Usize, a - 1#usize = ok r ∧ r.val = a.val - 1 := by
  obtain ⟨r, hr, hv⟩ := spec_imp_exists (Usize.sub_spec (x := a) (y := 1#usize) (by simp; omega))
  have h2 : r.val = a.val - 1 ∧ 1 ≤ a.val := by simpa using hv
  exact ⟨r, hr, h2.1⟩

theorem vec_len_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.len v).val = v.val.length := by
  simp [alloc.vec.Vec.len]

theorem vec_index_usize_ok {U : Type} (v : alloc.vec.Vec U) (i : Std.Usize)
    (h : i.val < v.val.length) : v.index_usize i = ok (v.val[i.val]'h) := by
  rw [← alloc.vec.Vec.index_slice_index]
  exact vec_index_ok v i h

theorem massert_true_ok : massert (true = true) = ok () := by simp

open verified.merc_collections.indexed_partition in
theorem set_block_spec (ip : IndexedPartition) (u : Std.Usize) (hu : u.val < ip.partition.val.length)
    (ti : TagIndex Std.Usize BlockTag) (hti : ti.index.val < Usize.max) :
    ∃ m : Std.Usize, IndexedPartition.set_block ip u ti =
      ok ({ partition := vset ip.partition u ti, num_of_blocks := m } : IndexedPartition) ∧
      m.val = max ip.num_of_blocks.val (ti.index.val + 1) := by
  unfold IndexedPartition.set_block
  simp only [tag_value_id, bind_ok]
  have hne : (ti.index != NOT_IN_PARTITION) = true := by
    have : ti.index ≠ NOT_IN_PARTITION := by
      intro h
      have := congrArg UScalar.val h
      simp [NOT_IN_PARTITION, core.num.Usize.MAX] at this
      omega
    simpa using this
  rw [hne]
  obtain ⟨i1, hi1, hi1v⟩ := usize_add_one ti.index hti
  rw [massert_true_ok]; simp only [bind_ok]; rw [hi1]
  simp only [bind_ok, lift]
  rw [vec_index_mut_ok ip.partition u hu]
  simp only [bind_ok]
  refine ⟨core.cmp.impls.OrdUsize.max ip.num_of_blocks i1, rfl, ?_⟩
  rw [ordusize_max_val, hi1v]

section Scan

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

/-- The model graph of the LTS: all transitions with their hidden flag. -/
noncomputable def gOf {n : Nat} (hn0 : 0 < n) (hnlt : n < Usize.max) : Sigref.Tarjan.Graph n where
  adj s := (outVec LTSInst sys (stOf s)).val.map
    (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
  unv := Usize.max
  unv_gt := hnlt

open verified.merc_reduction.scc_decomposition in
theorem next_child_loop_spec {n : Nat} (hn0 : 0 < n) (hnlt : n < Usize.max)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (s : Fin n) (su : Std.Usize) (hsu : su.val = s.val)
    (ts : alloc.vec.Vec Transition) (hts : outVec LTSInst sys (stOf s) = ts)
    (htlt : ∀ t ∈ ts.val, t.to.index.val < n) :
    ∀ (k : Nat) (index : Std.Usize) (ctx : SC) (c : Sigref.Tarjan.Ctx n),
      ts.val.length - index.val = k → SR n ctx c →
      ∃ ctx' child idx', scc_next_child_loop LTSInst sys ctx su ts none index false =
          ok (ctx', child, idx') ∧
        SR n ctx' (Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
          ((ts.val.drop index.val).map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)))
          index.val c).2.2 ∧
        child.map (fun t => t.index.val) =
          ((Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
            ((ts.val.drop index.val).map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)))
            index.val c).1).map Fin.val ∧
        idx'.val = (Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
          ((ts.val.drop index.val).map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)))
          index.val c).2.1 := by
  have hgadj : (gOf LTSInst sys hn0 hnlt).adj s =
      ts.val.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)) := by
    simp [gOf, hts]
  have hunv : (gOf LTSInst sys hn0 hnlt).unv = Usize.max := rfl
  have hlenmax : ts.val.length ≤ Usize.max := by
    have := (alloc.vec.Vec.len ts).hBounds
    simp
  intro k
  induction k with
  | zero =>
    intro index ctx c hk hsr
    have hge : ts.val.length ≤ index.val := by omega
    have hdrop : ts.val.drop index.val = [] := List.drop_eq_nil_of_le hge
    refine ⟨ctx, none, index, ?_, ?_, ?_, ?_⟩
    · unfold scc_next_child_loop
      apply loop_done'
      unfold scc_next_child_loop.body
      simp only [Bool.false_eq_true, ↓reduceIte]
      have : ¬ index < alloc.vec.Vec.len ts := by simp [alloc.vec.Vec.len]; omega
      rw [if_neg this]
    all_goals simp [hdrop, Sigref.Tarjan.scan, hsr]
  | succ k ih =>
    intro index ctx c hk hsr
    have hi : index.val < ts.val.length := by omega
    obtain ⟨index1, hi1, hi1v⟩ := usize_add_one index (by omega)
    have hdrop : ts.val.drop index.val = ts.val[index.val]'hi :: ts.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons hi
    set t := ts.val[index.val]'hi with ht
    have htmem : t ∈ ts.val := List.getElem_mem hi
    have htlt' := htlt t htmem
    have hbase : ∀ (rest : Result (ControlFlow (SC × Option (TagIndex Std.Usize StateTag) × Std.Usize × Bool)
        (SC × Option (TagIndex Std.Usize StateTag) × Std.Usize))), True := fun _ => trivial
    have hlt : index < alloc.vec.Vec.len ts := by simp [alloc.vec.Vec.len]; omega
    have hnext : ∀ (ctx1 : SC) (c1 : Sigref.Tarjan.Ctx n), SR n ctx1 c1 →
        scc_next_child_loop.body LTSInst sys su ts ctx none index false =
          ok (cont (ctx1, none, index1, false)) →
        ∃ ctx' child idx', scc_next_child_loop LTSInst sys ctx su ts none index false =
            ok (ctx', child, idx') ∧
          SR n ctx' (Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
            ((ts.val.drop (index1.val)).map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)))
            index1.val c1).2.2 ∧
          child.map (fun t => t.index.val) =
            ((Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
              ((ts.val.drop index1.val).map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)))
              index1.val c1).1).map Fin.val ∧
          idx'.val = (Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
            ((ts.val.drop index1.val).map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)))
            index1.val c1).2.1 := by
      intro ctx1 c1 hsr1 hb
      obtain ⟨ctx', child, idx', hl, h1, h2, h3⟩ := ih index1 ctx1 c1 (by omega) hsr1
      refine ⟨ctx', child, idx', ?_, h1, h2, h3⟩
      unfold scc_next_child_loop at hl ⊢
      rw [loop_cont' _ _ _ hb]
      exact hl
    have hbody0 : scc_next_child_loop.body LTSInst sys su ts ctx none index false =
        (do
          let b ← LTSInst.is_hidden_label sys t.label
          if b = true then do
            let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize)
              ctx.disc t.to.index
            if i1 = SCC_UNVISITED then do
              let (_, index_mut_back) ← alloc.vec.Vec.index_mut
                (core.slice.index.SliceIndexUsizeSlice Std.Usize) ctx.disc t.to.index
              ok (cont ({ ctx with disc := index_mut_back 0#usize }, some t.to, index1, true))
            else do
              let b1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bool)
                ctx.on_scc_stack t.to.index
              if b1 = true then do
                let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize)
                  ctx.low su
                if i1 < i2 then do
                  let (_, index_mut_back) ← alloc.vec.Vec.index_mut
                    (core.slice.index.SliceIndexUsizeSlice Std.Usize) ctx.low su
                  ok (cont ({ ctx with low := index_mut_back i1 }, none, index1, false))
                else ok (cont (ctx, none, index1, false))
              else ok (cont (ctx, none, index1, false))
          else ok (cont (ctx, none, index1, false))) := by
      unfold scc_next_child_loop.body
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [if_pos hlt, vec_index_ok ts index hi]
      simp only [bind_ok]
      rw [hi1]
      simp only [bind_ok, tag_value_id]
      rfl
    have hfound : ∀ (ctx1 : SC) (ch : TagIndex Std.Usize StateTag),
        scc_next_child_loop LTSInst sys ctx1 su ts (some ch) index1 true = ok (ctx1, some ch, index1) := by
      intro ctx1 ch
      unfold scc_next_child_loop
      apply loop_done'
      unfold scc_next_child_loop.body
      simp
    rw [hdrop, List.map_cons]
    have hdr1 : ts.val.drop (index.val + 1) = ts.val.drop index1.val := by rw [hi1v]
    by_cases hh : t.label.index.val = 0
    · have hv : t.to.index.val < ctx.disc.val.length := by rw [hsr.dlen]; exact htlt'
      have hwv : (toFin hn0 t.to).val = t.to.index.val := toFin_val hn0 t.to htlt'
      have hdisc : (ctx.disc.val[t.to.index.val]'hv).val = c.disc (toFin hn0 t.to) := by
        rw [← hsr.disc, view_get _ _ _ _ (by rw [hwv]; exact hv)]
        simp [hwv]
      have hvo : t.to.index.val < ctx.on_scc_stack.val.length := by rw [hsr.olen]; exact htlt'
      have hon : ctx.on_scc_stack.val[t.to.index.val]'hvo = c.onSt (toFin hn0 t.to) := by
        rw [← hsr.onSt, view_get _ _ _ _ (by rw [hwv]; exact hvo)]
        simp [hwv]
      have hsl : su.val < ctx.low.val.length := by rw [hsr.llen, hsu]; exact s.2
      have hlow : (ctx.low.val[su.val]'hsl).val = c.low s := by
        rw [← hsr.low, view_get _ _ _ _ (by rw [← hsu]; exact hsl)]
        simp [hsu]
      have hbody1 : scc_next_child_loop.body LTSInst sys su ts ctx none index false =
          (do
            let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize)
              ctx.disc t.to.index
            if i1 = SCC_UNVISITED then do
              let (_, index_mut_back) ← alloc.vec.Vec.index_mut
                (core.slice.index.SliceIndexUsizeSlice Std.Usize) ctx.disc t.to.index
              ok (cont ({ ctx with disc := index_mut_back 0#usize }, some t.to, index1, true))
            else do
              let b1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bool)
                ctx.on_scc_stack t.to.index
              if b1 = true then do
                let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize)
                  ctx.low su
                if i1 < i2 then do
                  let (_, index_mut_back) ← alloc.vec.Vec.index_mut
                    (core.slice.index.SliceIndexUsizeSlice Std.Usize) ctx.low su
                  ok (cont ({ ctx with low := index_mut_back i1 }, none, index1, false))
                else ok (cont (ctx, none, index1, false))
              else ok (cont (ctx, none, index1, false))) := by
        rw [hbody0, hid t.label, show decide (t.label.index.val = 0) = true from decide_eq_true hh]
        simp only [bind_ok, if_true]
      rw [show decide (t.label.index.val = 0) = true from decide_eq_true hh]
      have hunv' : (gOf LTSInst sys hn0 hnlt).unv = Usize.max := hunv
      by_cases hu1 : c.disc (toFin hn0 t.to) = Usize.max
      · have hcond : ctx.disc.val[t.to.index.val]'hv = SCC_UNVISITED :=
          UScalar.eq_of_val_eq (by rw [hdisc, hu1, unvisited_val])
        have hb' : scc_next_child_loop.body LTSInst sys su ts ctx none index false =
            ok (cont ({ ctx with disc := vset ctx.disc t.to.index 0#usize }, some t.to, index1, true)) := by
          rw [hbody1, vec_index_ok ctx.disc t.to.index hv]
          simp only [bind_ok]
          rw [if_pos hcond, vec_index_mut_ok ctx.disc t.to.index hv]
          simp only [bind_ok]
          rfl
        have hl : scc_next_child_loop LTSInst sys ctx su ts none index false =
            ok ({ ctx with disc := vset ctx.disc t.to.index 0#usize }, some t.to, index1) := by
          have := hfound { ctx with disc := vset ctx.disc t.to.index 0#usize } t.to
          unfold scc_next_child_loop at this ⊢
          rw [loop_cont' _ _ _ hb']
          exact this
        have hsc : Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
            ((true, toFin hn0 t.to) :: List.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
              (ts.val.drop index1.val)) index.val c =
            (some (toFin hn0 t.to), index.val + 1,
              { c with disc := Function.update c.disc (toFin hn0 t.to) 0 }) := by
          simp [Sigref.Tarjan.scan, hu1, hunv']
        rw [← hdr1] at hsc
        rw [hsc]
        refine ⟨_, _, _, hl, hsr.set_disc t.to.index (toFin hn0 t.to) hwv.symm 0#usize, ?_, ?_⟩
        · simp [hwv]
        · simp [hi1v]
      · have hncond : ¬ (ctx.disc.val[t.to.index.val]'hv = SCC_UNVISITED) := by
          intro h
          apply hu1
          rw [← hdisc, h, unvisited_val]
        have hbA : ∀ rest : Result (ControlFlow (SC × Option (TagIndex Std.Usize StateTag) × Std.Usize × Bool)
            (SC × Option (TagIndex Std.Usize StateTag) × Std.Usize)),
            True := fun _ => trivial
        by_cases hos : c.onSt (toFin hn0 t.to) = true
        · have hb1 : ctx.on_scc_stack.val[t.to.index.val]'hvo = true := by rw [hon]; exact hos
          by_cases hlt2 : c.disc (toFin hn0 t.to) < c.low s
          · have hlt3 : ctx.disc.val[t.to.index.val]'hv < ctx.low.val[su.val]'hsl := by
              show (ctx.disc.val[t.to.index.val]'hv).val < (ctx.low.val[su.val]'hsl).val
              rw [hdisc, hlow]; exact hlt2
            have hb' : scc_next_child_loop.body LTSInst sys su ts ctx none index false =
                ok (cont ({ ctx with low := vset ctx.low su (ctx.disc.val[t.to.index.val]'hv) },
                  none, index1, false)) := by
              rw [hbody1, vec_index_ok ctx.disc t.to.index hv]
              simp only [bind_ok]
              rw [if_neg hncond, vec_index_ok ctx.on_scc_stack t.to.index hvo, hb1]
              simp only [bind_ok, if_true]
              rw [vec_index_ok ctx.low su hsl]
              simp only [bind_ok]
              rw [if_pos hlt3, vec_index_mut_ok ctx.low su hsl]
              simp only [bind_ok]
              rfl
            obtain ⟨ctx', child, idx', hl, h1, h2, h3⟩ := hnext _
              { c with low := Function.update c.low s (ctx.disc.val[t.to.index.val]'hv).val }
              (hsr.set_low su s hsu _) hb'
            have hsc : Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
                ((true, toFin hn0 t.to) :: List.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
                  (ts.val.drop index1.val)) index.val c =
                Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
                  (List.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
                    (ts.val.drop index1.val)) (index.val + 1)
                  { c with low := Function.update c.low s (c.disc (toFin hn0 t.to)) } := by
              simp [Sigref.Tarjan.scan, hu1, hunv', hos, hlt2]
            rw [hdr1, hsc, ← hdisc, ← hi1v]
            exact ⟨ctx', child, idx', hl, h1, h2, h3⟩
          · have hlt3 : ¬ (ctx.disc.val[t.to.index.val]'hv < ctx.low.val[su.val]'hsl) := by
              show ¬ ((ctx.disc.val[t.to.index.val]'hv).val < (ctx.low.val[su.val]'hsl).val)
              rw [hdisc, hlow]; exact hlt2
            have hb' : scc_next_child_loop.body LTSInst sys su ts ctx none index false =
                ok (cont (ctx, none, index1, false)) := by
              rw [hbody1, vec_index_ok ctx.disc t.to.index hv]
              simp only [bind_ok]
              rw [if_neg hncond, vec_index_ok ctx.on_scc_stack t.to.index hvo, hb1]
              simp only [bind_ok, if_true]
              rw [vec_index_ok ctx.low su hsl]
              simp only [bind_ok]
              rw [if_neg hlt3]
            obtain ⟨ctx', child, idx', hl, h1, h2, h3⟩ := hnext ctx c hsr hb'
            have hsc : Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
                ((true, toFin hn0 t.to) :: List.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
                  (ts.val.drop index1.val)) index.val c =
                Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
                  (List.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
                    (ts.val.drop index1.val)) (index.val + 1) c := by
              simp [Sigref.Tarjan.scan, hu1, hunv', hos, hlt2]
            rw [hdr1, hsc, ← hi1v]
            exact ⟨ctx', child, idx', hl, h1, h2, h3⟩
        · have hb1 : ctx.on_scc_stack.val[t.to.index.val]'hvo = false := by
            rw [hon]; simpa using hos
          have hb' : scc_next_child_loop.body LTSInst sys su ts ctx none index false =
              ok (cont (ctx, none, index1, false)) := by
            rw [hbody1, vec_index_ok ctx.disc t.to.index hv]
            simp only [bind_ok]
            rw [if_neg hncond, vec_index_ok ctx.on_scc_stack t.to.index hvo, hb1]
            simp
          obtain ⟨ctx', child, idx', hl, h1, h2, h3⟩ := hnext ctx c hsr hb'
          have hsc : Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
              ((true, toFin hn0 t.to) :: List.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
                (ts.val.drop index1.val)) index.val c =
              Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) s
                (List.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to))
                  (ts.val.drop index1.val)) (index.val + 1) c := by
            have hos' : c.onSt (toFin hn0 t.to) = false := by simpa using hos
            simp [Sigref.Tarjan.scan, hu1, hunv', hos']
          rw [hdr1, hsc, ← hi1v]
          exact ⟨ctx', child, idx', hl, h1, h2, h3⟩
    · have hb : scc_next_child_loop.body LTSInst sys su ts ctx none index false =
          ok (cont (ctx, none, index1, false)) := by
        rw [hbody0, hid t.label, show decide (t.label.index.val = 0) = false from decide_eq_false hh]
        simp only [bind_ok]
        simp
      obtain ⟨ctx', child, idx', hl, h1, h2, h3⟩ := hnext ctx c hsr hb
      refine ⟨ctx', child, idx', hl, ?_, ?_, ?_⟩
      all_goals simp only [Sigref.Tarjan.scan, hh, decide_false, Bool.false_eq_true, if_false, ← hi1v]
      · exact h1
      · exact h2
      · exact h3

end Scan

section Pop

open verified.merc_reduction.scc_decomposition in
theorem pop_loop_spec {n : Nat} (s : Fin n) (su : Std.Usize) (hsu : su.val = s.val) (e : Nat)
    (he : e < Usize.max) :
    ∀ (stk : List (Fin n)) (onSt : Fin n → Bool) (blk : Fin n → ℕ) (ctx : SC)
      (rest : List (Fin n)) (onSt' : Fin n → Bool) (blk' : Fin n → ℕ),
      Sigref.Tarjan.popComp s e stk onSt blk = some (rest, onSt', blk') →
      ctx.scc_stack.val.map (fun u : Std.Usize => u.val) = (stk.map Fin.val).reverse →
      view n (fun b : Bool => b) false ctx.on_scc_stack.val = onSt →
      ctx.on_scc_stack.val.length = n →
      view n (fun t : TagIndex Std.Usize verified.merc_collections.indexed_partition.BlockTag =>
        t.index.val) 0 ctx.partition.partition.val = blk →
      ctx.partition.partition.val.length = n → ctx.eq_class.val = e →
      ∃ ctx', scc_pop_component_loop ctx su false = ok ctx' ∧
        ctx'.scc_stack.val.map (fun u : Std.Usize => u.val) = (rest.map Fin.val).reverse ∧
        view n (fun b : Bool => b) false ctx'.on_scc_stack.val = onSt' ∧
        ctx'.on_scc_stack.val.length = n ∧
        view n (fun t : TagIndex Std.Usize verified.merc_collections.indexed_partition.BlockTag =>
          t.index.val) 0 ctx'.partition.partition.val = blk' ∧
        ctx'.partition.partition.val.length = n ∧
        ctx'.partition.num_of_blocks.val = max ctx.partition.num_of_blocks.val (e + 1) ∧
        ctx'.low = ctx.low ∧ ctx'.disc = ctx.disc ∧ ctx'.work = ctx.work ∧
        ctx'.discovery_time = ctx.discovery_time ∧ ctx'.eq_class = ctx.eq_class := by
  intro stk
  induction stk with
  | nil => intro onSt blk ctx rest onSt' blk' h; simp [Sigref.Tarjan.popComp] at h
  | cons u rest0 ih =>
    intro onSt blk ctx rest onSt' blk' hpop hstk hon hol hbl hpl hee
    have hdone : ∀ ctx1 : SC, scc_pop_component_loop.body su ctx1 true = ok (done ctx1) := by
      intro ctx1; unfold scc_pop_component_loop.body; simp
    have hstk' : ctx.scc_stack.val.map (fun u : Std.Usize => u.val) =
        (rest0.map Fin.val).reverse ++ [u.val] := by
      rw [hstk]; simp
    rcases List.eq_nil_or_concat ctx.scc_stack.val with hnil | ⟨rest', x, hrest⟩
    · rw [hnil] at hstk'; simp at hstk'
    rw [List.concat_eq_append] at hrest
    have hstk'' : rest'.map (fun u : Std.Usize => u.val) ++ [x.val] =
        (rest0.map Fin.val).reverse ++ [u.val] := by
      rw [hrest, List.map_append] at hstk'; simpa using hstk'
    obtain ⟨hrmap, hxu'⟩ := List.append_inj' hstk'' (by simp)
    have hxu : x.val = u.val := by simpa using hxu'
    obtain ⟨D1, hpopv, hD1v⟩ := alloc.vec.Vec.pop_cons_spec Global ctx.scc_stack x rest' hrest
    have hxo : x.val < ctx.on_scc_stack.val.length := by rw [hol, hxu]; exact u.2
    have hxp : x.val < ctx.partition.partition.val.length := by rw [hpl, hxu]; exact u.2
    set ti : TagIndex Std.Usize verified.merc_collections.indexed_partition.BlockTag :=
      { index := ctx.eq_class, marker := () } with hti
    have hnew : verified.merc_utilities.tagged_index.TagIndex.new
        verified.merc_collections.indexed_partition.BlockTag ctx.eq_class = ok ti := by
      simp [hti]
    obtain ⟨m, hsb, hmv⟩ := set_block_spec ctx.partition x hxp ti (by simp [hti]; omega)
    have hmut := vec_index_mut_ok ctx.on_scc_stack x hxo
    set ip' : verified.merc_collections.indexed_partition.IndexedPartition :=
      { partition := vset ctx.partition.partition x ti, num_of_blocks := m } with hip'
    set ctx1 : SC :=
      { ctx with
        partition := ip'
        on_scc_stack := vset ctx.on_scc_stack x false
        scc_stack := D1 } with hctx1
    have hbodyfalse : scc_pop_component_loop.body su ctx false =
        (if x = su then ok (cont (ctx1, true)) else ok (cont (ctx1, false))) := by
      unfold scc_pop_component_loop.body
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp [hpopv, core.option.Option.unwrap, ofOption]
      rw [vec_index_mut_usize_ok ctx.on_scc_stack x hxo]
      simp only [bind_ok]
      rw [← hti, hsb]
      simp only [bind_ok]
      split_ifs <;> rfl
    have htie : ti.index.val = e := by simp [hti, hee]
    have hf1 : ctx1.scc_stack.val.map (fun u : Std.Usize => u.val) = (rest0.map Fin.val).reverse := by
      show D1.val.map _ = _
      rw [hD1v, hrmap]
    have hf2 : view n (fun b : Bool => b) false ctx1.on_scc_stack.val = Function.update onSt u false := by
      show view n _ _ (vset ctx.on_scc_stack x false).val = _
      rw [vset_val, hxu, view_set _ _ _ u (by rw [hol]; exact u.2), hon]
    have hf3 : ctx1.on_scc_stack.val.length = n := by
      show (vset ctx.on_scc_stack x false).val.length = n
      rw [vset_val]; simpa using hol
    have hf4 : view n (fun t : TagIndex Std.Usize verified.merc_collections.indexed_partition.BlockTag =>
        t.index.val) 0 ctx1.partition.partition.val = Function.update blk u e := by
      show view n _ _ (vset ctx.partition.partition x ti).val = _
      rw [vset_val, hxu, view_set _ _ _ u (by rw [hpl]; exact u.2), hbl, htie]
    have hf5 : ctx1.partition.partition.val.length = n := by
      show (vset ctx.partition.partition x ti).val.length = n
      rw [vset_val]; simpa using hpl
    have hf6 : ctx1.partition.num_of_blocks.val = max ctx.partition.num_of_blocks.val (e + 1) := by
      show m.val = _
      rw [hmv, htie]
    by_cases hxs : x = su
    · have hus : u = s := Fin.ext (by rw [← hxu, hxs, hsu])
      subst hus
      have hpop' : rest = rest0 ∧ onSt' = Function.update onSt u false ∧ blk' = Function.update blk u e := by
        simp [Sigref.Tarjan.popComp] at hpop
        exact ⟨hpop.1.symm, hpop.2.1.symm, hpop.2.2.symm⟩
      obtain ⟨hr, ho, hb⟩ := hpop'
      subst hr ho hb
      have hb' : scc_pop_component_loop.body su ctx false = ok (cont (ctx1, true)) := by
        rw [hbodyfalse, if_pos hxs]
      refine ⟨ctx1, ?_, hf1, hf2, hf3, hf4, hf5, hf6, rfl, rfl, rfl, rfl, rfl⟩
      unfold scc_pop_component_loop
      rw [loop_cont' _ _ _ hb']
      exact loop_done' _ _ _ (hdone ctx1)
    · have hus : u ≠ s := fun h => hxs (UScalar.eq_of_val_eq (by rw [hxu, h, hsu]))
      have hpop' : Sigref.Tarjan.popComp s e rest0 (Function.update onSt u false)
          (Function.update blk u e) = some (rest, onSt', blk') := by
        simpa [Sigref.Tarjan.popComp, hus] using hpop
      have hb' : scc_pop_component_loop.body su ctx false = ok (cont (ctx1, false)) := by
        rw [hbodyfalse, if_neg hxs]
      obtain ⟨ctx', hl, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ :=
        ih _ _ ctx1 rest onSt' blk' hpop' hf1 hf2 hf3 hf4 hf5 (by simpa [ctx1] using hee)
      refine ⟨ctx', ?_, g1, g2, g3, g4, g5, ?_, g7, g8, g9, g10, ?_⟩
      · unfold scc_pop_component_loop at hl ⊢
        rw [loop_cont' _ _ _ hb']
        exact hl
      · rw [g6, hf6]; omega
      · rw [g11]

end Pop

section Finish

open verified.merc_reduction.scc_decomposition in
theorem finish_tail {n : Nat} (_hn0 : 0 < n) (ctxM : SC) (cM : Sigref.Tarjan.Ctx n) (hsr : SR n ctxM cM)
    (s : Fin n) (su : Std.Usize) (hsu : su.val = s.val) :
    ∃ ctx', (let work_len := alloc.vec.Vec.len ctxM.work
      if work_len > 0#usize then do
        let i4 ← work_len - 1#usize
        let (ti, _) ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          ((TagIndex Std.Usize StateTag) × Std.Usize)) ctxM.work i4
        let p ← TagIndex.value core.marker.CopyUsize ti
        let i5 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize) ctxM.low su
        let i6 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize) ctxM.low p
        if i5 < i6 then do
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice Std.Usize) ctxM.low p
          let v5 := index_mut_back i5
          ok { ctxM with low := v5 }
        else ok ctxM
      else ok ctxM) = ok ctx' ∧
      SR n ctx' (match cM.work with
        | [] => cM
        | (p, _) :: _ =>
          if cM.low s < cM.low p then { cM with low := Function.update cM.low p (cM.low s) } else cM) := by
  have hwv := hsr.work
  rcases hcw : cM.work with _ | ⟨⟨p, off⟩, W⟩
  · rw [hcw] at hwv
    have hnil : ctxM.work.val = [] := by simpa using hwv
    have hlt : ¬ (alloc.vec.Vec.len ctxM.work > 0#usize) := by
      show ¬ (0 < (alloc.vec.Vec.len ctxM.work).val)
      rw [vec_len_val, hnil]; simp
    refine ⟨ctxM, ?_, ?_⟩
    · simp only [hlt, if_false]
    · exact hsr
  · rw [hcw] at hwv
    rcases List.eq_nil_or_concat ctxM.work.val with hnil | ⟨rest', x, hrest⟩
    · rw [hnil] at hwv; simp at hwv
    rw [List.concat_eq_append] at hrest
    obtain ⟨t, o⟩ := x
    have hwv' : rest'.map (fun p : TagIndex Std.Usize StateTag × Std.Usize => (p.1.index.val, p.2.val)) ++
        [(t.index.val, o.val)] = (W.map fun p => (p.1.val, p.2)).reverse ++ [(p.val, off)] := by
      rw [hrest] at hwv; simpa using hwv
    obtain ⟨_, hxe⟩ := List.append_inj' hwv' (by simp)
    have htp : t.index.val = p.val := by simpa using (Prod.mk.inj (List.singleton_inj.mp hxe)).1
    have hlenw : ctxM.work.val.length = rest'.length + 1 := by rw [hrest]; simp
    have hgt : alloc.vec.Vec.len ctxM.work > 0#usize := by
      show 0 < (alloc.vec.Vec.len ctxM.work).val
      rw [vec_len_val]; omega
    obtain ⟨i4, hi4, hi4v⟩ := usize_sub_one (alloc.vec.Vec.len ctxM.work) (by rw [vec_len_val]; omega)
    have hi4lt : i4.val < ctxM.work.val.length := by rw [hi4v, vec_len_val]; omega
    have hget : ctxM.work.val[i4.val]'hi4lt = (t, o) := by
      simp only [hrest]
      rw [List.getElem_append_right (by rw [hi4v, vec_len_val, hrest]; simp)]
      simp [hi4v, hrest]
    have hpn : p.val < n := p.2
    have hpl : p.val < ctxM.low.val.length := by rw [hsr.llen]; exact hpn
    have hsl : su.val < ctxM.low.val.length := by rw [hsr.llen, hsu]; exact s.2
    have hlowp : (ctxM.low.val[t.index.val]'(by rw [htp]; exact hpl)).val = cM.low p := by
      rw [← hsr.low, view_get _ _ _ _ hpl]; simp [htp]
    have hlows : (ctxM.low.val[su.val]'hsl).val = cM.low s := by
      rw [← hsr.low, view_get _ _ _ _ (by rw [← hsu]; exact hsl)]; simp [hsu]
    simp only [hgt, if_true, hi4, bind_ok]
    rw [vec_index_ok ctxM.work i4 hi4lt, hget]
    simp only [bind_ok, tag_value_id]
    simp
    rw [vec_index_usize_ok ctxM.low su hsl, vec_index_usize_ok ctxM.low t.index (by rw [htp]; exact hpl)]
    simp only [bind_ok]
    by_cases hlt : cM.low s < cM.low p
    · have hlt' : ctxM.low.val[su.val]'hsl < ctxM.low.val[t.index.val]'(by rw [htp]; exact hpl) := by
        show (ctxM.low.val[su.val]'hsl).val < (ctxM.low.val[t.index.val]'(by rw [htp]; exact hpl)).val
        rw [hlows, hlowp]; exact hlt
      have hlt'' : (ctxM.low.val[su.val]'hsl).val < (ctxM.low.val[t.index.val]'(by rw [htp]; exact hpl)).val := hlt'
      rw [if_pos hlt'', vec_index_mut_usize_ok ctxM.low t.index (by rw [htp]; exact hpl)]
      simp only [bind_ok]
      refine ⟨_, rfl, ?_⟩
      rw [if_pos hlt]
      have := hsr.set_low t.index p htp (ctxM.low.val[su.val]'hsl)
      rw [hlows, hcw] at this
      exact this
    · have hlt' : ¬ (ctxM.low.val[su.val]'hsl < ctxM.low.val[t.index.val]'(by rw [htp]; exact hpl)) := by
        show ¬ ((ctxM.low.val[su.val]'hsl).val < (ctxM.low.val[t.index.val]'(by rw [htp]; exact hpl)).val)
        rw [hlows, hlowp]; exact hlt
      have hlt'' : ¬ ((ctxM.low.val[su.val]'hsl).val < (ctxM.low.val[t.index.val]'(by rw [htp]; exact hpl)).val) := hlt'
      rw [if_neg hlt'']
      refine ⟨ctxM, rfl, ?_⟩
      rw [if_neg hlt]
      exact hsr

open verified.merc_reduction.scc_decomposition in
theorem finish_spec {n : Nat} (hn0 : 0 < n) (ctx : SC) (c : Sigref.Tarjan.Ctx n) (hsr : SR n ctx c)
    (s : Fin n) (su : Std.Usize) (hsu : su.val = s.val) (hmax : c.eq < Usize.max)
    (c' : Sigref.Tarjan.Ctx n) (hfin : Sigref.Tarjan.finish s c = some c') :
    ∃ ctx', scc_finish ctx su = ok ctx' ∧ SR n ctx' c' := by
  have hsd : su.val < ctx.disc.val.length := by rw [hsr.dlen, hsu]; exact s.2
  have hsl : su.val < ctx.low.val.length := by rw [hsr.llen, hsu]; exact s.2
  have hdv : (ctx.disc.val[su.val]'hsd).val = c.disc s := by
    rw [← hsr.disc, view_get _ _ _ _ (by rw [← hsu]; exact hsd)]; simp [hsu]
  have hlv : (ctx.low.val[su.val]'hsl).val = c.low s := by
    rw [← hsr.low, view_get _ _ _ _ (by rw [← hsu]; exact hsl)]; simp [hsu]
  unfold scc_finish
  rw [vec_index_ok ctx.disc su hsd, vec_index_ok ctx.low su hsl]
  simp only [bind_ok]
  by_cases hd : c.disc s = c.low s
  · have hcond : ctx.disc.val[su.val]'hsd = ctx.low.val[su.val]'hsl :=
      UScalar.eq_of_val_eq (by rw [hdv, hlv, hd])
    rw [if_pos hcond]
    have hpop : ∃ r, Sigref.Tarjan.popComp s c.eq c.stk c.onSt c.blk = some r := by
      by_contra hno
      push Not at hno
      have hn : Sigref.Tarjan.popComp s c.eq c.stk c.onSt c.blk = none := by
        cases h : Sigref.Tarjan.popComp s c.eq c.stk c.onSt c.blk with
        | none => rfl
        | some r => exact absurd h (hno r)
      simp [Sigref.Tarjan.finish, hd, hn] at hfin
    obtain ⟨⟨rest, onSt', blk'⟩, hpr⟩ := hpop
    obtain ⟨ctx1, hl, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ :=
      pop_loop_spec s su hsu c.eq hmax c.stk c.onSt c.blk ctx rest onSt' blk' hpr
        (by rw [hsr.stk]) (by rw [hsr.onSt]) hsr.olen (by rw [hsr.blk]) hsr.plen hsr.eq
    obtain ⟨i4, hi4, hi4v⟩ := usize_add_one ctx1.eq_class (by rw [g11, hsr.eq]; exact hmax)
    set cM : Sigref.Tarjan.Ctx n := { c with stk := rest, onSt := onSt', blk := blk', eq := c.eq + 1 }
      with hcM
    have hsrM : SR n { ctx1 with eq_class := i4 } cM := by
      refine ⟨?_, ?_, g3, g5, ?_, ?_, g2, g4, ?_, g1, ?_, ?_, ?_⟩
      · show ctx1.low.val.length = n; rw [g7]; exact hsr.llen
      · show ctx1.disc.val.length = n; rw [g8]; exact hsr.dlen
      · show view n _ 0 ctx1.low.val = c.low; rw [g7]; exact hsr.low
      · show view n _ 0 ctx1.disc.val = c.disc; rw [g8]; exact hsr.disc
      · show ctx1.partition.num_of_blocks.val = max 1 (c.eq + 1)
        rw [g6, hsr.nb]; omega
      · show ctx1.work.val.map _ = _; rw [g9]; exact hsr.work
      · show ctx1.discovery_time.val = c.time; rw [g10]; exact hsr.time
      · show i4.val = c.eq + 1; rw [hi4v, g11, hsr.eq]
    unfold scc_pop_component
    rw [hl]
    simp only [bind_ok]
    rw [hi4]
    simp only [bind_ok]
    obtain ⟨ctx', hct, hsr'⟩ := finish_tail hn0 _ cM hsrM s su hsu
    refine ⟨ctx', hct, ?_⟩
    have hc' : c' = (match cM.work with
        | [] => cM
        | (p, _) :: _ =>
          if cM.low s < cM.low p then { cM with low := Function.update cM.low p (cM.low s) } else cM) := by
      simp only [Sigref.Tarjan.finish, hd, if_true, hpr, Option.map_some] at hfin
      exact (Option.some.inj hfin).symm
    rw [hc']
    exact hsr'
  · have hcond : ¬ (ctx.disc.val[su.val]'hsd = ctx.low.val[su.val]'hsl) := by
      intro h
      apply hd
      rw [← hdv, ← hlv, h]
    rw [if_neg hcond]
    simp only [bind_ok]
    obtain ⟨ctx', hct, hsr'⟩ := finish_tail hn0 ctx c hsr s su hsu
    refine ⟨ctx', hct, ?_⟩
    have hc' : c' = (match c.work with
        | [] => c
        | (p, _) :: _ =>
          if c.low s < c.low p then { c with low := Function.update c.low p (c.low s) } else c) := by
      simp only [Sigref.Tarjan.finish, hd, if_false, Option.map_some] at hfin
      exact (Option.some.inj hfin).symm
    rw [hc']
    exact hsr'

end Finish

section Step

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

open verified.merc_reduction.scc_decomposition in
theorem next_child_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max)
    (sv : TagIndex Std.Usize StateTag) (hsv : sv.index.val < n0.val) (off : Std.Usize)
    (ctx : SC) (c : Sigref.Tarjan.Ctx n0.val) (hsr : SR n0.val ctx c) :
    ∃ child idx ctx1, scc_next_child LTSInst sys ctx sv off = ok ((child, idx), ctx1) ∧
      SR n0.val ctx1 (Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) (toFin hn0 sv)
        (((gOf LTSInst sys hn0 hnlt).adj (toFin hn0 sv)).drop off.val) off.val c).2.2 ∧
      child.map (fun t => t.index.val) = ((Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) (toFin hn0 sv)
        (((gOf LTSInst sys hn0 hnlt).adj (toFin hn0 sv)).drop off.val) off.val c).1).map Fin.val ∧
      idx.val = (Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) (toFin hn0 sv)
        (((gOf LTSInst sys hn0 hnlt).adj (toFin hn0 sv)).drop off.val) off.val c).2.1 := by
  obtain ⟨_, hout, _⟩ := hwf
  obtain ⟨ts, hts, htlt⟩ := hout n0 hns sv hsv
  have hn : n0.val ≤ Usize.max := hnlt.le
  have hsvf : stOf (toFin hn0 sv) = sv := by
    apply merc_utilities.tagged_index.TagIndex.ext
    apply UScalar.eq_of_val_eq
    rw [stOf_index _ hn, toFin_val hn0 sv hsv]
  have hovec : outVec LTSInst sys (stOf (toFin hn0 sv)) = ts := by
    rw [hsvf]; exact outVec_of_ok LTSInst sys sv ts hts
  have hgadj : (gOf LTSInst sys hn0 hnlt).adj (toFin hn0 sv) =
      ts.val.map (fun t => (decide (t.label.index.val = 0), toFin hn0 t.to)) := by
    simp [gOf, hovec]
  obtain ⟨ctx', child, idx', hl, h1, h2, h3⟩ := next_child_loop_spec LTSInst sys hn0 hnlt hid
    (toFin hn0 sv) sv.index (toFin_val hn0 sv hsv).symm ts hovec htlt _ off ctx c rfl hsr
  unfold scc_next_child
  simp only [tag_value_id, bind_ok]
  rw [hts]
  simp only [bind_ok]
  rw [hl]
  rw [hgadj, ← List.map_drop]
  exact ⟨child, idx', ctx', by simp, h1, h2, h3⟩

open verified.merc_reduction.scc_decomposition in
theorem step_rest_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max)
    (sv : TagIndex Std.Usize StateTag) (hsv : sv.index.val < n0.val) (off : Std.Usize)
    (ctx1 : SC) (c1 : Sigref.Tarjan.Ctx n0.val) (hsr : SR n0.val ctx1 c1)
    (hweq : c1.eq < Usize.max) (hwl : c1.work.length + 1 < Usize.max)
    (W : List (Fin n0.val × ℕ)) (hW : c1.work = W)
    (c' : Sigref.Tarjan.Ctx n0.val)
    (chm : Option (Fin n0.val)) (offm : ℕ) (c2 : Sigref.Tarjan.Ctx n0.val)
    (hsc : Sigref.Tarjan.scan (gOf LTSInst sys hn0 hnlt) (toFin hn0 sv)
        (((gOf LTSInst sys hn0 hnlt).adj (toFin hn0 sv)).drop off.val) off.val c1 = (chm, offm, c2))
    (hres1 : ∀ ch, chm = some ch → c' = { c2 with work := (ch, 0) :: (toFin hn0 sv, offm) :: W })
    (hres2 : chm = none → Sigref.Tarjan.finish (toFin hn0 sv) c2 = some c') :
    ∃ ctx', (do
      let ((child, next_offset), ctx2) ← scc_next_child LTSInst sys ctx1 sv off
      match child with
      | none => scc_finish ctx2 sv.index
      | some child_vertex =>
        let v4 ← alloc.vec.Vec.push ctx2.work (sv, next_offset)
        let v5 ← alloc.vec.Vec.push v4 (child_vertex, 0#usize)
        ok { ctx2 with work := v5 }) = ok ctx' ∧ SR n0.val ctx' c' := by
  obtain ⟨child, idx, ctx2, hnc, h1, h2, h3⟩ :=
    next_child_spec LTSInst sys hwf n0 hns hn0 hid hnlt sv hsv off ctx1 c1 hsr
  rw [hnc]
  rw [hsc] at h1 h2 h3
  simp only at h1 h2 h3
  have hwe := Sigref.Tarjan.scan_work_eq (gOf LTSInst sys hn0 hnlt) (toFin hn0 sv)
    (((gOf LTSInst sys hn0 hnlt).adj (toFin hn0 sv)).drop off.val) off.val c1
  rw [hsc] at hwe
  simp only at hwe
  obtain ⟨hw2, he2, _⟩ := hwe
  cases chm with
  | none =>
    have hc : child = none := by simpa using h2
    subst hc
    obtain ⟨ctx', hfe, hsr'⟩ := finish_spec hn0 ctx2 c2 h1 (toFin hn0 sv) sv.index
      (toFin_val hn0 sv hsv).symm (by rw [he2]; exact hweq) c' (hres2 rfl)
    refine ⟨ctx', ?_, hsr'⟩
    simpa using hfe
  | some ch =>
    obtain ⟨cv, hcv⟩ : ∃ cv, child = some cv := by
      cases hch : child with
      | none => rw [hch] at h2; simp at h2
      | some cv => exact ⟨cv, rfl⟩
    subst hcv
    simp only [Option.map_some, Option.some.injEq] at h2
    have hout := hres1 ch rfl
    subst hout
    have hl2 : ctx2.work.val.length = c1.work.length := by
      have := congrArg List.length h1.work
      simpa [hw2] using this
    obtain ⟨v4, hp4, hv4⟩ := vec_push_val ctx2.work (sv, idx) (by omega)
    obtain ⟨v5, hp5, hv5⟩ := vec_push_val v4 (cv, 0#usize) (by rw [hv4]; simp; omega)
    refine ⟨{ ctx2 with work := v5 }, ?_, ?_⟩
    · simp [hp4, hp5]
    · refine ⟨h1.llen, h1.dlen, h1.olen, h1.plen, h1.low, h1.disc, h1.onSt, h1.blk, h1.nb,
        h1.stk, ?_, h1.time, h1.eq⟩
      show v5.val.map _ = _
      rw [hv5, hv4]
      have := h1.work
      simp only [List.map_append, this, hw2, hW]
      simp [h2, h3, toFin_val hn0 sv hsv]

open verified.merc_reduction.scc_decomposition in
theorem step_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max)
    (c : Sigref.Tarjan.Ctx n0.val) (hI : Sigref.Tarjan.Inv (gOf LTSInst sys hn0 hnlt) c)
    (sv : TagIndex Std.Usize StateTag) (hsv : sv.index.val < n0.val) (off : Std.Usize)
    (W : List (Fin n0.val × ℕ)) (hwork : c.work = (toFin hn0 sv, off.val) :: W)
    (c' : Sigref.Tarjan.Ctx n0.val)
    (hstep : Sigref.Tarjan.step (gOf LTSInst sys hn0 hnlt) c = Sigref.Tarjan.Out.next c')
    (ctx : SC) (hsr : SR n0.val ctx { c with work := W }) :
    ∃ ctx', scc_step LTSInst sys ctx sv off = ok ctx' ∧ SR n0.val ctx' c' := by
  set g := gOf LTSInst sys hn0 hnlt with hg
  set s : Fin n0.val := toFin hn0 sv with hs
  have hsvs : sv.index.val = s.val := (toFin_val hn0 sv hsv).symm
  have htime := hI.time_le
  have hstkl := hI.stk_len_le
  have hweql := hI.eq_le
  have hworkl := hI.work_len_le
  have hwl : W.length + 1 ≤ n0.val := by rw [hwork] at hworkl; simpa using hworkl
  have hc1 := Sigref.Tarjan.inv_initNode hI hwork
  rcases hsc : Sigref.Tarjan.scan g s ((g.adj s).drop off.val) off.val
      (Sigref.Tarjan.initNode g s { c with work := W }) with ⟨chm, offm, c2⟩
  have hres1 : ∀ ch, chm = some ch → c' = { c2 with work := (ch, 0) :: (s, offm) :: W } := by
    intro ch hch
    simp only [Sigref.Tarjan.step, hwork, hsc, hch] at hstep
    exact (Sigref.Tarjan.Out.next.inj hstep).symm
  have hres2 : chm = none → Sigref.Tarjan.finish s c2 = some c' := by
    intro hch
    simp only [Sigref.Tarjan.step, hwork, hsc, hch] at hstep
    cases hf : Sigref.Tarjan.finish s c2 with
    | none => rw [hf] at hstep; cases hstep
    | some c3 => rw [hf] at hstep; rw [Sigref.Tarjan.Out.next.inj hstep]
  have hc1w : (Sigref.Tarjan.initNode g s { c with work := W }).work = W := by
    rw [Sigref.Tarjan.initNode_work]
  have hc1e : (Sigref.Tarjan.initNode g s { c with work := W }).eq = c.eq := by
    rw [Sigref.Tarjan.initNode_eq]
  have hsl : sv.index.val < ctx.low.val.length := by rw [hsr.llen, hsvs]; exact s.2
  have hsd : sv.index.val < ctx.disc.val.length := by rw [hsr.dlen, hsvs]; exact s.2
  have hso : sv.index.val < ctx.on_scc_stack.val.length := by rw [hsr.olen, hsvs]; exact s.2
  have hlv : (ctx.low.val[sv.index.val]'hsl).val = c.low s := by
    have := hsr.low
    rw [← this, view_get _ _ _ _ (by rw [← hsvs]; exact hsl)]; simp [hsvs]
  unfold scc_step
  simp only [tag_value_id, bind_ok]
  rw [vec_index_ok ctx.low sv.index hsl]
  simp only [bind_ok]
  by_cases hu : c.low s = g.unv
  · have hcond : ctx.low.val[sv.index.val]'hsl = SCC_UNVISITED :=
      UScalar.eq_of_val_eq (by rw [hlv, hu, unvisited_val]; rfl)
    rw [if_pos hcond]
    have hcinit : Sigref.Tarjan.initNode g s { c with work := W } =
        { c with
          work := W
          disc := Function.update c.disc s c.time
          low := Function.update c.low s c.time
          time := c.time + 1
          stk := s :: c.stk
          onSt := Function.update c.onSt s true } := by
      unfold Sigref.Tarjan.initNode
      simp [hu]
    rw [vec_index_mut_ok ctx.disc sv.index hsd]
    simp only [bind_ok]
    rw [vec_index_mut_ok ctx.low sv.index hsl]
    simp only [bind_ok]
    obtain ⟨i2, hi2, hi2v⟩ := usize_add_one ctx.discovery_time (by rw [hsr.time]; show c.time < Usize.max; omega)
    rw [hi2]
    simp only [bind_ok]
    have hstkl' : ctx.scc_stack.val.length < Usize.max := by
      have := congrArg List.length hsr.stk
      simp at this
      show _ < _
      omega
    obtain ⟨v4, hp4, hv4⟩ := vec_push_val ctx.scc_stack sv.index hstkl'
    rw [hp4]
    simp only [bind_ok]
    rw [vec_index_mut_ok ctx.on_scc_stack sv.index hso]
    simp only [bind_ok]
    have hsr1 : SR n0.val
        { ctx with
          low := vset ctx.low sv.index ctx.discovery_time
          disc := vset ctx.disc sv.index ctx.discovery_time
          on_scc_stack := vset ctx.on_scc_stack sv.index true
          scc_stack := v4
          discovery_time := i2 }
        (Sigref.Tarjan.initNode g s { c with work := W }) := by
      rw [hcinit]
      refine ⟨?_, ?_, ?_, hsr.plen, ?_, ?_, ?_, hsr.blk, hsr.nb, ?_, hsr.work, ?_, hsr.eq⟩
      · show (vset ctx.low sv.index ctx.discovery_time).val.length = _
        rw [vset_val]; simpa using hsr.llen
      · show (vset ctx.disc sv.index ctx.discovery_time).val.length = _
        rw [vset_val]; simpa using hsr.dlen
      · show (vset ctx.on_scc_stack sv.index true).val.length = _
        rw [vset_val]; simpa using hsr.olen
      · show view _ _ _ (vset ctx.low sv.index ctx.discovery_time).val = _
        rw [vset_val, hsvs, view_set _ _ _ s (by rw [hsr.llen]; exact s.2), hsr.low, hsr.time]
      · show view _ _ _ (vset ctx.disc sv.index ctx.discovery_time).val = _
        rw [vset_val, hsvs, view_set _ _ _ s (by rw [hsr.dlen]; exact s.2), hsr.disc, hsr.time]
      · show view _ _ _ (vset ctx.on_scc_stack sv.index true).val = _
        rw [vset_val, hsvs, view_set _ _ _ s (by rw [hsr.olen]; exact s.2), hsr.onSt]
      · show v4.val.map _ = _
        rw [hv4, List.map_append, hsr.stk]; simp [hsvs]
      · show i2.val = c.time + 1
        rw [hi2v, hsr.time]
    obtain ⟨ctx', hct, hsr'⟩ := step_rest_spec LTSInst sys hwf n0 hns hn0 hid hnlt sv hsv off _
      _ hsr1 (by rw [hc1e]; show c.eq < Usize.max; omega)
      (by rw [hc1w]; show W.length + 1 < Usize.max; omega) W hc1w c' chm offm c2 hsc hres1 hres2
    refine ⟨ctx', ?_, hsr'⟩
    simp
    exact hct
  · have hcond : ¬ (ctx.low.val[sv.index.val]'hsl = SCC_UNVISITED) := by
      intro h
      apply hu
      rw [← hlv, h, unvisited_val]; rfl
    rw [if_neg hcond]
    have hcinit : Sigref.Tarjan.initNode g s { c with work := W } = { c with work := W } := by
      unfold Sigref.Tarjan.initNode
      simp [hu]
    rw [hcinit] at hsc
    obtain ⟨ctx', hct, hsr'⟩ := step_rest_spec LTSInst sys hwf n0 hns hn0 hid hnlt sv hsv off ctx
      { c with work := W } hsr (by show c.eq < Usize.max; omega)
      (by show W.length + 1 < Usize.max; omega) W rfl c' chm offm c2 hsc hres1 hres2
    refine ⟨ctx', ?_, hsr'⟩
    simp only [bind_ok]
    exact hct

open verified.merc_reduction.scc_decomposition in
theorem process_work_loop_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max) :
    ∀ (m : ℕ) (ctx : SC) (c : Sigref.Tarjan.Ctx n0.val),
      Sigref.Tarjan.measure (gOf LTSInst sys hn0 hnlt) c = m →
      Sigref.Tarjan.Inv (gOf LTSInst sys hn0 hnlt) c → SR n0.val ctx c →
      ∃ ctx' cE, scc_process_work_loop LTSInst sys ctx =
          ok (ctx'.partition, ctx'.low, ctx'.disc, ctx'.on_scc_stack, ctx'.scc_stack, ctx'.work,
            ctx'.discovery_time, ctx'.eq_class) ∧
        Relation.ReflTransGen (Sigref.Tarjan.Step (gOf LTSInst sys hn0 hnlt)) c cE ∧
        cE.work = [] ∧ SR n0.val ctx' cE ∧ cE.ri = c.ri := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro ctx c hm hI hsr
    unfold scc_process_work_loop
    rcases hcw : c.work with _ | ⟨⟨s, off⟩, W⟩
    · have hnil : ctx.work.val = [] := by
        have := hsr.work
        rw [hcw] at this
        simpa using this
      refine ⟨ctx, c, ?_, Relation.ReflTransGen.refl, hcw, hsr, rfl⟩
      apply loop_done'
      unfold scc_process_work_loop.body
      rw [alloc.vec.Vec.pop_nil_spec Global ctx.work hnil]
      simp
    · have hwv := hsr.work
      rw [hcw] at hwv
      rcases List.eq_nil_or_concat ctx.work.val with hnil | ⟨rest, x, hrest⟩
      · rw [hnil] at hwv; simp at hwv
      rw [List.concat_eq_append] at hrest
      obtain ⟨t, o⟩ := x
      have hwv' : rest.map (fun p : TagIndex Std.Usize StateTag × Std.Usize => (p.1.index.val, p.2.val)) ++
          [(t.index.val, o.val)] = (W.map fun p => (p.1.val, p.2)).reverse ++ [(s.val, off)] := by
        rw [hrest] at hwv; simpa using hwv
      obtain ⟨hrw, hxe⟩ := List.append_inj' hwv' (by simp)
      have hts : t.index.val = s.val := by simpa using (Prod.mk.inj (List.singleton_inj.mp hxe)).1
      have hos : o.val = off := by simpa using (Prod.mk.inj (List.singleton_inj.mp hxe)).2
      obtain ⟨D1, hpop, hD1v⟩ := alloc.vec.Vec.pop_cons_spec Global ctx.work (t, o) rest hrest
      obtain ⟨c', hstep, hI', hmeas⟩ := Sigref.Tarjan.step_cons hI hcw
      have hsvlt : t.index.val < n0.val := by rw [hts]; exact s.2
      have hsW : SR n0.val { ctx with work := D1 } { c with work := W } := by
        refine ⟨hsr.llen, hsr.dlen, hsr.olen, hsr.plen, hsr.low, hsr.disc, hsr.onSt, hsr.blk, hsr.nb,
          hsr.stk, ?_, hsr.time, hsr.eq⟩
        show D1.val.map _ = _
        rw [hD1v]; exact hrw
      have hsf : toFin hn0 t = s := Fin.ext (by rw [toFin_val hn0 t hsvlt, hts])
      obtain ⟨ctx1, hst, hsr1⟩ := step_spec LTSInst sys hwf n0 hns hn0 hid hnlt c hI t hsvlt o W
        (by rw [hsf, hos]; exact hcw) c' hstep { ctx with work := D1 } hsW
      obtain ⟨ctx', cE, hl, hreach, hwE, hsrE, hriE⟩ := ih _ (hm ▸ hmeas) ctx1 c' rfl hI' hsr1
      refine ⟨ctx', cE, ?_, Relation.ReflTransGen.head hstep hreach, hwE, hsrE,
        hriE.trans (Sigref.Tarjan.step_ri_cons hcw hstep)⟩
      have hb : scc_process_work_loop.body LTSInst sys ctx = ok (cont ctx1) := by
        unfold scc_process_work_loop.body
        rw [hpop]
        simp only [bind_ok]
        simp [hst]
      rw [loop_cont' _ _ _ hb]
      unfold scc_process_work_loop at hl
      exact hl

open verified.merc_reduction.scc_decomposition in
theorem process_work_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max)
    (ctx : SC) (c : Sigref.Tarjan.Ctx n0.val)
    (hI : Sigref.Tarjan.Inv (gOf LTSInst sys hn0 hnlt) c) (hsr : SR n0.val ctx c) :
    ∃ ctx' cE, scc_process_work LTSInst sys ctx = ok ctx' ∧
      Relation.ReflTransGen (Sigref.Tarjan.Step (gOf LTSInst sys hn0 hnlt)) c cE ∧
      cE.work = [] ∧ SR n0.val ctx' cE ∧ cE.ri = c.ri := by
  obtain ⟨ctx', cE, hl, hr, hw, hs, hri⟩ :=
    process_work_loop_spec LTSInst sys hwf n0 hns hn0 hid hnlt _ ctx c rfl hI hsr
  refine ⟨ctx', cE, ?_, hr, hw, hs, hri⟩
  unfold scc_process_work
  rw [hl]
  simp

end Step

section Roots

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

open verified.merc_reduction.scc_decomposition in
theorem visit_roots_loop_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max)
    (ctx0 : SC) (hsr0 : SR n0.val ctx0 (Sigref.Tarjan.init (gOf LTSInst sys hn0 hnlt))) :
    ∃ ctx cE, scc_visit_roots_loop LTSInst { start := 0#usize, «end» := n0 } sys ctx0 = ok ctx ∧
      Relation.ReflTransGen (Sigref.Tarjan.Step (gOf LTSInst sys hn0 hnlt))
        (Sigref.Tarjan.init (gOf LTSInst sys hn0 hnlt)) cE ∧
      cE.work = [] ∧ cE.ri = n0.val ∧ SR n0.val ctx cE := by
  set g := gOf LTSInst sys hn0 hnlt with hg
  unfold scc_visit_roots_loop
  have hspec := range_loop_spec (σ := SC) (ρ := SC)
    (fun x => scc_visit_roots_loop.body LTSInst sys x.1 x.2)
    (fun i ctx => ∃ c, Relation.ReflTransGen (Sigref.Tarjan.Step g) (Sigref.Tarjan.init g) c ∧
      c.work = [] ∧ c.ri = i ∧ SR n0.val ctx c)
    (fun r => ∃ c, Relation.ReflTransGen (Sigref.Tarjan.Step g) (Sigref.Tarjan.init g) c ∧
      c.work = [] ∧ c.ri = n0.val ∧ SR n0.val r c)
    n0 ?hsome ?hnone 0#usize ctx0 (by simp) ?h0
  case h0 => exact ⟨Sigref.Tarjan.init g, Relation.ReflTransGen.refl, rfl, rfl, hsr0⟩
  case hnone =>
    intro i ctx hi hinv
    obtain ⟨c, hreach, hw, hci, hsr⟩ := hinv
    obtain ⟨o, it1, hnext, hone, hident⟩ := MercVerified.Lts.Proofs.next_range_none
      ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) (by simp [hi])
    refine ⟨ctx, ?_, c, hreach, hw, by rw [hci, hi], hsr⟩
    unfold scc_visit_roots_loop.body
    rw [hnext, hone]
    simp
  case hsome =>
    intro i ctx hi hinv
    obtain ⟨c, hreach, hw, hci, hsr⟩ := hinv
    have hi' : i.val < n0.val := hi
    obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some
      ({ start := i, «end» := n0 } : core.ops.range.Range Std.Usize) (by simpa using hi)
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := n0 } := by rw [he1]
    rw [hit1] at hnext
    have hI := Sigref.Tarjan.inv_run g c hreach
    have hril : c.ri < n0.val := by rw [hci]; exact hi'
    have hfin : (⟨c.ri, hril⟩ : Fin n0.val) = ⟨i.val, hi'⟩ := Fin.ext hci
    have hsl : i.val < ctx.low.val.length := by rw [hsr.llen]; exact hi'
    have hlv : (ctx.low.val[i.val]'hsl).val = c.low ⟨i.val, hi'⟩ := by
      rw [← hsr.low, view_get _ _ _ ⟨i.val, hi'⟩ hsl]
    by_cases hu : c.low ⟨i.val, hi'⟩ = g.unv
    · have hcond : ctx.low.val[i.val]'hsl = SCC_UNVISITED :=
        UScalar.eq_of_val_eq (by rw [hlv, hu, unvisited_val]; rfl)
      have hc1 : Sigref.Tarjan.Step g c
          { c with work := [(⟨i.val, hi'⟩, 0)], ri := c.ri + 1 } := by
        unfold Sigref.Tarjan.Step Sigref.Tarjan.step
        rw [hw]
        simp only [hril, dif_pos]
        rw [hfin, if_pos hu]
      have hreach1 := Relation.ReflTransGen.tail hreach hc1
      have hI1 := Sigref.Tarjan.inv_run g _ hreach1
      have hnilw : ctx.work.val = [] := by
        have := hsr.work; rw [hw] at this; simpa using this
      obtain ⟨v, hpv, hvv⟩ := vec_push_val ctx.work
        (({ index := i, marker := () } : TagIndex Std.Usize StateTag), 0#usize)
        (by rw [hnilw]; simp; omega)
      have hsr0 : SR n0.val { ctx with work := v } { c with work := [(⟨i.val, hi'⟩, 0)], ri := c.ri + 1 } := by
        refine ⟨hsr.llen, hsr.dlen, hsr.olen, hsr.plen, hsr.low, hsr.disc, hsr.onSt, hsr.blk, hsr.nb,
          hsr.stk, ?_, hsr.time, hsr.eq⟩
        show v.val.map _ = _
        rw [hvv, hnilw]; simp
      obtain ⟨ctx', cE, hl, hrE, hwE, hsrE, hriE⟩ := process_work_spec LTSInst sys hwf n0 hns hn0 hid hnlt
        { ctx with work := v } _ hI1 hsr0
      refine ⟨st1, ctx', hs1, ?_, cE, hreach1.trans hrE, hwE, ?_, hsrE⟩
      · unfold scc_visit_roots_loop.body
        rw [hnext, hsome]
        simp
        rw [vec_index_usize_ok ctx.low i hsl]
        simp only [bind_ok]
        rw [if_pos hcond]
        simp [hpv, hl]
      · rw [hriE]; simp [hci]
    · have hcond : ¬ (ctx.low.val[i.val]'hsl = SCC_UNVISITED) := by
        intro h
        apply hu
        rw [← hlv, h, unvisited_val]; rfl
      have hc1 : Sigref.Tarjan.Step g c { c with ri := c.ri + 1 } := by
        unfold Sigref.Tarjan.Step Sigref.Tarjan.step
        rw [hw]
        simp only [hril, dif_pos]
        rw [hfin, if_neg hu]
      have hreach1 := Relation.ReflTransGen.tail hreach hc1
      refine ⟨st1, ctx, hs1, ?_, { c with ri := c.ri + 1 }, hreach1, hw, ?_,
        ⟨hsr.llen, hsr.dlen, hsr.olen, hsr.plen, hsr.low, hsr.disc, hsr.onSt, hsr.blk, hsr.nb,
          hsr.stk, hsr.work, hsr.time, hsr.eq⟩⟩
      · unfold scc_visit_roots_loop.body
        rw [hnext, hsome]
        simp
        rw [vec_index_usize_ok ctx.low i hsl]
        simp only [bind_ok]
        rw [if_neg hcond]
      · simp [hci]
  obtain ⟨r, hr, c, hrc, hw, hri, hsr⟩ := hspec
  exact ⟨r, c, hr, hrc, hw, hri, hsr⟩

end Roots

section Top

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

theorem view_replicate {α β : Type} (n : Nat) (f : α → β) (d : β) (x : α) :
    view n f d (List.replicate n x) = fun _ => f x := by
  funext i
  simp [view, i.2]

open verified.merc_reduction.scc_decomposition in
open verified.merc_collections.indexed_partition in
theorem tau_scc_spec (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hid : ∀ l : TagIndex Std.Usize LabelTag,
      LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0)))
    (hnlt : n0.val < Usize.max) :
    ∃ (ip : IndexedPartition) (k : Nat),
      tau_scc_decomposition_iterative LTSInst sys = ok ip ∧
      ip.partition.val.length = n0.val ∧ ip.num_of_blocks.val = max 1 k ∧
      Sigref.Tarjan.IsSccPartition (gOf LTSInst sys hn0 hnlt)
        (view n0.val (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val) k := by
  set g := gOf LTSInst sys hn0 hnlt with hg
  unfold tau_scc_decomposition_iterative
  rw [hns]
  simp only [bind_ok]
  have hclb : ∀ x : TagIndex Std.Usize BlockTag,
      (TagIndex.Insts.CoreCloneClone BlockTag core.clone.CloneUsize).clone x = ok x := by
    intro x
    simp [TagIndex.Insts.CoreCloneClone.clone]
  obtain ⟨vp, hvp, hvpv, _⟩ := spec_imp_exists (alloc.vec.from_elem_spec
    (TagIndex.Insts.CoreCloneClone BlockTag core.clone.CloneUsize)
    ({ index := 0#usize, marker := () } : TagIndex Std.Usize BlockTag) n0 (hclb _))
  have hnew : TagIndex.new BlockTag 0#usize = ok ({ index := 0#usize, marker := () } : TagIndex Std.Usize BlockTag) := by
    simp
  unfold IndexedPartition.new
  rw [hnew]
  simp only [bind_ok]
  rw [hvp]
  simp only [bind_ok]
  have hclu : ∀ x : Std.Usize, core.clone.CloneUsize.clone x = ok x := by intro x; simp
  have hclbo : ∀ x : Bool, core.clone.CloneBool.clone x = ok x := by intro x; simp
  obtain ⟨vl, hvl, hvlv, _⟩ := spec_imp_exists (alloc.vec.from_elem_spec core.clone.CloneUsize
    SCC_UNVISITED n0 (hclu _))
  obtain ⟨vo, hvo, hvov, _⟩ := spec_imp_exists (alloc.vec.from_elem_spec core.clone.CloneBool
    false n0 (hclbo _))
  rw [hvl]
  simp only [bind_ok]
  rw [hvo]
  simp only [bind_ok]
  set ctx0 : SC :=
    { partition := { partition := vp, num_of_blocks := 1#usize }, low := vl, disc := vl, on_scc_stack := vo,
      scc_stack := alloc.vec.Vec.new Usize, work := alloc.vec.Vec.new (TagIndex Usize StateTag × Usize),
      discovery_time := 0#usize, eq_class := 0#usize } with hctx0
  have hsr0 : SR n0.val ctx0 (Sigref.Tarjan.init g) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show vl.val.length = _; rw [hvlv]; simp
    · show vl.val.length = _; rw [hvlv]; simp
    · show vo.val.length = _; rw [hvov]; simp
    · show vp.val.length = _; rw [hvpv]; simp
    · show view _ _ _ vl.val = _; rw [hvlv, view_replicate]; funext i; simp [Sigref.Tarjan.init, hg, gOf, unvisited_val]
    · show view _ _ _ vl.val = _; rw [hvlv, view_replicate]; funext i; simp [Sigref.Tarjan.init, hg, gOf, unvisited_val]
    · show view _ _ _ vo.val = _; rw [hvov, view_replicate]; funext i; simp [Sigref.Tarjan.init]
    · show view _ _ _ vp.val = _; rw [hvpv, view_replicate]; funext i; simp [Sigref.Tarjan.init]
    · simp [Sigref.Tarjan.init, hctx0]
    · simp [Sigref.Tarjan.init, hctx0, alloc.vec.Vec.new]
    · simp [Sigref.Tarjan.init, hctx0, alloc.vec.Vec.new]
    · simp [Sigref.Tarjan.init, hctx0]
    · simp [Sigref.Tarjan.init, hctx0]
  obtain ⟨ctx, cE, hl, hreach, hw, hri, hsr⟩ :=
    visit_roots_loop_spec LTSInst sys hwf n0 hns hn0 hid hnlt ctx0 hsr0
  have hstop : Sigref.Tarjan.step g cE = Sigref.Tarjan.Out.stop := by
    simp [Sigref.Tarjan.step, hw, hri]
  have hpart := ((Sigref.Tarjan.tarjanCorrect g) cE hreach).1 hstop
  refine ⟨ctx.partition, cE.eq, ?_, hsr.plen, by rw [hsr.nb], ?_⟩
  · unfold scc_visit_roots
    rw [hns]
    simp only [bind_ok]
    rw [hl]
    simp
  · rw [hsr.blk]; exact hpart

end Top

end MercVerified.Refinement.Proofs
