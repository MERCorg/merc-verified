import MercVerified.Lts.Proofs.LabelledTransitionSystem_Proofs

/-!
# The logical content of a `LabelledTransitionSystem`

`RawOf sys n off labs tos` says that `sys` stores the offsets `off`, the transition labels `labs` and
the transition targets `tos` (by the `toList` model of `ByteCompressedVec`) and that these satisfy the
structural invariants of `assert_valid`. From it we derive `LabelledTransitionSystemValid` and the
exact outgoing transitions of every state (`raw_outgoing`).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel Transition LTS)
open verified.merc_lts.labelled_transition_system (LabelledTransitionSystem)
open merc_collections.compressed_vec (ByteCompressedVec)

namespace MercVerified.Lts.Proofs

noncomputable abbrev UIdx := verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry

noncomputable abbrev LIdx :=
  verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
    LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize

noncomputable abbrev SIdx :=
  verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
    StateTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize

/-- The stored arrays of `sys` and the invariants of `assert_valid`. -/
structure RawOf {Label : Type} (sys : LabelledTransitionSystem Label) (n : Nat) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag)) : Prop where
  st : (ByteCompressedVec.toList sys.states).map (fun u : Std.Usize => u.val) = off
  lab : ByteCompressedVec.toList sys.transition_labels = labs
  tl : ByteCompressedVec.toList sys.transition_to = tos
  offlen : off.length = n + 1
  mono : off.Pairwise (· ≤ ·)
  last : off.getLast? = some labs.length
  len_eq : labs.length = tos.length
  tlt : ∀ t ∈ tos, t.index.val < n
  init : sys.initial_state.index.val < n
  small : n * (n + 2) ≤ Std.Usize.max
  tmax : labs.length < Std.Usize.max

theorem RawOf.n_pos {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) : 0 < n := by
  have := h.init; omega

theorem RawOf.off_le {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) : n + 1 ≤ Std.Usize.max := by
  have := h.small
  have := h.n_pos
  nlinarith

theorem le_last_of_pairwise {l : List Nat} {L : Nat} (hp : l.Pairwise (· ≤ ·))
    (hl : l.getLast? = some L) : ∀ x ∈ l, x ≤ L := by
  intro x hx
  obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hl
  rw [hl'] at hp hx
  rw [List.pairwise_append] at hp
  rcases List.mem_append.mp hx with h | h
  · exact hp.2.2 x h L (by simp)
  · simp at h; omega

theorem RawOf.st_length {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) : (ByteCompressedVec.toList sys.states).length = n + 1 := by
  have := congrArg List.length h.st
  simpa [h.offlen] using this

theorem RawOf.st_get {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (i : Nat) (hi : i < (ByteCompressedVec.toList sys.states).length) :
    ((ByteCompressedVec.toList sys.states)[i]).val = off.getD i 0 := by
  rw [← h.st]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem raw_valid {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) : LabelledTransitionSystemValid sys := by
  have hn := h.n_pos
  have hmax := h.off_le
  have hlenS := h.st_length
  have hbound := le_last_of_pairwise h.mono h.last
  have hoff := h.offlen
  have htm := h.tmax
  refine ⟨n, labs.length, fun i => off.getD i 0, ?_, ?_, ?_, ?_, h.init, ?_, ?_, h.small, ?_, h.tmax⟩
  · obtain ⟨l, hl, hlv⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec UIdx sys.states
      (by omega)
    exact ⟨l, hl, by rw [hlv, hlenS]⟩
  · intro i hi
    have hi' : i.val < (ByteCompressedVec.toList sys.states).length := by omega
    exact ⟨_, merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states i hi',
      h.st_get i.val hi'⟩
  · intro i hi
    have := List.pairwise_iff_getElem.mp h.mono i (i + 1) (by omega) (by omega) (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < off.length by omega),
      List.getElem?_eq_getElem (show i + 1 < off.length by omega)] using this
  · have := h.last
    rw [List.getLast?_eq_getElem?, h.offlen] at this
    simp at this
    simp [List.getD_eq_getElem?_getD, this]
  · intro k hk
    have hk' : k.val < (ByteCompressedVec.toList sys.transition_labels).length := by
      rw [h.lab]; exact hk
    exact ⟨_, merc_collections.compressed_vec.ByteCompressedVec.index_spec LIdx sys.transition_labels k hk'⟩
  · intro k hk
    have hk' : k.val < (ByteCompressedVec.toList sys.transition_to).length := by
      rw [h.tl, ← h.len_eq]; exact hk
    refine ⟨_, merc_collections.compressed_vec.ByteCompressedVec.index_spec SIdx sys.transition_to k hk', ?_⟩
    apply h.tlt
    rw [← h.tl]; exact List.getElem_mem _
  · have hl : (ByteCompressedVec.toList sys.transition_labels).length ≤ Std.Usize.max := by
      rw [h.lab]; omega
    obtain ⟨l, hl', hlv⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec LIdx
      sys.transition_labels hl
    exact ⟨l, hl', by rw [hlv, h.lab]⟩

theorem loop_unfold_step {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) :
    Aeneas.Std.loop body x
      = (do
          let r ← body x
          match r with
          | ControlFlow.cont c => Aeneas.Std.loop body c
          | ControlFlow.done d => ok d) := by
  rw [Aeneas.Std.loop]
  rfl

/-- The transitions stored between two offsets. -/
def segment (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (a m : Nat) : List Transition :=
  List.zipWith (fun l t => ({ label := l, «to» := t } : Transition)) ((labs.drop a).take m)
    ((tos.drop a).take m)

theorem segment_succ (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (a m : Nat) (hl : a < labs.length) (ht : a < tos.length) :
    segment labs tos a (m + 1) = ({ label := labs[a], «to» := tos[a] } : Transition) ::
      segment labs tos (a + 1) m := by
  unfold segment
  rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons ht, List.take_succ_cons,
    List.take_succ_cons, List.zipWith_cons_cons]

theorem outgoing_loop_content (bcv : ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (bcv1 : ByteCompressedVec (TagIndex Std.Usize StateTag))
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (hl : ByteCompressedVec.toList bcv = labs) (ht : ByteCompressedVec.toList bcv1 = tos)
    (hlen : labs.length = tos.length) (_hmax : labs.length < Std.Usize.max) :
    ∀ m (iter : core.ops.range.Range Std.Usize) (result : alloc.vec.Vec Transition),
      iter.«end».val - iter.start.val = m → iter.«end».val ≤ labs.length →
      result.val.length + m < Std.Usize.max →
      ∃ result',
        verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop
          iter bcv bcv1 result = ok result' ∧
        result'.val = result.val ++ segment labs tos iter.start.val m := by
  let ul : (core.ops.range.Range Std.Usize × alloc.vec.Vec Transition) →
      Result (ControlFlow (core.ops.range.Range Std.Usize × alloc.vec.Vec Transition)
        (alloc.vec.Vec Transition)) :=
    fun (iter1, result1) =>
      verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body
        bcv bcv1 iter1 result1
  have hloop_unfold : ∀ (it : core.ops.range.Range Std.Usize) (r : alloc.vec.Vec Transition),
      Aeneas.Std.loop ul (it, r) =
        verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop
          it bcv bcv1 r := by
    intro it r
    rw [verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop]
  intro m
  induction m with
  | zero =>
    intro iter result hm hend hcap
    refine ⟨result, ?_, by simp [segment]⟩
    rw [← hloop_unfold, loop_unfold_step]
    have hge : iter.start.val ≥ iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hident⟩ := next_range_none iter hge
    have hbody : ul (iter, result) = ok (ControlFlow.done result) := by
      show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body
        bcv bcv1 iter result = ok (ControlFlow.done result)
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body
      rw [hnext, ho]
      simp
    simp [hbody]
  | succ m ih =>
    intro iter result hm hend hcap
    have hlt : iter.start.val < iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hstart', hend'⟩ := next_range_some iter hlt
    have hk1 : iter.start.val < labs.length := by omega
    have hk2 : iter.start.val < tos.length := by omega
    have hkl : iter.start.val < (ByteCompressedVec.toList bcv).length := by rw [hl]; exact hk1
    have hkt : iter.start.val < (ByteCompressedVec.toList bcv1).length := by rw [ht]; exact hk2
    have hvl := merc_collections.compressed_vec.ByteCompressedVec.index_spec LIdx bcv iter.start hkl
    have hvt := merc_collections.compressed_vec.ByteCompressedVec.index_spec SIdx bcv1 iter.start hkt
    have hvl' : (ByteCompressedVec.toList bcv)[iter.start.val] = labs[iter.start.val] := by
      simp [hl]
    have hvt' : (ByteCompressedVec.toList bcv1)[iter.start.val] = tos[iter.start.val] := by
      simp [ht]
    rw [hvl'] at hvl
    rw [hvt'] at hvt
    obtain ⟨result1, hpush', hpushv⟩ := vec_push_val result
      ({ label := labs[iter.start.val], «to» := tos[iter.start.val] } : Transition) (by omega)
    have hbody : ul (iter, result) = ok (ControlFlow.cont (iter1, result1)) := by
      show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body
        bcv bcv1 iter result = ok (ControlFlow.cont (iter1, result1))
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body
      simp [hnext, ho, hvl, hvt, hpush']
    have hlen1 : result1.val.length = result.val.length + 1 := by rw [hpushv]; simp
    have hn1 : iter1.«end».val - iter1.start.val = m := by
      have : iter1.«end».val = iter.«end».val := by rw [hend']
      omega
    obtain ⟨result', hloop', hv'⟩ := ih iter1 result1 hn1 (by rw [hend']; exact hend) (by omega)
    refine ⟨result', ?_, ?_⟩
    · rw [← hloop_unfold, loop_unfold_step, hbody]
      simp [hloop_unfold, hloop']
    · rw [hv', hpushv, segment_succ labs tos _ m hk1 hk2, hstart']
      simp

theorem RawOf.off_mono {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) {i j : Nat} (hij : i ≤ j) (hj : j < n + 1) :
    off.getD i 0 ≤ off.getD j 0 := by
  have hoff := h.offlen
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · have := List.pairwise_iff_getElem.mp h.mono i j (by omega) (by omega) hlt
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < off.length by omega),
      List.getElem?_eq_getElem (show j < off.length by omega)] using this

theorem RawOf.off_le_labs {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) {i : Nat} (hi : i < n + 1) : off.getD i 0 ≤ labs.length := by
  have hoff := h.offlen
  apply le_last_of_pairwise h.mono h.last
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < off.length by omega)]
  simp

theorem raw_outgoing {Label : Type} (TLInst : TransitionLabel Label)
    {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (s : TagIndex Std.Usize StateTag) (hs : s.index.val < n) :
    ∃ ts : alloc.vec.Vec Transition,
      (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).outgoing_transitions sys s = ok ts ∧
      ts.val = segment labs tos (off.getD s.index.val 0)
        (off.getD (s.index.val + 1) 0 - off.getD s.index.val 0) := by
  have hoff := h.offlen
  have hlenS := h.st_length
  have htm := h.tmax
  have hmax := h.off_le
  have hsl : s.index.val < (ByteCompressedVec.toList sys.states).length := by omega
  have hstart := merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states s.index hsl
  obtain ⟨i1, hi1, hi1v⟩ := spec_imp_exists (Usize.add_spec (x := s.index) (y := 1#usize)
    (by simp; omega))
  have hi1v' : i1.val = s.index.val + 1 := by simpa using hi1v
  have hel : i1.val < (ByteCompressedVec.toList sys.states).length := by omega
  have hend := merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states i1 hel
  set startV := (ByteCompressedVec.toList sys.states)[s.index.val] with hsV
  set endV := (ByteCompressedVec.toList sys.states)[i1.val] with heV
  have hsv : startV.val = off.getD s.index.val 0 := h.st_get _ hsl
  have hev : endV.val = off.getD (s.index.val + 1) 0 := by rw [h.st_get _ hel, hi1v']
  have hle : startV.val ≤ endV.val := by
    rw [hsv, hev]; exact h.off_mono (by omega) (by omega)
  obtain ⟨i2, hi2, hi2v⟩ := spec_imp_exists (Usize.sub_spec (x := endV) (y := startV) hle)
  have hi2v' : i2.val = endV.val - startV.val := (by simpa using hi2v : _ ∧ _).1
  have hendle : endV.val ≤ labs.length := by rw [hev]; exact h.off_le_labs (by omega)
  have hwc : (alloc.vec.Vec.with_capacity Transition i2).val = [] := by
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  obtain ⟨res, hres, hresv⟩ := outgoing_loop_content sys.transition_labels sys.transition_to
    labs tos h.lab h.tl h.len_eq h.tmax (endV.val - startV.val)
    { start := startV, «end» := endV } (alloc.vec.Vec.with_capacity Transition i2) rfl hendle
    (by rw [hwc]; simp; omega)
  refine ⟨res, ?_, ?_⟩
  · show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions
      TLInst sys s = ok res
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions
    have hderef : verified.merc_utilities.tagged_index.TagIndex.Insts.CoreOpsDerefDeref.deref s
        = ok s.index := rfl
    simp [hderef, hstart, hi1, hend, hi2]
    exact hres
  · rw [hresv, hwc]
    simp [hsv, hev]

theorem massert_of (b : Prop) [Decidable b] (h : b) : massert b = ok () := by
  unfold massert; simp [h]

/-- A `loop` over a `Range` whose body only checks: every step with index in `[lo, e)` advances by one,
    and the exhausted range finishes. -/
theorem range_check_loop
    (body : core.ops.range.Range Std.Usize → Result (ControlFlow (core.ops.range.Range Std.Usize) Unit))
    (e : Std.Usize) (lo : Nat)
    (hsome : ∀ i : Std.Usize, lo ≤ i.val → i.val < e.val →
      ∃ i1 : Std.Usize, i1.val = i.val + 1 ∧
        body ({ start := i, «end» := e } : core.ops.range.Range Std.Usize)
          = ok (cont ({ start := i1, «end» := e } : core.ops.range.Range Std.Usize)))
    (hnone : ∀ i : Std.Usize, i.val = e.val →
      body ({ start := i, «end» := e } : core.ops.range.Range Std.Usize) = ok (done ()))
    (start : Std.Usize) (hlo : lo ≤ start.val) (hst : start.val ≤ e.val) :
    loop body ({ start := start, «end» := e } : core.ops.range.Range Std.Usize) = ok () := by
  have : ∃ r : Unit, loop body ({ start := start, «end» := e } : core.ops.range.Range Std.Usize) = ok r ∧ True := by
    apply Std.WP.spec_imp_exists
    apply loop.spec_decr_nat
      (measure := fun x => e.val - x.start.val)
      (inv := fun x => x.«end» = e ∧ lo ≤ x.start.val ∧ x.start.val ≤ e.val)
    · rintro ⟨i, e'⟩ ⟨hend, hlo', hle⟩
      simp only at hend hlo' hle
      subst hend
      by_cases hlt : i.val < e'.val
      · obtain ⟨i1, hi1, hb⟩ := hsome i hlo' hlt
        exact Std.WP.exists_imp_spec ⟨cont _, hb, ⟨rfl, by simp only; omega, by simp only; omega⟩,
          by simp only; omega⟩
      · have heq : i.val = e'.val := by omega
        exact Std.WP.exists_imp_spec ⟨done (), hnone i heq, trivial⟩
    · exact ⟨rfl, hlo, hst⟩
  obtain ⟨r, hr, -⟩ := this
  cases r
  exact hr

theorem offsets_valid_ok {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (nU : Std.Usize) (hnU : nU.val = n) :
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid_loop
      { start := 0#usize, «end» := nU } sys = ok () := by
  have hoff := h.offlen
  have hmax := h.off_le
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid_loop
  apply range_check_loop _ nU 0
  · intro i _ hi
    have hi' : i.val < n := by omega
    obtain ⟨i2, hi2, hi2v⟩ := spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi2v' : i2.val = i.val + 1 := by simpa using hi2v
    obtain ⟨o, it1, hnext, ho, hs1, he1⟩ := next_range_some
      ({ start := i, «end» := nU } : core.ops.range.Range Std.Usize) hi
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := nU } := by rw [he1]
    rw [hit1] at hnext
    refine ⟨st1, hs1, ?_⟩
    have hl1 : i.val < (ByteCompressedVec.toList sys.states).length := by rw [h.st_length]; omega
    have hl2 : i2.val < (ByteCompressedVec.toList sys.states).length := by rw [h.st_length]; omega
    have e1 := merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states i hl1
    have e2 := merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states i2 hl2
    have hle : ((ByteCompressedVec.toList sys.states)[i.val]'hl1).val ≤
        ((ByteCompressedVec.toList sys.states)[i2.val]'hl2).val := by
      rw [h.st_get _ hl1, h.st_get _ hl2, hi2v']
      exact h.off_mono (by omega) (by omega)
    have hm := massert_of _ hle
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid_loop.body
    simp [hnext, ho, e1, hi2, e2, hm]
  · intro i hi
    obtain ⟨o, it1, hnext, ho, hident⟩ := next_range_none
      ({ start := i, «end» := nU } : core.ops.range.Range Std.Usize) (by simp [hi])
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid_loop.body
    rw [hnext, ho]
    simp
  · simp
  · simp [hnU]

theorem vec_len_val' {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.len v).val = v.val.length := by
  simp [alloc.vec.Vec.len]

theorem vec_index_ok' {U : Type} (v : alloc.vec.Vec U) (i : Std.Usize)
    (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U) v i = ok (v.val[i.val]'h) := by
  have hs := Slice.index_usize_spec v.slice i (by simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h)
  obtain ⟨x, hx, hxe⟩ := Std.WP.spec_imp_exists hs
  simp only [alloc.vec.Vec.index, core.slice.index.Usize.index]
  rw [hx, hxe]
  rfl

theorem tag_eq_ok {Tag : Type} (a b : TagIndex Std.Usize Tag) :
    verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq
      core.cmp.PartialEqUsize a b = ok (decide (a.index.val = b.index.val)) := by
  rw [tag_partial_eq_inst]
  simp only
  by_cases h : a.index = b.index
  · simp [h]
  · have : a.index.val ≠ b.index.val := fun e => h (UScalar.eq_of_val_eq e)
    simp [h, this]

/-- Side conditions of `assert_valid` beyond `RawOf`. -/
structure RawGood {Label : Type} (sys : LabelledTransitionSystem Label) (n : Nat) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag)) : Prop where
  labs_lt : ∀ l ∈ labs, l.index.val < sys.labels.val.length
  nodup : ∀ s, s < n → ∀ i j, off.getD s 0 ≤ i → i < j → j < off.getD (s + 1) 0 →
    ∀ (hi : i < labs.length) (hj : j < labs.length) (hi' : i < tos.length) (hj' : j < tos.length),
      labs[i] = labs[j] → tos[i] = tos[j] → False

theorem transitions_valid_ok {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (g : RawGood sys n off labs tos) (nU tU : Std.Usize)
    (hnU : nU.val = n) (htU : tU.val = labs.length) :
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid_loop
      { start := 0#usize, «end» := tU } sys nU = ok () := by
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid_loop
  apply range_check_loop _ tU 0
  · intro i _ hi
    obtain ⟨o, it1, hnext, ho, hs1, he1⟩ := next_range_some
      ({ start := i, «end» := tU } : core.ops.range.Range Std.Usize) hi
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := tU } := by rw [he1]
    rw [hit1] at hnext
    refine ⟨st1, hs1, ?_⟩
    have hil : i.val < labs.length := by omega
    have hit : i.val < tos.length := by rw [← h.len_eq]; exact hil
    have hl1 : i.val < (ByteCompressedVec.toList sys.transition_labels).length := by rw [h.lab]; exact hil
    have hl2 : i.val < (ByteCompressedVec.toList sys.transition_to).length := by rw [h.tl]; exact hit
    have e1 := merc_collections.compressed_vec.ByteCompressedVec.index_spec LIdx sys.transition_labels i hl1
    have e2 := merc_collections.compressed_vec.ByteCompressedVec.index_spec SIdx sys.transition_to i hl2
    have hlt1 : ((ByteCompressedVec.toList sys.transition_labels)[i.val]'hl1).index.val <
        sys.labels.val.length := by
      apply g.labs_lt; rw [← h.lab]; exact List.getElem_mem _
    have hlt2 : ((ByteCompressedVec.toList sys.transition_to)[i.val]'hl2).index.val < nU.val := by
      rw [hnU]; apply h.tlt; rw [← h.tl]; exact List.getElem_mem _
    have hm1 := massert_of _ hlt1
    have hm2 := massert_of _ hlt2
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid_loop.body
    simp [hnext, ho, e1, e2, hm1, hm2, alloc.vec.Vec.len]
  · intro i hi
    obtain ⟨o, it1, hnext, ho, hident⟩ := next_range_none
      ({ start := i, «end» := tU } : core.ops.range.Range Std.Usize) (by simp [hi])
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid_loop.body
    rw [hnext, ho]
    simp
  · simp
  · simp

theorem unique_inner_ok {Label : Type} {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (i end_ : Std.Usize) (hend : end_.val ≤ labs.length)
    (hdup : ∀ j, i.val < j → j < end_.val →
      ∀ (hi : i.val < labs.length) (hj : j < labs.length) (hi' : i.val < tos.length) (hj' : j < tos.length),
        labs[i.val] = labs[j] → tos[i.val] = tos[j] → False)
    (hi : i.val < end_.val) (i1 : Std.Usize) (hi1 : i1.val = i.val + 1) :
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique_loop
      { start := i1, «end» := end_ } sys i = ok () := by
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique_loop
  apply range_check_loop _ end_ (i.val + 1)
  · intro j hjlo hj
    obtain ⟨o, it1, hnext, ho, hs1, he1⟩ := next_range_some
      ({ start := j, «end» := end_ } : core.ops.range.Range Std.Usize) hj
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := end_ } := by rw [he1]
    rw [hit1] at hnext
    refine ⟨st1, hs1, ?_⟩
    have hil : i.val < labs.length := by omega
    have hjl : j.val < labs.length := by omega
    have hit : i.val < tos.length := by rw [← h.len_eq]; exact hil
    have hjt : j.val < tos.length := by rw [← h.len_eq]; exact hjl
    have hli : i.val < (ByteCompressedVec.toList sys.transition_labels).length := by rw [h.lab]; exact hil
    have hlj : j.val < (ByteCompressedVec.toList sys.transition_labels).length := by rw [h.lab]; exact hjl
    have hti : i.val < (ByteCompressedVec.toList sys.transition_to).length := by rw [h.tl]; exact hit
    have htj : j.val < (ByteCompressedVec.toList sys.transition_to).length := by rw [h.tl]; exact hjt
    have e1 := merc_collections.compressed_vec.ByteCompressedVec.index_spec LIdx sys.transition_labels i hli
    have e2 := merc_collections.compressed_vec.ByteCompressedVec.index_spec LIdx sys.transition_labels j hlj
    have e3 := merc_collections.compressed_vec.ByteCompressedVec.index_spec SIdx sys.transition_to i hti
    have e4 := merc_collections.compressed_vec.ByteCompressedVec.index_spec SIdx sys.transition_to j htj
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique_loop.body
    by_cases hb : ((ByteCompressedVec.toList sys.transition_labels)[i.val]'hli).index.val =
        ((ByteCompressedVec.toList sys.transition_labels)[j.val]'hlj).index.val
    · have hne : ¬ (((ByteCompressedVec.toList sys.transition_to)[i.val]'hti).index.val =
          ((ByteCompressedVec.toList sys.transition_to)[j.val]'htj).index.val) := by
        intro hh
        apply hdup j.val (by omega) hj hil hjl hit hjt
        · have := merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq hb)
          simpa [h.lab] using this
        · have := merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq hh)
          simpa [h.tl] using this
      have hm := massert_of (¬ (((ByteCompressedVec.toList sys.transition_to)[i.val]'hti).index.val =
          ((ByteCompressedVec.toList sys.transition_to)[j.val]'htj).index.val)) hne
      have hbI := UScalar.eq_of_val_eq hb
      simp [hnext, ho, e1, e2, e3, e4, hbI, hm]
    · have hbI : ¬ (((ByteCompressedVec.toList sys.transition_labels)[i.val]'hli).index =
          ((ByteCompressedVec.toList sys.transition_labels)[j.val]'hlj).index) :=
        fun e => hb (congrArg UScalar.val e)
      simp [hnext, ho, e1, e2, hbI]
  · intro j hj
    obtain ⟨o, it1, hnext, ho, hident⟩ := next_range_none
      ({ start := j, «end» := end_ } : core.ops.range.Range Std.Usize) (by simp [hj])
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique_loop.body
    rw [hnext, ho]
    simp
  · omega
  · omega

theorem unique_ok {Label : Type} (TLInst : TransitionLabel Label)
    {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (i end_ : Std.Usize) (hend : end_.val ≤ labs.length)
    (hdup : ∀ j, i.val < j → j < end_.val →
      ∀ (hi : i.val < labs.length) (hj : j < labs.length) (hi' : i.val < tos.length) (hj' : j < tos.length),
        labs[i.val] = labs[j] → tos[i.val] = tos[j] → False)
    (hi : i.val < end_.val) :
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique
      TLInst sys i end_ = ok () := by
  have hmax := h.tmax
  obtain ⟨i1, hi1, hi1v⟩ := spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
  have hi1v' : i1.val = i.val + 1 := by simpa using hi1v
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique
  rw [hi1]
  simp only [bind_ok]
  exact unique_inner_ok h i end_ hend hdup hi i1 hi1v'

theorem loop00_ok {Label : Type} (TLInst : TransitionLabel Label)
    {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (a b : Std.Usize) (hab : a.val ≤ b.val) (hb : b.val ≤ labs.length)
    (hdup : ∀ i j, a.val ≤ i → i < j → j < b.val →
      ∀ (hi : i < labs.length) (hj : j < labs.length) (hi' : i < tos.length) (hj' : j < tos.length),
        labs[i] = labs[j] → tos[i] = tos[j] → False) :
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0_loop0
      TLInst { start := a, «end» := b } sys.states sys.transition_labels sys.transition_to sys.labels
      sys.initial_state b = ok () := by
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0_loop0
  apply range_check_loop _ b a.val
  · intro i hlo hi
    obtain ⟨o, it1, hnext, ho, hs1, he1⟩ := next_range_some
      ({ start := i, «end» := b } : core.ops.range.Range Std.Usize) hi
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := b } := by rw [he1]
    rw [hit1] at hnext
    refine ⟨st1, hs1, ?_⟩
    have hu := unique_ok TLInst h i b hb (fun j hij hjb hi hj hi' hj' => hdup i.val j hlo hij hjb hi hj hi' hj') hi
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0_loop0.body
    simp [hnext, ho, hu]
  · intro i hi
    obtain ⟨o, it1, hnext, ho, hident⟩ := next_range_none
      ({ start := i, «end» := b } : core.ops.range.Range Std.Usize) (by simp [hi])
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0_loop0.body
    rw [hnext, ho]
    simp
  · simp
  · simpa using hab

theorem no_dup_ok {Label : Type} (TLInst : TransitionLabel Label)
    {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (g : RawGood sys n off labs tos) (nU : Std.Usize) (hnU : nU.val = n) :
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions
      TLInst sys nU = ok () := by
  have hoff := h.offlen
  have hmax := h.off_le
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0
  apply range_check_loop _ nU 0
  · intro i _ hi
    have hi' : i.val < n := by omega
    obtain ⟨o, it1, hnext, ho, hs1, he1⟩ := next_range_some
      ({ start := i, «end» := nU } : core.ops.range.Range Std.Usize) hi
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := nU } := by rw [he1]
    rw [hit1] at hnext
    refine ⟨st1, hs1, ?_⟩
    obtain ⟨i2, hi2, hi2v⟩ := spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi2v' : i2.val = i.val + 1 := by simpa using hi2v
    have hl1 : i.val < (ByteCompressedVec.toList sys.states).length := by rw [h.st_length]; omega
    have hl2 : i2.val < (ByteCompressedVec.toList sys.states).length := by rw [h.st_length]; omega
    have e1 := merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states i hl1
    have e2 := merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states i2 hl2
    set a := (ByteCompressedVec.toList sys.states)[i.val]'hl1 with ha
    set b := (ByteCompressedVec.toList sys.states)[i2.val]'hl2 with hb
    have hav : a.val = off.getD i.val 0 := h.st_get _ hl1
    have hbv : b.val = off.getD (i.val + 1) 0 := by rw [h.st_get _ hl2, hi2v']
    have hab : a.val ≤ b.val := by rw [hav, hbv]; exact h.off_mono (by omega) (by omega)
    have hbl : b.val ≤ labs.length := by rw [hbv]; exact h.off_le_labs (by omega)
    have hl00 := loop00_ok TLInst h a b hab hbl (by
      intro i' j hai hij hj hil hjl hit hjt
      exact g.nodup i.val hi' i' j (by rw [← hav]; exact hai) hij (by rw [← hbv]; exact hj) hil hjl hit hjt)
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0.body
    simp [hnext, ho, e1, hi2, e2, hl00]
  · intro i hi
    obtain ⟨o, it1, hnext, ho, hident⟩ := next_range_none
      ({ start := i, «end» := nU } : core.ops.range.Range Std.Usize) (by simp [hi])
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0.body
    rw [hnext, ho]
    simp
  · simp
  · simp

theorem assert_valid_ok {Label : Type} (TLInst : TransitionLabel Label)
    {sys : LabelledTransitionSystem Label} {n : Nat} {off labs tos}
    (h : RawOf sys n off labs tos) (g : RawGood sys n off labs tos)
    (hlab : 1 ≤ sys.labels.val.length)
    (htau : ∃ t, sys.labels.val[0]? = some t ∧ TLInst.is_tau_label t = ok true) :
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_valid TLInst sys
      = ok () := by
  have hoff := h.offlen
  have hmax := h.off_le
  have htm := h.tmax
  have hn := h.n_pos
  obtain ⟨ls, hls, hlsv⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec UIdx sys.states
    (by rw [h.st_length]; omega)
  rw [h.st_length] at hlsv
  obtain ⟨nU, hnU, hnUv⟩ := spec_imp_exists (Usize.sub_spec (x := ls) (y := 1#usize) (by simp; omega))
  have hnUv' : nU.val = n := by have := hnUv.1; simp at this; omega
  obtain ⟨tl, htl, htlv⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec LIdx
    sys.transition_labels (by rw [h.lab]; omega)
  rw [h.lab] at htlv
  obtain ⟨tl2, htl2, htlv2⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec SIdx
    sys.transition_to (by rw [h.tl, ← h.len_eq]; omega)
  rw [h.tl, ← h.len_eq] at htlv2
  have hnsl : nU.val < (ByteCompressedVec.toList sys.states).length := by rw [h.st_length]; omega
  have e1 := merc_collections.compressed_vec.ByteCompressedVec.index_spec UIdx sys.states nU hnsl
  have hsent : ((ByteCompressedVec.toList sys.states)[nU.val]'hnsl).val = tl.val := by
    rw [h.st_get _ hnsl, hnUv', htlv]
    have := h.last
    rw [List.getLast?_eq_getElem?, hoff] at this
    simp at this
    simp [List.getD_eq_getElem?_getD, this]
  obtain ⟨t0, ht0, htau0⟩ := htau
  have hlab0 : 0 < sys.labels.val.length := by omega
  have hm1 : massert (ls ≥ 1#usize) = ok () := massert_of _ (by show (1#usize).val ≤ ls.val; rw [hlsv]; simp)
  have hm2 : massert (sys.initial_state.index < nU) = ok () :=
    massert_of _ (by show sys.initial_state.index.val < nU.val; rw [hnUv']; exact h.init)
  have hm3 : massert ((ByteCompressedVec.toList sys.states)[nU.val]'hnsl = tl) = ok () :=
    massert_of _ (UScalar.eq_of_val_eq hsent)
  have hm4 : massert (tl = tl2) = ok () := massert_of _ (UScalar.eq_of_val_eq (by rw [htlv, htlv2]))
  have hm5 : massert (alloc.vec.Vec.len sys.labels ≥ 1#usize) = ok () :=
    massert_of _ (by show 1 ≤ (alloc.vec.Vec.len sys.labels).val; rw [vec_len_val']; simpa using hlab)
  have hidx0 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Label) sys.labels 0#usize
      = ok t0 := by
    rw [vec_index_ok' sys.labels 0#usize (by simpa using hlab0)]
    simp [List.getElem?_eq_getElem hlab0] at ht0
    simp [ht0]
  have hm6 : massert true = ok () := by simp
  have hoff_ok := offsets_valid_ok h nU hnUv'
  have htr_ok := transitions_valid_ok h g nU tl hnUv' htlv
  have hdup_ok := no_dup_ok TLInst h g nU hnUv'
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_valid
  unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_states
    verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_transitions
  simp only [hls, bind_ok, hnU, htl]
  have hoff2 : verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid
      TLInst sys nU = ok () := hoff_ok
  have htr2 : verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid
      TLInst sys nU tl = ok () := htr_ok
  simp only [hm1, bind_ok, tag_value_id, hm2, e1, hm3, htl2, hm4, hm5, hidx0, htau0, hoff2, htr2,
    hdup_ok]
  simp

end MercVerified.Lts.Proofs
