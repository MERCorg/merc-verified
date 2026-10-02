import MercVerified.Lts.Lts
import MercVerified.Lts.Proofs.IncomingTransitions_Proofs
import Aeneas.Std.WP

/-!
# `lts_wellFormed`: `LabelledTransitionSystem` satisfies `LTS.WellFormed`

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

`LabelledTransitionSystemValid` (defined below; moved out of `Basic.lean` while it is not part
of the pinned contract, to be restated as a theorem later - see `docs/axiom-audit-plan.md`) states the raw structural
validity of a `LabelledTransitionSystem`'s internal representation - exactly what Rust's
`assert_valid` checks, restricted to what `LTS.WellFormed` needs, and phrased over the
opaque `ByteCompressedVec` primitive's `index`/`len` (which carries no model of its own).
`lts_wellFormed` below derives `WellFormed` from that hypothesis by unfolding the translated
`num_of_states`/`outgoing_transitions` definitions - a real proof, not an axiom, and
*conditional* on `LabelledTransitionSystemValid sys` rather than asserted unconditionally for
every `sys` (which would be false in general, since `ByteCompressedVec` carries no invariant
tying `index`/`len` together on its own - only a value actually produced by a safe constructor,
which Charon does not translate, is trusted to satisfy it).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel Transition LTS)
open verified.merc_lts.labelled_transition_system (LabelledTransitionSystem)

/-- Raw structural validity of a `LabelledTransitionSystem`'s internal representation: exactly
    what Rust's `assert_valid` (`labelled_transition_system.rs:365-447`, run by every safe
    constructor - `from_raw_parts`, `new`, `relabel`, ... - so no reachable instance skips it)
    checks, restricted to the part `LTS.WellFormed` needs: `states` has one entry per state plus
    a sentinel (`statesAt numStates = numTransitions`, `statesAt` monotone), every transition's
    target is `< numStates`, and `initial_state.value() < numStates`.

    Phrased over the boundary `ByteCompressedVec` primitive's `index`/`len` (an existential
    `statesAt : Nat → Nat` stands in for the array read, since `ByteCompressedVec` is a fully
    opaque external type with no `.val` model of its own - see
    `MercVerified/Code/TypesExternal_Template.lean`). `lts_wellFormed` (below) derives
    `LTS.WellFormed` from this by real proof. It is a *hypothesis* of the contract theorems, not
    an axiom: it holds for every value built by a safe constructor (`from_raw_parts` runs
    `assert_valid`), which is to be proved once those constructors are translated
    (see `docs/axiom-audit-plan.md`). -/
def LabelledTransitionSystemValid {Label : Type}
    (sys : LabelledTransitionSystem Label) : Prop :=
  ∃ (numStates numTransitions : Nat) (statesAt : Nat → Nat),
    (∃ statesLen : Std.Usize,
      merc_collections.compressed_vec.ByteCompressedVec.len
        verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry sys.states = ok statesLen ∧
      statesLen.val = numStates + 1) ∧
    (∀ i : Std.Usize, i.val ≤ numStates →
      ∃ v : Std.Usize, merc_collections.compressed_vec.ByteCompressedVec.index
        verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry sys.states i = ok v ∧
        v.val = statesAt i.val) ∧
    (∀ i, i < numStates → statesAt i ≤ statesAt (i + 1)) ∧
    statesAt numStates = numTransitions ∧
    sys.initial_state.index.val < numStates ∧
    (∀ k : Std.Usize, k.val < numTransitions →
      ∃ vl : TagIndex Std.Usize LabelTag, merc_collections.compressed_vec.ByteCompressedVec.index
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_labels k = ok vl) ∧
    (∀ k : Std.Usize, k.val < numTransitions →
      ∃ vt : TagIndex Std.Usize StateTag, merc_collections.compressed_vec.ByteCompressedVec.index
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          StateTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_to k = ok vt ∧
        vt.index.val < numStates) ∧
    numStates * (numStates + 2) ≤ Std.Usize.max ∧
    (∃ tl : Std.Usize, merc_collections.compressed_vec.ByteCompressedVec.len
        (verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
          LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize)
        sys.transition_labels = ok tl ∧ tl.val = numTransitions) ∧
    numTransitions < Std.Usize.max

namespace MercVerified.Lts.Proofs

private theorem loop_unfold_step {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) :
    Aeneas.Std.loop body x
      = (do
          let r ← body x
          match r with
          | ControlFlow.cont c => Aeneas.Std.loop body c
          | ControlFlow.done d => ok d) := by
  rw [Aeneas.Std.loop]
  rfl

private theorem usize_le_max (x : Std.Usize) : x.val ≤ Usize.max := by scalar_tac

private noncomputable def LabelsIdx :=
  verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
    LabelTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize

private noncomputable def StatesIdx :=
  verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry
    StateTag verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry core.marker.CopyUsize

/-- Transitive monotonicity from the pointwise (adjacent-index) monotonicity
    `LabelledTransitionSystemValid` provides. -/
private theorem statesAt_mono {numStates : Nat} {statesAt : Nat → Nat}
    (hmono : ∀ i, i < numStates → statesAt i ≤ statesAt (i + 1)) (a : Nat) :
    ∀ b, a ≤ b → b ≤ numStates → statesAt a ≤ statesAt b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ b hab ih =>
    intro hbn
    exact le_trans (ih (by omega)) (hmono b (by omega))

private theorem outgoing_transitions_loop_bounded
    (bcv : merc_collections.compressed_vec.ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (bcv1 : merc_collections.compressed_vec.ByteCompressedVec (TagIndex Std.Usize StateTag))
    (numStates numTransitions : Nat) (hnumTransMax : numTransitions ≤ Usize.max)
    (hlabels : ∀ k : Std.Usize, k.val < numTransitions →
      ∃ vl : TagIndex Std.Usize LabelTag,
        merc_collections.compressed_vec.ByteCompressedVec.index LabelsIdx bcv k = ok vl)
    (htarget : ∀ k : Std.Usize, k.val < numTransitions →
      ∃ vt : TagIndex Std.Usize StateTag,
        merc_collections.compressed_vec.ByteCompressedVec.index StatesIdx bcv1 k = ok vt ∧
        vt.index.val < numStates) :
    ∀ n (iter : core.ops.range.Range Std.Usize) (result : alloc.vec.Vec Transition),
      iter.«end».val - iter.start.val = n →
      iter.«end».val ≤ numTransitions →
      result.val.length + (iter.«end».val - iter.start.val) ≤ numTransitions →
      (∀ t ∈ result.val, t.to.index.val < numStates) →
      ∃ result',
        verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop
          iter bcv bcv1 result = ok result' ∧
        (∀ t ∈ result'.val, t.to.index.val < numStates) ∧
        result'.val.length = result.val.length + n := by
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
  intro n
  induction n with
  | zero =>
    intro iter result hn hend hcap hbound
    refine ⟨result, ?_, hbound, by omega⟩
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
  | succ n ih =>
    intro iter result hn hend hcap hbound
    have hlt : iter.start.val < iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hstart', hend'⟩ := next_range_some iter hlt
    have hkval : iter.start.val < numTransitions := by omega
    obtain ⟨vl, hvl⟩ := hlabels iter.start hkval
    obtain ⟨vt, hvt, hvtb⟩ := htarget iter.start hkval
    unfold LabelsIdx at hvl
    unfold StatesIdx at hvt
    have hcaplen : result.val.length < Usize.max := by omega
    have hpush := alloc.vec.Vec.push_spec result ({ label := vl, «to» := vt } : Transition) hcaplen
    obtain ⟨result1, hpush', hpushv⟩ := Std.WP.spec_imp_exists hpush
    have hbody : ul (iter, result) = ok (ControlFlow.cont (iter1, result1)) := by
      show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body
        bcv bcv1 iter result = ok (ControlFlow.cont (iter1, result1))
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body
      simp [hnext, ho, hvl, hvt, hpush']
    have hbound1 : ∀ t ∈ result1.val, t.to.index.val < numStates := by
      intro t ht
      rw [hpushv] at ht
      rcases List.mem_append.mp ht with hmem | hmem
      · exact hbound t hmem
      · simp at hmem
        rw [hmem]
        exact hvtb
    have hn1 : iter1.«end».val - iter1.start.val = n := by
      have : iter1.«end».val = iter.«end».val := by rw [hend']
      omega
    have hend1 : iter1.«end».val ≤ numTransitions := by
      have : iter1.«end».val = iter.«end».val := by rw [hend']
      omega
    have hcap1 : result1.val.length + (iter1.«end».val - iter1.start.val) ≤ numTransitions := by
      have hlen1 : result1.val.length = result.val.length + 1 := by
        rw [hpushv]; simp
      have : iter1.«end».val = iter.«end».val := by rw [hend']
      omega
    have hlen1 : result1.val.length = result.val.length + 1 := by
      rw [hpushv]; simp
    obtain ⟨result', hloop', hbound', hlen'⟩ := ih iter1 result1 hn1 hend1 hcap1 hbound1
    refine ⟨result', ?_, hbound', by omega⟩
    rw [← hloop_unfold, loop_unfold_step, hbody]
    simp [hloop_unfold, hloop']

/-- `LabelledTransitionSystem` satisfies the `LTS.WellFormed` requirement, given the raw
    structural validity `LabelledTransitionSystemValid` (defined in this file) - a real
    proof, not an axiom, conditional on this hypothesis (rather than asserted unconditionally
    for every `sys`, which is not true in general: `ByteCompressedVec` is a fully opaque
    external type with no invariant of its own connecting `index` and `len`; only a value
    actually produced by a safe constructor - `from_raw_parts`, `new`, `relabel`, ..., none of
    which Charon translates - is trusted to satisfy it). -/
theorem lts_wellFormed {Label : Type}
    (TLInst : verified.merc_lts.lts.TransitionLabel Label)
    (sys : LabelledTransitionSystem Label)
    (hvalid : LabelledTransitionSystemValid sys) :
    MercVerified.Lts.WellFormed (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) sys := by
  obtain ⟨numStates, numTransitions, statesAt, ⟨statesLen, hstatesLen, hstatesLenV⟩,
    hstatesIdx, hmono, hsentinel, hinit, hlabelsIdx, htargetIdx, hsmall, ⟨tl, htl, htlv⟩, htmax⟩ := hvalid
  -- A real `Usize` whose value is `numStates` (obtained from `statesLen - 1`), used to look
  -- up the sentinel entry `statesAt numStates = numTransitions` and bound `numTransitions`.
  have h1le : (1#usize).val ≤ statesLen.val := by simp; omega
  obtain ⟨numStatesU, hnsu_eq, hnsu_val, -⟩ := Std.WP.spec_imp_exists (Usize.sub_spec h1le)
  have hnsu_valEq : numStatesU.val = numStates := by simp at hnsu_val; omega
  have hnumStatesMax : numStates ≤ Usize.max := by have := usize_le_max numStatesU; omega
  obtain ⟨sentinelV, hsentinelV_eq, hsentinelV_val⟩ := hstatesIdx numStatesU (by omega)
  have hnumTransMax : numTransitions ≤ Usize.max := by
    have := usize_le_max sentinelV
    rw [hnsu_valEq] at hsentinelV_val
    omega
  -- `num_of_states sys` succeeds with value `numStates`.
  have hnumOfStates :
      (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).num_of_states sys = ok numStatesU := by
    show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_states
      TLInst sys = ok numStatesU
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_states
    rw [hstatesLen]
    simp
    exact hnsu_eq
  have key : ∀ s : TagIndex Std.Usize StateTag, s.index.val < numStates →
      ∃ ts : alloc.vec.Vec Transition,
        (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).outgoing_transitions sys s = ok ts ∧
        (∀ t ∈ ts.val, t.to.index.val < numStates) ∧
        ts.val.length = statesAt (s.index.val + 1) - statesAt s.index.val := by
    intro s hs
    -- unfold `outgoing_transitions sys s`
    have hderef : verified.merc_utilities.tagged_index.TagIndex.Insts.CoreOpsDerefDeref.deref s
        = ok s.index := rfl
    have hile : s.index.val ≤ numStates := by omega
    obtain ⟨startV, hstartV_eq, hstartV_val⟩ := hstatesIdx s.index hile
    have hi1max : s.index.val + 1 ≤ Usize.max := by omega
    obtain ⟨i1, hi1_eq, hi1_val⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := s.index) (y := 1#usize)
      (by simp [hi1max]))
    have hi1le : i1.val ≤ numStates := by simp at hi1_val; omega
    obtain ⟨endV, hendV_eq, hendV_val⟩ := hstatesIdx i1 hi1le
    have hstartend : startV.val ≤ endV.val := by
      rw [hstartV_val, hendV_val]
      have hi1v' : i1.val = s.index.val + 1 := by simp at hi1_val; omega
      rw [hi1v']
      exact statesAt_mono hmono s.index.val (s.index.val + 1) (by omega) (by omega)
    obtain ⟨i2, hi2_eq, hi2_val, -⟩ := Std.WP.spec_imp_exists (Usize.sub_spec (x := endV) (y := startV) hstartend)
    have hendMax : endV.val ≤ numTransitions := by
      rw [hendV_val]
      have hi1v' : i1.val = s.index.val + 1 := by simp at hi1_val; omega
      rw [hi1v']
      calc statesAt (s.index.val + 1) ≤ statesAt numStates :=
            statesAt_mono hmono (s.index.val + 1) numStates (by omega) (by omega)
        _ = numTransitions := hsentinel
    have houtgoing :
        (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).outgoing_transitions sys s
          = verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop
              { start := startV, «end» := endV } sys.transition_labels sys.transition_to
              (alloc.vec.Vec.with_capacity Transition i2) := by
      show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions
        TLInst sys s = _
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions
      simp [hderef, hstartV_eq, hi1_eq, hendV_eq, hi2_eq]
    have hcap0 : (alloc.vec.Vec.with_capacity Transition i2).val.length
        + (endV.val - startV.val) ≤ numTransitions := by
      have : (alloc.vec.Vec.with_capacity Transition i2).val = [] := by
        simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
      rw [this]
      simp
      omega
    obtain ⟨result', hloop', hbound', hlen'⟩ :=
      outgoing_transitions_loop_bounded sys.transition_labels sys.transition_to numStates
        numTransitions hnumTransMax hlabelsIdx htargetIdx (endV.val - startV.val)
        { start := startV, «end» := endV } (alloc.vec.Vec.with_capacity Transition i2) rfl
        hendMax hcap0 (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
    refine ⟨result', by rw [houtgoing, hloop'], hbound', ?_⟩
    have hwc : (alloc.vec.Vec.with_capacity Transition i2).val = [] := by
      simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
    rw [hlen', hwc, hendV_val, hstartV_val]
    have hi1v' : i1.val = s.index.val + 1 := by simp at hi1_val; omega
    rw [hi1v']
    simp

  refine ⟨?_, ?_, ?_⟩
  · -- `NonEmpty`
    refine ⟨numStatesU, hnumOfStates, ?_⟩
    omega
  · intro n hn s hs
    have hnEq : n = numStatesU := Result.ok_injective (hn.symm.trans hnumOfStates)
    have hnval : n.val = numStates := by rw [hnEq]; exact hnsu_valEq
    obtain ⟨ts, h1, h2, -⟩ := key s (by omega)
    exact ⟨ts, h1, fun t ht => by have := h2 t ht; omega⟩
  · intro n hn
    have hnEq : n = numStatesU := Result.ok_injective (hn.symm.trans hnumOfStates)
    have hnval : n.val = numStates := by rw [hnEq]; exact hnsu_valEq
    -- the enumeration of the states
    have hnb : numStates < 2 ^ UScalarTy.Usize.numBits := lt_two_pow_of_le_max hnumStatesMax
    obtain ⟨sv, hsvcall, hsvlen, hsvget⟩ : ∃ sv : alloc.vec.Vec (TagIndex Std.Usize StateTag),
        (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).iter_states sys = ok sv ∧
        sv.val.length = numStates ∧ ∀ k, k < numStates → sv.val.getD k (uTag 0) = uTag k := by
      have hg := gather_loop_spec (α := TagIndex Std.Usize StateTag) numStatesU
        (fun k => uTag k) (uTag 0) (by
          have hMaxPos : 0 < Usize.max := by
            have := usize_le_max 1#usize
            simp at this
            omega
          have : numStates < Usize.max := by
            by_contra hcon
            replace hcon := Nat.not_lt.mp hcon
            nlinarith
          omega)
        (fun it v => verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states_loop.body
          it v)
        (fun it v hend hvl hlt hvs => by
          obtain ⟨o, it1, hnext, hopt, hstart, hend'⟩ := next_range_some it hlt
          rcases vec_push_val v (uTag it.start.val) hvl with ⟨v1, hpush, hv1⟩
          refine ⟨it1, v1, ?_, hstart, hend', hv1⟩
          unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states_loop.body
          have hu : (uTag it.start.val : TagIndex Std.Usize StateTag) = { index := it.start, marker := () } := by
            simp only [uTag]
            congr 1
            apply UScalar.eq_of_val_eq
            exact uTotal_val_of_lt (lt_two_pow_of_le_max (usize_le_max it.start))
          rw [hu] at hpush
          rw [hnext]; subst hopt
          simp [verified.merc_utilities.tagged_index.TagIndex.new, hpush])
        (fun it v hge => by
          obtain ⟨o, it1, hnext, hopt, hident⟩ := next_range_none it hge
          unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states_loop.body
          rw [hnext, hopt]
          simp)
      obtain ⟨sv, hsv, hpost⟩ := Std.WP.spec_imp_exists hg
      refine ⟨sv, ?_, by rw [hpost.1, hnsu_valEq], fun k hk => by rw [hpost.2 k (by omega)]⟩
      show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states
        TLInst sys = ok sv
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states
      have hnumOfStatesX : verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_states
          TLInst sys = ok numStatesU := hnumOfStates
      rw [hnumOfStatesX]
      simp only [bind_ok]
      exact hsv
    have hsvl : sv.val = (List.range numStates).map (fun k => (uTag k : TagIndex Std.Usize StateTag)) := by
      apply List.ext_getElem
      · simp [hsvlen]
      · intro k h1 h2
        have hk : k < numStates := by rw [hsvlen] at h1; exact h1
        have := hsvget k hk
        rw [List.getD_eq_getElem _ _ h1] at this
        rw [this]; simp
    have hidx : ∀ k, k < numStates → (uTag k : TagIndex Std.Usize StateTag).index.val = k :=
      fun k hk => uTotal_val_of_lt (by omega)
    have hnumT : (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).num_of_transitions sys = ok tl := by
      show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_transitions
        TLInst sys = ok tl
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_transitions
      exact htl
    refine ⟨sv, tl, hsvcall, ?_, ?_, hnumT, by omega, ?_⟩
    · rw [hsvl]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro a ha b hb h
      have ha' := List.mem_range.mp ha
      have hb' := List.mem_range.mp hb
      have := congrArg (fun x : TagIndex Std.Usize StateTag => x.index.val) h
      rwa [hidx a ha', hidx b hb'] at this
    · intro s'
      rw [hsvl, List.mem_map, hnval]
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [hidx k (List.mem_range.mp hk)]; exact List.mem_range.mp hk
      · intro hs'
        refine ⟨s'.index.val, List.mem_range.mpr hs', ?_⟩
        apply merc_utilities.tagged_index.TagIndex.ext
        exact sz_eq_from_val (uTotal_val_of_lt (by omega))
    · intro ts hts
      have hlenTs : ∀ k, k < numStates → (ts (uTag k)).val.length = statesAt (k + 1) - statesAt k := by
        intro k hk
        have hmemk : (uTag k : TagIndex Std.Usize StateTag) ∈ sv.val := by
          rw [hsvl]; exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
        obtain ⟨ts', h1, -, h3⟩ := key (uTag k) (by rw [hidx k hk]; exact hk)
        have hh : ts (uTag k) = ts' := Result.ok_injective ((hts _ hmemk).symm.trans h1)
        rw [hh, h3, hidx k hk]
      rw [hsvl, List.map_map]
      have hcongr : (List.map ((fun s => (ts s).val.length) ∘ fun k => (uTag k : TagIndex Std.Usize StateTag))
            (List.range numStates)).sum
          = ((List.range numStates).map (fun k => statesAt (k + 1) - statesAt k)).sum := by
        congr 1
        apply List.map_congr_left
        intro k hk
        exact hlenTs k (List.mem_range.mp hk)
      rw [hcongr]
      have htel : ∀ k, k ≤ numStates →
          ((List.range k).map (fun i => statesAt (i + 1) - statesAt i)).sum + statesAt 0
            = statesAt k := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          rw [List.range_succ, List.map_append, List.sum_append]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          have := ih (by omega)
          have := hmono k (by omega)
          omega
      have := htel numStates (le_refl _)
      omega

end MercVerified.Lts.Proofs
