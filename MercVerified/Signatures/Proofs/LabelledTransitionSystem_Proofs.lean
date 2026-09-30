import MercVerified.Basic
import MercVerified.Signatures.Proofs.Partition_Proofs
import Aeneas.Std.WP

/-!
# `lts_wellFormed`: `LabelledTransitionSystem` satisfies `LTS.WellFormed`

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

`LabelledTransitionSystemValid` (`MercVerified/Basic.lean`) states the raw structural
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

namespace MercVerified.Signatures.Proofs

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
        ∀ t ∈ result'.val, t.to.index.val < numStates := by
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
    refine ⟨result, ?_, hbound⟩
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
    obtain ⟨result', hloop', hbound'⟩ := ih iter1 result1 hn1 hend1 hcap1 hbound1
    refine ⟨result', ?_, hbound'⟩
    rw [← hloop_unfold, loop_unfold_step, hbody]
    simp [hloop_unfold, hloop']

/-- `LabelledTransitionSystem` satisfies the `LTS.WellFormed` requirement, given the raw
    structural validity `LabelledTransitionSystemValid` (`MercVerified/Basic.lean`) - a real
    proof, not an axiom, conditional on this hypothesis (rather than asserted unconditionally
    for every `sys`, which is not true in general: `ByteCompressedVec` is a fully opaque
    external type with no invariant of its own connecting `index` and `len`; only a value
    actually produced by a safe constructor - `from_raw_parts`, `new`, `relabel`, ..., none of
    which Charon translates - is trusted to satisfy it). -/
theorem lts_wellFormed {Label : Type}
    (TLInst : verified.merc_lts.lts.TransitionLabel Label)
    (sys : LabelledTransitionSystem Label)
    (hvalid : LabelledTransitionSystemValid sys) :
    (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).WellFormed sys := by
  obtain ⟨numStates, numTransitions, statesAt, ⟨statesLen, hstatesLen, hstatesLenV⟩,
    hstatesIdx, hmono, hsentinel, hinit, hlabelsIdx, htargetIdx⟩ := hvalid
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
  constructor
  · -- `NonEmpty`
    refine ⟨numStatesU, hnumOfStates, ?_⟩
    omega
  · intro n hn s hs
    have hnEq : n = numStatesU := Result.ok_injective (hn.symm.trans hnumOfStates)
    have hnval : n.val = numStates := by rw [hnEq]; exact hnsu_valEq
    rw [hnEq] at hs
    rw [hnsu_valEq] at hs
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
    obtain ⟨result', hloop', hbound'⟩ :=
      outgoing_transitions_loop_bounded sys.transition_labels sys.transition_to numStates
        numTransitions hnumTransMax hlabelsIdx htargetIdx (endV.val - startV.val)
        { start := startV, «end» := endV } (alloc.vec.Vec.with_capacity Transition i2) rfl
        hendMax hcap0 (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
    refine ⟨result', ?_, ?_⟩
    · rw [houtgoing, hloop']
    · intro t ht
      have := hbound' t ht
      omega

end MercVerified.Signatures.Proofs
