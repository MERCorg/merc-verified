import MercVerified.Refinement.Proofs.LoopTools_Proofs
import MercVerified.Refinement.Proofs.BranchingClosure_Proofs
import MercVerified.Lts.Proofs.IncomingTransitionsCorrect_Proofs
import Aeneas.Std.WP

/-!
# `incoming_silent_transitions` returns exactly the silent incoming transitions

`IncomingTransitions::new` sorts the incoming transitions of every state by label
(`IncomingTransitionsCorrect_Proofs`, `Zp`), so the silent ones (label `0`) come first and
`incoming_silent_transitions`, which stops at the first non-silent one, returns all of them.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem label_ne_zero (l : TagIndex Std.Usize LabelTag) :
    core.cmp.PartialEq.ne.trait_default
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag
        core.cmp.PartialEqUsize) l ({ index := 0#usize, marker := () } : TagIndex Std.Usize LabelTag)
      = ok (decide (l.index.val ≠ 0)) := by
  rw [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  simp [tag_partial_eq_inst]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact UScalar.eq_of_val_eq (by simpa using h)

/-- The postcondition of the silent loop, once it stops at position `k`. -/
theorem silent_post (transitions : alloc.vec.Vec FromTransition)
    (hz : ∀ (p q : Nat) (h1 : p < q) (h2 : q < transitions.val.length),
      (transitions.val[q]'h2).label.index.val = 0 →
        (transitions.val[p]'(lt_trans h1 h2)).label.index.val = 0)
    (k : Nat) (hk : k ≤ transitions.val.length)
    (hall : ∀ p (h : p < k), (transitions.val[p]'(by omega)).label.index.val = 0)
    (hstop : k = transitions.val.length ∨
      ∃ h : k < transitions.val.length, ¬ (transitions.val[k]'h).label.index.val = 0) :
    ∀ i : FromTransition, i ∈ transitions.val.take k ↔
      i ∈ transitions.val ∧ i.label.index.val = 0 := by
  intro i
  constructor
  · intro hi
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hi
    have hn' : n < k := by simp at hn; omega
    simp only [List.getElem_take]
    exact ⟨List.getElem_mem _, hall n hn'⟩
  · rintro ⟨hi, h0⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hi
    have hqk : q < k := by
      by_contra hc
      rcases hstop with h | ⟨hk', hne⟩
      · omega
      · by_cases hqe : q = k
        · subst hqe; exact hne h0
        · exact hne (hz k q (by omega) hq h0)
    refine List.mem_iff_getElem.mpr ⟨q, by simp; omega, ?_⟩
    simp

abbrev SilSt := core.ops.range.Range Std.Usize × alloc.vec.Vec FromTransition

/-- The loop of `incoming_silent_transitions` on silent-first transitions collects exactly the
silent ones. -/
theorem incoming_silent_loop_spec (transitions : alloc.vec.Vec FromTransition)
    (hlen : transitions.val.length ≤ Usize.max)
    (hz : ∀ (p q : Nat) (h1 : p < q) (h2 : q < transitions.val.length),
      (transitions.val[q]'h2).label.index.val = 0 →
        (transitions.val[p]'(lt_trans h1 h2)).label.index.val = 0)
    (r0 : alloc.vec.Vec FromTransition) (hr0 : r0.val = []) (e : Std.Usize)
    (he : e.val = transitions.val.length) :
    ∃ sil, verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop { start := 0#usize, «end» := e } transitions r0 =
        ok sil ∧
      ∀ i : FromTransition, i ∈ sil.val ↔ i ∈ transitions.val ∧ i.label.index.val = 0 := by
  have hspec : (@loop SilSt (alloc.vec.Vec FromTransition)
      (fun st => verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
        transitions st.1 st.2) ({ start := 0#usize, «end» := e }, r0))
      ⦃ fun r : alloc.vec.Vec FromTransition => ∀ i : FromTransition,
        i ∈ r.val ↔ i ∈ transitions.val ∧ i.label.index.val = 0 ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : SilSt => st.1.end.val - st.1.start.val)
      (inv := fun st : SilSt => st.1.end.val = transitions.val.length ∧
        st.1.start.val ≤ transitions.val.length ∧
        st.2.val = transitions.val.take st.1.start.val ∧
        ∀ p (h : p < st.1.start.val) (h' : p < transitions.val.length),
          (transitions.val[p]'h').label.index.val = 0)
      (post := fun r : alloc.vec.Vec FromTransition => ∀ i : FromTransition,
        i ∈ r.val ↔ i ∈ transitions.val ∧ i.label.index.val = 0)
      (body := fun st => verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
        transitions st.1 st.2)
      (x := ({ start := 0#usize, «end» := e }, r0))
    · intro st ⟨hend, hle, hres, hall⟩
      by_cases hdone : st.1.end.val ≤ st.1.start.val
      · obtain ⟨o, it1, hnext, hone, hident⟩ := MercVerified.Lts.Proofs.next_range_none st.1 hdone
        have hbody : verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
            transitions st.1 st.2 = ok (done st.2) := by
          unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
          rw [hnext, hone]
          simp
        refine Std.WP.exists_imp_spec ⟨done st.2, hbody, ?_⟩
        show ∀ i : FromTransition, i ∈ st.2.val ↔ i ∈ transitions.val ∧ i.label.index.val = 0
        rw [hres]
        exact silent_post transitions hz _ hle (fun p h => hall p h (by omega)) (Or.inl (by omega))
      · have hlt : st.1.start.val < st.1.end.val := by omega
        obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some st.1 hlt
        have hlt' : st.1.start.val < transitions.val.length := by omega
        have hidx : transitions.index_usize st.1.start = ok (transitions.val[st.1.start.val]'hlt') := by
          have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec transitions st.1.start hlt'
          rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
          rw [hy, hyv]
        have hnew : TagIndex.new LabelTag 0#usize = ok ({ index := 0#usize, marker := () } :
            TagIndex Std.Usize LabelTag) := by simp
        by_cases hl : (transitions.val[st.1.start.val]'hlt').label.index.val = 0
        · obtain ⟨v', hpush, hv'⟩ := MercVerified.Lts.Proofs.vec_push_val st.2
            (transitions.val[st.1.start.val]'hlt') (by
              rw [hres]; simp; have := hlen; omega)
          have hbody : verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
              transitions st.1 st.2 = ok (cont (it1, v')) := by
            unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
            rw [hnext, hsome]
            simp [hidx, label_ne_zero, hl, hpush]
          refine Std.WP.exists_imp_spec ⟨cont (it1, v'), hbody, ?_⟩
          show (it1.end.val = transitions.val.length ∧ it1.start.val ≤ transitions.val.length ∧
            v'.val = transitions.val.take it1.start.val ∧
            ∀ p (h : p < it1.start.val) (h' : p < transitions.val.length),
              (transitions.val[p]'h').label.index.val = 0) ∧
            it1.end.val - it1.start.val < st.1.end.val - st.1.start.val
          have he1v : it1.end.val = st.1.end.val := congrArg _ he1
          refine ⟨⟨by omega, by omega, ?_, ?_⟩, by omega⟩
          · rw [hv', hres, hs1, List.take_add_one]
            simp [hlt']
          · intro p hp hp'
            by_cases hpk : p < st.1.start.val
            · exact hall p hpk hp'
            · have : p = st.1.start.val := by omega
              subst this; exact hl
        · have hbody : verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
              transitions st.1 st.2 = ok (done st.2) := by
            unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body
            rw [hnext, hsome]
            simp [hidx, label_ne_zero, hl]
          refine Std.WP.exists_imp_spec ⟨done st.2, hbody, ?_⟩
          show ∀ i : FromTransition, i ∈ st.2.val ↔ i ∈ transitions.val ∧ i.label.index.val = 0
          rw [hres]
          exact silent_post transitions hz _ hle (fun p h => hall p h (by omega)) (Or.inr ⟨hlt', hl⟩)
    · exact ⟨he, Nat.zero_le _, by simp [hr0], fun p hp => by simp at hp⟩
  obtain ⟨sil, hsil, hpost⟩ := Std.WP.spec_imp_exists hspec
  refine ⟨sil, ?_, hpost⟩
  unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop
  exact hsil

/-- **`IncomingTransitions::new` produces silent-first ranges**: `incoming_silent_transitions`
returns exactly the silent incoming transitions of every state. -/
theorem incoming_silent_correct {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys)
    (incoming : IncomingTransitions)
    (hinc : IncomingTransitions.new LTSInst sys = ok incoming)
    (n : Std.Usize) (hns : LTSInst.num_of_states sys = ok n) :
    IncSilent LTSInst sys n.val incoming := by
  intro x hx
  obtain ⟨incoming', hinc', sv, hnd, hmem, hrlen, hrmono, hrfill, hlens, hlmax, hwin, hzp⟩ :=
    incoming_new_structure LTSInst sys hwf hfit n hns
  have hii : incoming' = incoming := by
    have := hinc'.symm.trans hinc; simpa using this
  subst hii
  have hIC := incoming_transitions_correct LTSInst sys hwf hfit incoming' hinc
  obtain ⟨res, hres, -, hiff⟩ := hIC n hns x hx
  have hs : x.index.val + 1 < incoming'.state2incoming.val.length := by rw [hrlen]; omega
  obtain ⟨res', hres', hresv⟩ := incoming_transitions_spec incoming' x hs
    (hrmono x.index.val hs) (hrfill (x.index.val + 1) hs) hlens hlmax
  have hrr : res' = res := by
    rw [hres'] at hres; simpa using hres
  subst hrr
  have hlenres : res'.val.length = (incoming'.state2incoming.val.getD (x.index.val + 1) 0#usize).val
      - (incoming'.state2incoming.val.getD x.index.val 0#usize).val := by
    rw [hresv]; simp [slotEntries]
  have hlab : ∀ k (hk : k < res'.val.length), (res'.val[k]'hk).label =
      incoming'.transition_labels.val.getD
        ((incoming'.state2incoming.val.getD x.index.val 0#usize).val + k) zeroLabel := by
    intro k hk
    have h := List.getElem_of_eq hresv hk
    rw [h]
    simp [slotEntries, pairAt, List.getElem_map, List.getElem_range']
  have hz : ∀ (p q : Nat) (h1 : p < q) (h2 : q < res'.val.length),
      (res'.val[q]'h2).label.index.val = 0 →
        (res'.val[p]'(lt_trans h1 h2)).label.index.val = 0 := by
    intro p q h1 h2 hq0
    rw [hlab q h2] at hq0
    rw [hlab p (lt_trans h1 h2)]
    exact hzp x.index.val hx _ _ (by omega) (by omega) (by omega) hq0
  have hlenmax : res'.val.length ≤ Usize.max := by
    have := res'.property; simpa [Usize.max] using this
  obtain ⟨sil, hsil, hpost⟩ := incoming_silent_loop_spec res' hlenmax hz
    (alloc.vec.Vec.with_capacity FromTransition (alloc.vec.Vec.len res')) (by simp [alloc.vec.Vec.with_capacity])
    (alloc.vec.Vec.len res') (by simp [alloc.vec.Vec.len])
  refine ⟨sil, ?_, fun i => ?_⟩
  · unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions
    rw [hres]
    simpa using hsil
  · rw [hpost i, hiff i]
    constructor
    · rintro ⟨⟨μ, s', hs'n, htr, hpair⟩, h0⟩
      have hl : i.label = μ := (Prod.mk.inj hpair).1
      have hf : i.«from» = s' := (Prod.mk.inj hpair).2
      exact ⟨h0, by rw [hf]; exact hs'n, by rw [hl, hf]; exact htr⟩
    · rintro ⟨h0, hfn, htr⟩
      exact ⟨⟨i.label, i.«from», hfn, htr, rfl⟩, h0⟩

end MercVerified.Refinement.Proofs
