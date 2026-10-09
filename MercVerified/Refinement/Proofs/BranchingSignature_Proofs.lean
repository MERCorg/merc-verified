import MercVerified.Refinement.Proofs.Spme_Proofs
import MercVerified.Refinement.Proofs.SigKey_Proofs
import MercVerified.Refinement.Proofs.MarkDirty_Proofs
import Aeneas.Std.WP

/-!
# Leaf functions of the branching algorithm

Specifications of `is_element_marked`, `tau_hat`, `branching_bisim_signature_inductive` (the flat
signature of the key computation, `Sigref.RP.flatSig`).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

open Classical in
/-- `is_element_marked` on a state of a consistent partition is `IsMarked`. -/
theorem is_element_marked_ok {n : Nat} {p : BlockPartition} (hp : PartInv n p) (t : ST)
    (ht : t.index.val < n) :
    verified.merc_reduction.block_partition.BlockPartition.is_element_marked p t
      = ok (decide (IsMarked p t.index.val)) := by
  obtain ⟨hK, ho1, ho2⟩ := hp.own _ ht
  have h1 : t.index.val < p.element_to_block.val.length := by rw [hp.len_e2b]; exact ht
  have h2 : t.index.val < p.element_offset.val.length := by rw [hp.len_off]; exact ht
  unfold verified.merc_reduction.block_partition.BlockPartition.is_element_marked
  rw [vec_tagged_index_val _ _ h1]
  simp only [bind_ok]
  rw [vec_tagged_index_val _ _ h2]
  simp only [bind_ok]
  have hbi : ((p.element_to_block.slice.val)[t.index.val]'h1).index.val = e2bAt p t.index.val := by
    simp [e2bAt, List.getD_eq_getElem?_getD, h1]
    rfl
  have hoo : ((p.element_offset.slice.val)[t.index.val]'h2).val = offAt p t.index.val := by
    simp [offAt, List.getD_eq_getElem?_getD, h2]
    rfl
  generalize ((p.element_to_block.slice.val)[t.index.val]'h1) = bi at hbi ⊢
  generalize ((p.element_offset.slice.val)[t.index.val]'h2) = o at hoo ⊢
  have hbN : bi.index.val < p.blocks.length := by rw [hbi]; exact hK
  rw [vec_tagged_index_val p.blocks bi hbN]
  simp only [bind_ok]
  have hbl : (p.blocks.slice.val[bi.index.val]'hbN) = blkAt p (e2bAt p t.index.val) := by
    rw [← hbi]
    exact (blkAt_eq_getElem hbN).symm
  rw [hbl]
  congr 1
  unfold IsMarked
  rw [← hoo]
  simp [Aeneas.Std.UScalar.le_equiv]

/-- `TagIndex`'s `usize` equality is decidable equality, and never fails. -/
theorem eqTag_ok {Tag : Type} (a b : TagIndex Std.Usize Tag) :
    verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq
      core.cmp.PartialEqUsize a b = ok (decide (a = b)) := by
  obtain ⟨r, hr, hiff⟩ := tagIndex_partialEq_lawful (Tag := Tag) _ usize_partialEq_lawful a b
  have hr' : verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq
      core.cmp.PartialEqUsize a b = ok r := hr
  rw [hr']
  congr 1
  by_cases h : a = b
  · simp [h] at hiff ⊢; exact hiff
  · simp [h] at hiff ⊢; exact hiff

/-- `tau_hat`: the label index `num_of_labels`. -/
theorem tau_hat_ok {L Label : Type} (LTSInst : LTS L Label) (sys : L) (nl : Std.Usize)
    (h : LTSInst.num_of_labels sys = ok nl) :
    verified.merc_reduction.signatures.tau_hat LTSInst sys
      = ok ({ index := nl, marker := () } : TagIndex Std.Usize LabelTag) := by
  unfold verified.merc_reduction.signatures.tau_hat
  rw [h]
  simp only [bind_ok]
  rfl

/-- The entry that `branching_bisim_signature_inductive` pushes for a transition `t` of `s`: an
inert τ-step into a *marked* state of the same block contributes the hat entry carrying the key of
its target; every other transition contributes `(label, block of target)`. -/
def brEntry (hat : TagIndex Std.Usize LabelTag) (bn : ST → BT) (hid : TagIndex Std.Usize LabelTag → Bool)
    (mk : ST → Bool) (key : ST → BT) (s : ST) (t : Transition) : SigEntry :=
  if bn s = bn t.to ∧ hid t.label = true ∧ mk t.to = true then (hat, key t.to)
  else (t.label, bn t.to)

/-- All the calls the loop makes for the transitions `l` of `s` succeed with the given values. -/
structure BrOk {L Label : Type} (LTSInst : LTS L Label) (sys : L) (partition : BlockPartition)
    (state_to_key : Slice BT) (s : ST) (bn : ST → BT) (hid : TagIndex Std.Usize LabelTag → Bool)
    (mk : ST → Bool) (key : ST → BT) (hat : TagIndex Std.Usize LabelTag) (l : List Transition) : Prop where
  bs : verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number
    partition s = ok (bn s)
  bt : ∀ t ∈ l, verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number
    partition t.to = ok (bn t.to)
  hid : ∀ t ∈ l, LTSInst.is_hidden_label sys t.label = ok (hid t.label)
  mkd : ∀ t ∈ l, verified.merc_reduction.block_partition.BlockPartition.is_element_marked partition t.to
    = ok (mk t.to)
  key : ∀ t ∈ l, verified.Slice.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
    (core.slice.index.SliceIndexUsizeSlice BT) state_to_key t.to = ok (key t.to)
  tau : verified.merc_reduction.signatures.tau_hat LTSInst sys = ok hat

set_option allowUnsafeReducibility true
attribute [local reducible] alloc.vec.into_iter.IntoIter
attribute [local reducible] Aeneas.Std.WP.Post

private abbrev BrState := alloc.vec.Vec Transition × alloc.vec.Vec SigEntry

/-- One iteration of the loop of `branching_bisim_signature_inductive`. -/
theorem br_body_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L) (partition : BlockPartition)
    (state_to_key : Slice BT) (s : ST) {bn hid mk key hat} (hd : Transition) (tl : List Transition)
    (hok : BrOk LTSInst sys partition state_to_key s bn hid mk key hat (hd :: tl))
    (iter : alloc.vec.into_iter.IntoIter Transition) (hiter : iter.val = hd :: tl)
    (builder : alloc.vec.Vec SigEntry) (hlen : builder.val.length < Usize.max) :
    ∃ it1 b1, verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop.body
        LTSInst s sys partition state_to_key iter builder = ok (cont (it1, b1)) ∧
      it1.val = tl ∧ b1.val = builder.val ++ [brEntry hat bn hid mk key s hd] := by
  obtain ⟨it1, hnext, hit1⟩ := into_iter_next_some' iter hd tl hiter
  have hdm : hd ∈ hd :: tl := List.mem_cons_self
  have push_ok : ∀ e : SigEntry, ∃ v', builder.push e = ok v' ∧ v'.val = builder.val ++ [e] :=
    fun e => spec_imp_exists (alloc.vec.Vec.push_spec builder e hlen)
  unfold verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop.body
  rw [hnext]
  by_cases hc1 : bn s = bn hd.to
  · cases hh : hid hd.label
    · obtain ⟨b1, hb1, hb1v⟩ := push_ok (hd.label, bn hd.to)
      simp [hok.bt hd hdm, hok.bs, hc1, hok.hid hd hdm, hh, hb1]
      exact ⟨hit1, by rw [hb1v]; simp [brEntry, hh]⟩
    · cases hm : mk hd.to
      · obtain ⟨b1, hb1, hb1v⟩ := push_ok (hd.label, bn hd.to)
        simp [hok.bt hd hdm, hok.bs, hc1, hok.hid hd hdm, hh, hok.mkd hd hdm, hm, hb1]
        exact ⟨hit1, by rw [hb1v]; simp [brEntry, hh, hm]⟩
      · obtain ⟨b1, hb1, hb1v⟩ := push_ok (hat, key hd.to)
        simp [hok.bt hd hdm, hok.bs, hc1, hok.hid hd hdm, hh, hok.mkd hd hdm, hm, hok.tau,
          hok.key hd hdm, hb1]
        exact ⟨hit1, by rw [hb1v]; simp [brEntry, hh, hm, hc1]⟩
  · obtain ⟨b1, hb1, hb1v⟩ := push_ok (hd.label, bn hd.to)
    have hc1' : ¬ (bn s).index = (bn hd.to).index := fun h =>
      hc1 (merc_utilities.tagged_index.TagIndex.ext h)
    simp [hok.bt hd hdm, hok.bs, hc1', hb1]
    exact ⟨hit1, by rw [hb1v]; simp [brEntry, hc1]⟩

theorem BrOk.mono {L Label : Type} {LTSInst : LTS L Label} {sys : L} {partition : BlockPartition}
    {state_to_key : Slice BT} {s : ST} {bn hid mk key hat} {l l' : List Transition}
    (h : BrOk LTSInst sys partition state_to_key s bn hid mk key hat l) (hsub : ∀ t ∈ l', t ∈ l) :
    BrOk LTSInst sys partition state_to_key s bn hid mk key hat l' :=
  ⟨h.bs, fun t ht => h.bt t (hsub t ht), fun t ht => h.hid t (hsub t ht),
    fun t ht => h.mkd t (hsub t ht), fun t ht => h.key t (hsub t ht), h.tau⟩

/-- The loop of `branching_bisim_signature_inductive` appends the entry of every transition. -/
theorem br_loop_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L) (partition : BlockPartition)
    (state_to_key : Slice BT) (s : ST) {bn hid mk key hat} (l : List Transition)
    (hok : BrOk LTSInst sys partition state_to_key s bn hid mk key hat l)
    (iter : alloc.vec.into_iter.IntoIter Transition) (hiter : iter.val = l)
    (builder : alloc.vec.Vec SigEntry)
    (hlen : (builder.val ++ l.map (brEntry hat bn hid mk key s)).length ≤ Usize.max) :
    ∃ b', verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop LTSInst iter s
        sys partition state_to_key builder = ok b' ∧
      b'.val = builder.val ++ l.map (brEntry hat bn hid mk key s) := by
  unfold verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop
  apply spec_imp_exists
  have hspec :
      loop (fun x : alloc.vec.into_iter.IntoIter Transition × alloc.vec.Vec SigEntry =>
          verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop.body LTSInst s
            sys partition state_to_key x.1 x.2) (iter, builder)
        ⦃ b' => b'.val = builder.val ++ l.map (brEntry hat bn hid mk key s) ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : alloc.vec.into_iter.IntoIter Transition × alloc.vec.Vec SigEntry =>
        x.1.val.length)
      (inv := fun x : alloc.vec.into_iter.IntoIter Transition × alloc.vec.Vec SigEntry =>
        ∃ pref rest : List Transition, l = pref ++ rest ∧ x.1.val = rest
          ∧ x.2.val = builder.val ++ pref.map (brEntry hat bn hid mk key s))
      (post := fun b' : alloc.vec.Vec SigEntry =>
        b'.val = builder.val ++ l.map (brEntry hat bn hid mk key s))
      (body := fun x : alloc.vec.into_iter.IntoIter Transition × alloc.vec.Vec SigEntry =>
        verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop.body LTSInst s
          sys partition state_to_key x.1 x.2)
      (x := (iter, builder))
    · intro x hx
      rcases hx with ⟨pref, rest, hl, hx1, hx2⟩
      cases rest with
      | nil =>
        have hnil : x.1.val = [] := hx1
        unfold verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop.body
        rw [into_iter_next_none' _ hnil]
        simp [spec_ok]
        rw [hx2, hl]
        simp
      | cons hd tl =>
        have hhd : BrOk LTSInst sys partition state_to_key s bn hid mk key hat (hd :: tl) :=
          hok.mono (fun t ht => by rw [hl]; exact List.mem_append_right _ ht)
        have hlen' : x.2.val.length < Usize.max := by
          have : x.2.val.length + 1 ≤ (builder.val ++ l.map (brEntry hat bn hid mk key s)).length := by
            rw [hx2, hl]
            simp [List.length_append, List.map_append]
          omega
        obtain ⟨it1, b1, hbody, hit1, hb1⟩ :=
          br_body_spec LTSInst sys partition state_to_key s hd tl hhd x.1 hx1 x.2 hlen'
        rw [hbody]
        simp only [spec_ok]
        refine ⟨⟨pref ++ [hd], tl, ?_, hit1, ?_⟩, ?_⟩
        · rw [hl]; simp
        · rw [hb1, hx2]; simp [List.map_append]
        · show it1.val.length < x.1.val.length
          rw [hit1, hx1]; simp
    · exact ⟨[], l, by simp, hiter, by simp⟩
  simpa using hspec

/-- **`branching_bisim_signature_inductive`**: succeeds and returns a strictly sorted list of
exactly the entries of the outgoing transitions of `s`. -/
theorem branching_signature_key {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (partition : BlockPartition) (state_to_key : Slice BT) (s : ST) {bn hid mk key hat}
    (ts : alloc.vec.Vec Transition) (houtgoing : LTSInst.outgoing_transitions sys s = ok ts)
    (hok : BrOk LTSInst sys partition state_to_key s bn hid mk key hat ts.val)
    (builder0 : alloc.vec.Vec SigEntry) :
    ∃ result, verified.merc_reduction.signatures.branching_bisim_signature_inductive LTSInst s sys
        partition state_to_key builder0 = ok result ∧
      (∀ e, e ∈ result.val ↔ e ∈ ts.val.map (brEntry hat bn hid mk key s)) ∧
      List.Pairwise entLt result.val := by
  unfold verified.merc_reduction.signatures.branching_bisim_signature_inductive
  rcases (alloc.vec.Vec.clear_spec (T := SigEntry) Global builder0) with ⟨builder1, hb1, hb1val⟩
  let iter : alloc.vec.into_iter.IntoIter Transition := ts
  have hlen : (builder1.val ++ ts.val.map (brEntry hat bn hid mk key s)).length ≤ Usize.max := by
    simp [hb1val]
  rcases br_loop_spec LTSInst sys partition state_to_key s ts.val hok iter (by rfl) builder1 hlen with
    ⟨builder2, hb2, hb2val⟩
  rcases (core.slice.Slice.sort_unstable_spec (T := SigEntry)
      (verified.Pair.Insts.CoreCmpOrd
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd BlockTag core.cmp.OrdUsize))
      entry_ord_total builder2.slice) with ⟨s1, hs1, hs1perm, hs1sorted⟩
  let builder3 : alloc.vec.Vec SigEntry := { slice := s1 }
  rcases (alloc.vec.Vec.dedup_spec (T := SigEntry) Global
      (verified.Pair.Insts.CoreCmpPartialEqPair
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag core.cmp.PartialEqUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag core.cmp.PartialEqUsize))
      entry_partialEq_lawful builder3) with ⟨result, hdedup, hdedupspec⟩
  obtain ⟨hdmem, hdsub, hdchain⟩ := hdedupspec
  refine ⟨result, ?_, ?_, ?_⟩
  · rw [hb1]
    simp
    rw [houtgoing]
    simp
    simp [alloc.vec.IntoIteratorVec.into_iter]
    rw [hb2]
    simp [Aeneas.Std.lift, alloc.vec.Vec.deref_mut]
    rw [hs1]
    simp
    rw [hdedup]
  · intro e
    have hperm : List.Perm s1.val builder2.val := by simpa [alloc.vec.Vec.val] using hs1perm
    calc
      e ∈ result.val ↔ e ∈ builder3.val := hdmem e
      _ ↔ e ∈ builder2.val := by
            have hb3 : builder3.val = s1.val := by simp [builder3, alloc.vec.Vec.val]
            rw [hb3]
            exact List.Perm.mem_iff hperm
      _ ↔ e ∈ ts.val.map (brEntry hat bn hid mk key s) := by
            rw [hb2val, hb1val]
            simp
  · have hb3 : builder3.val = s1.val := by simp [builder3, alloc.vec.Vec.val]
    have hsorted : List.Pairwise (fun a b => entryOrd.cmp a b ≠ ok Ordering.gt) result.val :=
      List.Pairwise.sublist hdsub (by rw [hb3]; exact hs1sorted)
    exact sorted_chain_strict hsorted hdchain

end MercVerified.Refinement.Proofs
