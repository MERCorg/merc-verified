import MercVerified.Refinement.Proofs.BranchingSubset_Proofs
import Aeneas.Std.WP

/-!
# `renumber_branching`

The backwards scan of a sorted signature: for the hat entries from the largest key down, the key of
the first whose interned signature absorbs the rest of the signature; the scan stops at the first
non-hat entry.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

open Classical

/-- The scan of `renumber_branching` over the entries `rest` (given largest first); `full` is the
whole signature, `kts` the interned signatures and `nl` the number of labels (the hat label). -/
noncomputable def rnScan (nl : Nat) (kts : List (List SigEntry)) (full : List SigEntry) :
    List SigEntry → Option BT
  | [] => none
  | e :: rest =>
    if e.1.index.val = nl then
      (if ∀ x ∈ full, x ≠ e → x ∈ kts.getD e.2.index.val [] then some e.2 else rnScan nl kts full rest)
    else none

/-- `is_tau_hat` compares the label index with `num_of_labels`. -/
theorem isTauHat_ok {L Label : Type} (LTSInst : LTS L Label) (sys : L) (nl : Std.Usize)
    (h : LTSInst.num_of_labels sys = ok nl) (label : TagIndex Std.Usize LabelTag) :
    verified.merc_reduction.signatures.is_tau_hat LTSInst label sys
      = ok (decide (label.index.val = nl.val)) := by
  unfold verified.merc_reduction.signatures.is_tau_hat
  rw [h]
  simp only [bind_ok]
  obtain ⟨r, hr, hiff⟩ := usize_partialEq_lawful label.index nl
  have hr' : verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEq.eq
      core.cmp.PartialEqUsize label nl = ok r := by
    unfold verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEq.eq
    simpa using hr
  rw [hr']
  congr 1
  by_cases hh : label.index = nl
  · simp [hh] at hiff ⊢; exact hiff
  · have : ¬ label.index.val = nl.val := fun e => hh (UScalar.eq_of_val_eq e)
    simp [hh, this] at hiff ⊢; exact hiff

theorem rn_take_succ (nl : Nat) (kts : List (List SigEntry)) (sig : List SigEntry) (m : Nat)
    (hm : m < sig.length) :
    rnScan nl kts sig (sig.take (m + 1)).reverse =
      (if (sig[m]'hm).1.index.val = nl then
        (if ∀ x ∈ sig, x ≠ sig[m]'hm → x ∈ kts.getD (sig[m]'hm).2.index.val [] then
          some (sig[m]'hm).2
        else rnScan nl kts sig (sig.take m).reverse)
      else none) := by
  have h : (sig.take (m + 1)).reverse = sig[m]'hm :: (sig.take m).reverse := by
    rw [List.take_add_one, List.getElem?_eq_getElem hm]; simp
  rw [h]
  simp only [rnScan]

open verified.merc_reduction.signature_refinement in
/-- One step of the loop of `renumber_branching` (not yet done, index positive). -/
theorem rn_body {L Label : Type} (LTSInst : LTS L Label) (sys : L) (nl : Std.Usize)
    (hnl : LTSInst.num_of_labels sys = ok nl) (sig : Slice SigEntry) (kts : alloc.vec.Vec (alloc.vec.Vec SigEntry))
    (hsig : List.Pairwise entLt sig.val) (hkts : ∀ v ∈ kts.val, List.Pairwise entLt v.val)
    (hkeys : ∀ e ∈ sig.val, e.1.index.val = nl.val → e.2.index.val < kts.val.length)
    (result : Option BT) (index : Std.Usize) (hidx : 0 < index.val) (_hle : index.val ≤ sig.val.length) :
    ∃ i1 : Std.Usize, i1.val = index.val - 1 ∧
      ∀ hm : index.val - 1 < sig.val.length,
      ((sig.val[index.val - 1]'hm).1.index.val = nl.val →
        (∀ x ∈ sig.val, x ≠ sig.val[index.val - 1]'hm →
          x ∈ (kts.val.map (·.val)).getD (sig.val[index.val - 1]'hm).2.index.val []) →
        renumber_branching_loop.body LTSInst sys sig kts result index false
          = ok (cont (some (sig.val[index.val - 1]'hm).2, i1, true))) ∧
      ((sig.val[index.val - 1]'hm).1.index.val = nl.val →
        ¬ (∀ x ∈ sig.val, x ≠ sig.val[index.val - 1]'hm →
          x ∈ (kts.val.map (·.val)).getD (sig.val[index.val - 1]'hm).2.index.val []) →
        renumber_branching_loop.body LTSInst sys sig kts result index false
          = ok (cont (result, i1, false))) ∧
      ((sig.val[index.val - 1]'hm).1.index.val ≠ nl.val →
        renumber_branching_loop.body LTSInst sys sig kts result index false
          = ok (cont (result, i1, true))) := by
  obtain ⟨i1, hi1e, hi1v⟩ : ∃ i1 : Std.Usize, index - 1#usize = ok i1 ∧ i1.val = index.val - 1 := by
    obtain ⟨y, hy, hv, -⟩ := spec_imp_exists (Usize.sub_spec (x := index) (y := 1#usize) (by simp; omega))
    exact ⟨y, hy, by simpa using hv⟩
  refine ⟨i1, hi1v, fun hm => ?_⟩
  have hgt : index > 0#usize := by simp [UScalar.lt_equiv]; omega
  have hm' : i1.val < sig.val.length := by omega
  have hidx1 := slice_index_ok sig i1 hm'
  have hsigi : sig.val[i1.val]'hm' = sig.val[index.val - 1]'hm := by simp [hi1v]
  rcases hE : sig.val[index.val - 1]'hm with ⟨label, key⟩
  have hidx2 : Slice.index_usize sig i1 = ok (label, key) := by rw [hidx1, hsigi, hE]
  have hmem : (label, key) ∈ sig.val := by rw [← hE]; exact List.getElem_mem hm
  have htau := isTauHat_ok LTSInst sys nl hnl label
  have hhat : label.index.val = nl.val → key.index.val < kts.val.length :=
    fun hlab => hkeys (label, key) hmem hlab
  have hgetD : ∀ hk : key.index.val < kts.val.length,
      (kts.val.map (·.val)).getD key.index.val [] = (kts.val[key.index.val]'hk).val := by
    intro hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have hcase : ∀ (hlab : label.index.val = nl.val),
      ∃ r, renumber_branching_loop.body LTSInst sys sig kts result index false =
          (if r = true then ok (cont (some key, i1, true)) else ok (cont (result, i1, false))) ∧
        (r = true ↔ ∀ x ∈ sig.val, x ≠ (label, key) → x ∈ (kts.val.map (·.val)).getD key.index.val []) := by
    intro hlab
    have hk := hhat hlab
    have hvec := vec_tagged_index_val kts key hk
    obtain ⟨r, hr, hriff⟩ := is_subset_excluding_spec (alloc.vec.Vec.deref (kts.val[key.index.val]'hk))
      sig (label, key) (by simpa [alloc.vec.Vec.deref] using hkts _ (List.getElem_mem hk)) hsig
    have hr2 : is_subset_excluding (alloc.vec.Vec.deref (kts.slice.val[key.index.val]'(by
        simpa [alloc.vec.Vec.val] using hk))) sig (label, key) = ok r := hr
    refine ⟨r, ?_, ?_⟩
    · unfold renumber_branching_loop.body
      simp [hgt, hi1e, hidx2, htau, hlab, hvec, hr2]
    · rw [hgetD hk, hriff]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  refine ⟨fun hlab hsub => ?_, fun hlab hsub => ?_, fun hlab => ?_⟩
  · obtain ⟨r, hb, hr⟩ := hcase hlab
    have : r = true := hr.2 hsub
    rw [hb, this]; simp
  · obtain ⟨r, hb, hr⟩ := hcase hlab
    have : r = false := by
      cases r
      · rfl
      · exact absurd (hr.1 rfl) hsub
    rw [hb, this]; simp
  · unfold renumber_branching_loop.body
    have hlab' : ¬ label.index.val = nl.val := hlab
    simp [hgt, hi1e, hidx2, htau, hlab']

open verified.merc_reduction.signature_refinement in
/-- **`renumber_branching`** computes the backwards scan `rnScan`. -/
theorem renumber_branching_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L) (nl : Std.Usize)
    (hnl : LTSInst.num_of_labels sys = ok nl) (sig : Slice SigEntry)
    (kts : alloc.vec.Vec (alloc.vec.Vec SigEntry))
    (hsig : List.Pairwise entLt sig.val) (hkts : ∀ v ∈ kts.val, List.Pairwise entLt v.val)
    (hkeys : ∀ e ∈ sig.val, e.1.index.val = nl.val → e.2.index.val < kts.val.length) :
    ∃ r, renumber_branching LTSInst sys sig kts = ok r ∧
      r = rnScan nl.val (kts.val.map (·.val)) sig.val sig.val.reverse := by
  unfold renumber_branching renumber_branching_loop
  simp only
  apply spec_imp_exists
  set F := rnScan nl.val (kts.val.map (·.val)) sig.val sig.val.reverse with hF
  have hspec :
      loop (fun x : Option BT × Std.Usize × Bool =>
          renumber_branching_loop.body LTSInst sys sig kts x.1 x.2.1 x.2.2)
        (none, Slice.len sig, false) ⦃ r => r = F ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : Option BT × Std.Usize × Bool =>
        x.2.1.val + (if x.2.2 then 0 else 1))
      (inv := fun x : Option BT × Std.Usize × Bool =>
        x.2.1.val ≤ sig.val.length ∧
        (x.2.2 = false → x.1 = none ∧
          rnScan nl.val (kts.val.map (·.val)) sig.val (sig.val.take x.2.1.val).reverse = F) ∧
        (x.2.2 = true → x.1 = F))
      (post := fun r : Option BT => r = F)
      (body := fun x : Option BT × Std.Usize × Bool =>
        renumber_branching_loop.body LTSInst sys sig kts x.1 x.2.1 x.2.2)
      (x := (none, Slice.len sig, false))
    · intro x hx
      obtain ⟨result, index, done⟩ := x
      obtain ⟨hle, hF1, hF2⟩ := hx
      simp only at hle hF1 hF2
      cases done with
      | true =>
        unfold renumber_branching_loop.body
        simp only [if_true, spec_ok]
        exact hF2 rfl
      | false =>
        obtain ⟨hres, hFe⟩ := hF1 rfl
        by_cases hidx : 0 < index.val
        · obtain ⟨i1, hi1v, hcases⟩ := rn_body LTSInst sys nl hnl sig kts hsig hkts hkeys result index
            hidx hle
          have hm : index.val - 1 < sig.val.length := by omega
          obtain ⟨hc1, hc2, hc3⟩ := hcases hm
          have hstep := rn_take_succ nl (kts.val.map (·.val)) sig.val (index.val - 1) hm
          have htk : index.val - 1 + 1 = index.val := by omega
          rw [htk] at hstep
          by_cases hhat : (sig.val[index.val - 1]'hm).1.index.val = nl.val
          · by_cases hsub : ∀ x ∈ sig.val, x ≠ sig.val[index.val - 1]'hm →
                x ∈ (kts.val.map (·.val)).getD (sig.val[index.val - 1]'hm).2.index.val []
            · rw [hc1 hhat hsub]; simp only [spec_ok]
              refine ⟨⟨by omega, fun h => absurd h (by simp), fun _ => ?_⟩, ?_⟩
              · rw [← hFe, hstep, if_pos hhat, if_pos hsub]
              · simp [hi1v]; try omega
            · rw [hc2 hhat hsub]; simp only [spec_ok]
              refine ⟨⟨by omega, fun _ => ⟨hres, ?_⟩, fun h => absurd h (by simp)⟩, ?_⟩
              · rw [hi1v, ← hFe, hstep, if_pos hhat, if_neg hsub]
              · simp [hi1v]; try omega
          · rw [hc3 hhat]; simp only [spec_ok]
            refine ⟨⟨by omega, fun h => absurd h (by simp), fun _ => ?_⟩, ?_⟩
            · rw [hres, ← hFe, hstep, if_neg hhat]
            · simp [hi1v]; try omega
        · have hz : index.val = 0 := by omega
          have hnz : ¬ index > 0#usize := by simp [UScalar.lt_equiv]; omega
          unfold renumber_branching_loop.body
          simp only [Bool.false_eq_true, if_false, hnz, spec_ok]
          rw [hres, ← hFe, hz]; simp [rnScan]
    · refine ⟨by simp [Slice.len], fun _ => ⟨rfl, ?_⟩, fun h => absurd h (by simp)⟩
      simp [Slice.len, hF]
  simpa using hspec

end MercVerified.Refinement.Proofs
