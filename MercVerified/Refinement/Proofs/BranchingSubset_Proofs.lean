import MercVerified.Refinement.Proofs.BranchingSignature_Proofs
import Aeneas.Std.WP

/-!
# `is_subset_excluding`

The two-pointer subset test of the branching algorithm: on strictly sorted slices it decides
`∀ e ∈ subset, e ≠ exclude → e ∈ superset`.

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

/-- The equality instance of signature entries. -/
noncomputable abbrev entryEqInst : core.cmp.PartialEq SigEntry SigEntry :=
  verified.Pair.Insts.CoreCmpPartialEqPair
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag
      core.cmp.PartialEqUsize)
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag
      core.cmp.PartialEqUsize)

/-- Equality of signature entries never fails and is decidable equality. -/
theorem entEq_ok (a b : SigEntry) :
    Pair.Insts.CoreCmpPartialEqPair.eq
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag
        core.cmp.PartialEqUsize)
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag
        core.cmp.PartialEqUsize) a b = ok (decide (a = b)) := by
  obtain ⟨r, hr, hiff⟩ := entry_partialEq_lawful a b
  have hr' : Pair.Insts.CoreCmpPartialEqPair.eq
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag
        core.cmp.PartialEqUsize)
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag
        core.cmp.PartialEqUsize) a b = ok r := hr
  rw [hr']
  congr 1
  by_cases h : a = b
  · simp [h] at hiff ⊢; exact hiff
  · simp [h] at hiff ⊢; exact hiff

theorem slice_index_ok {α : Type} (s : Slice α) (i : Std.Usize) (h : i.val < s.val.length) :
    Slice.index_usize s i = ok (s.val[i.val]'h) := by
  have hs := Slice.index_usize_spec s i h
  obtain ⟨x, hx, hxe⟩ := Std.WP.spec_imp_exists hs
  rw [hx, hxe]

theorem entCmp_ok (a b : SigEntry) :
    Pair.Insts.CoreCmpOrd.cmp
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd BlockTag core.cmp.OrdUsize)
      a b = ok (entCmp a b) := entry_cmp_eq a b

open verified.merc_reduction.signature_refinement in
/-- One step of the two-pointer loop while `result = true`. -/
theorem iss_body {sup sub : Slice SigEntry} {ex : SigEntry} {i j : Std.Usize}
    (hi : i.val ≤ sup.val.length) (hj : j.val < sub.val.length) :
    (sub.val[j.val]'hj = ex → ∃ j', j'.val = j.val + 1 ∧
      is_subset_excluding_loop.body sup sub ex i j true = ok (cont (i, j', true))) ∧
    (sub.val[j.val]'hj ≠ ex → ∀ hij : i.val < sup.val.length,
      (sup.val[i.val]'hij = sub.val[j.val]'hj → ∃ i' j', i'.val = i.val + 1 ∧ j'.val = j.val + 1 ∧
        is_subset_excluding_loop.body sup sub ex i j true = ok (cont (i', j', true))) ∧
      (sup.val[i.val]'hij ≠ sub.val[j.val]'hj → entLt (sup.val[i.val]'hij) (sub.val[j.val]'hj) →
        ∃ i', i'.val = i.val + 1 ∧
          is_subset_excluding_loop.body sup sub ex i j true = ok (cont (i', j, true))) ∧
      (sup.val[i.val]'hij ≠ sub.val[j.val]'hj → ¬ entLt (sup.val[i.val]'hij) (sub.val[j.val]'hj) →
        is_subset_excluding_loop.body sup sub ex i j true = ok (cont (i, j, false)))) ∧
    (sub.val[j.val]'hj ≠ ex → ¬ i.val < sup.val.length →
      is_subset_excluding_loop.body sup sub ex i j true = ok (cont (i, j, false))) := by
  have hjlt : j < Slice.len sub := by
    simp [Slice.len, UScalar.lt_equiv]; exact hj
  have hmax_j : j.val + 1 ≤ Usize.max := by
    have := sub.property; scalar_tac
  have hidx := slice_index_ok sub j hj
  obtain ⟨j', hj'e, hj'v⟩ : ∃ j' : Std.Usize, j + 1#usize = ok j' ∧ j'.val = j.val + 1 :=
    spec_imp_exists (Usize.add_spec (x := j) (y := 1#usize) (by simp; omega))
  refine ⟨fun hex => ⟨j', hj'v, ?_⟩, fun hne hij => ?_, fun hne hij => ?_⟩
  · unfold is_subset_excluding_loop.body
    simp [hjlt, hidx, entEq_ok, hex, hj'e]
  · have hpidx := slice_index_ok sup i hij
    obtain ⟨i', hi'e, hi'v⟩ : ∃ i' : Std.Usize, i + 1#usize = ok i' ∧ i'.val = i.val + 1 :=
      spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by
        have := sup.property; simp; omega))
    have hilt : i < Slice.len sup := by simp [Slice.len, UScalar.lt_equiv]; exact hij
    refine ⟨fun heq => ⟨i', j', hi'v, hj'v, ?_⟩, fun hneq hlt => ⟨i', hi'v, ?_⟩, fun hneq hnlt => ?_⟩
    · unfold is_subset_excluding_loop.body
      simp [hjlt, hidx, hpidx, entEq_ok, hne, hilt, heq, hj'e, hi'e]
    · unfold is_subset_excluding_loop.body
      have hcmp : entCmp (sup.val[i.val]'hij) (sub.val[j.val]'hj) = Ordering.lt :=
        (entCmp_lt_iff _ _).2 hlt
      simp [hjlt, hidx, hpidx, entEq_ok, hne, hilt, hneq, entCmp_ok, hcmp, hi'e]
    · unfold is_subset_excluding_loop.body
      have hcmp : entCmp (sup.val[i.val]'hij) (sub.val[j.val]'hj) ≠ Ordering.lt :=
        fun h => hnlt ((entCmp_lt_iff _ _).1 h)
      simp [hjlt, hidx, hpidx, entEq_ok, hne, hilt, hneq, entCmp_ok]
      cases hc : entCmp (sup.val[i.val]'hij) (sub.val[j.val]'hj) <;> simp_all
  · have hilt : ¬ i < Slice.len sup := by simp [Slice.len, UScalar.lt_equiv]; omega
    unfold is_subset_excluding_loop.body
    simp [hjlt, hidx, entEq_ok, hne, hilt]

open verified.merc_reduction.signature_refinement in
/-- **`is_subset_excluding`** on strictly sorted slices decides `subset ∖ {exclude} ⊆ superset`. -/
theorem is_subset_excluding_spec (sup sub : Slice SigEntry) (ex : SigEntry)
    (hsup : List.Pairwise entLt sup.val) (hsub : List.Pairwise entLt sub.val) :
    ∃ r, is_subset_excluding sup sub ex = ok r ∧
      (r = true ↔ ∀ e ∈ sub.val, e ≠ ex → e ∈ sup.val) := by
  unfold is_subset_excluding is_subset_excluding_loop
  apply spec_imp_exists
  have hspec :
      loop (fun x : Std.Usize × Std.Usize × Bool =>
          is_subset_excluding_loop.body sup sub ex x.1 x.2.1 x.2.2) (0#usize, 0#usize, true)
        ⦃ r => r = true ↔ ∀ e ∈ sub.val, e ≠ ex → e ∈ sup.val ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : Std.Usize × Std.Usize × Bool =>
        (sub.val.length - x.2.1.val) * (sup.val.length + 2) + (sup.val.length - x.1.val) * 1 +
          (if x.2.2 then 1 else 0))
      (inv := fun x : Std.Usize × Std.Usize × Bool =>
        x.1.val ≤ sup.val.length ∧ x.2.1.val ≤ sub.val.length ∧
        (x.2.2 = true → (∀ e ∈ sub.val.take x.2.1.val, e ≠ ex → e ∈ sup.val) ∧
          ∀ a ∈ sup.val.take x.1.val, ∀ b ∈ sub.val.drop x.2.1.val, entLt a b) ∧
        (x.2.2 = false → ∃ e ∈ sub.val, e ≠ ex ∧ e ∉ sup.val))
      (post := fun r : Bool => r = true ↔ ∀ e ∈ sub.val, e ≠ ex → e ∈ sup.val)
      (body := fun x : Std.Usize × Std.Usize × Bool =>
        is_subset_excluding_loop.body sup sub ex x.1 x.2.1 x.2.2)
      (x := (0#usize, 0#usize, true))
    · intro x hx
      obtain ⟨i, j, r⟩ := x
      obtain ⟨hi, hj, hT, hF⟩ := hx
      simp only at hi hj hT hF
      cases r with
      | false =>
        obtain ⟨e, he, hne, hnot⟩ := hF rfl
        unfold is_subset_excluding_loop.body
        simp only [Bool.false_eq_true, if_false, spec_ok]
        simp only [false_iff, not_forall]
        exact ⟨e, he, hne, hnot⟩
      | true =>
        obtain ⟨hT1, hT2⟩ := hT rfl
        by_cases hjl : j.val < sub.val.length
        · obtain ⟨hB1, hB2, hB3⟩ := iss_body (sup := sup) (sub := sub) (ex := ex) hi hjl
          have hdrop : sub.val.drop j.val = sub.val[j.val]'hjl :: sub.val.drop (j.val + 1) :=
            List.drop_eq_getElem_cons hjl
          have htake : sub.val.take (j.val + 1) = sub.val.take j.val ++ [sub.val[j.val]'hjl] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hjl]; rfl
          have hsorto : ∀ b ∈ sub.val.drop (j.val + 1), entLt (sub.val[j.val]'hjl) b := by
            have := hsub.sublist (List.drop_sublist j.val sub.val)
            rw [hdrop] at this
            exact (List.pairwise_cons.1 this).1
          have hmulj : (sub.val.length - (j.val + 1)) * (sup.val.length + 2) + (sup.val.length + 2)
              = (sub.val.length - j.val) * (sup.val.length + 2) := by
            have : sub.val.length - j.val = (sub.val.length - (j.val + 1)) + 1 := by omega
            rw [this, Nat.add_mul]; simp
          have hmem_drop : ∀ b ∈ sub.val.drop (j.val + 1), b ∈ sub.val.drop j.val := by
            intro b hb; rw [hdrop]; exact List.mem_cons_of_mem _ hb
          by_cases hoex : sub.val[j.val]'hjl = ex
          · obtain ⟨j', hj'v, hbe⟩ := hB1 hoex
            rw [hbe]; simp only [spec_ok]
            refine ⟨⟨hi, by omega, fun _ => ⟨?_, ?_⟩, fun h => absurd h (by simp)⟩, ?_⟩
            · rw [hj'v, htake]
              intro e he hne
              rcases List.mem_append.1 he with h | h
              · exact hT1 e h hne
              · rw [List.mem_singleton.1 h] at hne; exact absurd hoex hne
            · rw [hj'v]
              exact fun a ha b hb => hT2 a ha b (hmem_drop b hb)
            · simp only [hj'v, if_true]; omega
          · by_cases hil : i.val < sup.val.length
            · obtain ⟨hC1, hC2, hC3⟩ := hB2 hoex hil
              have hdropi : sup.val.drop i.val = sup.val[i.val]'hil :: sup.val.drop (i.val + 1) :=
                List.drop_eq_getElem_cons hil
              have htakei : sup.val.take (i.val + 1) = sup.val.take i.val ++ [sup.val[i.val]'hil] := by
                rw [List.take_add_one, List.getElem?_eq_getElem hil]; rfl
              have hsortp : ∀ b ∈ sup.val.drop (i.val + 1), entLt (sup.val[i.val]'hil) b := by
                have := hsup.sublist (List.drop_sublist i.val sup.val)
                rw [hdropi] at this
                exact (List.pairwise_cons.1 this).1
              by_cases hpeq : sup.val[i.val]'hil = sub.val[j.val]'hjl
              · obtain ⟨i', j', hi'v, hj'v, hbe⟩ := hC1 hpeq
                rw [hbe]; simp only [spec_ok]
                refine ⟨⟨by omega, by omega, fun _ => ⟨?_, ?_⟩, fun h => absurd h (by simp)⟩, ?_⟩
                · rw [hj'v, htake]
                  intro e he hne
                  rcases List.mem_append.1 he with h | h
                  · exact hT1 e h hne
                  · rw [List.mem_singleton.1 h, ← hpeq]; exact List.getElem_mem hil
                · rw [hi'v, hj'v, htakei]
                  intro a ha b hb
                  rcases List.mem_append.1 ha with h | h
                  · exact hT2 a h b (hmem_drop b hb)
                  · rw [List.mem_singleton.1 h, hpeq]; exact hsorto b hb
                · simp only [hi'v, hj'v, if_true]; omega
              · by_cases hplt : entLt (sup.val[i.val]'hil) (sub.val[j.val]'hjl)
                · obtain ⟨i', hi'v, hbe⟩ := hC2 hpeq hplt
                  rw [hbe]; simp only [spec_ok]
                  refine ⟨⟨by omega, hj, fun _ => ⟨hT1, ?_⟩, fun h => absurd h (by simp)⟩, ?_⟩
                  · rw [hi'v, htakei]
                    intro a ha b hb
                    rcases List.mem_append.1 ha with h | h
                    · exact hT2 a h b hb
                    · rw [List.mem_singleton.1 h]
                      rw [hdrop] at hb
                      rcases List.mem_cons.1 hb with h2 | h2
                      · rw [h2]; exact hplt
                      · exact _root_.trans hplt (hsorto b h2)
                  · simp only [hi'v, if_true]; omega
                · have hgt : entLt (sub.val[j.val]'hjl) (sup.val[i.val]'hil) := by
                    rcases entLt_trichotomy (sup.val[i.val]'hil) (sub.val[j.val]'hjl) with h | h | h
                    · exact absurd h hplt
                    · exact h
                    · exact absurd h hpeq
                  have hbe := hC3 hpeq hplt
                  rw [hbe]; simp only [spec_ok]
                  refine ⟨⟨hi, hj, fun h => absurd h (by simp), fun _ => ?_⟩, ?_⟩
                  · refine ⟨sub.val[j.val]'hjl, List.getElem_mem hjl, hoex, fun hmem => ?_⟩
                    have hmem' : sub.val[j.val]'hjl ∈ sup.val.take i.val ++ sup.val.drop i.val := by
                      rw [List.take_append_drop]; exact hmem
                    have hirr : ¬ entLt (sub.val[j.val]'hjl) (sub.val[j.val]'hjl) := fun h => by
                      unfold entLt at h; omega
                    rcases List.mem_append.1 hmem' with h | h
                    · exact hirr (hT2 _ h _ (by rw [hdrop]; exact List.mem_cons_self))
                    · rw [hdropi] at h
                      rcases List.mem_cons.1 h with h | h
                      · exact hpeq h.symm
                      · exact hplt (hsortp _ h)
                  · simp only [if_true, if_false, Bool.false_eq_true]; omega
            · have hbe := hB3 hoex hil
              rw [hbe]; simp only [spec_ok]
              refine ⟨⟨hi, hj, fun h => absurd h (by simp), fun _ => ?_⟩, ?_⟩
              · refine ⟨sub.val[j.val]'hjl, List.getElem_mem hjl, hoex, fun hmem => ?_⟩
                have hall : sup.val.take i.val = sup.val := List.take_of_length_le (by omega)
                have := hT2 _ (by rw [hall]; exact hmem) (sub.val[j.val]'hjl)
                  (by rw [hdrop]; exact List.mem_cons_self)
                exact absurd this (by unfold entLt; omega)
              · simp only [if_true, if_false, Bool.false_eq_true]; omega
        · have hjeq : j.val = sub.val.length := by omega
          have hnj : ¬ j < Slice.len sub := by simp [Slice.len, UScalar.lt_equiv]; omega
          unfold is_subset_excluding_loop.body
          simp only [if_true, hnj, if_false, spec_ok]
          simp only [true_iff]
          intro e he hne
          apply hT1 e _ hne
          rw [hjeq, List.take_length]; exact he
    · refine ⟨by simp, by simp, fun _ => ⟨by simp, by simp⟩, by simp⟩
  simpa using hspec

end MercVerified.Refinement.Proofs
