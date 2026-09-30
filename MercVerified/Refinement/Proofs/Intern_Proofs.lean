import MercVerified.Refinement.Proofs.WorklistLoop_Proofs
import MercVerified.Refinement.Proofs.SigKey_Proofs
import MercVerified.Refinement.Proofs.LoopTools_Proofs
import Aeneas.Std.WP

/-!
# Interning of signature keys

`strong_process_marked_elements` interns each state's signature key in a hash map `id` and a table
`key_to_signature` (`kts`). `IdInv` records that the two agree: a lookup returns exactly the key
that was asked for, stored at the class index that names its position in `kts`. Consequently `kts`
has no duplicates, so two states get the same class iff their keys are equal.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_lts.lts (StateTag LabelTag)

open MercVerified.Lts.Proofs

namespace MercVerified.Refinement.Proofs

/-- Lookup in the interning map. -/
noncomputable abbrev internGet (id : InternMap) (q : SigKey) :=
  std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst internBuildHasher
    (verified.core.borrow.Borrow.Blanket SigKey) internHashInst internEqInst id q

theorem allM_zip_lawful {α : Type} [DecidableEq α] (I : core.cmp.PartialEq α α) (hI : core.cmp.PartialEq.IsLawfulEq I) :
    ∀ (l1 l2 : List α), l1.length = l2.length →
      List.allM (fun (x : α × α) => match x with | (x0, x1) => I.eq x0 x1) (List.zip l1 l2) = ok (decide (l1 = l2))
  | [], [], _ => by simp only [List.zip_nil_left, List.allM]; rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    obtain ⟨r, hr, hiff⟩ := hI a b
    have ih := allM_zip_lawful I hI l1 l2 (by simpa using h)
    simp only [List.zip_cons_cons, List.allM]
    simp only [hr, bind_tc_ok]
    cases r
    · have : ¬ a = b := fun e => by simpa using hiff.mpr e
      simp [this]; rfl
    · have hab : a = b := hiff.mp rfl
      subst hab
      simp only [ih]
      simp

/-- The equality instance of signature keys is lawful. -/
theorem sigKey_eq_lawful : core.cmp.PartialEq.IsLawfulEq internEqInst.partialEqInst := by
  intro a b
  have hI : core.cmp.PartialEq.IsLawfulEq
      (verified.Pair.Insts.CoreCmpEq
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpEq LabelTag core.cmp.EqUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpEq BlockTag core.cmp.EqUsize)).partialEqInst :=
    entry_partialEq_lawful
  show ∃ r, alloc.vec.partial_eq.PartialEqVec.eq _ a b = ok r ∧ _
  unfold alloc.vec.partial_eq.PartialEqVec.eq
  by_cases hl : a.length = b.length
  · rw [if_pos hl]
    have := allM_zip_lawful _ hI a.val b.val hl
    refine ⟨decide (a.val = b.val), this, ?_⟩
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact alloc.vec.Vec.ext _ _ h
    · intro h; rw [h]
  · rw [if_neg hl]
    refine ⟨false, rfl, ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro h; exact hl (by rw [h])


theorem sigKey_eq_false {a b : SigKey} (h : a ≠ b) :
    internEqInst.partialEqInst.eq a b = ok false := by
  obtain ⟨r, hr, hiff⟩ := sigKey_eq_lawful a b
  rw [hr]
  cases r
  · rfl
  · exact absurd (hiff.mp rfl) h

/-- The interning map and the key table agree: a lookup returns exactly the queried key, stored at
    the class index naming its position in the table, and every table entry is found at its own
    position. -/
def IdInv (id : InternMap) (kts : VecTy SigKey) : Prop :=
  (∀ q k v, internGet id q = ok (some (k, v)) →
      k = q ∧ ∃ h : v.index.val < kts.val.length, kts.val[v.index.val] = q) ∧
  (∀ i (h : i < kts.val.length), internGet id kts.val[i] = ok (some (kts.val[i], uTag i)))

theorem IdInv.of_empty {id : InternMap} {kts : VecTy SigKey} (hid : ∀ q, internGet id q = ok none)
    (hkts : kts.val = []) : IdInv id kts := by
  refine ⟨fun q k v h => ?_, fun i h => ?_⟩
  · rw [hid q] at h; simp at h
  · rw [hkts] at h; simp at h

theorem IdInv.nodup {id : InternMap} {kts : VecTy SigKey} (h : IdInv id kts)
    (hlen : kts.val.length ≤ Usize.max) : kts.val.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hi := h.2 i.1 i.2
  have hj := h.2 j.1 j.2
  have hij' : kts.val[i.1] = kts.val[j.1] := hij
  rw [hij'] at hi
  rw [hi] at hj
  simp only [ok.injEq, Option.some.injEq, Prod.mk.injEq] at hj
  have h2 : uTag (Tag := BlockTag) i.1 = uTag j.1 := hj.2
  have hi2 : i.1 < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; have := i.2; omega
  have hj2 : j.1 < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; have := j.2; omega
  have h3 : (uTag (Tag := BlockTag) i.1).index.val = (uTag (Tag := BlockTag) j.1).index.val := by rw [h2]
  simp only [uTag] at h3
  rw [uTotal_val_of_lt hi2, uTotal_val_of_lt hj2] at h3
  exact Fin.ext h3

theorem len_tag_eq (kts : VecTy SigKey) :
    ({ index := alloc.vec.Vec.len kts, marker := () } : BT) = uTag kts.val.length := by
  apply merc_utilities.tagged_index.TagIndex.ext
  apply UScalar.eq_of_val_eq
  have hk : kts.val.length < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; have := kts.property; omega
  show (alloc.vec.Vec.len kts).val = (uTotal kts.val.length).val
  rw [uTotal_val_of_lt hk]
  simp [alloc.vec.Vec.len]

/-- A cache miss keeps the interning invariant: the new key is appended and found at the new index,
    all other lookups are unchanged. -/
theorem IdInv.new {id id' : InternMap} {kts kts' : VecTy SigKey} (h : IdInv id kts) {sb : SigKey}
    (hget : internGet id sb = ok none) (hkts' : kts'.val = kts.val ++ [sb])
    (hlook : internGet id' sb = ok (some (sb, uTag kts.val.length)))
    (hother : ∀ q, internEqInst.partialEqInst.eq sb q = ok false → internGet id' q = internGet id q)
    (hlen : kts.val.length < 2 ^ UScalarTy.Usize.numBits) : IdInv id' kts' := by
  refine ⟨fun q k v hq => ?_, fun i hi => ?_⟩
  · by_cases hqs : q = sb
    · subst hqs
      rw [hlook] at hq
      simp only [ok.injEq, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      refine ⟨rfl, ?_, ?_⟩
      · rw [hkts']; simp only [List.length_append, List.length_singleton]
        show (uTag (Tag := BlockTag) kts.val.length).index.val < _
        simp only [uTag]; rw [uTotal_val_of_lt hlen]; omega
      · simp only [hkts']
        have : (uTag (Tag := BlockTag) kts.val.length).index.val = kts.val.length := by
          simp only [uTag]; rw [uTotal_val_of_lt hlen]
        simp [this]
    · rw [hother q (sigKey_eq_false (fun e => hqs e.symm))] at hq
      obtain ⟨hk, hv, hkv⟩ := h.1 q k v hq
      refine ⟨hk, ?_, ?_⟩
      · rw [hkts']; simp only [List.length_append]; omega
      · simp only [hkts']
        rw [List.getElem_append_left hv]; exact hkv
  · have hi' : i < kts.val.length + 1 := by rw [hkts'] at hi; simpa using hi
    by_cases hik : i < kts.val.length
    · have hqs : kts.val[i] ≠ sb := by
        intro e
        have := h.2 i hik
        rw [e, hget] at this
        simp at this
      have e1 : kts'.val[i] = kts.val[i] := by
        simp only [hkts']; rw [List.getElem_append_left hik]
      rw [e1, hother _ (sigKey_eq_false (fun e => hqs e.symm))]
      exact h.2 i hik
    · have hie : i = kts.val.length := by omega
      subst hie
      have e1 : kts'.val[kts.val.length] = sb := by
        simp only [hkts']; simp
      rw [e1]
      exact hlook

end MercVerified.Refinement.Proofs
