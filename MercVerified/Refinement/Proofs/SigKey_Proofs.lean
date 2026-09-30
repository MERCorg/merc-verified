import MercVerified.Lts.Proofs.Foundation_Proofs
import MercVerified.Code.FunsExternal
import Aeneas.Std.WP

/-!
# Signature keys: equality and ordering of `(label, block)` entries

`strong_bisim_signature` sorts and deduplicates a vector of `(label, block)` entries. With the
lexicographic order on the underlying indices, a strictly sorted list is determined by its
members. This file proves that the instances used (`Pair` of `TagIndex`-of-`usize`) satisfy the
lawfulness hypotheses of the `sort_unstable`/`dedup` axioms and derives the canonical-form lemma
`sigKey_unique`.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag)
open verified.merc_collections.indexed_partition (BlockTag)
open MercVerified.Lts.Proofs

namespace MercVerified.Refinement.Proofs

/-- A signature entry: a label index paired with a block index. -/
abbrev SigEntry := (TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)

/-- Lexicographic strict order on signature entries (on the underlying indices). -/
def entLt (a b : SigEntry) : Prop :=
  a.1.index.val < b.1.index.val ∨ (a.1.index.val = b.1.index.val ∧ a.2.index.val < b.2.index.val)

instance : Std.Irrefl entLt := ⟨by intro a h; unfold entLt at h; omega⟩

instance : Std.Antisymm entLt := ⟨by intro a b h1 h2; unfold entLt at h1 h2; omega⟩

instance : Trans entLt entLt entLt := ⟨by intro a b c h1 h2; unfold entLt at *; omega⟩

theorem entry_ext {a b : SigEntry} (h1 : a.1.index.val = b.1.index.val)
    (h2 : a.2.index.val = b.2.index.val) : a = b := by
  obtain ⟨⟨a1, ma1⟩, ⟨a2, ma2⟩⟩ := a
  obtain ⟨⟨b1, mb1⟩, ⟨b2, mb2⟩⟩ := b
  cases ma1; cases ma2; cases mb1; cases mb2
  simp only at h1 h2
  have e1 : a1 = b1 := UScalar.eq_of_val_eq h1
  have e2 : a2 = b2 := UScalar.eq_of_val_eq h2
  subst e1; subst e2; rfl

/-- The `PartialEq` instance on `usize` never fails and is equality. -/
theorem usize_partialEq_lawful : core.cmp.PartialEq.IsLawfulEq core.cmp.PartialEqUsize := by
  intro a b
  refine ⟨decide (a = b), ?_, by simp⟩
  rfl

/-- `TagIndex`'s `PartialEq` is lawful when the payload's is. -/
theorem tagIndex_partialEq_lawful {Tag : Type} {T : Type} (I : core.cmp.PartialEq T T)
    (hI : core.cmp.PartialEq.IsLawfulEq I) :
    core.cmp.PartialEq.IsLawfulEq
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex (T := T) Tag I) := by
  intro a b
  obtain ⟨r, hr, hiff⟩ := hI a.index b.index
  refine ⟨r, ?_, ?_⟩
  · show verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq I a b = ok r
    rw [tag_partial_eq_inst]; exact hr
  · rw [hiff]
    constructor
    · intro h; exact merc_utilities.tagged_index.TagIndex.ext h
    · intro h; rw [h]

/-- Tuple `PartialEq` is lawful when both components' are. -/
theorem pair_partialEq_lawful {U T : Type} (iU : core.cmp.PartialEq U U) (iT : core.cmp.PartialEq T T)
    (hU : core.cmp.PartialEq.IsLawfulEq iU) (hT : core.cmp.PartialEq.IsLawfulEq iT) :
    core.cmp.PartialEq.IsLawfulEq (verified.Pair.Insts.CoreCmpPartialEqPair iU iT) := by
  intro a b
  obtain ⟨a1, b1⟩ := a
  obtain ⟨a2, b2⟩ := b
  obtain ⟨r1, h1, i1⟩ := hU a1 a2
  obtain ⟨r2, h2, i2⟩ := hT b1 b2
  show ∃ r, Pair.Insts.CoreCmpPartialEqPair.eq iU iT (a1, b1) (a2, b2) = ok r ∧ _
  rw [Pair.Insts.CoreCmpPartialEqPair.eq_spec, h1]
  cases r1
  · refine ⟨false, by simp, ?_⟩
    simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, not_and]
    intro h; exact absurd (i1.mpr h) (by simp)
  · refine ⟨r2, by simpa using h2, ?_⟩
    simp only [Prod.mk.injEq]
    rw [i2]
    exact ⟨fun h => ⟨i1.mp rfl, h⟩, fun h => h.2⟩

/-- The signature entries' equality instance is lawful. -/
theorem entry_partialEq_lawful :
    core.cmp.PartialEq.IsLawfulEq
      (verified.Pair.Insts.CoreCmpPartialEqPair
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag
          core.cmp.PartialEqUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag
          core.cmp.PartialEqUsize)) :=
  pair_partialEq_lawful _ _ (tagIndex_partialEq_lawful _ usize_partialEq_lawful)
    (tagIndex_partialEq_lawful _ usize_partialEq_lawful)

/-- The `Ord` instance of signature entries. -/
noncomputable abbrev entryOrd : core.cmp.Ord SigEntry :=
  verified.Pair.Insts.CoreCmpOrd
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd BlockTag core.cmp.OrdUsize)

/-- The lexicographic comparison of signature entries. -/
def entCmp (a b : SigEntry) : Ordering :=
  if compare a.1.index.val b.1.index.val = Ordering.eq then compare a.2.index.val b.2.index.val
  else compare a.1.index.val b.1.index.val

theorem entry_cmp_eq (a b : SigEntry) : entryOrd.cmp a b = ok (entCmp a b) := by
  obtain ⟨a1, b1⟩ := a
  obtain ⟨a2, b2⟩ := b
  show Pair.Insts.CoreCmpOrd.cmp _ _ (a1, b1) (a2, b2) = _
  rw [Pair.Insts.CoreCmpOrd.cmp_spec]
  have h1 : (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag
      core.cmp.OrdUsize).cmp a1 a2 = ok (compare a1.index.val a2.index.val) := rfl
  have h2 : (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd BlockTag
      core.cmp.OrdUsize).cmp b1 b2 = ok (compare b1.index.val b2.index.val) := rfl
  rw [h1]
  simp only [bind_tc_ok, entCmp]
  split_ifs
  · exact h2
  · rfl

theorem entCmp_gt_iff (a b : SigEntry) : entCmp a b = Ordering.gt ↔ entLt b a := by
  unfold entCmp entLt
  by_cases h : compare a.1.index.val b.1.index.val = Ordering.eq
  · rw [if_pos h]
    have h' : a.1.index.val = b.1.index.val := compare_eq_iff_eq.mp h
    rw [compare_gt_iff_gt]
    omega
  · rw [if_neg h]
    rw [compare_gt_iff_gt]
    have : ¬ a.1.index.val = b.1.index.val := fun e => h (compare_eq_iff_eq.mpr e)
    omega

theorem entCmp_lt_iff (a b : SigEntry) : entCmp a b = Ordering.lt ↔ entLt a b := by
  unfold entCmp entLt
  by_cases h : compare a.1.index.val b.1.index.val = Ordering.eq
  · rw [if_pos h]
    have h' : a.1.index.val = b.1.index.val := compare_eq_iff_eq.mp h
    rw [compare_lt_iff_lt]
    omega
  · rw [if_neg h]
    rw [compare_lt_iff_lt]
    have : ¬ a.1.index.val = b.1.index.val := fun e => h (compare_eq_iff_eq.mpr e)
    omega

theorem entCmp_eq_iff (a b : SigEntry) : entCmp a b = Ordering.eq ↔ a = b := by
  unfold entCmp
  by_cases h : compare a.1.index.val b.1.index.val = Ordering.eq
  · rw [if_pos h]
    have h' : a.1.index.val = b.1.index.val := compare_eq_iff_eq.mp h
    rw [compare_eq_iff_eq]
    constructor
    · intro h2; exact entry_ext h' h2
    · intro h2; rw [h2]
  · rw [if_neg h]
    have : ¬ a.1.index.val = b.1.index.val := fun e => h (compare_eq_iff_eq.mpr e)
    constructor
    · intro h2; exact absurd h2 h
    · intro h2; subst h2; exact absurd rfl this

theorem entry_ord_total : core.cmp.Ord.IsTotalOrder entryOrd := by
  refine ⟨fun a b => ⟨_, entry_cmp_eq a b⟩, fun a b => ?_, fun a b c => ?_⟩
  · rw [entry_cmp_eq, entry_cmp_eq]
    simp only [ok.injEq]
    rw [entCmp_gt_iff, entCmp_lt_iff]
  · rw [entry_cmp_eq, entry_cmp_eq, entry_cmp_eq]
    simp only [ne_eq, ok.injEq, entCmp_gt_iff]
    intro h1 h2
    unfold entLt at *
    omega

/-- A strictly sorted list of entries is determined by its members. -/
theorem sigKey_unique {l l' : List SigEntry} (h : List.Pairwise entLt l) (h' : List.Pairwise entLt l')
    (hmem : ∀ x, x ∈ l ↔ x ∈ l') : l = l' :=
  List.Pairwise.eq_of_mem_iff h h' hmem

theorem entLt_trichotomy (a b : SigEntry) : entLt a b ∨ entLt b a ∨ a = b := by
  unfold entLt
  by_cases h1 : a.1.index.val = b.1.index.val
  · by_cases h2 : a.2.index.val = b.2.index.val
    · exact Or.inr (Or.inr (entry_ext h1 h2))
    · omega
  · omega

/-- A sorted (`≤`) list without equal neighbours is strictly sorted. -/
theorem sorted_chain_strict : ∀ {l : List SigEntry},
    List.Pairwise (fun a b => entryOrd.cmp a b ≠ ok Ordering.gt) l →
    List.IsChain (fun a b => a ≠ b) l → List.Pairwise entLt l
  | [], _, _ => List.Pairwise.nil
  | [a], _, _ => List.pairwise_singleton _ _
  | a :: b :: t, hs, hc => by
    have hs' := List.pairwise_cons.mp hs
    have hc' := List.isChain_cons_cons.mp hc
    have ih := sorted_chain_strict hs'.2 hc'.2
    have hgt : entryOrd.cmp a b ≠ ok Ordering.gt := hs'.1 b (by simp)
    rw [entry_cmp_eq] at hgt
    have hnb : ¬ entLt b a := fun h => hgt (by rw [(entCmp_gt_iff a b).mpr h])
    have hab : entLt a b := by
      rcases entLt_trichotomy a b with h | h | h
      · exact h
      · exact absurd h hnb
      · exact absurd h hc'.1
    refine List.pairwise_cons.mpr ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab
    · exact _root_.trans hab ((List.pairwise_cons.mp ih).1 x hx)

end MercVerified.Refinement.Proofs
