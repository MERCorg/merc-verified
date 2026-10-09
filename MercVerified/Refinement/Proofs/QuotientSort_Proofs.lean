import MercVerified.Refinement.Proofs.SigKey_Proofs

/-!
# Quotient entries: equality and ordering of `(label, target state)` pairs

The analogue of `SigKey_Proofs` for the pairs collected by `quotient_collect_transitions`
(`(label, block)` with the block as a `StateTag` index of the quotient).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag)
open MercVerified.Lts.Proofs

namespace MercVerified.Refinement.Proofs

abbrev QElem' := (TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize StateTag)

/-- Lexicographic strict order on signature entries (on the underlying indices). -/
def qLt (a b : QElem') : Prop :=
  a.1.index.val < b.1.index.val ∨ (a.1.index.val = b.1.index.val ∧ a.2.index.val < b.2.index.val)

instance : Std.Irrefl qLt := ⟨by intro a h; unfold qLt at h; omega⟩

instance : Std.Antisymm qLt := ⟨by intro a b h1 h2; unfold qLt at h1 h2; omega⟩

instance : Trans qLt qLt qLt := ⟨by intro a b c h1 h2; unfold qLt at *; omega⟩

theorem qelem_ext {a b : QElem'} (h1 : a.1.index.val = b.1.index.val)
    (h2 : a.2.index.val = b.2.index.val) : a = b := by
  obtain ⟨⟨a1, ma1⟩, ⟨a2, ma2⟩⟩ := a
  obtain ⟨⟨b1, mb1⟩, ⟨b2, mb2⟩⟩ := b
  cases ma1; cases ma2; cases mb1; cases mb2
  simp only at h1 h2
  have e1 : a1 = b1 := UScalar.eq_of_val_eq h1
  have e2 : a2 = b2 := UScalar.eq_of_val_eq h2
  subst e1; subst e2; rfl

/-- The signature entries' equality instance is lawful. -/
theorem q_partialEq_lawful :
    core.cmp.PartialEq.IsLawfulEq
      (verified.Pair.Insts.CoreCmpPartialEqPair
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag
          core.cmp.PartialEqUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex StateTag
          core.cmp.PartialEqUsize)) :=
  pair_partialEq_lawful _ _ (tagIndex_partialEq_lawful _ usize_partialEq_lawful)
    (tagIndex_partialEq_lawful _ usize_partialEq_lawful)

/-- The `Ord` instance of signature entries. -/
noncomputable abbrev qOrd : core.cmp.Ord QElem' :=
  verified.Pair.Insts.CoreCmpOrd
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
    (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd StateTag core.cmp.OrdUsize)

/-- The lexicographic comparison of signature entries. -/
def qCmp (a b : QElem') : Ordering :=
  if compare a.1.index.val b.1.index.val = Ordering.eq then compare a.2.index.val b.2.index.val
  else compare a.1.index.val b.1.index.val

theorem q_cmp_eq (a b : QElem') : qOrd.cmp a b = ok (qCmp a b) := by
  obtain ⟨a1, b1⟩ := a
  obtain ⟨a2, b2⟩ := b
  show Pair.Insts.CoreCmpOrd.cmp _ _ (a1, b1) (a2, b2) = _
  rw [Pair.Insts.CoreCmpOrd.cmp_spec]
  have h1 : (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag
      core.cmp.OrdUsize).cmp a1 a2 = ok (compare a1.index.val a2.index.val) := rfl
  have h2 : (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd StateTag
      core.cmp.OrdUsize).cmp b1 b2 = ok (compare b1.index.val b2.index.val) := rfl
  rw [h1]
  simp only [bind_ok, qCmp]
  split_ifs
  · exact h2
  · rfl

theorem qCmp_gt_iff (a b : QElem') : qCmp a b = Ordering.gt ↔ qLt b a := by
  unfold qCmp qLt
  by_cases h : compare a.1.index.val b.1.index.val = Ordering.eq
  · rw [if_pos h]
    have h' : a.1.index.val = b.1.index.val := compare_eq_iff_eq.mp h
    rw [compare_gt_iff_gt]
    omega
  · rw [if_neg h]
    rw [compare_gt_iff_gt]
    have : ¬ a.1.index.val = b.1.index.val := fun e => h (compare_eq_iff_eq.mpr e)
    omega

theorem qCmp_lt_iff (a b : QElem') : qCmp a b = Ordering.lt ↔ qLt a b := by
  unfold qCmp qLt
  by_cases h : compare a.1.index.val b.1.index.val = Ordering.eq
  · rw [if_pos h]
    have h' : a.1.index.val = b.1.index.val := compare_eq_iff_eq.mp h
    rw [compare_lt_iff_lt]
    omega
  · rw [if_neg h]
    rw [compare_lt_iff_lt]
    have : ¬ a.1.index.val = b.1.index.val := fun e => h (compare_eq_iff_eq.mpr e)
    omega

theorem qCmp_eq_iff (a b : QElem') : qCmp a b = Ordering.eq ↔ a = b := by
  unfold qCmp
  by_cases h : compare a.1.index.val b.1.index.val = Ordering.eq
  · rw [if_pos h]
    have h' : a.1.index.val = b.1.index.val := compare_eq_iff_eq.mp h
    rw [compare_eq_iff_eq]
    constructor
    · intro h2; exact qelem_ext h' h2
    · intro h2; rw [h2]
  · rw [if_neg h]
    have : ¬ a.1.index.val = b.1.index.val := fun e => h (compare_eq_iff_eq.mpr e)
    constructor
    · intro h2; exact absurd h2 h
    · intro h2; subst h2; exact absurd rfl this

theorem q_ord_total : core.cmp.Ord.IsTotalOrder qOrd := by
  refine ⟨fun a b => ⟨_, q_cmp_eq a b⟩, fun a b => ?_, fun a b c => ?_⟩
  · rw [q_cmp_eq, q_cmp_eq]
    simp only [ok.injEq]
    rw [qCmp_gt_iff, qCmp_lt_iff]
  · rw [q_cmp_eq, q_cmp_eq, q_cmp_eq]
    simp only [ne_eq, ok.injEq, qCmp_gt_iff]
    intro h1 h2
    unfold qLt at *
    omega

/-- A strictly sorted list of entries is determined by its members. -/
theorem qSorted_unique {l l' : List QElem'} (h : List.Pairwise qLt l) (h' : List.Pairwise qLt l')
    (hmem : ∀ x, x ∈ l ↔ x ∈ l') : l = l' :=
  List.Pairwise.eq_of_mem_iff h h' hmem

theorem qLt_trichotomy (a b : QElem') : qLt a b ∨ qLt b a ∨ a = b := by
  unfold qLt
  by_cases h1 : a.1.index.val = b.1.index.val
  · by_cases h2 : a.2.index.val = b.2.index.val
    · exact Or.inr (Or.inr (qelem_ext h1 h2))
    · omega
  · omega

/-- A sorted (`≤`) list without equal neighbours is strictly sorted. -/
theorem q_sorted_chain_strict : ∀ {l : List QElem'},
    List.Pairwise (fun a b => qOrd.cmp a b ≠ ok Ordering.gt) l →
    List.IsChain (fun a b => a ≠ b) l → List.Pairwise qLt l
  | [], _, _ => List.Pairwise.nil
  | [a], _, _ => List.pairwise_singleton _ _
  | a :: b :: t, hs, hc => by
    have hs' := List.pairwise_cons.mp hs
    have hc' := List.isChain_cons_cons.mp hc
    have ih := q_sorted_chain_strict hs'.2 hc'.2
    have hgt : qOrd.cmp a b ≠ ok Ordering.gt := hs'.1 b (by simp)
    rw [q_cmp_eq] at hgt
    have hnb : ¬ qLt b a := fun h => hgt (by rw [(qCmp_gt_iff a b).mpr h])
    have hab : qLt a b := by
      rcases qLt_trichotomy a b with h | h | h
      · exact h
      · exact absurd h hnb
      · exact absurd h hc'.1
    refine List.pairwise_cons.mpr ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab
    · exact _root_.trans hab ((List.pairwise_cons.mp ih).1 x hx)

end MercVerified.Refinement.Proofs
