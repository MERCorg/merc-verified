import Signatures.BranchingBisimilarity
import Mathlib.Logic.Relation

/-!
# Branching bisimilarity of an embedded sub-LTS

If `f : S → T` embeds `l1` into `l2` as a closed sub-LTS, branching bisimilarity of `l1` and of
`l2` agree on the image of `f`. Used to move between the LTS on `Fin n` of the real states and
the LTS on all state indices.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Cslib

namespace MercVerified.Refinement.Proofs

theorem bb_embed {S T Label : Type} [HasTau Label] (l1 : LTS S Label) (l2 : LTS T Label)
    (f : S → T) (hf : ∀ a μ b, l1.Tr a μ b ↔ l2.Tr (f a) μ (f b))
    (hcl : ∀ a μ t, l2.Tr (f a) μ t → ∃ b, t = f b) (a a' : S) :
    BranchingBisimilarity l1 a a' ↔ BranchingBisimilarity l2 (f a) (f a') := by
  have hdown : ∀ a b, l1.τSTr a b → l2.τSTr (f a) (f b) := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ ht ih => exact ih.tail ((hf _ HasTau.τ _).1 ht)
  have hup : ∀ a t, l2.τSTr (f a) t → ∃ b, t = f b ∧ l1.τSTr a b := by
    intro a t h
    induction h with
    | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
    | tail _ ht ih =>
      obtain ⟨b, rfl, hb⟩ := ih
      obtain ⟨c, rfl⟩ := hcl b _ _ ht
      exact ⟨c, rfl, hb.tail ((hf b HasTau.τ c).2 ht)⟩
  constructor
  · rintro ⟨r, hr, hbis⟩
    refine ⟨fun x y => ∃ a a', x = f a ∧ y = f a' ∧ r a a', ⟨a, a', rfl, rfl, hr⟩, ?_⟩
    rintro _ _ ⟨a, a', rfl, rfl, hra⟩ μ
    obtain ⟨hL, hR⟩ := hbis hra μ
    constructor
    · intro s1' ht
      obtain ⟨b, rfl⟩ := hcl a μ s1' ht
      rcases hL b ((hf a μ b).2 ht) with ⟨hμ, hrb⟩ | ⟨t2, t2', hs, htr, hr1, hr2⟩
      · exact Or.inl ⟨hμ, b, a', rfl, rfl, hrb⟩
      · exact Or.inr ⟨f t2, f t2', (LTS.sTr_τSTr l2).mpr (hdown _ _ ((LTS.sTr_τSTr l1).mp hs)),
          (hf t2 μ t2').1 htr, ⟨a, t2, rfl, rfl, hr1⟩, ⟨b, t2', rfl, rfl, hr2⟩⟩
    · intro s2' ht
      obtain ⟨b, rfl⟩ := hcl a' μ s2' ht
      rcases hR b ((hf a' μ b).2 ht) with ⟨hμ, hrb⟩ | ⟨t1, t1', hs, htr, hr1, hr2⟩
      · exact Or.inl ⟨hμ, a, b, rfl, rfl, hrb⟩
      · exact Or.inr ⟨f t1, f t1', (LTS.sTr_τSTr l2).mpr (hdown _ _ ((LTS.sTr_τSTr l1).mp hs)),
          (hf t1 μ t1').1 htr, ⟨t1, a', rfl, rfl, hr1⟩, ⟨t1', b, rfl, rfl, hr2⟩⟩
  · rintro ⟨r, hr, hbis⟩
    refine ⟨fun x y => r (f x) (f y), hr, ?_⟩
    intro x y hxy μ
    obtain ⟨hL, hR⟩ := hbis hxy μ
    constructor
    · intro x' ht
      rcases hL (f x') ((hf x μ x').1 ht) with ⟨hμ, hrb⟩ | ⟨t2, t2', hs, htr, hr1, hr2⟩
      · exact Or.inl ⟨hμ, hrb⟩
      · obtain ⟨c, rfl, hc⟩ := hup y t2 ((LTS.sTr_τSTr l2).mp hs)
        obtain ⟨d, rfl⟩ := hcl c μ t2' htr
        exact Or.inr ⟨c, d, (LTS.sTr_τSTr l1).mpr hc, (hf c μ d).2 htr, hr1, hr2⟩
    · intro y' ht
      rcases hR (f y') ((hf y μ y').1 ht) with ⟨hμ, hrb⟩ | ⟨t1, t1', hs, htr, hr1, hr2⟩
      · exact Or.inl ⟨hμ, hrb⟩
      · obtain ⟨c, rfl, hc⟩ := hup x t1 ((LTS.sTr_τSTr l2).mp hs)
        obtain ⟨d, rfl⟩ := hcl c μ t1' htr
        exact Or.inr ⟨c, d, (LTS.sTr_τSTr l1).mpr hc, (hf c μ d).2 htr, hr1, hr2⟩

end MercVerified.Refinement.Proofs
