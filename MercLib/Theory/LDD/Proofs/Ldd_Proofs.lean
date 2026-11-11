module

public import MercLib.Theory.LDD.Ldd
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Proofs: list decision diagrams

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/LDD.lean` (human-vetted).
-/

namespace MercLib.LDD

namespace Ldd

variable {α : Type*} [LinearOrder α]

private theorem length_of_mem : ∀ (a : Ldd α) (n : ℕ), a.WellFormed n →
    ∀ x ∈ a.denote, x.length = n
  | zero, _, _, x, hx => by simp [denote] at hx
  | one, n, h, x, hx => by
      simp only [WellFormed] at h; simp only [denote, Set.mem_singleton_iff] at hx; simp [hx, h]
  | node _ _ _, 0, h, _, _ => by simp [WellFormed] at h
  | node v d r, n + 1, h, x, hx => by
      obtain ⟨-, hd, hr, -⟩ := h
      rcases hx with ⟨y, hy, rfl⟩ | hx
      · simp [length_of_mem d n hd y hy]
      · exact length_of_mem r (n + 1) hr x hx

/-- Every vector of a well-formed LDD of positive height starts with a value above every `v`
    that the LDD's head is above. -/
private theorem head_of_mem : ∀ (a : Ldd α) (n : ℕ), a.WellFormed (n + 1) →
    ∀ x ∈ a.denote, ∃ b xs, x = b :: xs ∧ ∀ v, HeadAbove v a → v < b
  | zero, _, _, x, hx => by simp [denote] at hx
  | one, n, h, _, _ => by simp [WellFormed] at h
  | node w e s, n, h, x, hx => by
      obtain ⟨-, -, hs, hws⟩ := h
      rcases hx with ⟨y, -, rfl⟩ | hx
      · exact ⟨w, y, rfl, fun v hv => hv⟩
      · obtain ⟨b, xs, rfl, hb⟩ := head_of_mem s n hs x hx
        exact ⟨b, xs, rfl, fun v hv => lt_trans hv (hb w hws)⟩

private theorem nonempty_of_ne_zero : ∀ (a : Ldd α) (n : ℕ), a.WellFormed n → a ≠ zero →
    a.denote.Nonempty
  | zero, _, _, h => absurd rfl h
  | one, _, _, _ => ⟨[], rfl⟩
  | node _ _ _, 0, h, _ => by simp [WellFormed] at h
  | node v d _, n + 1, h, _ => by
      obtain ⟨hd0, hd, -, -⟩ := h
      obtain ⟨x, hx⟩ := nonempty_of_ne_zero d n hd hd0
      exact ⟨v :: x, Or.inl ⟨x, hx, rfl⟩⟩

private theorem eq_zero_of_denote_empty {a : Ldd α} {n : ℕ} (h : a.WellFormed n)
    (he : a.denote = ∅) : a = zero := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_of_ne_zero a n h hne
  simp [he] at hx

/-- The vectors of `node v d r` that start with `v` are exactly `v :: d`. -/
private theorem mem_node_cons {v : α} {d r : Ldd α} {n : ℕ} (h : (node v d r).WellFormed (n + 1))
    (x : List α) : v :: x ∈ (node v d r).denote ↔ x ∈ d.denote := by
  obtain ⟨-, -, hr, hvr⟩ := h
  constructor
  · rintro (⟨y, hy, hxy⟩ | hx)
    · cases hxy; exact hy
    · obtain ⟨b, xs, hbx, hb⟩ := head_of_mem r n hr _ hx
      cases hbx
      exact absurd (hb v hvr) (lt_irrefl _)
  · intro hx; exact Or.inl ⟨x, hx, rfl⟩

/-- The vectors of `r` are those of `node v d r` that do not start with `v`. -/
private theorem mem_node_right {v : α} {d r : Ldd α} {n : ℕ}
    (h : (node v d r).WellFormed (n + 1)) (x : List α) :
    x ∈ r.denote ↔ x ∈ (node v d r).denote ∧ x.head? ≠ some v := by
  obtain ⟨-, -, hr, hvr⟩ := h
  constructor
  · intro hx
    refine ⟨Or.inr hx, ?_⟩
    obtain ⟨b, xs, rfl, hb⟩ := head_of_mem r n hr _ hx
    simpa using (ne_of_lt (hb v hvr)).symm
  · rintro ⟨(⟨y, -, rfl⟩ | hx), hne⟩
    · simp at hne
    · exact hx

private theorem head_le_of_mem {v : α} {d r : Ldd α} {n : ℕ} (h : (node v d r).WellFormed (n + 1))
    {b : α} {xs : List α} (hx : b :: xs ∈ (node v d r).denote) : v ≤ b := by
  rcases hx with ⟨y, -, hy⟩ | hx
  · cases hy; exact le_rfl
  · obtain ⟨-, -, hr, hvr⟩ := h
    obtain ⟨b', xs', hb', hlt⟩ := head_of_mem r n hr _ hx
    cases hb'
    exact le_of_lt (hlt v hvr)

private theorem canonical_aux : ∀ (a : Ldd α) (n : ℕ) (b : Ldd α), a.WellFormed n →
    b.WellFormed n → a.denote = b.denote → a = b
  | zero, n, b, _, hb, he => (eq_zero_of_denote_empty hb (by rw [← he]; rfl)).symm
  | one, n, b, ha, hb, he => by
      simp only [WellFormed] at ha; subst ha
      match b, hb with
      | zero, _ => simp [denote] at he
      | one, _ => rfl
  | node v d r, 0, b, ha, _, _ => by simp [WellFormed] at ha
  | node v d r, n + 1, b, ha, hb, he => by
      match b, hb with
      | zero, _ =>
        exact absurd (eq_zero_of_denote_empty ha he) (by simp)
      | node w e s, hb =>
        have ha' : (node v d r).WellFormed (n + 1) := ha
        have hb' : (node w e s).WellFormed (n + 1) := hb
        obtain ⟨hd0, hd, hr, -⟩ := ha
        obtain ⟨he0, he', hs, -⟩ := hb
        -- the heads agree
        obtain ⟨x, hx⟩ := nonempty_of_ne_zero d n hd hd0
        obtain ⟨y, hy⟩ := nonempty_of_ne_zero e n he' he0
        have h1 : w ≤ v := by
          have : v :: x ∈ (node w e s).denote := he ▸ Or.inl ⟨x, hx, rfl⟩
          exact head_le_of_mem hb' this
        have h2 : v ≤ w := by
          have : w :: y ∈ (node v d r).denote := he ▸ Or.inl ⟨y, hy, rfl⟩
          exact head_le_of_mem ha' this
        have hvw : v = w := le_antisymm h2 h1
        subst hvw
        have hde : d.denote = e.denote := by
          ext z
          rw [← mem_node_cons ha' z, ← mem_node_cons hb' z, he]
        have hrs : r.denote = s.denote := by
          ext z
          rw [mem_node_right ha' z, mem_node_right hb' z, he]
        rw [canonical_aux d n e hd he' hde, canonical_aux r (n + 1) s hr hs hrs]

open scoped Classical in
/-- The spine for the heads `H`: every finite set of vectors of length `n + 1` whose heads are in
    `H` is represented by a well-formed LDD whose head is above every `v` below all of `H`. -/
private theorem complete_spine (n : ℕ)
    (ih : ∀ S : Set (List α), S.Finite → (∀ x ∈ S, x.length = n) →
      ∃ a : Ldd α, a.WellFormed n ∧ a.denote = S) (H : Finset α) :
    ∀ S : Set (List α), S.Finite → (∀ x ∈ S, x.length = n + 1) →
      (∀ x ∈ S, ∃ h ∈ H, x.head? = some h) →
      ∃ a : Ldd α, a.WellFormed (n + 1) ∧ a.denote = S ∧ ∀ v, (∀ h ∈ H, v < h) → HeadAbove v a := by
  induction H using Finset.induction_on_min with
  | empty =>
    intro S _ _ hH
    refine ⟨zero, trivial, ?_, fun _ _ => trivial⟩
    ext x
    simp only [denote, Set.mem_empty_iff_false, false_iff]
    intro hx
    obtain ⟨h, hh, -⟩ := hH x hx
    simp at hh
  | insert a H haH ihH =>
    intro S hS hlen hH
    -- the vectors starting with `a`, and the others
    let Sa : Set (List α) := List.cons a ⁻¹' S
    let S' : Set (List α) := {x | x ∈ S ∧ x.head? ≠ some a}
    have hSa : Sa.Finite := hS.preimage List.cons_injective.injOn
    have hSa_len : ∀ x ∈ Sa, x.length = n := by
      intro x hx; have := hlen _ hx; simpa using this
    have hS' : S'.Finite := hS.subset fun x hx => hx.1
    have hS'_len : ∀ x ∈ S', x.length = n + 1 := fun x hx => hlen x hx.1
    have hS'_H : ∀ x ∈ S', ∃ h ∈ H, x.head? = some h := by
      intro x hx
      obtain ⟨h, hh, hxh⟩ := hH x hx.1
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact absurd hxh hx.2
      · exact ⟨h, hh, hxh⟩
    obtain ⟨d, hd, hdS⟩ := ih Sa hSa hSa_len
    obtain ⟨r, hr, hrS, hrH⟩ := ihH S' hS' hS'_len hS'_H
    have hS_split : S = (List.cons a '' Sa) ∪ S' := by
      ext x
      constructor
      · intro hx
        by_cases hxa : x.head? = some a
        · left
          match x, hxa with
          | _ :: xs, hxa =>
            simp only [List.head?_cons, Option.some.injEq] at hxa
            subst hxa
            exact ⟨xs, hx, rfl⟩
        · exact Or.inr ⟨hx, hxa⟩
      · rintro (⟨y, hy, rfl⟩ | hx)
        · exact hy
        · exact hx.1
    by_cases hd0 : d = zero
    · refine ⟨r, hr, ?_, fun v hv => hrH v fun h hh => hv h (Finset.mem_insert_of_mem hh)⟩
      have : Sa = ∅ := by rw [← hdS, hd0]; rfl
      rw [hrS, hS_split, this, Set.image_empty, Set.empty_union]
    · refine ⟨node a d r, ⟨hd0, hd, hr, hrH a haH⟩, ?_, fun v hv => hv a (Finset.mem_insert_self _ _)⟩
      rw [hS_split, ← hdS, ← hrS]
      rfl

private theorem complete_aux : ∀ (n : ℕ) (S : Set (List α)), S.Finite →
    (∀ x ∈ S, x.length = n) → ∃ a : Ldd α, a.WellFormed n ∧ a.denote = S
  | 0, S, _, hlen => by
    by_cases hS : S = ∅
    · exact ⟨zero, trivial, hS.symm⟩
    · refine ⟨one, rfl, ?_⟩
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS
      have hx0 : x = [] := List.eq_nil_of_length_eq_zero (hlen x hx)
      ext y
      simp only [denote, Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact hx0 ▸ hx
      · intro hy; exact List.eq_nil_of_length_eq_zero (hlen y hy)
  | n + 1, S, hS, hlen => by
    classical
    let T : Set (Option α) := List.head? '' S
    have hT : T.Finite := hS.image _
    have hH : (Option.some ⁻¹' T).Finite := hT.preimage (Option.some_injective α).injOn
    obtain ⟨a, ha, haS, -⟩ := complete_spine n (complete_aux n) hH.toFinset S hS hlen (by
      intro x hx
      match x, hlen x hx, hx with
      | b :: xs, _, hx => exact ⟨b, by simpa [T] using ⟨b :: xs, hx, rfl⟩, rfl⟩)
    exact ⟨a, ha, haS⟩

end Ldd

open Ldd

/-- **LDDs are canonical.** -/
theorem canonical (α : Type*) [LinearOrder α] : Canonical α :=
  fun n a b ha hb he => canonical_aux a n b ha hb he

/-- **Every finite set of vectors is an LDD.** -/
theorem complete (α : Type*) [LinearOrder α] : Complete α :=
  complete_aux

end MercLib.LDD
