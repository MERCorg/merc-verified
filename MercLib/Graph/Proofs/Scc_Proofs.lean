module

public import MercLib.Graph.Scc
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section

/-!
# Proofs: strongly connected components

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The "headline" theorem is
stated in `Challenges/Graph.lean` (human-vetted).
-/

namespace MercLib.Graph

variable {V : Type*} {E : V → V → Prop}

theorem Reach.trans {X : Set V} {a b c : V} (h1 : Reach E X a b) (h2 : Reach E X b c) :
    Reach E X a c :=
  Relation.ReflTransGen.trans h1 h2

theorem Reach.single {X : Set V} {a b : V} (ha : a ∈ X) (hb : b ∈ X) (he : E a b) :
    Reach E X a b :=
  Relation.ReflTransGen.single ⟨ha, hb, he⟩

theorem Reach.refl {X : Set V} (a : V) : Reach E X a a :=
  Relation.ReflTransGen.refl

theorem Reach.mem_of_ne {X : Set V} {a b : V} (h : Reach E X a b) (hne : a ≠ b) :
    a ∈ X ∧ b ∈ X := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hr⟩
  · exact absurd rfl hne
  · refine ⟨hc.1, ?_⟩
    clear hne
    induction hr with
    | refl => exact hc.2.1
    | tail _ hs _ => exact hs.2.1

/-- Paths between vertices of an SCC stay inside it. -/
theorem IsSCC.reach_within {X D : Set V} (h : IsSCC E X D) {u v : V} (hu : u ∈ D) (hv : v ∈ D) :
    Reach E D u v := by
  obtain ⟨-, hDX, hconn, hmax⟩ := h
  have key : ∀ a, Reach E X a v → a ∈ D → Reach E D a v := by
    intro a hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Reach.refl _
    | head hac hcv ih =>
      rename_i a c
      intro ha
      have hcD : c ∈ D := by
        refine hmax a ha c hac.2.1 (Reach.single hac.1 hac.2.1 hac.2.2) ?_
        exact hcv.trans (hconn v hv a ha)
      exact (Reach.single ha hcD hac.2.2).trans (ih hcD)
  exact key u (hconn u hu v hv) hu

/-- Every non-empty subset of a finite graph has a final SCC. -/
theorem exists_isFinalSCC (E : V → V → Prop) [Finite V] {X : Set V} (hne : X.Nonempty) :
    ∃ C, IsFinalSCC E X C := by
  classical
  let R : V → Set V := fun v => {w | w ∈ X ∧ Reach E X v w}
  obtain ⟨v, hvX, hmin⟩ := Set.exists_min_image X (fun v => (R v).ncard) (Set.toFinite X) hne
  have hvR : v ∈ R v := ⟨hvX, Reach.refl v⟩
  have hsubR : ∀ a, a ∈ R v → R a ⊆ R v := fun a ha b hb => ⟨hb.1, ha.2.trans hb.2⟩
  have hback : ∀ a ∈ R v, Reach E X a v := by
    intro a ha
    have hle := hmin a ha.1
    have heq : R a = R v := by
      refine Set.eq_of_subset_of_ncard_le (hsubR a ha) hle (Set.toFinite _)
    have : v ∈ R a := heq ▸ hvR
    exact this.2
  let C : Set V := {w | w ∈ X ∧ Reach E X v w ∧ Reach E X w v}
  have hvC : v ∈ C := ⟨hvX, Reach.refl v, Reach.refl v⟩
  refine ⟨C, ⟨⟨⟨v, hvC⟩, fun w hw => hw.1, ?_, ?_⟩, ?_⟩⟩
  · rintro u ⟨-, hu1, hu2⟩ w ⟨-, hw1, hw2⟩
    exact hu2.trans hw1
  · rintro u ⟨-, hu1, hu2⟩ w hwX huw hwu
    exact ⟨hwX, hu1.trans huw, hwu.trans hu2⟩
  · rintro a ⟨haX, ha1, ha2⟩ b hbX he
    have hb : b ∈ R v := ⟨hbX, ha1.trans (Reach.single haX hbX he)⟩
    exact ⟨hbX, hb.2, hback b hb⟩

theorem finalSCCExists (E : V → V → Prop) [Finite V] (X : Set V) : FinalSCCExists E X :=
  fun h => exists_isFinalSCC E h

theorem finalSCC_spec (E : V → V → Prop) [Finite V] {X : Set V} (hne : X.Nonempty) :
    IsFinalSCC E X (finalSCC E X) := by
  classical
  unfold finalSCC
  rw [dite_eq_left (exists_isFinalSCC E hne)]
  exact (exists_isFinalSCC E hne).choose_spec

end MercLib.Graph
