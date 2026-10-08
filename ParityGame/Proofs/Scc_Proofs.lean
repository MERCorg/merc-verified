module

public import ParityGame.Scc
public import Mathlib.Data.Set.Card

@[expose] public section SccProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). -/

variable {V : Type*}

theorem Game.Reach.trans {G : Game V} {X : Set V} {a b c : V} (h1 : G.Reach X a b)
    (h2 : G.Reach X b c) : G.Reach X a c :=
  Relation.ReflTransGen.trans h1 h2

theorem Game.Reach.single {G : Game V} {X : Set V} {a b : V} (ha : a ∈ X) (hb : b ∈ X)
    (he : G.edge a b) : G.Reach X a b :=
  Relation.ReflTransGen.single ⟨ha, hb, he⟩

theorem Game.Reach.refl {G : Game V} {X : Set V} (a : V) : G.Reach X a a :=
  Relation.ReflTransGen.refl

theorem Game.Reach.mem_of_ne {G : Game V} {X : Set V} {a b : V} (h : G.Reach X a b) (hne : a ≠ b) :
    a ∈ X ∧ b ∈ X := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hr⟩
  · exact absurd rfl hne
  · refine ⟨hc.1, ?_⟩
    clear hne
    induction hr with
    | refl => exact hc.2.1
    | tail _ hs _ => exact hs.2.1

/-- Every non-empty subgame of a finite game has a final SCC. -/
theorem Game.exists_isFinalSCC (G : Game V) [Finite V] {X : Set V} (hne : X.Nonempty) :
    ∃ C, G.IsFinalSCC X C := by
  classical
  let R : V → Set V := fun v => {w | w ∈ X ∧ G.Reach X v w}
  obtain ⟨v, hvX, hmin⟩ := Set.exists_min_image X (fun v => (R v).ncard) (Set.toFinite X) hne
  have hvR : v ∈ R v := ⟨hvX, Game.Reach.refl v⟩
  have hsubR : ∀ a, a ∈ R v → R a ⊆ R v := fun a ha b hb => ⟨hb.1, ha.2.trans hb.2⟩
  have hback : ∀ a ∈ R v, G.Reach X a v := by
    intro a ha
    have hle := hmin a ha.1
    have heq : R a = R v := by
      refine Set.eq_of_subset_of_ncard_le (hsubR a ha) hle (Set.toFinite _)
    have : v ∈ R a := heq ▸ hvR
    exact this.2
  let C : Set V := {w | w ∈ X ∧ G.Reach X v w ∧ G.Reach X w v}
  have hvC : v ∈ C := ⟨hvX, Game.Reach.refl v, Game.Reach.refl v⟩
  refine ⟨C, ⟨⟨⟨v, hvC⟩, fun w hw => hw.1, ?_, ?_⟩, ?_⟩⟩
  · rintro u ⟨-, hu1, hu2⟩ w ⟨-, hw1, hw2⟩
    exact hu2.trans hw1
  · rintro u ⟨-, hu1, hu2⟩ w hwX huw hwu
    exact ⟨hwX, hu1.trans huw, hwu.trans hu2⟩
  · rintro a ⟨haX, ha1, ha2⟩ b hbX he
    have hb : b ∈ R v := ⟨hbX, ha1.trans (Game.Reach.single haX hbX he)⟩
    exact ⟨hbX, hb.2, hback b hb⟩

theorem Game.finalSCCExists (G : Game V) [Finite V] (X : Set V) : G.FinalSCCExists X :=
  fun h => G.exists_isFinalSCC h

theorem Game.finalSCC_spec (G : Game V) [Finite V] {X : Set V} (hne : X.Nonempty) :
    G.IsFinalSCC X (G.finalSCC X) := by
  classical
  unfold Game.finalSCC
  rw [dif_pos (G.exists_isFinalSCC hne)]
  exact (G.exists_isFinalSCC hne).choose_spec

end ParityGame

end SccProofs
