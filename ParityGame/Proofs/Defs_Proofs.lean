module

public import ParityGame.Defs
public import Cslib.Foundations.Data.OmegaSequence.Init

open Cslib (ωSequence)

@[expose] public section DefsProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/`. -/

variable {V : Type*}

theorem infOcc_drop (s : ωSequence ℕ) (N : ℕ) : (s.drop N).infOcc = s.infOcc := by
  ext x
  simp only [ωSequence.infOcc, Set.mem_setOf_eq, ωSequence.get_drop, Filter.frequently_atTop]
  constructor
  · intro h a
    obtain ⟨b, hb, e⟩ := h a
    exact ⟨N + b, by omega, e⟩
  · intro h a
    obtain ⟨b, hb, e⟩ := h (a + N)
    exact ⟨b - N, by omega, by rwa [show N + (b - N) = b by omega]⟩

theorem Game.playWonBy_drop (G : Game V) (i : Player) (p : ωSequence V) (N : ℕ) :
    G.PlayWonBy i (p.drop N) ↔ G.PlayWonBy i p := by
  simp only [Game.PlayWonBy, Game.MaxInfPrio, ← ωSequence.drop_map, infOcc_drop]

theorem Game.maxInfPrio_unique (G : Game V) {p : ωSequence V} {n m : ℕ}
    (hn : G.MaxInfPrio p n) (hm : G.MaxInfPrio p m) : n = m :=
  le_antisymm (hm.2 _ hn.1) (hn.2 _ hm.1)

theorem Game.exists_maxInfPrio (G : Game V) [Finite V] (p : ωSequence V) :
    ∃ n, G.MaxInfPrio p n := by
  obtain ⟨x, -, hx⟩ := (ωSequence.frequently_in_finite_type (s := Set.univ) (xs := p)).mp
    (Filter.Frequently.of_forall fun _ => Set.mem_univ _)
  have hne : (p.map G.prio).infOcc.Nonempty :=
    ⟨G.prio x, hx.mono fun k hk => by simp [ωSequence.map, hk]⟩
  have hfin : (p.map G.prio).infOcc.Finite := by
    refine (Set.finite_range G.prio).subset ?_
    rintro m (hm : ∃ᶠ k in Filter.atTop, G.prio (p k) = m)
    obtain ⟨k, hk⟩ := hm.exists
    exact ⟨p k, hk⟩
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image _ id hfin hne
  exact ⟨n, hn, fun m hm => hmax m hm⟩

theorem Game.playHasUniqueWinner (G : Game V) [Finite V] : G.PlayHasUniqueWinner := by
  intro p
  obtain ⟨n, hn⟩ := G.exists_maxInfPrio p
  refine ⟨Player.ofPrio n, ⟨n, hn, rfl⟩, ?_⟩
  rintro i ⟨m, hm, rfl⟩
  rw [G.maxInfPrio_unique hm hn]

/-- The nodes occurring infinitely often along a play. -/
def nodeInf (p : ωSequence V) : Set V := {v | ∃ᶠ k in Filter.atTop, p k = v}

theorem mem_infOcc_map_iff [Finite V] (f : V → ℕ) (p : ωSequence V) (m : ℕ) :
    m ∈ (p.map f).infOcc ↔ ∃ v ∈ nodeInf p, f v = m := by
  constructor
  · intro h
    have h' : ∃ᶠ k in Filter.atTop, p k ∈ {v | f v = m} := h
    obtain ⟨x, hx, hxf⟩ := (ωSequence.frequently_in_finite_type (s := {v | f v = m}) (xs := p)).mp h'
    exact ⟨x, hxf, hx⟩
  · rintro ⟨v, hv, rfl⟩
    exact hv.mono fun k hk => by simp [ωSequence.map, hk]

/-- The greatest recurring priority, in terms of the recurring nodes. -/
theorem Game.maxInfPrio_iff [Finite V] (G : Game V) (p : ωSequence V) (M : ℕ) :
    G.MaxInfPrio p M ↔ (∃ v ∈ nodeInf p, G.prio v = M) ∧ ∀ v ∈ nodeInf p, G.prio v ≤ M := by
  unfold Game.MaxInfPrio
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_infOcc_map_iff _ _ _).mp h1, fun v hv => h2 _ ?_⟩
    exact (mem_infOcc_map_iff _ _ _).mpr ⟨v, hv, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_infOcc_map_iff _ _ _).mpr h1, fun m hm => ?_⟩
    obtain ⟨v, hv, rfl⟩ := (mem_infOcc_map_iff _ _ _).mp hm
    exact h2 v hv

theorem Game.playWonBy_iff_of_maxInfPrio {G G' : Game V} {p : ωSequence V} {M M' : ℕ}
    (h : G.MaxInfPrio p M) (h' : G'.MaxInfPrio p M') (hp : Player.ofPrio M = Player.ofPrio M')
    (i : Player) : G'.PlayWonBy i p ↔ G.PlayWonBy i p := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨M, h, ?_⟩
    rw [hp, G'.maxInfPrio_unique hn h']
  · rintro ⟨n, hn, rfl⟩
    refine ⟨M', h', ?_⟩
    rw [← hp, G.maxInfPrio_unique hn h]

theorem exists_frequently_of_frequently {α : Type*} [Finite α] (P : ℕ → Prop) (f : ℕ → α)
    (h : ∃ᶠ k in Filter.atTop, P k) : ∃ a, ∃ᶠ k in Filter.atTop, P k ∧ f k = a := by
  by_contra hcon
  push Not at hcon
  have : ∀ᶠ k in Filter.atTop, ∀ a, ¬ (P k ∧ f k = a) := Filter.eventually_all.mpr fun a => (hcon a).mono fun k hk h => hk h.1 h.2
  exact h (this.mono fun k hk hP => hk (f k) ⟨hP, rfl⟩)

/-- A recurring node of a play has a recurring successor along the play. -/
theorem exists_succ_nodeInf [Finite V] (G : Game V) {p : ωSequence V}
    (hp : ∀ n, G.edge (p n) (p (n + 1))) {v : V} (hv : v ∈ nodeInf p) :
    ∃ u ∈ nodeInf p, G.edge v u := by
  obtain ⟨u, hu⟩ := exists_frequently_of_frequently (fun k => p k = v) (fun k => p (k + 1)) hv
  obtain ⟨k, hk1, hk2⟩ := hu.exists
  refine ⟨u, ?_, hk1 ▸ hk2 ▸ hp k⟩
  rw [nodeInf, Set.mem_setOf_eq, Filter.frequently_atTop] at *
  intro a
  obtain ⟨b, hb, h1, h2⟩ := hu a
  exact ⟨b + 1, by omega, h2⟩

/-- A recurring node of a play has a recurring predecessor along the play. -/
theorem exists_pred_nodeInf [Finite V] (G : Game V) {p : ωSequence V}
    (hp : ∀ n, G.edge (p n) (p (n + 1))) {v : V} (hv : v ∈ nodeInf p) :
    ∃ u ∈ nodeInf p, G.edge u v := by
  have hv' : ∃ᶠ k in Filter.atTop, p (k + 1) = v := by
    rw [nodeInf, Set.mem_setOf_eq, Filter.frequently_atTop] at hv
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨b, hb, h⟩ := hv (a + 1)
    exact ⟨b - 1, by omega, by rwa [show b - 1 + 1 = b by omega]⟩
  obtain ⟨u, hu⟩ := exists_frequently_of_frequently (fun k => p (k + 1) = v) (fun k => p k) hv'
  obtain ⟨k, hk1, hk2⟩ := hu.exists
  refine ⟨u, ?_, hk1 ▸ hk2 ▸ hp k⟩
  rw [nodeInf, Set.mem_setOf_eq, Filter.frequently_atTop] at *
  intro a
  obtain ⟨b, hb, h1, h2⟩ := hu a
  exact ⟨b, hb, h2⟩

end ParityGame

end DefsProofs
