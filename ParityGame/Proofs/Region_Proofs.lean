module

public import ParityGame.Defs
public import ParityGame.Proofs.Defs_Proofs
public import Cslib.Foundations.Data.OmegaSequence.Init

open Cslib (ωSequence)

@[expose] public section RegionProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

Infrastructure shared by the correctness proofs of Zielonka's algorithm and of the generic solver:
closed *regions* (`Region`), partitions into two regions (`Strong`), and the equivalence of
`Strong` with the semantic `Solves` for finite games. -/

variable {V : Type*}

theorem Player.opp_ne (i : Player) : i.opp ≠ i := by cases i <;> simp [Player.opp]

theorem Player.eq_or_eq_opp (o i : Player) : o = i ∨ o = i.opp := by
  cases o <;> cases i <;> simp [Player.opp]

theorem Player.ne_iff {o i : Player} : o ≠ i ↔ o = i.opp := by
  cases o <;> cases i <;> simp [Player.opp]

theorem Player.opp_opp (i : Player) : i.opp.opp = i := by cases i <;> rfl

/-- `W` is a region of player `j` in `X` with strategy `σ`: `j` stays in `W` using `σ`, the
    opponent cannot leave `W` (inside `X`), and every play confined to `W` that conforms to `σ`
    is won by `j`. -/
structure Game.Region (G : Game V) (X : Set V) (j : Player) (W : Set V) (σ : Strategy V) :
    Prop where
  sub : W ⊆ X
  mine : ∀ v ∈ W, G.owner v = j → σ v ∈ W ∧ G.edge v (σ v)
  theirs : ∀ v ∈ W, G.owner v ≠ j → ∀ w ∈ X, G.edge v w → w ∈ W
  won : ∀ p : ωSequence V,
    (∀ n, p n ∈ W ∧ G.edge (p n) (p (n + 1)) ∧ (G.owner (p n) = j → p (n + 1) = σ (p n))) →
    G.PlayWonBy j p

/-- The invariant of the recursion: a partition of `X` into two regions. -/
structure Game.Strong (G : Game V) (X : Set V) (r : Solution V) : Prop where
  cover : r.win .zero ∪ r.win .one = X
  disj : Disjoint (r.win .zero) (r.win .one)
  region : ∀ j, G.Region X j (r.win j) (r.strat j)

theorem Game.Region.empty (G : Game V) (X : Set V) (j : Player) (σ : Strategy V) :
    G.Region X j ∅ σ :=
  ⟨Set.empty_subset _, by simp, by simp, fun p hp => absurd (hp 0).1 (Set.notMem_empty _)⟩

theorem Game.Strong.cover' {G : Game V} {X : Set V} {r : Solution V} (h : G.Strong X r)
    (i : Player) : r.win i ∪ r.win i.opp = X := by
  cases i
  · exact h.cover
  · simpa [Player.opp, Set.union_comm] using h.cover

theorem Game.Strong.disj' {G : Game V} {X : Set V} {r : Solution V} (h : G.Strong X r)
    (i : Player) : Disjoint (r.win i) (r.win i.opp) := by
  cases i
  · exact h.disj
  · simpa [Player.opp] using h.disj.symm

theorem Game.Strong.of_opp {G : Game V} {X : Set V} {r : Solution V} (i : Player)
    (hcov : r.win i ∪ r.win i.opp = X) (hdisj : Disjoint (r.win i) (r.win i.opp))
    (hi : G.Region X i (r.win i) (r.strat i))
    (hj : G.Region X i.opp (r.win i.opp) (r.strat i.opp)) : G.Strong X r := by
  refine ⟨?_, ?_, fun j => ?_⟩
  · cases i
    · exact hcov
    · simpa [Player.opp, Set.union_comm] using hcov
  · cases i
    · exact hdisj
    · simpa [Player.opp] using hdisj.symm
  · rcases Player.eq_or_eq_opp j i with rfl | rfl
    · exact hi
    · exact hj

/-- A node of a region is won by its player's strategy. -/
theorem Game.Region.winsFrom {G : Game V} {X : Set V} {j : Player} {W : Set V} {σ : Strategy V}
    (hreg : G.Region X j W σ) (hX : G.IsSubgame X) {v : V} (hv : v ∈ W) :
    G.WinsFrom X j σ v := by
  have hstep : ∀ a b, a ∈ W → G.Step X j σ a b → b ∈ W := by
    rintro a b ha ⟨-, hbX, he, hs⟩
    by_cases ho : G.owner a = j
    · rw [hs ho]; exact (hreg.mine a ha ho).1
    · exact hreg.theirs a ha ho b hbX he
  refine ⟨fun w hw => ?_, fun p hp0 hp => ?_⟩
  · have hwW : w ∈ W := by
      induction hw with
      | refl => exact hv
      | tail _ hs ih => exact hstep _ _ ih hs
    have hwX := hreg.sub hwW
    by_cases ho : G.owner w = j
    · exact ⟨_, hwX, (hreg.mine w hwW ho).1 |> hreg.sub, (hreg.mine w hwW ho).2, fun _ => rfl⟩
    · obtain ⟨u, hu, he⟩ := hX w hwX
      exact ⟨u, hwX, hu, he, fun h => absurd h ho⟩
  · have hall : ∀ n, p n ∈ W := by
      intro n
      induction n with
      | zero => rw [hp0]; exact hv
      | succ n ih => exact hstep _ _ ih (hp n)
    exact hreg.won p fun n => ⟨hall n, (hp n).2.2.1, (hp n).2.2.2⟩

/-- A strong solution of a subgame is a solution in the sense of `Game.Solves`. -/
theorem Game.Strong.solves {G : Game V} {X : Set V} {r : Solution V} (h : G.Strong X r)
    (hX : G.IsSubgame X) : G.Solves X r := by
  refine ⟨h.cover, h.disj, fun i v hv => ?_⟩
  have hreg := h.region i
  have hstep : ∀ a b, a ∈ r.win i → G.Step X i (r.strat i) a b → b ∈ r.win i := by
    rintro a b ha ⟨-, hbX, he, hs⟩
    by_cases ho : G.owner a = i
    · rw [hs ho]; exact (hreg.mine a ha ho).1
    · exact hreg.theirs a ha ho b hbX he
  refine ⟨fun w hw => ?_, fun p hp0 hp => ?_⟩
  · have hwW : w ∈ r.win i := by
      induction hw with
      | refl => exact hv
      | tail _ hs ih => exact hstep _ _ ih hs
    have hwX := hreg.sub hwW
    by_cases ho : G.owner w = i
    · exact ⟨_, hwX, (hreg.mine w hwW ho).1 |> hreg.sub, (hreg.mine w hwW ho).2, fun _ => rfl⟩
    · obtain ⟨u, hu, he⟩ := hX w hwX
      exact ⟨u, hwX, hu, he, fun h => absurd h ho⟩
  · have hall : ∀ n, p n ∈ r.win i := by
      intro n
      induction n with
      | zero => rw [hp0]; exact hv
      | succ n ih => exact hstep _ _ ih (hp n)
    exact hreg.won p fun n => ⟨hall n, (hp n).2.2.1, (hp n).2.2.2⟩


open Classical in
/-- The move following `σ` at nodes of `i` and `τ` elsewhere. -/
noncomputable def Game.joint (G : Game V) (i : Player) (σ τ : Strategy V) (u : V) : V :=
  if G.owner u = i then σ u else τ u

/-- Winning strategies of both players cannot coexist after a conforming move. -/
theorem Game.no_both (G : Game V) [Finite V] {X : Set V} {i : Player} {σ τ : Strategy V}
    {v w : V} (hv : G.WinsFrom X i σ v) (hw : G.WinsFrom X i.opp τ w) (hs : G.Step X i σ v w) :
    False := by
  classical
  let nxt := G.joint i σ τ
  let r : ωSequence V := ωSequence.iterate nxt w
  have hrs : ∀ n, r (n + 1) = nxt (r n) := fun n => by
    show nxt^[n + 1] w = nxt (nxt^[n] w)
    rw [Function.iterate_succ_apply']
  have hboth : ∀ n, Relation.ReflTransGen (G.Step X i σ) v (r n) →
      Relation.ReflTransGen (G.Step X i.opp τ) w (r n) →
      G.Step X i σ (r n) (r (n + 1)) ∧ G.Step X i.opp τ (r n) (r (n + 1)) := by
    intro n h1 h2
    obtain ⟨a, ha⟩ := hv.1 _ h1
    obtain ⟨b, hb⟩ := hw.1 _ h2
    rw [hrs]
    by_cases ho : G.owner (r n) = i
    · have e : nxt (r n) = σ (r n) := by simp [nxt, Game.joint, ho]
      rw [e]
      have ha' : a = σ (r n) := ha.2.2.2 ho
      subst ha'
      exact ⟨ha, ha.1, ha.2.1, ha.2.2.1, fun h =>
        absurd (ho.symm.trans h).symm (Player.opp_ne i)⟩
    · have ho' : G.owner (r n) = i.opp := Player.ne_iff.mp ho
      have e : nxt (r n) = τ (r n) := by simp [nxt, Game.joint, ho]
      rw [e]
      have hb' : b = τ (r n) := hb.2.2.2 ho'
      subst hb'
      exact ⟨⟨hb.1, hb.2.1, hb.2.2.1, fun h => absurd h ho⟩, hb⟩
  have hA : ∀ n, Relation.ReflTransGen (G.Step X i σ) v (r n) ∧
      Relation.ReflTransGen (G.Step X i.opp τ) w (r n) := by
    intro n
    induction n with
    | zero => exact ⟨Relation.ReflTransGen.single hs, Relation.ReflTransGen.refl⟩
    | succ n ih =>
      obtain ⟨s1, s2⟩ := hboth n ih.1 ih.2
      exact ⟨ih.1.tail s1, ih.2.tail s2⟩
  have hconf1 : G.ConformingPlay X i σ (ωSequence.cons v r) := by
    intro n
    cases n with
    | zero => exact hs
    | succ n => simpa using (hboth n (hA n).1 (hA n).2).1
  have hconf2 : G.ConformingPlay X i.opp τ r := fun n => (hboth n (hA n).1 (hA n).2).2
  have w1 := hv.2 _ (by simp) hconf1
  have w2 := hw.2 r rfl hconf2
  have w2' : G.PlayWonBy i.opp (ωSequence.cons v r) := by
    rw [← G.playWonBy_drop _ _ 1, ← ωSequence.tail_eq_drop, ωSequence.tail_cons]
    exact w2
  obtain ⟨j, -, hj⟩ := G.playHasUniqueWinner (ωSequence.cons v r)
  exact Player.opp_ne i ((hj _ w2').trans (hj _ w1).symm)

/-- A strong solution is a solution (given a finite game) and conversely. -/
theorem Game.Solves.strong {G : Game V} [Finite V] {X : Set V} {r : Solution V}
    (h : G.Solves X r) : G.Strong X r := by
  obtain ⟨hcov, hdisj, hwin⟩ := h
  have hsub : ∀ j, r.win j ⊆ X := fun j => by
    rw [← hcov]; cases j
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have hcov' : ∀ j, r.win j ∪ r.win j.opp = X := fun j => by
    cases j
    · exact hcov
    · simpa [Player.opp, Set.union_comm] using hcov
  have hnot : ∀ j, ∀ v ∈ r.win j, ∀ w ∈ X, G.Step X j (r.strat j) v w → w ∈ r.win j := by
    intro j v hv w hwX hs
    by_contra hw
    have hw' : w ∈ r.win j.opp := by
      have : w ∈ r.win j ∪ r.win j.opp := by rw [hcov']; exact hwX
      exact this.resolve_left hw
    exact G.no_both (hwin j v hv) (hwin j.opp w hw') hs
  refine ⟨hcov, hdisj, fun j => ⟨hsub j, ?_, ?_, ?_⟩⟩
  · intro v hv ho
    obtain ⟨u, hu⟩ := (hwin j v hv).1 v Relation.ReflTransGen.refl
    have hu' : u = r.strat j v := hu.2.2.2 ho
    subst hu'
    exact ⟨hnot j v hv _ hu.2.1 hu, hu.2.2.1⟩
  · intro v hv ho w hw he
    exact hnot j v hv w hw ⟨hsub j hv, hw, he, fun h => absurd h ho⟩
  · intro p hp
    exact (hwin j (p 0) (hp 0).1).2 p rfl fun n =>
      ⟨hsub j (hp n).1, hsub j (hp (n + 1)).1, (hp n).2.1, (hp n).2.2⟩

/-- Regions of the two players are disjoint. -/
theorem Game.Region.disjoint {G : Game V} [Finite V] {X : Set V} {i : Player} {W W' : Set V}
    {σ τ : Strategy V} (h : G.Region X i W σ) (h' : G.Region X i.opp W' τ) : Disjoint W W' := by
  classical
  refine Set.disjoint_left.mpr fun v hv hv' => ?_
  let nxt := G.joint i σ τ
  let q : ωSequence V := ωSequence.iterate nxt v
  have hqs : ∀ n, q (n + 1) = nxt (q n) := fun n => by
    show nxt^[n + 1] v = nxt (nxt^[n] v)
    rw [Function.iterate_succ_apply']
  have hmem : ∀ n, q n ∈ W ∧ q n ∈ W' := by
    intro n
    induction n with
    | zero => exact ⟨hv, hv'⟩
    | succ n ih =>
      obtain ⟨a, b⟩ := ih
      rw [hqs]
      by_cases ho : G.owner (q n) = i
      · have e : nxt (q n) = σ (q n) := by simp [nxt, Game.joint, ho]
        rw [e]
        obtain ⟨m1, m2⟩ := h.mine _ a ho
        exact ⟨m1, h'.theirs _ b (fun h => absurd (ho.symm.trans h).symm (Player.opp_ne i)) _
          (h.sub m1) m2⟩
      · have ho' : G.owner (q n) = i.opp := Player.ne_iff.mp ho
        have e : nxt (q n) = τ (q n) := by simp [nxt, Game.joint, ho]
        rw [e]
        obtain ⟨m1, m2⟩ := h'.mine _ b ho'
        exact ⟨h.theirs _ a ho _ (h'.sub m1) m2, m1⟩
  have hstep : ∀ n, G.edge (q n) (q (n + 1)) ∧
      (G.owner (q n) = i → q (n + 1) = σ (q n)) ∧
      (G.owner (q n) = i.opp → q (n + 1) = τ (q n)) := by
    intro n
    by_cases ho : G.owner (q n) = i
    · have e : q (n + 1) = σ (q n) := by rw [hqs]; simp [nxt, Game.joint, ho]
      refine ⟨?_, fun _ => e, fun h => absurd (ho.symm.trans h).symm (Player.opp_ne i)⟩
      rw [e]; exact (h.mine _ (hmem n).1 ho).2
    · have ho' : G.owner (q n) = i.opp := Player.ne_iff.mp ho
      have e : q (n + 1) = τ (q n) := by rw [hqs]; simp [nxt, Game.joint, ho]
      refine ⟨?_, fun h => absurd h ho, fun _ => e⟩
      rw [e]; exact (h'.mine _ (hmem n).2 ho').2
  have w1 := h.won q fun n => ⟨(hmem n).1, (hstep n).1, (hstep n).2.1⟩
  have w2 := h'.won q fun n => ⟨(hmem n).2, (hstep n).1, (hstep n).2.2⟩
  obtain ⟨j, -, hj⟩ := G.playHasUniqueWinner q
  exact Player.opp_ne i ((hj _ w2).trans (hj _ w1).symm)

/-- A region of a closed subset `C` of `X` is a region of `X`. -/
theorem Game.Region.lift {G : Game V} {X C : Set V} {j : Player} {W : Set V} {σ : Strategy V}
    (h : G.Region C j W σ) (hCX : C ⊆ X) (hC : ∀ v ∈ C, ∀ w ∈ X, G.edge v w → w ∈ C) :
    G.Region X j W σ :=
  ⟨fun _ hv => hCX (h.sub hv), h.mine, fun v hv ho w hw he => h.theirs v hv ho w (hC v (h.sub hv) w hw he) he,
    h.won⟩

end ParityGame

end RegionProofs
