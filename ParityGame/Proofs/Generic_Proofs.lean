module

public import ParityGame.Generic
public import ParityGame.Proofs.Region_Proofs
public import ParityGame.Proofs.Attractor_Proofs
public import ParityGame.Proofs.Zielonka_Proofs
public import ParityGame.Proofs.Scc_Proofs
public import ParityGame.Proofs.Special_Proofs
public import ParityGame.Proofs.Transform_Proofs

open Cslib (ωSequence)

@[expose] public section GenericProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorem below live in `ParityGame/Pins/Generic_Pins.lean`.

The proof maintains the invariant `Strong` (two disjoint closed regions covering the subgame).
Every iteration produces a `Partial` solution of the current subgame - closed regions of both
players, at least one of them non-empty - whose attractors are removed. -/

variable {V : Type*}

/-- Closed regions of both players that are not both empty. -/
structure Game.Partial (G : Game V) (X : Set V) (r : Solution V) : Prop where
  region : ∀ j, G.Region X j (r.win j) (r.strat j)
  nonempty : (r.win .zero ∪ r.win .one).Nonempty

theorem Game.Region.selfCycle (G : Game V) {X : Set V} {v : V} (h : G.IsSelfCycle X v) :
    ∀ j, G.Region X j ((G.selfCycleSolve v).win j) ((G.selfCycleSolve v).strat j) := by
  classical
  intro j
  by_cases hj : j = Player.ofPrio (G.prio v)
  · have hw : (G.selfCycleSolve v).win j = {v} := by simp [Game.selfCycleSolve, hj]
    rw [hw]
    obtain ⟨hvX, hl, hc⟩ := h
    refine ⟨Set.singleton_subset_iff.mpr hvX, ?_, ?_, ?_⟩
    · intro u hu _
      rw [Set.mem_singleton_iff.mp hu]
      exact ⟨rfl, hl⟩
    · intro u hu ho w hw he
      rw [Set.mem_singleton_iff.mp hu] at ho he
      rcases hc with hc | hc
      · exact absurd (hc.trans hj.symm) ho
      · exact hc w hw he
    · intro p hp
      have hpv : ∀ n, p n = v := fun n => (hp n).1
      refine ⟨G.prio v, ⟨?_, ?_⟩, hj.symm⟩
      · show ∃ᶠ n in Filter.atTop, (p.map G.prio) n = G.prio v
        exact Filter.Frequently.of_forall fun n => by simp [ωSequence.map, hpv n]
      · intro m hm
        obtain ⟨n, hn⟩ := (show ∃ᶠ n in Filter.atTop, (p.map G.prio) n = m from hm).exists
        have : G.prio (p n) = m := hn
        rw [hpv] at this
        exact this.symm.le
  · have hw : (G.selfCycleSolve v).win j = ∅ := by simp [Game.selfCycleSolve, hj]
    rw [hw]
    exact Game.Region.empty _ _ _ _

/-- A final SCC of a subgame is itself a subgame. -/
theorem Game.IsFinalSCC.isSubgame {G : Game V} {X C : Set V} (h : G.IsFinalSCC X C)
    (hX : G.IsSubgame X) : G.IsSubgame C := by
  intro v hv
  obtain ⟨w, hw, he⟩ := hX v (h.1.2.1 hv)
  exact ⟨w, h.2 v hv w hw he, he⟩

theorem Game.solveSCC_strong (G : Game V) [Finite V] {S : Backend V} (hS : S.Sound) {C : Set V}
    (hC : G.IsSubgame C) (hconn : ∀ u ∈ C, ∀ v ∈ C, G.Reach C u v) :
    G.Strong C (G.solveSCC S C) := by
  classical
  unfold Game.solveSCC
  by_cases h1 : ∃ i, G.OnePlayer C i
  · rw [dif_pos h1]
    exact G.onePlayerSolve_strong hC hconn h1.choose_spec
  · rw [dif_neg h1]
    by_cases h2 : ∃ i, G.OneParity C i
    · rw [dif_pos h2]
      exact G.oneParitySolve_strong hC h2.choose_spec
    · rw [dif_neg h2]
      have hsol := hS (G.withPrio (compress (G.prio '' C) ∘ G.prio)) C hC
      exact (G.solves_of_withPrio C _ (G.compressionSound C) _ hsol).strong

theorem Game.selfCycleSolve_correct (G : Game V) (X : Set V) (v : V) : G.SelfCycleCorrect X v :=
  fun hX h => ((Game.Region.selfCycle G h) _).winsFrom hX (by simp [Game.selfCycleSolve])

theorem Game.step_partial (G : Game V) [Finite V] {S : Backend V} (hS : S.Sound) {X : Set V}
    (hne : X.Nonempty) (hX : G.IsSubgame X) : G.Partial X (G.step S X) := by
  classical
  unfold Game.step
  by_cases h : ∃ v, G.IsSelfCycle X v
  · rw [dif_pos h]
    refine ⟨Game.Region.selfCycle G h.choose_spec, ⟨h.choose, ?_⟩⟩
    have hv : h.choose ∈ (G.selfCycleSolve h.choose).win (Player.ofPrio (G.prio h.choose)) := by
      simp [Game.selfCycleSolve]
    generalize Player.ofPrio (G.prio h.choose) = j at hv
    cases j
    · exact Or.inl hv
    · exact Or.inr hv
  · rw [dif_neg h]
    have hC := G.finalSCC_spec hne
    have hsub := hC.isSubgame hX
    have hconn : ∀ u ∈ G.finalSCC X, ∀ v ∈ G.finalSCC X, G.Reach (G.finalSCC X) u v :=
      fun u hu v hv => hC.1.reach_within hu hv
    have hstrong := G.solveSCC_strong hS hsub hconn
    refine ⟨fun j => (hstrong.region j).lift hC.1.2.1 hC.2, ?_⟩
    obtain ⟨v, hv⟩ := hC.1.1
    rw [← hstrong.cover] at hv
    exact ⟨v, hv⟩

theorem Game.mem_remainder_iff (G : Game V) (X : Set V) (r : Solution V) (j : Player) (v : V) :
    v ∈ G.remainder X r ↔
      v ∈ X ∧ v ∉ G.attr X j (r.win j) ∧ v ∉ G.attr X j.opp (r.win j.opp) := by
  cases j <;> simp [Game.remainder, Player.opp] <;> tauto

/-- The attractors of the regions of a partial solution leave a subgame. -/
theorem Game.remainder_isSubgame (G : Game V) [Finite V] {X : Set V} {r : Solution V}
    (hX : G.IsSubgame X) (hp : G.Partial X r) : G.IsSubgame (G.remainder X r) := by
  have hA : ∀ j, _ := fun j => G.attractorCorrect X j (r.win j) hX (hp.region j).sub
  intro v hv
  rw [G.mem_remainder_iff X r Player.zero] at hv
  obtain ⟨hvX, hv0, hv1⟩ := hv
  have hA0 := hA Player.zero
  have hA1 := hA Player.one
  obtain ⟨-, hsub0, htrap0, -⟩ := hA0
  obtain ⟨-, hsub1, htrap1, -⟩ := hA1
  rcases Player.eq_or_eq_opp (G.owner v) Player.zero with ho | ho
  · -- `0` owns `v`: all successors in `X` avoid the `0`-attractor
    obtain ⟨w, ⟨hwX, hw1⟩, he⟩ := hsub1 v ⟨hvX, hv1⟩
    refine ⟨w, ?_, he⟩
    rw [G.mem_remainder_iff X r Player.zero]
    exact ⟨hwX, htrap0 v ⟨hvX, hv0⟩ ho w hwX he, hw1⟩
  · obtain ⟨w, ⟨hwX, hw0⟩, he⟩ := hsub0 v ⟨hvX, hv0⟩
    refine ⟨w, ?_, he⟩
    rw [G.mem_remainder_iff X r Player.zero]
    exact ⟨hwX, hw0, htrap1 v ⟨hvX, hv1⟩ ho w hwX he⟩

/-- Adding the attractors back to a solution of the remainder gives closed regions. -/
theorem Game.merge_region (G : Game V) [Finite V] {X : Set V} {r r' : Solution V}
    (hp : G.Partial X r) (hr' : G.Strong (G.remainder X r) r') (j : Player) :
    G.Region X j ((G.merge X r r').win j) ((G.merge X r r').strat j) := by
  classical
  have hRj := hp.region j
  have hr'j := hr'.region j
  have hX' : r.win j ⊆ X := hRj.sub
  have hAX : G.attr X j (r.win j) ⊆ X := G.attr_subset X j (r.win j) hX'
  have hrAj : r.win j ⊆ G.attr X j (r.win j) := G.subset_attr X j (r.win j)
  have hr'X : r'.win j ⊆ X := fun v hv =>
    ((G.mem_remainder_iff X r j v).mp (hr'j.sub hv)).1
  have hwin : (G.merge X r r').win j = G.attr X j (r.win j) ∪ r'.win j := rfl
  have hstrat : ∀ v, (G.merge X r r').strat j v =
      if v ∈ r.win j then r.strat j v
      else if v ∈ G.attr X j (r.win j) then G.attrStrategy X j (r.win j) v
      else r'.strat j v := fun v => rfl
  have hunionX : G.attr X j (r.win j) ∪ r'.win j ⊆ X := Set.union_subset hAX hr'X
  rw [hwin]
  refine ⟨hunionX, ?_, ?_, ?_⟩
  · intro v hv ho
    rw [hstrat]
    by_cases h1 : v ∈ r.win j
    · rw [if_pos h1]
      have := hRj.mine v h1 ho
      exact ⟨Or.inl (hrAj this.1), this.2⟩
    · rw [if_neg h1]
      by_cases h2 : v ∈ G.attr X j (r.win j)
      · rw [if_pos h2]
        have := G.attrStrategy_mem X j (r.win j) h2 h1 ho
        exact ⟨Or.inl this.1, this.2⟩
      · rw [if_neg h2]
        have hv' : v ∈ r'.win j := hv.resolve_left h2
        have := hr'j.mine v hv' ho
        exact ⟨Or.inr this.1, this.2⟩
  · intro v hv ho w hw he
    rcases hv with hv | hv
    · by_cases h1 : v ∈ r.win j
      · exact Or.inl (hrAj (hRj.theirs v h1 ho w hw he))
      · exact Or.inl (G.attr_opp_closed X j (r.win j) hv h1 ho w hw he)
    · by_cases hwA : w ∈ G.attr X j (r.win j)
      · exact Or.inl hwA
      · right
        have hvo : G.owner v = j.opp := Player.ne_iff.mp ho
        have hvY := (G.mem_remainder_iff X r j v).mp (hr'j.sub hv)
        have hwA' : w ∉ G.attr X j.opp (r.win j.opp) := fun hw' =>
          hvY.2.2 (G.mem_attr_of_owner X j.opp (r.win j.opp) hvY.1 hvo he hw')
        exact hr'j.theirs v hv ho w ((G.mem_remainder_iff X r j w).mpr ⟨hw, hwA, hwA'⟩) he
  · intro p hp'
    by_cases hex : ∃ n, p n ∈ G.attr X j (r.win j)
    · obtain ⟨n₀, k, hk⟩ := hex
      have hconf : G.ConformingPlay X j ((G.merge X r r').strat j) p := fun n =>
        ⟨hunionX (hp' n).1, hunionX (hp' (n + 1)).1, (hp' n).2.1, (hp' n).2.2⟩
      have hσ : ∀ v ∈ G.attr X j (r.win j), v ∉ r.win j → G.owner v = j →
          (G.merge X r r').strat j v = G.attrStrategy X j (r.win j) v := by
        intro v hv h1 _
        rw [hstrat, if_neg h1, if_pos hv]
      obtain ⟨m, -, hm⟩ := G.reach_of_mem_stage X j (r.win j) _ hσ p hconf k n₀ hk
      have hstay : ∀ t, p (m + t) ∈ r.win j := by
        intro t
        induction t with
        | zero => exact hm
        | succ t ih' =>
          obtain ⟨-, h2, h3⟩ := hp' (m + t)
          by_cases ho : G.owner (p (m + t)) = j
          · rw [show m + (t + 1) = m + t + 1 from rfl, h3 ho, hstrat, if_pos ih']
            exact (hRj.mine _ ih' ho).1
          · exact hRj.theirs _ ih' ho _ (hunionX (hp' (m + t + 1)).1) h2
      rw [← G.playWonBy_drop j p m]
      refine hRj.won _ fun t => ?_
      simp only [ωSequence.get_drop]
      refine ⟨hstay t, (hp' _).2.1, fun ho => ?_⟩
      have := (hp' (m + t)).2.2 ho
      rw [hstrat, if_pos (hstay t)] at this
      exact this
    · push Not at hex
      refine hr'j.won p fun n => ?_
      obtain ⟨h1, h2, h3⟩ := hp' n
      have hv' : p n ∈ r'.win j := h1.resolve_left (hex n)
      refine ⟨hv', h2, fun ho => ?_⟩
      rw [h3 ho, hstrat, if_neg fun h => hex n (hrAj h), if_neg (hex n)]

theorem Game.merge_strong (G : Game V) [Finite V] {X : Set V} {r r' : Solution V}
    (hp : G.Partial X r) (hr' : G.Strong (G.remainder X r) r') : G.Strong X (G.merge X r r') := by
  have hR := G.merge_region hp hr'
  have hwin : ∀ j, (G.merge X r r').win j = G.attr X j (r.win j) ∪ r'.win j := fun j => rfl
  have hcov : (G.merge X r r').win Player.zero ∪ (G.merge X r r').win Player.one = X := by
    refine Set.Subset.antisymm (Set.union_subset (hR Player.zero).sub (hR Player.one).sub) ?_
    intro v hv
    by_cases h0 : v ∈ G.attr X Player.zero (r.win Player.zero)
    · exact Or.inl (Or.inl h0)
    · by_cases h1 : v ∈ G.attr X Player.one (r.win Player.one)
      · exact Or.inr (Or.inl h1)
      · have hY : v ∈ G.remainder X r := (G.mem_remainder_iff X r Player.zero v).mpr ⟨hv, h0, h1⟩
        rw [← hr'.cover] at hY
        rcases hY with hY | hY
        · exact Or.inl (Or.inr hY)
        · exact Or.inr (Or.inr hY)
  exact Game.Strong.of_opp Player.zero hcov
    (Game.Region.disjoint (hR Player.zero) (hR Player.one)) (hR Player.zero) (hR Player.one)

/-- The invariant of the generic solver holds on every subgame. -/
theorem Game.genericAux_strong (G : Game V) [Finite V] {S : Backend V} (hS : S.Sound) :
    ∀ (n : ℕ) (X : Set V), X.ncard = n → G.IsSubgame X → G.Strong X (G.genericAux S X) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hX
  rw [Game.genericAux]
  by_cases hne : X.Nonempty
  · rw [dif_pos hne]
    have hp := G.step_partial hS hne hX
    dsimp only
    set r := G.step S X with hr
    have hss : G.remainder X r ⊂ X := by
      refine ⟨fun v hv => ((G.mem_remainder_iff X r Player.zero v).mp hv).1, fun hsub => ?_⟩
      obtain ⟨v, hv⟩ := hp.nonempty
      have hvX : v ∈ X := by
        rcases hv with hv | hv
        · exact (hp.region Player.zero).sub hv
        · exact (hp.region Player.one).sub hv
      have := (G.mem_remainder_iff X r Player.zero v).mp (hsub hvX)
      rcases hv with hv | hv
      · exact this.2.1 (G.subset_attr X Player.zero _ hv)
      · exact this.2.2 (G.subset_attr X Player.one _ hv)
    rw [dif_pos hss]
    have hlt : (G.remainder X r).ncard < n := by
      rw [← hn]; exact Set.ncard_lt_ncard hss (Set.toFinite X)
    exact G.merge_strong hp (ih _ hlt _ rfl (G.remainder_isSubgame hX hp))
  · rw [dif_neg hne]
    have hX0 : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hX0
    refine Game.Strong.of_opp .zero (by simp [Solution.empty]) (by simp [Solution.empty]) ?_ ?_
    · exact Game.Region.empty _ _ _ _
    · exact Game.Region.empty _ _ _ _

/-- The generic solver with a sound backend is correct. -/
theorem Game.genericSolve_correct (G : Game V) [Finite V] (S : Backend V) : G.GenericCorrect S := by
  intro hS
  refine (G.genericAux_strong hS _ Set.univ rfl ?_).solves ?_ <;>
    exact fun v _ => by obtain ⟨w, hw⟩ := G.total v; exact ⟨w, Set.mem_univ _, hw⟩

theorem zielonkaBackend_sound [Finite V] : (zielonkaBackend : Backend V).Sound := by
  intro G X hX
  exact (G.zielonkaAux_strong _ X rfl hX).solves hX

/-- The generic solver with Zielonka's algorithm as backend solves every finite parity game. -/
theorem Game.genericSolve_zielonka_correct (G : Game V) [Finite V] :
    G.Solves Set.univ (G.genericSolve zielonkaBackend) :=
  G.genericSolve_correct zielonkaBackend zielonkaBackend_sound

end ParityGame

end GenericProofs
