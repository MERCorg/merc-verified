module

public import ParityGame.Zielonka
public import ParityGame.Proofs.Defs_Proofs
public import ParityGame.Proofs.Attractor_Proofs
public import ParityGame.Proofs.Region_Proofs

open Cslib (ωSequence)

@[expose] public section ZielonkaProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorem below live in `ParityGame/Pins/Zielonka_Pins.lean`.

The correctness proof is by strong induction on `|X|` with a strengthened invariant (`Strong`):
besides winning, each region `W` of player `j` is *closed* (`j` can stay inside `W` by following
its strategy and the opponent cannot leave it) and plays confined to `W` are won by `j`. -/

variable {V : Type*}

theorem Game.anyMove_spec (G : Game V) {X : Set V} (hX : G.IsSubgame X) {v : V} (hv : v ∈ X) :
    G.anyMove X v ∈ X ∧ G.edge v (G.anyMove X v) := by
  classical
  have h := hX v hv
  unfold Game.anyMove
  rw [dif_pos h]
  exact h.choose_spec

theorem Game.frequently_mem_of_frequently_attr (G : Game V) (X : Set V) (i : Player) (U : Set V)
    (σ : Strategy V)
    (hσ : ∀ v ∈ G.attr X i U, v ∉ U → G.owner v = i → σ v = G.attrStrategy X i U v)
    (p : ωSequence V) (hp : G.ConformingPlay X i σ p)
    (hA : ∃ᶠ n in Filter.atTop, p n ∈ G.attr X i U) : ∃ᶠ n in Filter.atTop, p n ∈ U := by
  rw [Filter.frequently_atTop] at *
  intro a
  obtain ⟨b, hb, k, hk⟩ := hA a
  obtain ⟨n, hn, hnU⟩ := G.reach_of_mem_stage X i U σ hσ p hp k b hk
  exact ⟨n, by omega, hnU⟩

/-- Step 2 of the algorithm is correct. -/
theorem Game.wonAll_strong (G : Game V) [Finite V] {X : Set V} {i : Player} {m : ℕ} {U : Set V}
    (hX : G.IsSubgame X) (hUX : U ⊆ X) (hUm : ∀ v ∈ U, G.prio v = m)
    (hmax : ∀ v ∈ X, G.prio v ≤ m) (hi : Player.ofPrio m = i) {r₁ : Solution V}
    (hr₁ : G.Strong (X \ G.attr X i U) r₁) (he : r₁.win i.opp = ∅) :
    G.Strong X (G.wonAll X i U r₁) := by
  classical
  have hwin : r₁.win i = X \ G.attr X i U := by
    have := hr₁.cover' i
    rwa [he, Set.union_empty] at this
  have h1 : (G.wonAll X i U r₁).win i = X := by simp [Game.wonAll]
  have h2 : (G.wonAll X i U r₁).win i.opp = ∅ := by simp [Game.wonAll, Player.opp_ne]
  have hstrat : ∀ v, (G.wonAll X i U r₁).strat i v =
      if v ∈ G.attr X i U then (if v ∈ U then G.anyMove X v else G.attrStrategy X i U v)
        else r₁.strat i v := by
    intro v; simp [Game.wonAll]
  refine Game.Strong.of_opp i (by rw [h1, h2, Set.union_empty]) (by rw [h1, h2]; simp) ?_ ?_
  swap
  · rw [h2]; exact Game.Region.empty _ _ _ _
  rw [h1]
  refine ⟨subset_rfl, ?_, fun _ _ _ w hw _ => hw, ?_⟩
  · intro v hv ho
    rw [hstrat]
    by_cases hA : v ∈ G.attr X i U
    · by_cases hU : v ∈ U
      · rw [if_pos hA, if_pos hU]
        exact G.anyMove_spec hX hv
      · rw [if_pos hA, if_neg hU]
        have := G.attrStrategy_mem X i U hA hU ho
        exact ⟨G.attr_subset X i U hUX this.1, this.2⟩
    · rw [if_neg hA]
      have hv' : v ∈ r₁.win i := by rw [hwin]; exact ⟨hv, hA⟩
      have := (hr₁.region i).mine v hv' ho
      rw [hwin] at this
      exact ⟨this.1.1, this.2⟩
  · intro p hp
    have hconf : G.ConformingPlay X i ((G.wonAll X i U r₁).strat i) p := fun n =>
      ⟨(hp n).1, (hp (n + 1)).1, (hp n).2.1, (hp n).2.2⟩
    have hσ : ∀ v ∈ G.attr X i U, v ∉ U → G.owner v = i →
        (G.wonAll X i U r₁).strat i v = G.attrStrategy X i U v := by
      intro v hv hvU _
      rw [hstrat, if_pos hv, if_neg hvU]
    by_cases hinf : ∃ᶠ n in Filter.atTop, p n ∈ G.attr X i U
    · have hU := G.frequently_mem_of_frequently_attr X i U _ hσ p hconf hinf
      refine ⟨m, ⟨?_, ?_⟩, hi⟩
      · show ∃ᶠ n in Filter.atTop, (p.map G.prio) n = m
        exact hU.mono fun n hn => by simp [ωSequence.map, hUm _ hn]
      · intro m' hm'
        obtain ⟨n, hn⟩ := (show ∃ᶠ n in Filter.atTop, (p.map G.prio) n = m' from hm').exists
        have : G.prio (p n) = m' := hn
        rw [← this]
        exact hmax _ (hp n).1
    · rw [Filter.not_frequently, Filter.eventually_atTop] at hinf
      obtain ⟨N, hN⟩ := hinf
      rw [← G.playWonBy_drop i p N]
      refine (hr₁.region i).won _ fun n => ?_
      simp only [ωSequence.get_drop]
      have hpn : p (N + n) ∈ r₁.win i := by
        rw [hwin]; exact ⟨(hp _).1, hN _ (by omega)⟩
      refine ⟨hpn, (hp _).2.1, fun ho => ?_⟩
      have := (hp (N + n)).2.2 ho
      rw [hstrat, if_neg (hN _ (by omega))] at this
      exact this

/-- Step 3 of the algorithm is correct. -/
theorem Game.wonSplit_strong (G : Game V) [Finite V] {X A : Set V} {i : Player}
    (hAtrap : ∀ v ∈ X \ A, G.owner v = i → ∀ w ∈ X, G.edge v w → w ∉ A)
    {r₁ r₂ : Solution V} (hr₁ : G.Strong (X \ A) r₁)
    (hr₂ : G.Strong (X \ G.attr X i.opp (r₁.win i.opp)) r₂) :
    G.Strong X (G.wonSplit X i r₁ r₂) := by
  classical
  set W := r₁.win i.opp with hW
  set B := G.attr X i.opp W with hB
  have hr₁j := hr₁.region i.opp
  have hWX : W ⊆ X := fun v hv => (hr₁j.sub hv).1
  have hWA : ∀ v ∈ W, v ∉ A := fun v hv => (hr₁j.sub hv).2
  have hBX : B ⊆ X := G.attr_subset X i.opp W hWX
  have hWB : W ⊆ B := G.subset_attr X i.opp W
  have hr₂i := hr₂.region i
  have hr₂j := hr₂.region i.opp
  have hwin_i : (G.wonSplit X i r₁ r₂).win i = r₂.win i := by simp [Game.wonSplit]
  have hwin_j : (G.wonSplit X i r₁ r₂).win i.opp = r₂.win i.opp ∪ B := by
    simp [Game.wonSplit, Player.opp_ne, hB, hW]
  have hstrat_i : ∀ v, (G.wonSplit X i r₁ r₂).strat i v = r₂.strat i v := by
    intro v; simp [Game.wonSplit]
  have hstrat_j : ∀ v, (G.wonSplit X i r₁ r₂).strat i.opp v =
      if v ∈ W then r₁.strat i.opp v
      else if v ∈ B then G.attrStrategy X i.opp W v else r₂.strat i.opp v := by
    intro v; simp [Game.wonSplit, Player.opp_ne, hB, hW]
  -- the opponent `i` cannot leave `W` within `X`
  have hWclosed : ∀ v ∈ W, G.owner v ≠ i.opp → ∀ w ∈ X, G.edge v w → w ∈ W := by
    intro v hv ho w hw he
    have hvA := hWA v hv
    have hvo : G.owner v = i := by
      have := Player.ne_iff.mp ho
      rwa [Player.opp_opp] at this
    exact hr₁j.theirs v hv ho w ⟨hw, hAtrap v ⟨hWX hv, hvA⟩ hvo w hw he⟩ he
  have hBdisj : ∀ v ∈ r₂.win i ∪ r₂.win i.opp, v ∉ B := fun v hv hvB => by
    have := (hr₂.cover' i).symm ▸ hv
    exact this.2 hvB
  have hr₂sub : ∀ v ∈ r₂.win i ∪ r₂.win i.opp, v ∈ X := fun v hv =>
    ((hr₂.cover' i).symm ▸ hv : v ∈ X \ B).1
  refine Game.Strong.of_opp i ?_ ?_ ?_ ?_
  · rw [hwin_i, hwin_j, ← Set.union_assoc, hr₂.cover' i, Set.sdiff_union_of_subset hBX]
  · rw [hwin_i, hwin_j]
    refine Set.disjoint_union_right.mpr ⟨hr₂.disj' i, ?_⟩
    exact Set.disjoint_left.mpr fun v hv hvB => hBdisj v (Or.inl hv) hvB
  · -- player `i` keeps its region of `r₂`
    rw [hwin_i]
    refine ⟨fun v hv => (hr₂i.sub hv).1, ?_, ?_, ?_⟩
    · intro v hv ho
      rw [hstrat_i]
      exact hr₂i.mine v hv ho
    · intro v hv ho w hw he
      have hvo : G.owner v = i.opp := Player.ne_iff.mp ho
      by_cases hwB : w ∈ B
      · exact absurd (G.mem_attr_of_owner X i.opp W (hr₂i.sub hv).1 hvo he hwB) (hr₂i.sub hv).2
      · exact hr₂i.theirs v hv ho w ⟨hw, hwB⟩ he
    · intro p hp
      refine hr₂i.won p fun n => ?_
      obtain ⟨h1, h2, h3⟩ := hp n
      exact ⟨h1, h2, fun ho => by rw [← hstrat_i]; exact h3 ho⟩
  · -- player `1 - i` wins `B` and its region of `r₂`
    rw [hwin_j]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Set.union_subset (fun v hv => (hr₂j.sub hv).1) hBX
    · intro v hv ho
      rw [hstrat_j]
      by_cases hvW : v ∈ W
      · rw [if_pos hvW]
        have := hr₁j.mine v hvW ho
        exact ⟨Or.inr (hWB this.1), this.2⟩
      · rw [if_neg hvW]
        by_cases hvB : v ∈ B
        · rw [if_pos hvB]
          have := G.attrStrategy_mem X i.opp W hvB hvW ho
          exact ⟨Or.inr this.1, this.2⟩
        · rw [if_neg hvB]
          have hv2 : v ∈ r₂.win i.opp := hv.resolve_right hvB
          have := hr₂j.mine v hv2 ho
          exact ⟨Or.inl this.1, this.2⟩
    · intro v hv ho w hw he
      by_cases hvB : v ∈ B
      · right
        by_cases hvW : v ∈ W
        · exact hWB (hWclosed v hvW ho w hw he)
        · exact G.attr_opp_closed X i.opp W hvB hvW ho w hw he
      · have hv2 : v ∈ r₂.win i.opp := hv.resolve_right hvB
        by_cases hwB : w ∈ B
        · exact Or.inr hwB
        · exact Or.inl (hr₂j.theirs v hv2 ho w ⟨hw, hwB⟩ he)
    · intro p hp
      by_cases hex : ∃ n, p n ∈ B
      · obtain ⟨n₀, hn₀⟩ := hex
        have hconf : G.ConformingPlay X i.opp ((G.wonSplit X i r₁ r₂).strat i.opp) p := by
          intro n
          obtain ⟨h1, h2, h3⟩ := hp n
          obtain ⟨h1', -, -⟩ := hp (n + 1)
          refine ⟨?_, ?_, h2, h3⟩
          · exact (show _ ⊆ X from Set.union_subset (fun v hv => (hr₂j.sub hv).1) hBX) h1
          · exact (show _ ⊆ X from Set.union_subset (fun v hv => (hr₂j.sub hv).1) hBX) h1'
        have hσ : ∀ v ∈ B, v ∉ W → G.owner v = i.opp →
            (G.wonSplit X i r₁ r₂).strat i.opp v = G.attrStrategy X i.opp W v := by
          intro v hv hvW _
          rw [hstrat_j, if_neg hvW, if_pos hv]
        obtain ⟨k, hk⟩ := hn₀
        obtain ⟨m, hm, hmW⟩ := G.reach_of_mem_stage X i.opp W _ hσ p hconf k n₀ hk
        have hstay : ∀ t, p (m + t) ∈ W := by
          intro t
          induction t with
          | zero => exact hmW
          | succ t ih =>
            obtain ⟨h1, h2, h3⟩ := hp (m + t)
            obtain ⟨h1', -, -⟩ := hp (m + t + 1)
            have hX' : p (m + t + 1) ∈ X :=
              (show _ ⊆ X from Set.union_subset (fun v hv => (hr₂j.sub hv).1) hBX) h1'
            by_cases ho : G.owner (p (m + t)) = i.opp
            · rw [show m + (t + 1) = m + t + 1 from rfl, h3 ho, hstrat_j, if_pos ih]
              exact (hr₁j.mine _ ih ho).1
            · exact hWclosed _ ih ho _ hX' h2
        rw [← G.playWonBy_drop i.opp p m]
        refine hr₁j.won _ fun t => ?_
        simp only [ωSequence.get_drop]
        refine ⟨hstay t, (hp (m + t)).2.1, fun ho => ?_⟩
        have := (hp (m + t)).2.2 ho
        rw [hstrat_j, if_pos (hstay t)] at this
        exact this
      · push Not at hex
        refine hr₂j.won p fun n => ?_
        obtain ⟨h1, h2, h3⟩ := hp n
        have hv2 : p n ∈ r₂.win i.opp := h1.resolve_right (hex n)
        refine ⟨hv2, h2, fun ho => ?_⟩
        rw [h3 ho, hstrat_j, if_neg fun hW' => hex n (hWB hW'), if_neg (hex n)]

/-- The invariant holds for the algorithm's result on every subgame. -/
theorem Game.zielonkaAux_strong (G : Game V) [Finite V] :
    ∀ (n : ℕ) (X : Set V), X.ncard = n → G.IsSubgame X → G.Strong X (G.zielonkaAux X) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hX
  rw [Game.zielonkaAux]
  by_cases hne : X.Nonempty
  · rw [dif_pos hne]
    have hmax : ∀ v ∈ X, G.prio v ≤ G.maxPrio X := fun v hv =>
      le_csSup (Set.toFinite _).bddAbove ⟨v, hv, rfl⟩
    have hex : ∃ v ∈ X, G.prio v = G.maxPrio X :=
      Nat.sSup_mem (hne.image _) (Set.toFinite _).bddAbove
    dsimp only
    generalize G.maxPrio X = m at hmax hex ⊢
    generalize hi : Player.ofPrio m = i
    have hUX : {v | v ∈ X ∧ G.prio v = m} ⊆ X := fun v hv => hv.1
    have hUm : ∀ v ∈ {v | v ∈ X ∧ G.prio v = m}, G.prio v = m := fun v hv => hv.2
    have hUne : ∃ v, v ∈ {v | v ∈ X ∧ G.prio v = m} := by
      obtain ⟨v, hv, h⟩ := hex; exact ⟨v, hv, h⟩
    generalize {v | v ∈ X ∧ G.prio v = m} = U at hUX hUm hUne ⊢
    obtain ⟨u, huU⟩ := hUne
    have hAc := G.attractorCorrect X i U hX hUX
    obtain ⟨⟨hUA, hAX⟩, hsub1, htrap1, -⟩ := hAc
    have hlt1 : (X \ G.attr X i U).ncard < n := by
      rw [← hn]
      refine Set.ncard_lt_ncard ⟨Set.sdiff_subset, fun hsub => ?_⟩ (Set.toFinite X)
      exact (hsub (hUX huU)).2 (hUA huU)
    have hr₁ := ih _ hlt1 _ rfl hsub1
    generalize G.zielonkaAux (X \ G.attr X i U) = r₁ at hr₁ ⊢
    by_cases he : r₁.win i.opp = ∅
    · rw [if_pos he]
      exact G.wonAll_strong hX hUX hUm hmax hi hr₁ he
    · rw [if_neg he]
      have hr₁j := hr₁.region i.opp
      have hWX : r₁.win i.opp ⊆ X := fun v hv => (hr₁j.sub hv).1
      obtain ⟨⟨hWB, hBX⟩, hsub2, -, -⟩ := G.attractorCorrect X i.opp (r₁.win i.opp) hX hWX
      have hBss : X \ G.attr X i.opp (r₁.win i.opp) ⊂ X := by
        obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr he
        refine ⟨Set.sdiff_subset, fun hsub => ?_⟩
        exact (hsub (hWX hw)).2 (hWB hw)
      rw [dif_pos hBss]
      have hlt2 : (X \ G.attr X i.opp (r₁.win i.opp)).ncard < n := by
        rw [← hn]; exact Set.ncard_lt_ncard hBss (Set.toFinite X)
      have hr₂ := ih _ hlt2 _ rfl hsub2
      exact G.wonSplit_strong htrap1 hr₁ hr₂
  · rw [dif_neg hne]
    have hX0 : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hX0
    refine Game.Strong.of_opp .zero (by simp [Solution.empty]) (by simp [Solution.empty]) ?_ ?_
    · exact Game.Region.empty _ _ _ _
    · exact Game.Region.empty _ _ _ _

/-- Zielonka's algorithm is correct (positional determinacy of parity games). -/
theorem Game.zielonka_correct (G : Game V) [Finite V] : G.ZielonkaCorrect := by
  refine (G.zielonkaAux_strong _ Set.univ rfl ?_).solves ?_ <;>
    exact fun v _ => by obtain ⟨w, hw⟩ := G.total v; exact ⟨w, Set.mem_univ _, hw⟩

end ParityGame

end ZielonkaProofs
