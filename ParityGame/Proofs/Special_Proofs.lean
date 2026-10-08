module

public import ParityGame.Special
public import ParityGame.Proofs.Defs_Proofs
public import ParityGame.Proofs.Region_Proofs
public import ParityGame.Proofs.Attractor_Proofs
public import ParityGame.Proofs.Zielonka_Proofs
public import ParityGame.Proofs.Scc_Proofs

open Cslib (ωSequence)

@[expose] public section SpecialProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). -/

variable {V : Type*}

/-! ### One-parity games -/

theorem Game.oneParitySolve_strong (G : Game V) [Finite V] {C : Set V} {i : Player}
    (hC : G.IsSubgame C) (hi : G.OneParity C i) : G.Strong C (G.oneParitySolve C i) := by
  classical
  have h1 : (G.oneParitySolve C i).win i = C := by simp [Game.oneParitySolve]
  have h2 : (G.oneParitySolve C i).win i.opp = ∅ := by
    simp [Game.oneParitySolve, Player.opp_ne]
  refine Game.Strong.of_opp i (by rw [h1, h2, Set.union_empty]) (by rw [h1, h2]; simp) ?_ ?_
  · rw [h1]
    refine ⟨subset_rfl, fun v hv _ => ?_, fun _ _ _ w hw _ => hw, fun p hp => ?_⟩
    · have : (G.oneParitySolve C i).strat i v = G.anyMove C v := by simp [Game.oneParitySolve]
      rw [this]
      exact G.anyMove_spec hC hv
    · obtain ⟨M, hM⟩ := G.exists_maxInfPrio p
      refine ⟨M, hM, ?_⟩
      rw [Game.maxInfPrio_iff] at hM
      obtain ⟨v, hv, rfl⟩ := hM.1
      obtain ⟨k, -, hk⟩ := (Filter.frequently_atTop.mp hv) 0
      exact hi v (hk ▸ (hp k).1)
  · rw [h2]; exact Game.Region.empty _ _ _ _

/-! ### Strongly connected sets -/

/-- Paths between nodes of an SCC stay inside it. -/
theorem Game.IsSCC.reach_within {G : Game V} {X D : Set V} (h : G.IsSCC X D) {u v : V}
    (hu : u ∈ D) (hv : v ∈ D) : G.Reach D u v := by
  obtain ⟨-, hDX, hconn, hmax⟩ := h
  have key : ∀ a, G.Reach X a v → a ∈ D → G.Reach D a v := by
    intro a hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Game.Reach.refl _
    | head hac hcv ih =>
      rename_i a c
      intro ha
      have hcD : c ∈ D := by
        refine hmax a ha c hac.2.1 (Game.Reach.single hac.1 hac.2.1 hac.2.2) ?_
        exact hcv.trans (hconn v hv a ha)
      exact (Game.Reach.single ha hcD hac.2.2).trans (ih hcD)
  exact key u (hconn u hu v hv) hu

/-- In a strongly connected set with an inner edge every node has a successor inside. -/
theorem Game.exists_succ_of_connected {G : Game V} {D : Set V}
    (hconn : ∀ u ∈ D, ∀ v ∈ D, G.Reach D u v) (hedge : ∃ a ∈ D, ∃ b ∈ D, G.edge a b) :
    ∀ v ∈ D, ∃ c ∈ D, G.edge v c := by
  obtain ⟨a, ha, b, hb, hab⟩ := hedge
  intro v hv
  rcases Relation.ReflTransGen.cases_head (hconn v hv a ha) with rfl | ⟨c, hc, -⟩
  · exact ⟨b, hb, hab⟩
  · exact ⟨c, hc.2.1, hc.2.2⟩

/-- In a one-player game, a node that reaches `U` is in the attractor of `U`. -/
theorem Game.subset_attr_of_reach (G : Game V) [Finite V] {X U : Set V} (i : Player)
    (huniq : ∀ v ∈ X, G.owner v ≠ i → ∀ w ∈ X, ∀ w' ∈ X, G.edge v w → G.edge v w' → w = w')
    (hreach : ∀ v ∈ X, ∃ u ∈ U, G.Reach X v u) : X ⊆ G.attr X i U := by
  intro v hv
  obtain ⟨u, hu, hvu⟩ := hreach v hv
  have key : ∀ a, G.Reach X a u → a ∈ X → a ∈ G.attr X i U := by
    intro a hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => G.subset_attr X i U hu
    | head hac hcv ih =>
      rename_i a c
      intro ha
      have hc := ih hac.2.1
      by_cases ho : G.owner a = i
      · exact G.mem_attr_of_owner X i U ha ho hac.2.2 hc
      · refine G.mem_attr_of_opp X i U ha ho fun w hw he => ?_
        rw [huniq a ha ho w hw c hac.2.1 he hac.2.2]
        exact hc
  exact key v hvu hv

/-! ### One-player games: soundness of the recursion -/

theorem Game.OnePlayerCore.sound {G : Game V} [Finite V] {i : Player} {Y Y₀ : Set V}
    (h : G.OnePlayerCore i Y Y₀) :
    (∀ u ∈ Y, ∀ v ∈ Y, G.Reach Y u v) →
      Y₀ ⊆ Y ∧ Y₀.Nonempty ∧ (∀ u ∈ Y₀, ∀ v ∈ Y₀, G.Reach Y₀ u v) ∧
        (∃ a ∈ Y₀, ∃ b ∈ Y₀, G.edge a b) ∧ Player.ofPrio (G.maxPrio Y₀) = i := by
  induction h with
  | base hne hedge hp => exact fun hc => ⟨subset_rfl, hne, hc, hedge, hp⟩
  | step hne hp hscc _ ih =>
    intro _
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih fun u hu v hv => hscc.reach_within hu hv
    exact ⟨h1.trans (hscc.2.1.trans Set.sdiff_subset), h2, h3, h4, h5⟩

/-- The greatest priority of a non-empty set is attained. -/
theorem Game.exists_prio_eq_maxPrio (G : Game V) [Finite V] {Y : Set V} (hY : Y.Nonempty) :
    ∃ v ∈ Y, G.prio v = G.maxPrio Y :=
  Nat.sSup_mem (hY.image _) (Set.toFinite _).bddAbove

theorem Game.prio_le_maxPrio (G : Game V) [Finite V] {Y : Set V} {v : V} (hv : v ∈ Y) :
    G.prio v ≤ G.maxPrio Y :=
  le_csSup (Set.toFinite _).bddAbove ⟨v, hv, rfl⟩

/-! ### One-player games: completeness of the recursion -/

/-- If `i` wins some play inside `Y ⊆ C` of a one-player game for `i`, the recursion finds a
    good strongly connected set. -/
theorem Game.OnePlayerCore.complete (G : Game V) [Finite V] {C : Set V} {i : Player}
    (huniq : ∀ v ∈ C, G.owner v ≠ i → ∀ w ∈ C, ∀ w' ∈ C, G.edge v w → G.edge v w' → w = w') :
    ∀ (n : ℕ) (Y : Set V), Y.ncard = n → Y ⊆ C → ∀ p : ωSequence V,
      (∀ t, p t ∈ Y ∧ G.edge (p t) (p (t + 1))) → G.PlayWonBy i p →
        ∃ Y₀, G.OnePlayerCore i Y Y₀ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hn hYC p hp hwon
  obtain ⟨M, hM, hMi⟩ := hwon
  have hY : Y.Nonempty := ⟨p 0, (hp 0).1⟩
  have hproper : ∃ v ∈ Y, ∃ w ∈ Y, G.edge v w := ⟨p 0, (hp 0).1, p 1, (hp 1).1, (hp 0).2⟩
  by_cases hq : Player.ofPrio (G.maxPrio Y) = i
  · exact ⟨Y, Game.OnePlayerCore.base hY hproper hq⟩
  set q := G.maxPrio Y with hqdef
  set P : Set V := {v | v ∈ Y ∧ G.prio v = q} with hP
  set A := G.attr Y i.opp P with hA
  have hPY : P ⊆ Y := fun v hv => hv.1
  obtain ⟨v₁, hv₁Y, hv₁q⟩ := G.exists_prio_eq_maxPrio hY
  have hv₁P : v₁ ∈ P := ⟨hv₁Y, hv₁q⟩
  -- the opponent of `i` drives plays into `P` from the attractor
  have hreach : ∀ k N, p N ∈ G.attrStage Y i.opp P k → ∃ n, N ≤ n ∧ p n ∈ P := by
    intro k
    induction k with
    | zero => exact fun N h => ⟨N, le_rfl, h⟩
    | succ k ih' =>
      intro N hN
      by_cases hk : p N ∈ G.attrStage Y i.opp P k
      · exact ih' N hk
      · obtain ⟨-, hc⟩ := G.attrStage_succ_mem Y i.opp P hN hk
        have hnext : p (N + 1) ∈ G.attrStage Y i.opp P k := by
          rcases hc with ⟨ho, w, hw, he⟩ | ⟨-, hall⟩
          · have hne : G.owner (p N) ≠ i := by rw [ho]; exact Player.opp_ne i
            have hwY := G.attrStage_subset Y i.opp P hPY k hw
            rw [← huniq _ (hYC (hp N).1) hne w (hYC hwY) _ (hYC (hp (N + 1)).1) he (hp N).2]
            exact hw
          · exact hall _ (hp (N + 1)).1 (hp N).2
        obtain ⟨n, hn, hnP⟩ := ih' (N + 1) hnext
        exact ⟨n, by omega, hnP⟩
  have hM' := (G.maxInfPrio_iff p M).mp hM
  have hnodeY : ∀ v ∈ nodeInf p, v ∈ Y := by
    intro v hv
    obtain ⟨k, -, hk⟩ := (Filter.frequently_atTop.mp hv) 0
    exact hk ▸ (hp k).1
  -- eventually `p` avoids the attractor
  have hev : ∃ N, ∀ t, N ≤ t → p t ∉ A := by
    by_contra hcon
    push Not at hcon
    have hfreq : ∃ᶠ t in Filter.atTop, p t ∈ P := by
      rw [Filter.frequently_atTop]
      intro a
      obtain ⟨t, ht, k, hk⟩ := hcon a
      obtain ⟨n, hn, hnP⟩ := hreach k t hk
      exact ⟨n, by omega, hnP⟩
    obtain ⟨v, hvP, hv⟩ := (ωSequence.frequently_in_finite_type (s := P) (xs := p)).mp hfreq
    have h1 : q ≤ M := hvP.2 ▸ hM'.2 v hv
    have h2 : M ≤ q := by
      obtain ⟨v₀, hv₀, rfl⟩ := hM'.1
      exact G.prio_le_maxPrio (hnodeY v₀ hv₀)
    exact hq (by rw [le_antisymm h1 h2]; exact hMi)
  obtain ⟨N, hN⟩ := hev
  -- eventually `p` only visits recurring nodes
  have hevinf : ∀ᶠ t in Filter.atTop, p t ∈ nodeInf p := by
    have : ∀ᶠ t in Filter.atTop, ∀ v, v ∉ nodeInf p → p t ≠ v :=
      Filter.eventually_all.mpr fun v => by
        by_cases hv : v ∈ nodeInf p
        · exact Filter.Eventually.of_forall fun t h => absurd hv h
        · have := Filter.not_frequently.mp hv
          exact this.mono fun t ht _ => ht
    refine this.mono fun t ht => ?_
    by_contra h
    exact ht _ h rfl
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hevinf
  set t₀ := max N T with ht₀
  set s := p t₀ with hs
  have hsInf : s ∈ nodeInf p := hT t₀ (le_max_right _ _)
  have hpYA : ∀ t, N ≤ t → p t ∈ Y \ A := fun t ht => ⟨(hp t).1, hN t ht⟩
  have hfwd : ∀ a b, N ≤ a → a ≤ b → G.Reach (Y \ A) (p a) (p b) := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact Game.Reach.refl _
    | succ b hab ih' =>
      exact ih'.trans (Game.Reach.single (hpYA b (by omega)) (hpYA (b + 1) (by omega)) (hp b).2)
  set D : Set V := {w | w ∈ Y \ A ∧ G.Reach (Y \ A) s w ∧ G.Reach (Y \ A) w s} with hD
  have hsD : s ∈ D := ⟨hpYA t₀ (le_max_left _ _), Game.Reach.refl _, Game.Reach.refl _⟩
  have hDscc : G.IsSCC (Y \ A) D := by
    refine ⟨⟨s, hsD⟩, fun w hw => hw.1, ?_, ?_⟩
    · rintro u ⟨-, -, hu⟩ w ⟨-, hw, -⟩
      exact hu.trans hw
    · rintro u ⟨-, hu1, hu2⟩ w hwX huw hwu
      exact ⟨hwX, hu1.trans huw, hwu.trans hu2⟩
  have hDY : D ⊆ Y \ A := fun w hw => hw.1
  have hlt : D.ncard < n := by
    rw [← hn]
    refine lt_of_le_of_lt (Set.ncard_le_ncard hDY (Set.toFinite _)) ?_
    refine Set.ncard_lt_ncard ⟨Set.sdiff_subset, fun hsub => ?_⟩ (Set.toFinite _)
    exact (hsub hv₁Y).2 (G.subset_attr Y i.opp P hv₁P)
  have htail : ∀ t, p (t₀ + t) ∈ D := by
    intro t
    refine ⟨hpYA _ (by omega), ?_, ?_⟩
    · exact hfwd t₀ (t₀ + t) (le_max_left _ _) (by omega)
    · obtain ⟨t', ht', hs'⟩ := Filter.frequently_atTop.mp hsInf (t₀ + t)
      have := hfwd (t₀ + t) t' (by omega) ht'
      rwa [hs'] at this
  obtain ⟨Y₀, hY₀⟩ := ih D.ncard hlt D rfl (hDY.trans (Set.sdiff_subset.trans hYC))
    (p.drop t₀) (fun t => by
      simp only [ωSequence.get_drop]
      exact ⟨htail t, (hp _).2⟩) ((G.playWonBy_drop i p t₀).mpr ⟨M, hM, hMi⟩)
  exact ⟨Y₀, Game.OnePlayerCore.step hY hq hDscc hY₀⟩

/-! ### One-player games: the direct solver -/

theorem Game.onePlayerSolve_strong (G : Game V) [Finite V] {C : Set V} {i : Player}
    (hC : G.IsSubgame C) (hconn : ∀ u ∈ C, ∀ v ∈ C, G.Reach C u v) (hone : G.OnePlayer C i) :
    G.Strong C (G.onePlayerSolve C i) := by
  classical
  by_cases h : ∃ Y₀, G.OnePlayerCore i C Y₀
  · -- `i` wins everything
    have hwin : (G.onePlayerSolve C i).win i = C ∧ (G.onePlayerSolve C i).win i.opp = ∅ := by
      unfold Game.onePlayerSolve
      rw [dif_pos h]
      simp [Player.opp_ne]
    have hstrat : ∀ v, (G.onePlayerSolve C i).strat i v =
        if v ∈ h.choose then
          (if v ∈ {u | u ∈ h.choose ∧ G.prio u = G.maxPrio h.choose} then G.anyMove h.choose v
          else G.attrStrategy h.choose i {u | u ∈ h.choose ∧ G.prio u = G.maxPrio h.choose} v)
        else G.attrStrategy C i h.choose v := by
      intro v
      unfold Game.onePlayerSolve
      rw [dif_pos h]
      simp
    obtain ⟨hY₀C, hY₀ne, hY₀conn, hY₀edge, hY₀i⟩ := h.choose_spec.sound hconn
    set Y₀ := h.choose with hY₀
    set P₀ : Set V := {u | u ∈ Y₀ ∧ G.prio u = G.maxPrio Y₀} with hP₀
    set σ := (G.onePlayerSolve C i).strat i with hσdef
    have hP₀Y : P₀ ⊆ Y₀ := fun v hv => hv.1
    have hY₀sub : G.IsSubgame Y₀ := Game.exists_succ_of_connected hY₀conn hY₀edge
    have huniq : ∀ v ∈ C, G.owner v ≠ i → ∀ w ∈ C, ∀ w' ∈ C, G.edge v w → G.edge v w' → w = w' :=
      hone
    have hattrY : Y₀ ⊆ G.attr Y₀ i P₀ := by
      refine G.subset_attr_of_reach i (fun v hv ho w hw w' hw' => huniq v (hY₀C hv) ho w
        (hY₀C hw) w' (hY₀C hw')) fun v hv => ?_
      obtain ⟨u, hu, hup⟩ := G.exists_prio_eq_maxPrio hY₀ne
      exact ⟨u, ⟨hu, hup⟩, hY₀conn v hv u hu⟩
    have hattrC : C ⊆ G.attr C i Y₀ := by
      refine G.subset_attr_of_reach i huniq fun v hv => ?_
      obtain ⟨u, hu⟩ := hY₀ne
      exact ⟨u, hu, hconn v hv u (hY₀C hu)⟩
    have hyclosed : ∀ v ∈ Y₀, G.owner v ≠ i → ∀ w ∈ C, G.edge v w → w ∈ Y₀ := by
      intro v hv ho w hw he
      obtain ⟨c, hc, hce⟩ := hY₀sub v hv
      rw [huniq v (hY₀C hv) ho w hw c (hY₀C hc) he hce]
      exact hc
    have hσY₀ : ∀ v ∈ Y₀, G.owner v = i → σ v ∈ Y₀ := by
      intro v hv ho
      rw [hstrat, if_pos hv]
      by_cases hvP : v ∈ P₀
      · rw [if_pos hvP]; exact (G.anyMove_spec hY₀sub hv).1
      · rw [if_neg hvP]
        exact G.attr_subset Y₀ i P₀ hP₀Y (G.attrStrategy_mem Y₀ i P₀ (hattrY hv) hvP ho).1
    have hσmine : ∀ v ∈ C, G.owner v = i → σ v ∈ C ∧ G.edge v (σ v) := by
      intro v hv ho
      by_cases hvY : v ∈ Y₀
      · refine ⟨hY₀C (hσY₀ v hvY ho), ?_⟩
        rw [hstrat, if_pos hvY]
        by_cases hvP : v ∈ P₀
        · rw [if_pos hvP]; exact (G.anyMove_spec hY₀sub hvY).2
        · rw [if_neg hvP]; exact (G.attrStrategy_mem Y₀ i P₀ (hattrY hvY) hvP ho).2
      · have := G.attrStrategy_mem C i Y₀ (hattrC hv) hvY ho
        rw [hstrat, if_neg hvY]
        exact ⟨G.attr_subset C i Y₀ hY₀C this.1, this.2⟩
    refine Game.Strong.of_opp i (by rw [hwin.1, hwin.2, Set.union_empty])
      (by rw [hwin.1, hwin.2]; simp) ?_ ?_
    swap
    · rw [hwin.2]; exact Game.Region.empty _ _ _ _
    rw [hwin.1]
    refine ⟨subset_rfl, hσmine, fun _ _ _ w hw _ => hw, fun p hp => ?_⟩
    have hconf : G.ConformingPlay C i σ p := fun n =>
      ⟨(hp n).1, (hp (n + 1)).1, (hp n).2.1, (hp n).2.2⟩
    have hσ1 : ∀ v ∈ G.attr C i Y₀, v ∉ Y₀ → G.owner v = i →
        σ v = G.attrStrategy C i Y₀ v := by
      intro v _ hvY _
      rw [hstrat, if_neg hvY]
    obtain ⟨k, hk⟩ := hattrC (hp 0).1
    obtain ⟨n, -, hn⟩ := G.reach_of_mem_stage C i Y₀ σ hσ1 p hconf k 0 hk
    have hstay : ∀ t, p (n + t) ∈ Y₀ := by
      intro t
      induction t with
      | zero => exact hn
      | succ t ih' =>
        obtain ⟨-, -, -, hs⟩ := hconf (n + t)
        by_cases ho : G.owner (p (n + t)) = i
        · rw [show n + (t + 1) = n + t + 1 from rfl, hs ho]; exact hσY₀ _ ih' ho
        · exact hyclosed _ ih' ho _ (hp (n + t + 1)).1 (hp (n + t)).2.1
    set q := p.drop n with hq
    have hqY : ∀ t, q t ∈ Y₀ := fun t => by
      rw [hq, ωSequence.get_drop]; exact hstay t
    have hconfq : G.ConformingPlay Y₀ i σ q := by
      intro t
      refine ⟨hqY t, hqY (t + 1), ?_, ?_⟩
      · simp only [hq, ωSequence.get_drop]; exact (hp _).2.1
      · intro ho
        simp only [hq, ωSequence.get_drop] at ho ⊢
        exact (hconf (n + t)).2.2.2 ho
    have hσ2 : ∀ v ∈ G.attr Y₀ i P₀, v ∉ P₀ → G.owner v = i →
        σ v = G.attrStrategy Y₀ i P₀ v := by
      intro v hv hvP _
      rw [hstrat, if_pos (G.attr_subset Y₀ i P₀ hP₀Y hv), if_neg hvP]
    have hfreq : ∃ᶠ t in Filter.atTop, q t ∈ P₀ := by
      rw [Filter.frequently_atTop]
      intro a
      obtain ⟨k, hk⟩ := hattrY (hqY a)
      obtain ⟨n', hn', hP⟩ := G.reach_of_mem_stage Y₀ i P₀ σ hσ2 q hconfq k a hk
      exact ⟨n', hn', hP⟩
    obtain ⟨v, hvP, hv⟩ := (ωSequence.frequently_in_finite_type (s := P₀) (xs := q)).mp hfreq
    have hMq : G.MaxInfPrio q (G.maxPrio Y₀) := by
      rw [Game.maxInfPrio_iff]
      refine ⟨⟨v, hv, hvP.2⟩, fun u hu => G.prio_le_maxPrio ?_⟩
      obtain ⟨t, -, ht⟩ := (Filter.frequently_atTop.mp hu) 0
      exact ht ▸ hqY t
    rw [← G.playWonBy_drop i p n]
    exact ⟨_, hMq, hY₀i⟩
  · -- the opponent of `i` wins everything
    have hwin : (G.onePlayerSolve C i).win i = ∅ ∧ (G.onePlayerSolve C i).win i.opp = C := by
      unfold Game.onePlayerSolve
      rw [dif_neg h]
      simp [(Player.opp_ne i).symm]
    have hstrat : ∀ v, (G.onePlayerSolve C i).strat i.opp v = G.anyMove C v := by
      intro v
      unfold Game.onePlayerSolve
      rw [dif_neg h]
      simp
    refine Game.Strong.of_opp i (by rw [hwin.1, hwin.2, Set.empty_union])
      (by rw [hwin.1]; simp) ?_ ?_
    · rw [hwin.1]; exact Game.Region.empty _ _ _ _
    rw [hwin.2]
    refine ⟨subset_rfl, fun v hv _ => ?_, fun _ _ _ w hw _ => hw, fun p hp => ?_⟩
    · rw [hstrat]; exact G.anyMove_spec hC hv
    · obtain ⟨M, hM⟩ := G.exists_maxInfPrio p
      rcases Player.eq_or_eq_opp (Player.ofPrio M) i with hMi | hMi
      · exfalso
        exact h (Game.OnePlayerCore.complete G hone _ C rfl subset_rfl p (fun t => ⟨(hp t).1, (hp t).2.1⟩)
          ⟨M, hM, hMi⟩ |>.imp fun _ h => h)
      · exact ⟨M, hM, hMi⟩

theorem Game.oneParitySolve_correct (G : Game V) [Finite V] (C : Set V) (i : Player) :
    G.OneParitySolveCorrect C i :=
  fun hC hi => (G.oneParitySolve_strong hC hi).solves hC

theorem Game.onePlayerSolve_correct (G : Game V) [Finite V] (C : Set V) (i : Player) :
    G.OnePlayerSolveCorrect C i :=
  fun hC hconn hone => (G.onePlayerSolve_strong hC hconn hone).solves hC

end ParityGame

end SpecialProofs



