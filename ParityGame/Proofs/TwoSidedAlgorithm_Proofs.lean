module

public import ParityGame.TwoSidedAlgorithm
public import ParityGame.Proofs.Lifting_Proofs

open Cslib (ωSequence)

@[expose] public section TwoSidedAlgorithmProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/TwoSidedAlgorithm_Pins.lean`.

* Duality: the dual game has the same steps (with the players swapped) and every greatest
  recurring priority shifted by one, which flips its parity.
* Dominion removal reuses the `Region` machinery of `Region_Proofs` (a dominion is exactly a
  region of a subgame) and Zielonka's algorithm for positional determinacy of `X \ A`.
* Certification is `progressMeasureSound` plus `step_prog`. -/

variable {V M N : Type*}

/-! ### Duality -/

theorem Player.opp_eq_iff (o i : Player) : o.opp = i ↔ o = i.opp := by
  cases o <;> cases i <;> simp [Player.opp]

theorem Player.ofPrio_succ (m : ℕ) : Player.ofPrio (m + 1) = (Player.ofPrio m).opp := by
  unfold Player.ofPrio
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have : (m + 1) % 2 = 1 := by omega
    simp [h, this, Player.opp]
  · have : (m + 1) % 2 = 0 := by omega
    simp [h, this, Player.opp]

theorem Game.dual_step (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) (v w : V) :
    G.dual.Step X i σ v w ↔ G.Step X i.opp σ v w := by
  simp only [Game.Step, Game.dual, Player.opp_eq_iff]

theorem Game.dual_playWonBy (G : Game V) (i : Player) (p : ωSequence V) :
    G.dual.PlayWonBy i p ↔ G.PlayWonBy i.opp p := by
  have key : ∀ m, m + 1 ∈ (p.map G.dual.prio).infOcc ↔ m ∈ (p.map G.prio).infOcc := by
    intro m
    simp [ωSequence.infOcc, Game.dual]
  have hz : 0 ∉ (p.map G.dual.prio).infOcc := by
    simp [ωSequence.infOcc, Game.dual]
  have hpos : ∀ n ∈ (p.map G.dual.prio).infOcc, ∃ m, n = m + 1 := by
    intro n hn
    cases n with
    | zero => exact absurd hn hz
    | succ m => exact ⟨m, rfl⟩
  constructor
  · rintro ⟨n, ⟨hn, hmax⟩, hi⟩
    obtain ⟨m, rfl⟩ := hpos n hn
    refine ⟨m, ⟨(key m).1 hn, fun k hk => ?_⟩, ?_⟩
    · have := hmax _ ((key k).2 hk); omega
    · rw [Player.ofPrio_succ] at hi; rw [← hi, Player.opp_opp]
  · rintro ⟨m, ⟨hm, hmax⟩, hi⟩
    refine ⟨m + 1, ⟨(key m).2 hm, fun k hk => ?_⟩, ?_⟩
    · obtain ⟨k', rfl⟩ := hpos k hk
      have := hmax _ ((key k').1 hk); omega
    · rw [Player.ofPrio_succ, hi, Player.opp_opp]

/-- Duality (headline). -/
theorem Game.dualWinsFrom (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) (v : V) :
    G.DualWinsFrom X i σ v := by
  have hs : G.dual.Step X i σ = G.Step X i.opp σ := by
    funext a b; exact propext (G.dual_step X i σ a b)
  unfold Game.DualWinsFrom Game.WinsFrom Game.ConformingPlay
  rw [hs]
  simp only [G.dual_playWonBy]

theorem Game.forPlayer_step (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) :
    (G.forPlayer i).Step X .zero σ = G.Step X i σ := by
  cases i
  · rfl
  · funext a b; exact propext (G.dual_step X .zero σ a b)

theorem Game.forPlayer_winsFrom (G : Game V) (X : Set V) (i : Player) (σ : Strategy V) (v : V) :
    (G.forPlayer i).WinsFrom X .zero σ v ↔ G.WinsFrom X i σ v := by
  cases i
  · exact Iff.rfl
  · exact G.dualWinsFrom X .zero σ v

theorem Game.forPlayer_isSubgame (G : Game V) (i : Player) (X : Set V) :
    (G.forPlayer i).IsSubgame X ↔ G.IsSubgame X := by
  cases i <;> exact Iff.rfl

/-! ### Dominions, regions and winning -/

/-- A dominion is a region. -/
theorem Game.IsDominion.region {G : Game V} {X : Set V} {i : Player} {D : Set V}
    {σ : Strategy V} (h : G.IsDominion X i D σ) : G.Region X i D σ := by
  obtain ⟨hDX, hwin, hcl⟩ := h
  refine ⟨hDX, fun v hv ho => ?_, fun v hv ho w hw he =>
    hcl v hv w ⟨hDX hv, hw, he, fun h => absurd h ho⟩, fun p hp => ?_⟩
  · obtain ⟨u, hu⟩ := (hwin v hv).1 v Relation.ReflTransGen.refl
    have := hu.2.2.2 ho
    subst this
    exact ⟨hcl v hv _ hu, hu.2.2.1⟩
  · exact (hwin (p 0) (hp 0).1).2 p rfl fun n =>
      ⟨hDX (hp n).1, hDX (hp (n + 1)).1, (hp n).2.1, (hp n).2.2⟩

/-- A region of a subgame is a dominion. -/
theorem Game.Region.dominion {G : Game V} {X : Set V} {i : Player} {D : Set V} {σ : Strategy V}
    (h : G.Region X i D σ) (hX : G.IsSubgame X) : G.IsDominion X i D σ := by
  refine ⟨h.sub, fun v hv => h.winsFrom hX hv, fun v hv w hst => ?_⟩
  obtain ⟨-, hw, he, hs⟩ := hst
  by_cases ho : G.owner v = i
  · rw [hs ho]; exact (h.mine v hv ho).1
  · exact h.theirs v hv ho w hw he

open scoped Classical in
/-- The attractor of a region, with the region's strategy on it and the attractor strategy
    elsewhere, is a region. -/
theorem Game.Region.attr {G : Game V} {X : Set V} {i : Player} {D : Set V} {σ : Strategy V}
    (h : G.Region X i D σ) :
    G.Region X i (G.attr X i D) (fun v => if v ∈ D then σ v else G.attrStrategy X i D v) := by
  classical
  generalize hτ : (fun v => if v ∈ D then σ v else G.attrStrategy X i D v) = τ
  have hτv : ∀ v, τ v = if v ∈ D then σ v else G.attrStrategy X i D v := fun v => by rw [← hτ]
  have hDX := h.sub
  have hDA : D ⊆ G.attr X i D := G.subset_attr X i D
  have hAX : G.attr X i D ⊆ X := G.attr_subset X i D hDX
  refine ⟨hAX, ?_, ?_, ?_⟩
  · intro v hv ho
    by_cases hvD : v ∈ D
    · rw [hτv, if_pos hvD]
      obtain ⟨m1, m2⟩ := h.mine v hvD ho
      exact ⟨hDA m1, m2⟩
    · rw [hτv, if_neg hvD]
      exact G.attrStrategy_mem X i D hv hvD ho
  · intro v hv ho w hw he
    by_cases hvD : v ∈ D
    · exact hDA (h.theirs v hvD ho w hw he)
    · exact G.attr_opp_closed X i D hv hvD ho w hw he
  · intro p hp
    have hconf : G.ConformingPlay X i τ p := fun n =>
      ⟨hAX (hp n).1, hAX (hp (n + 1)).1, (hp n).2.1, (hp n).2.2⟩
    obtain ⟨k, hk⟩ := (hp 0).1
    obtain ⟨m, -, hmD⟩ := G.reach_of_mem_stage X i D τ
      (fun v _ hvD _ => by rw [hτv, if_neg hvD]) p hconf k 0 hk
    have hstay : ∀ t, p (m + t) ∈ D := by
      intro t
      induction t with
      | zero => exact hmD
      | succ t ih =>
        obtain ⟨-, h2, h3⟩ := hp (m + t)
        have hX' : p (m + t + 1) ∈ X := hAX (hp (m + t + 1)).1
        by_cases ho : G.owner (p (m + t)) = i
        · rw [show m + (t + 1) = m + t + 1 from rfl, h3 ho]
          rw [hτv, if_pos ih]
          exact (h.mine _ ih ho).1
        · exact h.theirs _ ih ho _ hX' h2
    rw [← G.playWonBy_drop i p m]
    refine h.won _ fun t => ?_
    simp only [ωSequence.get_drop]
    refine ⟨hstay t, (hp (m + t)).2.1, fun ho => ?_⟩
    have := (hp (m + t)).2.2 ho
    rw [hτv, if_pos (hstay t)] at this
    exact this

open scoped Classical in
/-- A region `A` of `i` in `X` together with a region `R` of `i` in `X \ A` is a region of `i`
    in `X` (playing the strategy of `A` on `A`). -/
theorem Game.Region.extend {G : Game V} {X A R : Set V} {i : Player} {τ ρ : Strategy V}
    (hA : G.Region X i A τ) (hR : G.Region (X \ A) i R ρ) :
    G.Region X i (A ∪ R) (fun v => if v ∈ A then τ v else ρ v) := by
  classical
  generalize hκ : (fun v => if v ∈ A then τ v else ρ v) = κ
  have hκv : ∀ v, κ v = if v ∈ A then τ v else ρ v := fun v => by rw [← hκ]
  have hsub : A ∪ R ⊆ X := Set.union_subset hA.sub fun v hv => (hR.sub hv).1
  refine ⟨hsub, ?_, ?_, ?_⟩
  · intro v hv ho
    by_cases hvA : v ∈ A
    · rw [hκv, if_pos hvA]
      obtain ⟨m1, m2⟩ := hA.mine v hvA ho
      exact ⟨Or.inl m1, m2⟩
    · rw [hκv, if_neg hvA]
      obtain ⟨m1, m2⟩ := hR.mine v (hv.resolve_left hvA) ho
      exact ⟨Or.inr m1, m2⟩
  · intro v hv ho w hw he
    by_cases hvA : v ∈ A
    · exact Or.inl (hA.theirs v hvA ho w hw he)
    · by_cases hwA : w ∈ A
      · exact Or.inl hwA
      · exact Or.inr (hR.theirs v (hv.resolve_left hvA) ho w ⟨hw, hwA⟩ he)
  · intro p hp
    by_cases hex : ∃ n, p n ∈ A
    · obtain ⟨n₀, hn₀⟩ := hex
      have hstay : ∀ t, p (n₀ + t) ∈ A := by
        intro t
        induction t with
        | zero => exact hn₀
        | succ t ih =>
          obtain ⟨-, h2, h3⟩ := hp (n₀ + t)
          have hX' : p (n₀ + t + 1) ∈ X := hsub (hp (n₀ + t + 1)).1
          by_cases ho : G.owner (p (n₀ + t)) = i
          · rw [show n₀ + (t + 1) = n₀ + t + 1 from rfl, h3 ho]
            rw [hκv, if_pos ih]
            exact (hA.mine _ ih ho).1
          · exact hA.theirs _ ih ho _ hX' h2
      rw [← G.playWonBy_drop i p n₀]
      refine hA.won _ fun t => ?_
      simp only [ωSequence.get_drop]
      refine ⟨hstay t, (hp (n₀ + t)).2.1, fun ho => ?_⟩
      have := (hp (n₀ + t)).2.2 ho
      rw [hκv, if_pos (hstay t)] at this
      exact this
    · push Not at hex
      refine hR.won p fun n => ⟨(hp n).1.resolve_left (hex n), (hp n).2.1, fun ho => ?_⟩
      have := (hp n).2.2 ho
      rw [hκv, if_neg (hex n)] at this
      exact this

/-- A region of the opponent `1 - i` in a trap `X \ A` for `i` is a region in `X`. -/
theorem Game.Region.of_trap {G : Game V} {X A R : Set V} {i : Player} {ρ : Strategy V}
    (htrap : ∀ v ∈ X \ A, G.owner v = i → ∀ w ∈ X, G.edge v w → w ∉ A)
    (hR : G.Region (X \ A) i.opp R ρ) : G.Region X i.opp R ρ := by
  refine ⟨fun v hv => (hR.sub hv).1, hR.mine, fun v hv ho w hw he => ?_, hR.won⟩
  have ho' : G.owner v = i := by
    have := Player.ne_iff.mp ho
    rwa [Player.opp_opp] at this
  exact hR.theirs v hv ho w ⟨hw, htrap v (hR.sub hv) ho' w hw he⟩ he

/-- Winning is preserved along conforming moves. -/
theorem Game.WinsFrom.step {G : Game V} {X : Set V} {i : Player} {σ : Strategy V} {v w : V}
    (h : G.WinsFrom X i σ v) (hs : G.Step X i σ v w) : G.WinsFrom X i σ w := by
  refine ⟨fun u hu => h.1 u (Relation.ReflTransGen.head hs hu), fun p hp0 hp => ?_⟩
  have hq : G.ConformingPlay X i σ (ωSequence.cons v p) := by
    intro n
    cases n with
    | zero => show G.Step X i σ v (p 0); rw [hp0]; exact hs
    | succ n => exact hp n
  have hwon := (G.playWonBy_drop i (ωSequence.cons v p) 1).mpr (h.2 _ rfl hq)
  rwa [← ωSequence.tail_eq_drop, ωSequence.tail_cons] at hwon

/-- In a finite game the two players cannot both win from the same node. -/
theorem Game.not_winsFrom_both [Finite V] (G : Game V) {X : Set V} {i : Player}
    {σ τ : Strategy V} {v : V} (h1 : G.WinsFrom X i σ v) (h2 : G.WinsFrom X i.opp τ v) :
    False := by
  by_cases ho : G.owner v = i
  · obtain ⟨u, hu⟩ := h1.1 v Relation.ReflTransGen.refl
    have hs2 : G.Step X i.opp τ v u :=
      ⟨hu.1, hu.2.1, hu.2.2.1, fun h => absurd (ho.symm.trans h).symm (Player.opp_ne i)⟩
    exact G.no_both h1 (h2.step hs2) hu
  · obtain ⟨u, hu⟩ := h2.1 v Relation.ReflTransGen.refl
    have hs1 : G.Step X i σ v u := ⟨hu.1, hu.2.1, hu.2.2.1, fun h => absurd h ho⟩
    exact G.no_both h1 (h2.step hu) hs1

theorem Game.not_wins_both [Finite V] (G : Game V) {X : Set V} {i : Player} {v : V}
    (h1 : G.Wins X i v) (h2 : G.Wins X i.opp v) : False := by
  obtain ⟨σ, hσ⟩ := h1
  obtain ⟨τ, hτ⟩ := h2
  exact G.not_winsFrom_both hσ hτ

/-- Positional determinacy of subgames (from Zielonka's algorithm). -/
theorem Game.wins_or_wins [Finite V] (G : Game V) {X : Set V} (hX : G.IsSubgame X) {v : V}
    (hv : v ∈ X) (i : Player) : G.Wins X i v ∨ G.Wins X i.opp v := by
  have hs := G.zielonkaAux_strong _ X rfl hX
  have : v ∈ (G.zielonkaAux X).win i ∪ (G.zielonkaAux X).win i.opp := (hs.cover' i).symm ▸ hv
  rcases this with h | h
  · exact Or.inl ⟨_, (hs.region i).winsFrom hX h⟩
  · exact Or.inr ⟨_, (hs.region i.opp).winsFrom hX h⟩

theorem Game.wins_opp_iff [Finite V] (G : Game V) {X : Set V} (hX : G.IsSubgame X) {v : V}
    (hv : v ∈ X) (i : Player) : G.Wins X i.opp v ↔ ¬ G.Wins X i v :=
  ⟨fun h h' => G.not_wins_both h' h, fun h => (G.wins_or_wins hX hv i).resolve_left h⟩

/-! ### Dominion removal -/

theorem Game.dominionRemoval [Finite V] (G : Game V) (X : Set V) (i : Player) (D : Set V)
    (σ : Strategy V) : G.DominionRemoval X i D σ := by
  intro hX hD
  set A := G.attr X i D with hA
  have hAreg := hD.region.attr
  obtain ⟨-, hY, htrap, -⟩ := G.attractorCorrect X i D hX hD.1
  refine ⟨⟨_, hAreg.dominion hX⟩, hY, ?_⟩
  -- winning in `X \ A` lifts to winning in `X`
  have hlift : ∀ v ∈ X \ A, ∀ k, G.Wins (X \ A) k v → G.Wins X k v := by
    intro v hv k ⟨σ', hσ'⟩
    have hs := G.zielonkaAux_strong _ (X \ A) rfl hY
    have hvk : v ∈ (G.zielonkaAux (X \ A)).win k := by
      have : v ∈ _ ∪ _ := (hs.cover' k).symm ▸ hv
      refine this.resolve_right fun h => ?_
      exact G.not_winsFrom_both hσ' ((hs.region k.opp).winsFrom hY h)
    rcases Player.eq_or_eq_opp k i with rfl | rfl
    · exact ⟨_, (hAreg.extend (hs.region k)).winsFrom hX (Or.inr hvk)⟩
    · exact ⟨_, (Game.Region.of_trap htrap (hs.region i.opp)).winsFrom hX hvk⟩
  intro v hv j
  refine ⟨fun h => ?_, hlift v hv j⟩
  rcases G.wins_or_wins hY hv j with h' | h'
  · exact h'
  · exact ((G.wins_opp_iff hX hv.1 j).1 (hlift v hv _ h') h).elim

/-! ### Certification -/

theorem Game.isProgressMeasure_dominion [Finite V] (G : Game V) {X : Set V} {C : Codomain M}
    {D : Set V} {μ : V → M} {σ : Strategy V} (hX : G.IsSubgame X)
    (h : G.IsProgressMeasure X C D μ σ) : G.IsDominion X .zero D σ :=
  ⟨h.1, fun v hv => G.progressMeasureSound X C D μ σ hX h v hv,
    fun _ hv _ hs => (G.step_prog h hv hs).1⟩

/-- Certification is sound (headline). -/
theorem Game.certificationSound [Finite V] (G : Game V) (X : Set V) (i : Player)
    (C : Codomain M) (D : Set V) (μ : V → M) (σ : Strategy V) :
    G.CertificationSound X i C D μ σ := by
  intro hX h
  obtain ⟨hDX, hwin, hcl⟩ :=
    (G.forPlayer i).isProgressMeasure_dominion ((G.forPlayer_isSubgame i X).2 hX) h
  refine ⟨hDX, fun v hv => (G.forPlayer_winsFrom X i σ v).1 (hwin v hv), fun v hv w hs => ?_⟩
  exact hcl v hv w (by rw [G.forPlayer_step]; exact hs)

/-- The certified set is the greatest progress-measure domain (headline). -/
theorem Game.certifiedSetGreatest (G : Game V) (X : Set V) (C : Codomain M) (μ : V → M) :
    G.CertifiedSetGreatest X C μ := by
  classical
  refine ⟨?_, fun D σ h v hv => ⟨D, σ, h, hv⟩⟩
  have hw : ∀ v, ∃ τ : Strategy V, v ∈ G.certifiedSet X C μ →
      ∃ D, G.IsProgressMeasure X C D μ τ ∧ v ∈ D := by
    intro v
    by_cases hv : v ∈ G.certifiedSet X C μ
    · obtain ⟨D, τ, h, hvD⟩ := hv
      exact ⟨τ, fun _ => ⟨D, h, hvD⟩⟩
    · exact ⟨id, fun h => absurd h hv⟩
  choose f hf using hw
  refine ⟨fun v => f v v, fun v hv => ?_, fun v hv ho => ?_, fun v hv ho w hw he => ?_⟩
  · obtain ⟨D, hD, hvD⟩ := hf v hv
    exact hD.1 hvD
  · obtain ⟨D, hD, hvD⟩ := hf v hv
    obtain ⟨h1, h2, h3⟩ := hD.2.1 v hvD ho
    exact ⟨⟨D, f v, hD, h1⟩, h2, h3⟩
  · obtain ⟨D, hD, hvD⟩ := hf v hv
    obtain ⟨h1, h2⟩ := hD.2.2 v hvD ho w hw he
    exact ⟨⟨D, f v, hD, h1⟩, h2⟩

/-- Both players' certified sets can be removed in one round (headline). -/
theorem Game.simultaneousRemoval [Finite V] (G : Game V) (X : Set V) (C₀ : Codomain M)
    (D₀ : Set V) (μ₀ : V → M) (σ₀ : Strategy V) (C₁ : Codomain N) (D₁ : Set V) (μ₁ : V → N)
    (σ₁ : Strategy V) : G.SimultaneousRemoval X C₀ D₀ μ₀ σ₀ C₁ D₁ μ₁ σ₁ := by
  intro hX h₀ h₁
  have hA := (G.certificationSound X .zero C₀ D₀ μ₀ σ₀ hX h₀).region.attr
  have hD₁ := (G.certificationSound X .one C₁ D₁ μ₁ σ₁ hX h₁).region
  have hdisj : Disjoint (G.attr X .zero D₀) D₁ := Game.Region.disjoint (i := .zero) hA hD₁
  refine ⟨fun v hv => ⟨h₁.1 hv, Set.disjoint_right.1 hdisj hv⟩, h₁.2.1,
    fun v hv ho w hw he => h₁.2.2 v hv ho w hw.1 he⟩

/-! ### The algorithm -/

theorem Game.algInvInit (G : Game V) : G.AlgInvInit := by
  refine ⟨fun v _ => ?_, fun i v => ?_, fun v _ i => Iff.rfl⟩
  · obtain ⟨w, hw⟩ := G.total v; exact ⟨w, Set.mem_univ _, hw⟩
  · simp [AlgState.init]

theorem Game.algInvStep [Finite V] (G : Game V) (s s' : AlgState V) : G.AlgInvStep s s' := by
  intro hinv ⟨i, M, C, μ, σ, D, _, hpm, hs'⟩
  subst hs'
  obtain ⟨hX, hwon, hrest⟩ := hinv
  have hdom := G.certificationSound s.rest i C D μ σ hX hpm
  obtain ⟨⟨τ, hAdom⟩, hY, hiii⟩ := G.dominionRemoval s.rest i D σ hX hdom
  set X := s.rest with hXdef
  set A := G.attr X i D with hAdef
  have hAX : A ⊆ X := hAdom.1
  have hAwin : ∀ v ∈ A, G.Wins Set.univ i v := fun v hv =>
    (hrest v (hAX hv) i).1 ⟨τ, hAdom.2.1 v hv⟩
  refine ⟨hY, fun j v => ?_, fun v hv j => (hiii v hv j).symm.trans (hrest v hv.1 j)⟩
  show v ∈ (if j = i then s.won j ∪ A else s.won j) ↔ v ∉ X \ A ∧ G.Wins Set.univ j v
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl]
    constructor
    · rintro (h | h)
      · obtain ⟨h1, h2⟩ := (hwon j v).1 h
        exact ⟨fun h' => h1 h'.1, h2⟩
      · exact ⟨fun h' => h'.2 h, hAwin v h⟩
    · rintro ⟨h1, h2⟩
      by_cases hvX : v ∈ X
      · exact Or.inr (by by_contra hvA; exact h1 ⟨hvX, hvA⟩)
      · exact Or.inl ((hwon j v).2 ⟨hvX, h2⟩)
  · rw [if_neg hj]
    have hj' : j = i.opp := Player.ne_iff.mp hj
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := (hwon j v).1 h
      exact ⟨fun h' => h1 h'.1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hvX : v ∈ X
      · have hvA : v ∈ A := by by_contra hvA; exact h1 ⟨hvX, hvA⟩
        subst hj'
        exact (G.not_wins_both (hAwin v hvA) h2).elim
      · exact (hwon j v).2 ⟨hvX, h2⟩

theorem Game.completionCorrect [Finite V] (G : Game V) (s : AlgState V) (r : Player → Set V) :
    G.CompletionCorrect s r := by
  intro hinv ⟨i, T, _, _, val, C, ν, hC, hrepr, hleast, hr⟩
  subst hr
  obtain ⟨hX, hwon, hrest⟩ := hinv
  have hcorr := (G.forPlayer i).chainLiftingCorrect s.rest C val
    ((G.forPlayer_isSubgame i s.rest).2 hX) hC hrepr
  have key : ∀ v, ν v ≠ ⊤ ↔ G.Wins s.rest i v := fun v =>
    (hcorr.2 ν hleast v).trans (exists_congr fun σ => G.forPlayer_winsFrom s.rest i σ v)
  intro j v
  show v ∈ (if j = i then s.won j ∪ {v | v ∈ s.rest ∧ ν v ≠ ⊤}
    else s.won j ∪ {v | v ∈ s.rest ∧ ν v = ⊤}) ↔ _
  have hout : v ∉ s.rest → (v ∈ s.won j ∪ {v | v ∈ s.rest ∧ ν v ≠ ⊤} ∨
      v ∈ s.won j ∪ {v | v ∈ s.rest ∧ ν v = ⊤} → G.Wins Set.univ j v) := by
    rintro hvX ((h | h) | (h | h))
    · exact ((hwon j v).1 h).2
    · exact absurd h.1 hvX
    · exact ((hwon j v).1 h).2
    · exact absurd h.1 hvX
  by_cases hvX : v ∈ s.rest
  · have hnw : v ∉ s.won j := fun h => ((hwon j v).1 h).1 hvX
    by_cases hj : j = i
    · rw [if_pos hj, Set.mem_union, Set.mem_setOf_eq, or_iff_right hnw, and_iff_right hvX,
        key v, hj]
      exact hrest v hvX i
    · have hj' : j = i.opp := Player.ne_iff.mp hj
      rw [if_neg hj, Set.mem_union, Set.mem_setOf_eq, or_iff_right hnw, and_iff_right hvX,
        ← hrest v hvX j, hj', G.wins_opp_iff hX hvX i, ← key v, not_not]
  · refine ⟨fun h => hout hvX ?_, fun h => ?_⟩
    · split_ifs at h
      · exact Or.inl h
      · exact Or.inr h
    · have : v ∈ s.won j := (hwon j v).2 ⟨hvX, h⟩
      split_ifs
      · exact Or.inl this
      · exact Or.inl this

theorem Game.algInv_of_run [Finite V] (G : Game V) {s : AlgState V}
    (h : Relation.ReflTransGen G.RemovalStep AlgState.init s) : G.AlgInv s := by
  induction h with
  | refl => exact G.algInvInit
  | tail _ hst ih => exact G.algInvStep _ _ ih hst

/-- End-to-end correctness (headline). -/
theorem Game.twoSidedCorrect [Finite V] (G : Game V) : G.TwoSidedCorrect :=
  fun _ _ hrun hc => G.completionCorrect _ _ (G.algInv_of_run hrun) hc

/-- Every removal step strictly shrinks the undecided subgame (headline). -/
theorem Game.removalShrinks (G : Game V) (s s' : AlgState V) : G.RemovalShrinks s s' := by
  rintro ⟨i, M, C, μ, σ, D, ⟨v, hv⟩, hpm, rfl⟩
  refine ⟨Set.sdiff_subset, fun hsub => ?_⟩
  exact (hsub (hpm.1 hv)).2 (G.subset_attr s.rest i D hv)

/-- At most `|V|` removal steps (headline). -/
theorem Game.removalBound [Finite V] (G : Game V) : G.RemovalBound := by
  intro run N h0 hstep
  have : ∀ k ≤ N, (run k).rest.ncard + k ≤ Nat.card V := by
    intro k
    induction k with
    | zero => intro _; rw [h0]; simp [AlgState.init, Set.ncard_univ]
    | succ k ih =>
      intro hk
      have hlt := Set.ncard_lt_ncard (G.removalShrinks _ _ (hstep k (by omega)))
        (Set.toFinite _)
      have := ih (by omega)
      omega
  have := this N le_rfl
  omega

end ParityGame

end TwoSidedAlgorithmProofs
