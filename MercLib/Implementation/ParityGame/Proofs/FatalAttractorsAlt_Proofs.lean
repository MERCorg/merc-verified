module

public import MercLib.Implementation.ParityGame.FatalAttractorsAlt
public import Mathlib.Data.Set.Card
import all MercLib.Util.Proofs.While_Proofs
import all MercLib.Theory.ParityGame.Proofs.Game_Proofs
import all MercLib.Theory.ParityGame.Proofs.Attractor_Proofs
import all MercLib.Theory.ParityGame.Proofs.FatalAttractor_Proofs
import all MercLib.Implementation.ParityGame.Proofs.FatalAttractor_Proofs

open Cslib (ωSequence)

@[expose] public section

namespace MercLib.ParityGame

/-! Machine-generated; may be freely edited or regenerated. -/

variable {V : Type*}

/-! ## Attractors -/

/-- The attractor is contained in every set that contains the target and is closed under the
    attractor step. -/
private theorem Game.attr_subset_of_closed (G : Game V) (X : Set V) (i : Player) {U S : Set V}
    (hU : U ⊆ S)
    (hcl : ∀ v ∈ X, ((G.owner v = i ∧ ∃ w ∈ S, G.edge v w) ∨
      (G.owner v ≠ i ∧ ∀ w ∈ X, G.edge v w → w ∈ S)) → v ∈ S) :
    G.attr X i U ⊆ S := by
  rintro v ⟨k, hk⟩
  induction k generalizing v with
  | zero => exact hU hk
  | succ k ih =>
    simp only [Game.attrStage, Set.mem_union, Set.mem_ofPred_eq] at hk
    rcases hk with hk | ⟨hvX, ⟨ho, w, hw, he⟩ | ⟨ho, hall⟩⟩
    · exact ih hk
    · exact hcl v hvX (Or.inl ⟨ho, w, ih hw, he⟩)
    · exact hcl v hvX (Or.inr ⟨ho, fun w hw he => ih (hall w hw he)⟩)

/-- The `i`-attractor of `(X \ Y) ∪ Z` in `X` is `X \ Y` together with the `i`-attractor of `Z` in
    the subgame `Y`, when `Y ⊆ X` is a trap for `i` and `Z ⊆ Y`. -/
private theorem Game.attr_trap_eq (G : Game V) [Finite V] {X Y Z : Set V} (i : Player)
    (hYX : Y ⊆ X) (hZY : Z ⊆ Y)
    (htrap : ∀ v ∈ Y, G.owner v = i → ∀ w ∈ X, G.edge v w → w ∈ Y) :
    G.attr X i ((X \ Y) ∪ Z) = (X \ Y) ∪ G.attr Y i Z := by
  have hAY : G.attr Y i Z ⊆ Y := G.attr_subset Y i Z hZY
  apply Set.Subset.antisymm
  · refine G.attr_subset_of_closed X i
      (Set.union_subset_union_right _ (G.subset_attr Y i Z)) ?_
    intro v hvX hcase
    by_cases hvY : v ∈ Y
    · right
      rcases hcase with ⟨ho, w, hw, he⟩ | ⟨ho, hall⟩
      · have hwX : w ∈ X := by
          rcases hw with hw | hw
          · exact hw.1
          · exact hYX (hAY hw)
        have hwY := htrap v hvY ho w hwX he
        have hwA : w ∈ G.attr Y i Z := by
          rcases hw with hw | hw
          · exact absurd hwY hw.2
          · exact hw
        exact G.mem_attr_of_owner Y i Z hvY ho he hwA
      · refine G.mem_attr_of_opp Y i Z hvY ho fun w hwY he => ?_
        rcases hall w (hYX hwY) he with hw | hw
        · exact absurd hwY hw.2
        · exact hw
    · exact Or.inl ⟨hvX, hvY⟩
  · refine Set.union_subset (fun v hv => G.subset_attr X i _ (Or.inl hv)) ?_
    refine G.attr_subset_of_closed Y i (fun v hv => G.subset_attr X i _ (Or.inr hv)) ?_
    intro v hvY hcase
    rcases hcase with ⟨ho, w, hw, he⟩ | ⟨ho, hall⟩
    · exact G.mem_attr_of_owner X i _ (hYX hvY) ho he hw
    · refine G.mem_attr_of_opp X i _ (hYX hvY) ho fun w hwX he => ?_
      by_cases hwY : w ∈ Y
      · exact hall w hwY he
      · exact G.subset_attr X i _ (Or.inl ⟨hwX, hwY⟩)

/-- The attractor update of the fixed loop is the refinement inside the subgame `Y`. -/
theorem Game.subgameAttrCorrect (G : Game V) [Finite V] (X Y W : Set V) (i : Player) :
    G.SubgameAttrCorrect X Y W i := by
  intro hYX hWY htrap
  have hsplit : X \ W = (X \ Y) ∪ (Y \ W) := by
    ext v
    constructor
    · rintro ⟨hvX, hvW⟩
      by_cases hvY : v ∈ Y
      · exact Or.inr ⟨hvY, hvW⟩
      · exact Or.inl ⟨hvX, hvY⟩
    · rintro (⟨hvX, hvY⟩ | ⟨hvY, hvW⟩)
      · exact ⟨hvX, fun h => hvY (hWY h)⟩
      · exact ⟨hYX hvY, hvW⟩
  rw [hsplit, G.attr_trap_eq i hYX Set.sdiff_subset htrap]
  ext v
  constructor
  · rintro ⟨hvX, hv⟩
    simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hv
    exact ⟨hv.1 hvX, hv.2⟩
  · rintro ⟨hvY, hv⟩
    refine ⟨hYX hvY, ?_⟩
    rintro (⟨-, hvY'⟩ | hv')
    · exact hvY' hvY
    · exact hv hv'

/-! ## The region found by the fixed loop -/

private theorem Player.eq_opp_of_ne {a b : Player} (h : a ≠ b) : a = b.opp := by
  cases a <;> cases b <;> first | exact absurd rfl h | rfl

open scoped Classical in
/-- The strategy set by `acceptAlt` before closing under the attractor. -/
private noncomputable def Game.altStrat (G : Game V) (X : Set V) (j : ℕ) (U R A Y S : Set V)
    (τ : Strategy V) : Strategy V := fun v =>
  if v ∈ Y \ S ∧ G.owner v = Player.ofPrio j then
    if v ∈ U then
      if h : ∃ w ∈ X, G.edge v w ∧ w ∈ Y then h.choose else τ v
    else G.mattrStrategy R (Player.ofPrio j) j A v
  else τ v

private theorem Game.acceptAlt_eq (G : Game V) (X : Set V) (j : ℕ) (U R A Y : Set V)
    (r : Solution V) :
    G.acceptAlt X j U R A Y r =
      G.attrWithTau X (Player.ofPrio j)
        { win := Function.update r.win (Player.ofPrio j) (r.win (Player.ofPrio j) ∪ Y)
          strat := Function.update r.strat (Player.ofPrio j)
            (G.altStrat X j U R A Y (r.win (Player.ofPrio j)) (r.strat (Player.ofPrio j))) } :=
  rfl

/-- The fixed step: a closed winning region `S` of `α = Player.ofPrio j`, extended by a set
    `Y = AttrMinRank((U ∪ S) ∩ R, α, R, j)` of the priority-`j` nodes `U`, where `Y ⊆ X` is a subgame
    that the opponent cannot leave, is a closed winning region for the strategy `altStrat`. -/
private theorem Game.isClosedWinningRegion_alt (G : Game V) (X : Set V) (hsub : G.IsSubgame X)
    {j : ℕ} {U R S Y : Set V} {τ : Strategy V}
    (hS : G.IsClosedWinningRegion X (Player.ofPrio j) S τ) (hUj : ∀ u ∈ U, G.prio u = j)
    (hY : G.attrMinRank R (Player.ofPrio j) j ((U ∪ S) ∩ R) = Y) (hYX : Y ⊆ X)
    (hYsub : ∀ v ∈ Y, G.owner v = Player.ofPrio j → ∃ w ∈ X, G.edge v w ∧ w ∈ Y)
    (hYtrap : ∀ v ∈ Y, G.owner v ≠ Player.ofPrio j → ∀ w ∈ X, G.edge v w → w ∈ Y) :
    G.IsClosedWinningRegion X (Player.ofPrio j) (S ∪ Y)
      (G.altStrat X j U R ((U ∪ S) ∩ R) Y S τ) := by
  set α := Player.ofPrio j
  set A := (U ∪ S) ∩ R
  set M := G.mattr R α j A
  set σ := G.altStrat X j U R A Y S τ
  have hAY : A ⊆ Y := fun v hv => hY ▸ Or.inl hv
  have hMY : M ⊆ Y := fun v hv => hY ▸ Or.inr hv
  have hYR : Y ⊆ R := by
    rw [← hY]
    exact Set.union_subset Set.inter_subset_right (G.mattr_subset_X R α j A)
  -- A node of `Y \ S` outside `U` lies in the monotone attractor.
  have hM : ∀ v ∈ Y, v ∉ S → v ∉ U → v ∈ M := by
    intro v hv hvS hvU
    rw [← hY] at hv
    rcases hv with ⟨hvUS, -⟩ | hv
    · rcases hvUS with h | h
      · exact absurd h hvU
      · exact absurd h hvS
    · exact hv
  have hσS : ∀ v ∈ S, σ v = τ v := fun v hv => by simp [σ, Game.altStrat, hv]
  have hσM : ∀ v ∈ Y, v ∉ S → G.owner v = α → v ∉ U → σ v = G.mattrStrategy R α j A v :=
    fun v hv hvS ho hvU => by
      simp only [σ, Game.altStrat]
      rw [ite_eq_left ⟨⟨hv, hvS⟩, ho⟩, ite_eq_right hvU]
  have hlandY : ∀ v, ∀ w, w ∈ G.mattrStage R α j A (G.mattrRank R α j A v - 1) → w ∈ Y :=
    fun _ w hw => hMY ⟨_, hw⟩
  refine G.isClosedWinningRegion_of_reach X α hsub hS (Set.union_subset hS.1 hYX)
    (fun v hv _ => hσS v hv) ?_ ?_ ?_
  · intro v hv ho
    by_cases hvS : v ∈ S
    · rw [hσS v hvS]
      exact ⟨(hS.2.1 v hvS ho).1, Or.inl (hS.2.1 v hvS ho).2⟩
    have hvY : v ∈ Y := hv.resolve_left hvS
    by_cases hvU : v ∈ U
    · have hex := hYsub v hvY ho
      have hσv : σ v = hex.choose := by
        simp only [σ, Game.altStrat]
        rw [ite_eq_left ⟨⟨hvY, hvS⟩, ho⟩, ite_eq_left hvU, dite_eq_left hex]
      obtain ⟨-, he, hw⟩ := hex.choose_spec
      rw [hσv]
      exact ⟨he, Or.inr hw⟩
    · rw [hσM v hvY hvS ho hvU]
      obtain ⟨-, hme, hm⟩ := G.mattrStrategy_spec R α j A (hM v hvY hvS hvU) ho
      refine ⟨hme, Or.inr ?_⟩
      rcases hm with hm | hm
      · exact hlandY v _ hm
      · exact hAY hm
  · intro v hv ho w hw he
    by_cases hvS : v ∈ S
    · exact Or.inl (hS.2.2.1 v hvS ho w hw he)
    · exact Or.inr (hYtrap v (hv.resolve_left hvS) ho w hw he)
  · intro p hp hW
    by_cases hreach : ∃ n, p n ∈ S
    · exact Or.inl hreach
    right
    push Not at hreach
    have hYn : ∀ n, p n ∈ Y := fun n => (hW n).resolve_left (hreach n)
    -- Every move from a node of `M` goes to a lower stage or to `U`.
    have hnext : ∀ N, p N ∉ U →
        p (N + 1) ∈ G.mattrStage R α j A (G.mattrRank R α j A (p N) - 1) ∨ p (N + 1) ∈ U := by
      intro N hU
      have hmN := hM _ (hYn N) (hreach N) hU
      obtain ⟨-, -, he, hσ⟩ := hp N
      have hland : p (N + 1) ∈ G.mattrStage R α j A (G.mattrRank R α j A (p N) - 1) ∪ A := by
        by_cases ho : G.owner (p N) = α
        · rw [hσ ho, hσM _ (hYn N) (hreach N) ho hU]
          exact (G.mattrStrategy_spec R α j A hmN ho).2.2
        · obtain ⟨-, -, hcase⟩ := G.mem_mpre_of_mattr R α j A hmN
          rcases hcase with ⟨ho', -⟩ | ⟨-, hall⟩
          · exact absurd ho' ho
          · exact hall _ (hYR (hYn (N + 1))) he
      rcases hland with hm | ⟨hm | hm, -⟩
      · exact Or.inl hm
      · exact Or.inr hm
      · exact absurd hm (hreach (N + 1))
    -- `U` is visited infinitely often.
    have hvisit : ∀ r N, G.mattrRank R α j A (p N) = r → ∃ n, N ≤ n ∧ p n ∈ U := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro N hr
        by_cases hU : p N ∈ U
        · exact ⟨N, le_rfl, hU⟩
        rcases hnext N hU with hm | hm
        · have hlt : G.mattrRank R α j A (p (N + 1)) < r := by
            have hle := (G.mattrRank_spec R α j A ⟨_, hm⟩).2.2 _ hm
            have hpos := (G.mattrRank_spec R α j A (hM _ (hYn N) (hreach N) hU)).1
            omega
          obtain ⟨n, hn, hnU⟩ := ih _ hlt (N + 1) rfl
          exact ⟨n, by omega, hnU⟩
        · exact ⟨N + 1, by omega, hm⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · show ∃ᶠ k in Filter.atTop, G.prio (p k) = j
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn, hU⟩ := hvisit _ N rfl
      exact ⟨n, hn, hUj _ hU⟩
    · rintro m (hm : ∃ᶠ k in Filter.atTop, G.prio (p k) = m)
      obtain ⟨k, hk⟩ := hm.exists
      rw [← hk]
      by_cases hU : p k ∈ U
      · exact (hUj _ hU).le
      · exact G.prio_le_of_mattr R α j A (hM _ (hYn k) (hreach k) hU)

/-- `acceptAlt` preserves the invariant and extends the solution. -/
private theorem Game.acceptAlt_inv [Finite V] (G : Game V) (X : Set V) (hsub : G.IsSubgame X)
    {j : ℕ} {U R Y : Set V} {r : Solution V} (hr : G.ImplInv X r) (hUj : ∀ u ∈ U, G.prio u = j)
    (hY : G.attrMinRank R (Player.ofPrio j) j ((U ∪ r.win (Player.ofPrio j)) ∩ R) = Y)
    (hYX : Y ⊆ X)
    (hYsub : ∀ v ∈ Y, G.owner v = Player.ofPrio j → ∃ w ∈ X, G.edge v w ∧ w ∈ Y)
    (hYtrap : ∀ v ∈ Y, G.owner v ≠ Player.ofPrio j → ∀ w ∈ X, G.edge v w → w ∈ Y) :
    G.ImplInv X (G.acceptAlt X j U R ((U ∪ r.win (Player.ofPrio j)) ∩ R) Y r) ∧
      r.Extends (G.acceptAlt X j U R ((U ∪ r.win (Player.ofPrio j)) ∩ R) Y r) := by
  set α := Player.ofPrio j
  set r1 : Solution V :=
    { win := Function.update r.win α (r.win α ∪ Y)
      strat := Function.update r.strat α
        (G.altStrat X j U R ((U ∪ r.win α) ∩ R) Y (r.win α) (r.strat α)) }
  have h1 : G.SoundPartial X r1 := by
    intro k
    by_cases hk : k = α
    · subst hk
      simpa [r1] using G.isClosedWinningRegion_alt X hsub (hr.1 _) hUj hY hYX hYsub hYtrap
    · simpa [r1, Function.update_of_ne hk] using hr.1 k
  have hext1 : r.Extends r1 := by
    intro k
    by_cases hk : k = α
    · subst hk; simp [r1]
    · simp [r1, Function.update_of_ne hk]
  rw [G.acceptAlt_eq]
  obtain ⟨hs, hcl, hext⟩ := G.attrWithTau_sound X hsub α h1
  refine ⟨⟨hs, fun k => ?_⟩, hext1.trans hext⟩
  by_cases hk : k = α
  · subst hk; exact hcl
  · have hw : r1.win k = r.win k := Function.update_of_ne hk _ _
    rw [G.attrWithTau_win_ne X hk, hw]
    exact hr.2 k

/-! ## The loops -/

open scoped Classical in
/-- The `while` loop of the fixed version for priority `j`, with state `(R, Y)`, ends with
    `AttrMinRank(T ∩ R, α, R, j) = Y` and `Y` the complement of an opponent attractor: `Y` shrinks
    strictly in every iteration. -/
private theorem Game.altLoop_post [Finite V] (G : Game V) (X : Set V) (j : ℕ) (T : Set V)
    (g : Unit → Set V × Set V → Id (ForInStep (Set V × Set V)))
    (hg : ∀ R Y, (g () (R, Y)).run =
      if G.attrMinRank R (Player.ofPrio j) j (T ∩ R) ≠ Y then
        .yield (Y, X \ G.attr X (Player.ofPrio j).opp
          (X \ G.attrMinRank Y (Player.ofPrio j) j (T ∩ Y)))
      else .done (R, Y)) :
    ∀ s : Set V × Set V,
      s.2 = X \ G.attr X (Player.ofPrio j).opp
        (X \ G.attrMinRank s.1 (Player.ofPrio j) j (T ∩ s.1)) →
      G.attrMinRank (forIn Lean.Loop.mk s g).run.1 (Player.ofPrio j) j
          (T ∩ (forIn Lean.Loop.mk s g).run.1) = (forIn Lean.Loop.mk s g).run.2 ∧
        (forIn Lean.Loop.mk s g).run.2 = X \ G.attr X (Player.ofPrio j).opp
          (X \ G.attrMinRank (forIn Lean.Loop.mk s g).run.1 (Player.ofPrio j) j
            (T ∩ (forIn Lean.Loop.mk s g).run.1)) := by
  set α := Player.ofPrio j
  refine MercLib.Util.whileInduction g
    (InvImage.wf (fun s : Set V × Set V => s.1.ncard) Nat.lt_wfRel.wf)
    (fun s => s.2 = X \ G.attr X α.opp (X \ G.attrMinRank s.1 α j (T ∩ s.1)))
    (fun s => G.attrMinRank s.1 α j (T ∩ s.1) = s.2 ∧
      s.2 = X \ G.attr X α.opp (X \ G.attrMinRank s.1 α j (T ∩ s.1))) ?_
  rintro ⟨R, Y⟩ hInv
  rw [hg]
  by_cases hc : G.attrMinRank R α j (T ∩ R) ≠ Y
  · simp only [eq_true hc, ↓reduceIte]
    refine ⟨by trivial, ?_⟩
    show Set.ncard Y < Set.ncard R
    change Y = _ at hInv
    have hXsR : G.attrMinRank R α j (T ∩ R) ⊆ R :=
      Set.union_subset Set.inter_subset_right (G.mattr_subset_X R α j _)
    have hYXs : Y ⊆ G.attrMinRank R α j (T ∩ R) := by
      intro v hv
      rw [hInv] at hv
      by_contra hn
      exact hv.2 (G.subset_attr X α.opp _ ⟨hv.1, hn⟩)
    exact Set.ncard_lt_ncard
      (Set.ssubset_of_ssubset_of_subset (hYXs.ssubset_of_ne (Ne.symm hc)) hXsR) (Set.toFinite _)
  · simp only [eq_false hc, ↓reduceIte]
    exact ⟨not_not.mp hc, hInv⟩

open scoped Classical in
/-- Contract for the fixed `fatal_attractors_generic`. -/
theorem Game.fatalAttractorsAltSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : G.FatalAttractorsAltSound X js r := by
  intro hsub hr
  obtain ⟨hs0, -, he0⟩ := G.attrWithTau_sound X hsub .zero hr
  obtain ⟨hs1, hcl1, he1⟩ := G.attrWithTau_sound X hsub .one hs0
  have hinv : G.ImplInv X (G.attrWithTau X .one (G.attrWithTau X .zero r)) := by
    refine ⟨hs1, fun k => ?_⟩
    cases k with
    | one => exact hcl1
    | zero =>
      rw [G.attrWithTau_win_ne X (by decide : Player.zero ≠ Player.one),
        G.attrWithTau_win_self]
      exact G.attr_attr_subset X _ _
  unfold Game.fatalAttractorsAlt
  dsimp only [Id.run_bind]
  generalize hres : (forIn (m := Id) js _ _).run = res
  have key : G.ImplInv X res ∧
      (G.attrWithTau X .one (G.attrWithTau X .zero r)).Extends res := by
    rw [← hres]
    refine MercLib.Util.forInList_induction _
      (fun s => G.ImplInv X s ∧ (G.attrWithTau X .one (G.attrWithTau X .zero r)).Extends s) ?_
      _ _ ⟨hinv, Solution.Extends.refl _⟩
    rintro j s ⟨hs, hes⟩
    set α := Player.ofPrio j
    set U := {u | u ∈ X ∧ G.prio u = j} \ s.win α.opp
    set T := U ∪ s.win α
    have hbody : ∀ w : Set V × Set V, G.attrMinRank w.1 α j (T ∩ w.1) = w.2 →
        w.2 = X \ G.attr X α.opp (X \ G.attrMinRank w.1 α j (T ∩ w.1)) →
        G.ImplInv X (G.acceptAlt X j U w.1 (T ∩ w.1) w.2 s) ∧
          (G.attrWithTau X .one (G.attrWithTau X .zero r)).Extends
            (G.acceptAlt X j U w.1 (T ∩ w.1) w.2 s) := by
      rintro ⟨R, Y⟩ hpost hY
      simp only at hpost hY
      have hcorr := G.attractorCorrect X α.opp (X \ G.attrMinRank R α j (T ∩ R)) hsub
        Set.sdiff_subset
      have hYX : Y ⊆ X := by rw [hY]; exact Set.sdiff_subset
      have hYsub : ∀ v ∈ Y, G.owner v = α → ∃ w ∈ X, G.edge v w ∧ w ∈ Y := by
        intro v hv _
        rw [hY] at hv ⊢
        obtain ⟨w, hw, he⟩ := hcorr.2.1 v hv
        exact ⟨w, hw.1, he, hw⟩
      have hYtrap : ∀ v ∈ Y, G.owner v ≠ α → ∀ w ∈ X, G.edge v w → w ∈ Y := by
        intro v hv ho w hw he
        rw [hY] at hv ⊢
        exact ⟨hw, hcorr.2.2.1 v hv (Player.eq_opp_of_ne ho) w hw he⟩
      obtain ⟨hinv', hext'⟩ := G.acceptAlt_inv X hsub hs (fun u hu => hu.1.2) hpost hYX hYsub
        hYtrap
      exact ⟨hinv', hes.trans hext'⟩
    obtain ⟨hpost, hY⟩ := G.altLoop_post X j T
      (fun _ st => if G.attrMinRank st.1 α j (T ∩ st.1) ≠ st.2 then
        pure (ForInStep.yield (st.2, X \ G.attr X α.opp (X \ G.attrMinRank st.2 α j (T ∩ st.2))))
        else pure (ForInStep.done (st.1, st.2)))
      (fun _ _ => rfl)
      (X, X \ G.attr X α.opp (X \ G.attrMinRank X α j (T ∩ X))) rfl
    exact hbody _ hpost hY
  exact ⟨key.1.1, (he0.trans he1).trans key.2⟩

/-! ## The counterexample -/

private instance (a b : CexNode) : Decidable (cexGame.edge a b) :=
  inferInstanceAs (Decidable ((a, b) ∈ cexEdges))

private instance : Fintype CexNode :=
  ⟨{.v, .u, .w, .z, .d}, fun x => by cases x <;> decide⟩

/-- The monotone attractor is contained in every set closed under `mpre`. -/
private theorem Game.mattr_subset_of_closed (G : Game V) (X : Set V) (i : Player) (c : ℕ)
    (T S : Set V) (h : G.mpre X i c T S ⊆ S) : G.mattr X i c T ⊆ S := by
  rintro v ⟨k, hk⟩
  induction k generalizing v with
  | zero => exact absurd hk (Set.notMem_empty v)
  | succ k ih => exact h (G.mpre_mono X i c T (fun _ hw => ih hw) hk)

/-- In a subgame, the attractor of the empty set is empty. -/
private theorem Game.attr_empty (G : Game V) (X : Set V) (i : Player) (hsub : G.IsSubgame X) :
    G.attr X i ∅ = ∅ := by
  refine Set.eq_empty_of_subset_empty (G.attr_subset_of_closed X i le_rfl ?_)
  rintro v hvX (⟨-, w, hw, -⟩ | ⟨-, hall⟩)
  · exact hw
  · obtain ⟨w, hw, he⟩ := hsub v hvX
    exact hall w hw he

private theorem cexGame_sub : cexGame.IsSubgame Set.univ := fun a _ =>
  let ⟨b, he⟩ := cexGame.total a
  ⟨b, trivial, he⟩

open CexNode in
/-- The trace of the buggy loop on `cexGame` for priority `2`. -/
private theorem cex_trace :
    cexGame.attrMinRank Set.univ .zero 2 ({v, u} ∩ Set.univ) = {v, u, w, z} ∧
    Set.univ \ cexGame.attr Set.univ .one (Set.univ \ {v, u, w, z}) = {v, w, z} ∧
    cexGame.attrMinRank Set.univ .zero 2 ({v, u} ∩ {v, w, z}) = {v} ∧
    ({v, w, z} : Set CexNode) \ cexGame.attr Set.univ .one ({v, w, z} \ {v}) = {v} ∧
    cexGame.attr Set.univ .zero (∅ ∪ {v}) = {v} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `w` reaches `u`, `z` reaches `w`; `d` is not attracted.
    apply Set.Subset.antisymm
    · refine Set.union_subset (fun x hx => by cases x <;> simp_all) ?_
      refine cexGame.mattr_subset_of_closed _ _ _ _ _ ?_
      rintro x ⟨-, -, ⟨ho, y, -, he, hy⟩ | ⟨ho, hall⟩⟩
      · cases x <;> simp_all [cexGame, cexEdges]
      · cases x <;> simp_all [cexGame, cexEdges]
    · have hw : w ∈ cexGame.mattrStage Set.univ .zero 2 ({v, u} ∩ Set.univ) 1 :=
        ⟨trivial, by decide, Or.inl ⟨rfl, u, trivial, by decide, Or.inr (by simp)⟩⟩
      have hz : z ∈ cexGame.mattrStage Set.univ .zero 2 ({v, u} ∩ Set.univ) 2 :=
        ⟨trivial, by decide, Or.inl ⟨rfl, w, trivial, by decide, Or.inl hw⟩⟩
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inl (by simp)
      · exact Or.inr ⟨1, hw⟩
      · exact Or.inr ⟨2, hz⟩
  · -- `Attr₁({d}) = {d, u}`.
    have hA : cexGame.attr Set.univ .one (Set.univ \ {v, u, w, z}) = {d, u} := by
      apply Set.Subset.antisymm
      · refine cexGame.attr_subset_of_closed _ _ (fun x hx => by cases x <;> simp_all) ?_
        rintro x - (⟨ho, y, hy, he⟩ | ⟨ho, hall⟩)
        · cases x <;> simp_all [cexGame, cexEdges]
        · cases x
          · exact absurd (hall w trivial (by decide)) (by simp)
          · simp
          · exact absurd (hall z trivial (by decide)) (by simp)
          · exact absurd (hall w trivial (by decide)) (by simp)
          · simp
      · have hd : d ∈ cexGame.attr Set.univ .one (Set.univ \ {v, u, w, z}) :=
          cexGame.subset_attr _ _ _ (by simp)
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hd
        · exact cexGame.mem_attr_of_owner _ _ _ trivial rfl (by decide) hd
    rw [hA]
    ext x
    cases x <;> simp
  · -- Nothing has an edge into `v`.
    apply Set.Subset.antisymm
    · refine Set.union_subset (fun x hx => by cases x <;> simp_all) ?_
      refine cexGame.mattr_subset_of_closed _ _ _ _ _ ?_
      rintro x ⟨-, -, ⟨-, y, -, he, hy⟩ | ⟨ho, hall⟩⟩
      · cases x <;> cases y <;> simp_all [cexGame, cexEdges]
      · cases x <;> simp_all [cexGame, cexEdges]
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact Or.inl (by simp)
  · -- `Attr₁({w, z}) = {w, z}`: `v` keeps its move to `d`.
    have hA : cexGame.attr Set.univ .one (({v, w, z} : Set CexNode) \ {v}) ⊆ {w, z} := by
      refine cexGame.attr_subset_of_closed _ _ (fun x hx => by cases x <;> simp_all) ?_
      rintro x - (⟨ho, y, hy, he⟩ | ⟨ho, hall⟩)
      · cases x <;> cases y <;> simp_all [cexGame, cexEdges]
      · cases x
        · exact absurd (hall d trivial (by decide)) (by simp)
        · simp_all [cexGame, cexEdges]
        · simp
        · simp
        · simp_all [cexGame, cexEdges]
    ext x
    constructor
    · rintro ⟨hx, hxA⟩
      cases x
      · simp
      · simp at hx
      · exact absurd (cexGame.subset_attr _ _ _ (by simp)) hxA
      · exact absurd (cexGame.subset_attr _ _ _ (by simp)) hxA
      · simp at hx
    · intro hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨by simp, fun h => by simpa using hA h⟩
  · -- Nothing has an edge into `v`.
    apply Set.Subset.antisymm
    · refine cexGame.attr_subset_of_closed _ _ (fun x hx => by simpa using hx) ?_
      rintro x - (⟨ho, y, hy, he⟩ | ⟨ho, hall⟩)
      · cases x <;> simp_all [cexGame, cexEdges]
      · cases x
        · simp
        · exact absurd (hall d trivial (by decide)) (by simp)
        · simp_all [cexGame, cexEdges]
        · simp_all [cexGame, cexEdges]
        · exact absurd (hall d trivial (by decide)) (by simp)
    · exact fun x hx => cexGame.subset_attr _ _ _ (by simpa using hx)

open CexNode in
open scoped Classical in
/-- The buggy loop on `cexGame` puts exactly `v` in the region of player `0`. -/
private theorem cex_result :
    (cexGame.fatalAttractorsAltBuggy Set.univ [2] Solution.empty).win .zero = {v} := by
  have hα : Player.ofPrio 2 = .zero := rfl
  have hr1 : ∀ k, (cexGame.attrWithTau Set.univ .one
      (cexGame.attrWithTau Set.univ .zero Solution.empty)).win k = ∅ := by
    intro k
    cases k
    · rw [cexGame.attrWithTau_win_ne Set.univ (by decide : Player.zero ≠ Player.one),
        cexGame.attrWithTau_win_self]
      exact cexGame.attr_empty _ _ cexGame_sub
    · rw [cexGame.attrWithTau_win_self,
        cexGame.attrWithTau_win_ne Set.univ (by decide : Player.one ≠ Player.zero)]
      exact cexGame.attr_empty _ _ cexGame_sub
  obtain ⟨h1, h2, h3, h4, h5⟩ := cex_trace
  unfold Game.fatalAttractorsAltBuggy
  simp only [List.forIn_cons, List.forIn_nil]
  set r1 := cexGame.attrWithTau Set.univ .one (cexGame.attrWithTau Set.univ .zero Solution.empty)
  set U := {x | x ∈ Set.univ ∧ cexGame.prio x = 2} \ r1.win (Player.ofPrio 2).opp with hUdef
  set T := U ∪ r1.win (Player.ofPrio 2) with hTdef
  have hT : T = {v, u} := by
    rw [hTdef, hUdef, hr1, hr1]
    ext x
    cases x <;> simp [cexGame]
  have hne : ({v, u, w, z} : Set CexNode) ≠ {v, w, z} := fun h => by
    have : u ∈ ({v, w, z} : Set CexNode) := h ▸ (by simp)
    simp at this
  have hloop : (forIn (m := Id) Lean.Loop.mk
      (Set.univ, Set.univ \ cexGame.attr Set.univ (Player.ofPrio 2).opp
        (Set.univ \ cexGame.attrMinRank Set.univ (Player.ofPrio 2) 2 (T ∩ Set.univ)))
      (fun _ st => if cexGame.attrMinRank Set.univ (Player.ofPrio 2) 2 (T ∩ st.1) ≠ st.2 then
        pure (ForInStep.yield (st.2, st.2 \ cexGame.attr Set.univ (Player.ofPrio 2).opp
          (st.2 \ cexGame.attrMinRank Set.univ (Player.ofPrio 2) 2 (T ∩ st.2))))
        else pure (ForInStep.done (st.1, st.2)))).run =
      (({v, w, z} : Set CexNode), ({v} : Set CexNode)) := by
    refine MercLib.Util.whileInduction _
      (InvImage.wf (fun s : Set CexNode × Set CexNode => if s.1 = Set.univ then 1 else 0)
        Nat.lt_wfRel.wf)
      (fun s => s = (Set.univ, {v, w, z}) ∨ s = ({v, w, z}, {v}))
      (fun s => s = ({v, w, z}, {v})) ?_ _ ?_
    · rintro s (rfl | rfl)
      · simp only [hT, hα, Player.opp, h1, ne_eq, hne, not_false_eq_true, ↓reduceIte, h3, h4]
        refine ⟨Or.inr rfl, ?_⟩
        show (if ({v, w, z} : Set CexNode) = Set.univ then 1 else 0) <
          (if (Set.univ : Set CexNode) = Set.univ then 1 else 0)
        have : ({v, w, z} : Set CexNode) ≠ Set.univ := fun h => by
          have : d ∈ ({v, w, z} : Set CexNode) := h ▸ trivial
          simp at this
        simp [this]
      · simp only [hT, hα, h3, ne_eq, not_true_eq_false, ↓reduceIte]
        rfl
    · left
      simp only [hT, hα, Player.opp, h1, h2]
  have hbody : ∀ st : Set CexNode × Set CexNode, st = ({v, w, z}, {v}) →
      (cexGame.acceptAlt Set.univ 2 U Set.univ (T ∩ st.1) st.2 r1).win .zero = {v} := by
    rintro _ rfl
    rw [cexGame.acceptAlt_eq]
    simp only [hα, cexGame.attrWithTau_win_self, Function.update_self, hr1]
    exact h5
  exact hbody _ hloop

/-- The loop before the fix is unsound. -/
theorem Game.fatalAttractorsAltBuggyUnsound : Game.FatalAttractorsAltBuggyUnsound := by
  refine ⟨fun i => ⟨Set.empty_subset _, fun x hx => absurd hx (Set.notMem_empty x),
    fun x hx => absurd hx (Set.notMem_empty x), fun x hx => absurd hx (Set.notMem_empty x)⟩,
    by rw [cex_result]; rfl, fun h => ?_⟩
  have hcl := (h .zero).2.1 .v (by rw [cex_result]; rfl) rfl
  rw [cex_result] at hcl
  obtain ⟨he, hv⟩ := hcl
  rw [Set.mem_singleton_iff.mp hv] at he
  exact absurd he (by decide)

end MercLib.ParityGame
