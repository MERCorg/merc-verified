module

public import MercLib.ParityGame.Implementation
public import MercLib.ParityGame.Proofs.Attractor_Proofs
public import MercLib.ParityGame.Proofs.FatalAttractor_Proofs

open Cslib (ωSequence)

@[expose] public section

namespace MercLib.ParityGame

/-! Machine-generated; may be freely edited or regenerated. -/

variable {V : Type*}

/-! ## Combining closed winning regions -/

/-- A region `W ⊇ S` that is closed under `σ'`, where `σ'` agrees with `σ` on the closed winning
    region `S` and every conforming play inside `W` either reaches `S` or is won, is again a closed
    winning region. -/
theorem Game.isClosedWinningRegion_of_reach (G : Game V) (X : Set V) (i : Player)
    {S W : Set V} {σ σ' : Strategy V} (hsub : G.IsSubgame X)
    (hS : G.IsClosedWinningRegion X i S σ) (hWX : W ⊆ X)
    (hagree : ∀ v ∈ S, G.owner v = i → σ' v = σ v)
    (hown : ∀ v ∈ W, G.owner v = i → G.edge v (σ' v) ∧ σ' v ∈ W)
    (hopp : ∀ v ∈ W, G.owner v ≠ i → ∀ w ∈ X, G.edge v w → w ∈ W)
    (hwin : ∀ p : ωSequence V, G.ConformingPlay X i σ' p → (∀ n, p n ∈ W) →
      (∃ n, p n ∈ S) ∨ G.PlayWonBy i p) :
    G.IsClosedWinningRegion X i W σ' := by
  have hstepW : ∀ a b, a ∈ W → G.Step X i σ' a b → b ∈ W := by
    rintro a b ha ⟨-, hbX, he, hσ⟩
    by_cases ho : G.owner a = i
    · rw [hσ ho]; exact (hown a ha ho).2
    · exact hopp a ha ho b hbX he
  refine ⟨hWX, hown, hopp, fun v hv => ⟨?_, ?_⟩⟩
  · intro w hw
    have hwW : w ∈ W := by
      induction hw with
      | refl => exact hv
      | tail _ hs ih => exact hstepW _ _ ih hs
    have hwX := hWX hwW
    by_cases ho : G.owner w = i
    · obtain ⟨he, hm⟩ := hown w hwW ho
      exact ⟨σ' w, hwX, hWX hm, he, fun _ => rfl⟩
    · obtain ⟨u, huX, he⟩ := hsub w hwX
      exact ⟨u, hwX, huX, he, fun h => absurd h ho⟩
  · intro p hp0 hp
    have hW : ∀ n, p n ∈ W := by
      intro n
      induction n with
      | zero => rw [hp0]; exact hv
      | succ n ih => exact hstepW _ _ ih (hp n)
    rcases hwin p hp hW with ⟨n, hn⟩ | h
    · have hSall : ∀ m, p (n + m) ∈ S := by
        intro m
        induction m with
        | zero => simpa using hn
        | succ m ih =>
          obtain ⟨-, hX', he, hσ⟩ := hp (n + m)
          rw [show n + (m + 1) = n + m + 1 by omega]
          by_cases ho : G.owner (p (n + m)) = i
          · rw [hσ ho, hagree _ ih ho]; exact (hS.2.1 _ ih ho).2
          · exact hS.2.2.1 _ ih ho _ hX' he
      have hconf : G.ConformingPlay X i σ (p.drop n) := by
        intro m
        obtain ⟨h1, h2, h3, h4⟩ := hp (n + m)
        simp only [ωSequence.get_drop, show n + (m + 1) = n + m + 1 by omega]
        exact ⟨h1, h2, h3, fun ho => (h4 ho).trans (hagree _ (hSall m) ho)⟩
      have := (hS.2.2.2 (p n) hn).2 (p.drop n) (by simp [ωSequence.get_drop]) hconf
      exact (G.playWonBy_drop i p n).mp this
    · exact h

/-! ## The ordinary attractor -/

section
variable (G : Game V) (X : Set V) (i : Player)

/-- The attractor of the attractor adds nothing (finite games). -/
theorem Game.attr_attr_subset [Finite V] (S : Set V) :
    G.attr X i (G.attr X i S) ⊆ G.attr X i S := by
  rintro v ⟨k, hk⟩
  induction k generalizing v with
  | zero => exact hk
  | succ k ih =>
    simp only [Game.attrStage, Set.mem_union, Set.mem_ofPred_eq] at hk
    rcases hk with hk | ⟨hvX, ⟨ho, w, hw, he⟩ | ⟨ho, hall⟩⟩
    · exact ih hk
    · exact G.mem_attr_of_owner X i S hvX ho he (ih hw)
    · exact G.mem_attr_of_opp X i S hvX ho fun w hw he => ih (hall w hw he)

open scoped Classical in
/-- Closing a closed winning region under the attractor, with the attractor strategy on the new
    nodes, gives a closed winning region. -/
theorem Game.isClosedWinningRegion_attr [Finite V] (hsub : G.IsSubgame X) {S : Set V}
    {σ : Strategy V} (hS : G.IsClosedWinningRegion X i S σ) :
    G.IsClosedWinningRegion X i (G.attr X i S)
      (fun v => if v ∈ G.attr X i S \ S then G.attrStrategy X i S v else σ v) := by
  have hSX := hS.1
  refine G.isClosedWinningRegion_of_reach X i hsub hS (G.attr_subset X i S hSX)
    (fun v hv _ => by simp [hv]) ?_ ?_ ?_
  · intro v hv ho
    by_cases hvS : v ∈ S
    · simp only [Set.mem_sdiff, hvS, not_true_eq_false, and_false, ite_false]
      exact ⟨(hS.2.1 v hvS ho).1, G.subset_attr X i S (hS.2.1 v hvS ho).2⟩
    · simp only [Set.mem_sdiff, hv, hvS, not_false_eq_true, and_self, ite_true]
      exact (G.attrStrategy_mem X i S hv hvS ho).symm
  · intro v hv ho w hw he
    by_cases hvS : v ∈ S
    · exact G.subset_attr X i S (hS.2.2.1 v hvS ho w hw he)
    · exact G.attr_opp_closed X i S hv hvS ho w hw he
  · intro p hp hW
    left
    obtain ⟨k, hk⟩ := hW 0
    obtain ⟨n, -, hn⟩ := G.reach_of_mem_stage X i S _
      (fun v hv hvS _ => by simp [hv, hvS]) p hp k 0 hk
    exact ⟨n, hn⟩

end

/-! ## Invariant of the implementation -/

/-- The invariant: a sound partial solution whose regions are closed under their attractors. -/
def Game.ImplInv (G : Game V) (X : Set V) (r : Solution V) : Prop :=
  G.SoundPartial X r ∧ ∀ i, G.attr X i (r.win i) ⊆ r.win i

/-- `r'` extends `r`. -/
def Solution.Extends (r r' : Solution V) : Prop := ∀ i, r.win i ⊆ r'.win i

theorem Solution.Extends.refl (r : Solution V) : r.Extends r := fun _ => le_rfl

theorem Solution.Extends.trans {r r' r'' : Solution V} (h : r.Extends r') (h' : r'.Extends r'') :
    r.Extends r'' := fun i => (h i).trans (h' i)

section
variable (G : Game V) (X : Set V)

theorem Game.attrWithTau_win_self (i : Player) (r : Solution V) :
    (G.attrWithTau X i r).win i = G.attr X i (r.win i) := by
  simp [Game.attrWithTau]

theorem Game.attrWithTau_win_ne {i k : Player} (h : k ≠ i) (r : Solution V) :
    (G.attrWithTau X i r).win k = r.win k := by
  simp [Game.attrWithTau, Function.update_of_ne h]

theorem Game.attrWithTau_strat_ne {i k : Player} (h : k ≠ i) (r : Solution V) :
    (G.attrWithTau X i r).strat k = r.strat k := by
  simp [Game.attrWithTau, Function.update_of_ne h]

/-- `AttrDefaultWithTau` keeps the solution sound, closes the region of `i` under its attractor
    and leaves the other player's region alone. -/
theorem Game.attrWithTau_sound [Finite V] (hsub : G.IsSubgame X) (i : Player) {r : Solution V}
    (hr : G.SoundPartial X r) :
    G.SoundPartial X (G.attrWithTau X i r) ∧
      G.attr X i ((G.attrWithTau X i r).win i) ⊆ (G.attrWithTau X i r).win i ∧
      r.Extends (G.attrWithTau X i r) := by
  refine ⟨fun k => ?_, ?_, fun k => ?_⟩
  · by_cases hk : k = i
    · subst hk
      have := G.isClosedWinningRegion_attr X k hsub (hr k)
      simpa [Game.attrWithTau] using this
    · rw [G.attrWithTau_win_ne X hk, G.attrWithTau_strat_ne X hk]
      exact hr k
  · rw [G.attrWithTau_win_self]
    exact G.attr_attr_subset X i _
  · by_cases hk : k = i
    · subst hk; rw [G.attrWithTau_win_self]; exact G.subset_attr X k _
    · rw [G.attrWithTau_win_ne X hk]

end

/-! ## The fatal step -/

open scoped Classical in
/-- The strategy set by `acceptFatal` before closing under the attractor. -/
noncomputable def Game.fatalStrat (G : Game V) (X : Set V) (j : ℕ) (U Y S : Set V)
    (τ : Strategy V) : Strategy V := fun v =>
  if v ∈ Y \ S ∧ G.owner v = Player.ofPrio j then
    if v ∈ U then
      if h : ∃ w ∈ X, G.edge v w ∧ w ∈ Y then h.choose else τ v
    else G.mattrStrategy X (Player.ofPrio j) j (U ∪ S) v
  else τ v

theorem Game.acceptFatal_eq (G : Game V) (X : Set V) (j : ℕ) (U Y : Set V) (r : Solution V) :
    G.acceptFatal X j U Y r =
      G.attrWithTau X (Player.ofPrio j)
        { win := Function.update r.win (Player.ofPrio j) (r.win (Player.ofPrio j) ∪ Y)
          strat := Function.update r.strat (Player.ofPrio j)
            (G.fatalStrat X j U Y (r.win (Player.ofPrio j)) (r.strat (Player.ofPrio j))) } :=
  rfl

section
variable (G : Game V) (X : Set V) (i : Player) (c : ℕ) (T : Set V)

/-- Any strategy agreeing with the monotone attractor strategy at `v` moves from `v` into the
    previous stage or the target. -/
theorem Game.step_of_mattr_of_agree (σ : Strategy V) {v w : V} (hv : v ∈ G.mattr X i c T)
    (hσ : G.owner v = i → σ v = G.mattrStrategy X i c T v) (hs : G.Step X i σ v w) :
    w ∈ G.mattrStage X i c T (G.mattrRank X i c T v - 1) ∪ T := by
  obtain ⟨hvX, hwX, he, hσ'⟩ := hs
  refine G.step_of_mattr X i c T hv ⟨hvX, hwX, he, fun ho => ?_⟩
  rw [hσ' ho, hσ ho]

end

/-- The fatal step: a closed winning region `S` of `α = Player.ofPrio j` that is closed under the
    `α`-attractor, extended by a fatal monotone attractor `Y` of the priority-`j` nodes `U ⊆ Y`
    with target `U ∪ S`, is a closed winning region for the strategy `fatalStrat`. -/
theorem Game.isClosedWinningRegion_fatal [Finite V] (G : Game V) (X : Set V)
    (hsub : G.IsSubgame X) {j : ℕ} {U S : Set V} {τ : Strategy V}
    (hS : G.IsClosedWinningRegion X (Player.ofPrio j) S τ)
    (hSattr : G.attr X (Player.ofPrio j) S ⊆ S) (hUj : ∀ u ∈ U, G.prio u = j)
    (hUY : U ⊆ G.mattr X (Player.ofPrio j) j (U ∪ S)) :
    G.IsClosedWinningRegion X (Player.ofPrio j) (S ∪ G.mattr X (Player.ofPrio j) j (U ∪ S))
      (G.fatalStrat X j U (G.mattr X (Player.ofPrio j) j (U ∪ S)) S τ) := by
  set α := Player.ofPrio j
  set Y := G.mattr X α j (U ∪ S)
  set σ := G.fatalStrat X j U Y S τ
  have hYX : Y ⊆ X := G.mattr_subset_X X α j _
  have hσS : ∀ v ∈ S, σ v = τ v := fun v hv => by
    simp [σ, Game.fatalStrat, hv]
  have hσY : ∀ v ∈ Y, v ∉ S → G.owner v = α → v ∉ U → σ v = G.mattrStrategy X α j (U ∪ S) v :=
    fun v hv hvS ho hvU => by
      simp only [σ, Game.fatalStrat]
      rw [ite_eq_left ⟨⟨hv, hvS⟩, ho⟩, ite_eq_right hvU]
  -- Landing in `stage ∪ (U ∪ S)` but outside `S` means landing in `Y`.
  have hlandY : ∀ v ∈ Y, ∀ w, w ∈ G.mattrStage X α j (U ∪ S) (G.mattrRank X α j (U ∪ S) v - 1) →
      w ∈ Y := fun _ _ w hw => ⟨_, hw⟩
  refine G.isClosedWinningRegion_of_reach X α hsub hS (Set.union_subset hS.1 hYX)
    (fun v hv _ => hσS v hv) ?_ ?_ ?_
  · intro v hv ho
    by_cases hvS : v ∈ S
    · rw [hσS v hvS]
      exact ⟨(hS.2.1 v hvS ho).1, Or.inl (hS.2.1 v hvS ho).2⟩
    have hvY : v ∈ Y := hv.resolve_left hvS
    obtain ⟨hmX, hme, hm⟩ := G.mattrStrategy_spec X α j (U ∪ S) hvY ho
    by_cases hvU : v ∈ U
    · have hex : ∃ w ∈ X, G.edge v w ∧ w ∈ Y := by
        refine ⟨_, hmX, hme, ?_⟩
        rcases hm with hm | hm | hm
        · exact hlandY v hvY _ hm
        · exact hUY hm
        · exact absurd (hSattr (G.mem_attr_of_owner X α S (hYX hvY) ho hme
            (G.subset_attr X α S hm))) hvS
      have hσv : σ v = hex.choose := by
        simp only [σ, Game.fatalStrat]
        rw [ite_eq_left ⟨⟨hvY, hvS⟩, ho⟩, ite_eq_left hvU, dite_eq_left hex]
      obtain ⟨-, he, hw⟩ := hex.choose_spec
      rw [hσv]
      exact ⟨he, Or.inr hw⟩
    · rw [hσY v hvY hvS ho hvU]
      refine ⟨hme, ?_⟩
      rcases hm with hm | hm | hm
      · exact Or.inr (hlandY v hvY _ hm)
      · exact Or.inr (hUY hm)
      · exact Or.inl hm
  · intro v hv ho w hw he
    by_cases hvS : v ∈ S
    · exact Or.inl (hS.2.2.1 v hvS ho w hw he)
    have hvY : v ∈ Y := hv.resolve_left hvS
    obtain ⟨-, -, hcase⟩ := G.mem_mpre_of_mattr X α j (U ∪ S) hvY
    rcases hcase with ⟨ho', -⟩ | ⟨-, hall⟩
    · exact absurd ho' ho
    rcases hall w hw he with hm | hm | hm
    · exact Or.inr (hlandY v hvY _ hm)
    · exact Or.inr (hUY hm)
    · exact Or.inl hm
  · intro p hp hW
    by_cases hreach : ∃ n, p n ∈ S
    · exact Or.inl hreach
    right
    push Not at hreach
    have hY : ∀ n, p n ∈ Y := fun n => (hW n).resolve_left (hreach n)
    -- `U` is visited infinitely often.
    have hvisit : ∀ r N, G.mattrRank X α j (U ∪ S) (p N) = r → ∃ n, N ≤ n ∧ p n ∈ U := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro N hr
        by_cases hU : p N ∈ U
        · exact ⟨N, le_rfl, hU⟩
        have hnext := G.step_of_mattr_of_agree X α j (U ∪ S) σ (hY N)
          (fun ho => hσY _ (hY N) (hreach N) ho hU) (hp N)
        rcases hnext with hm | hm | hm
        · have hlt : G.mattrRank X α j (U ∪ S) (p (N + 1)) < r := by
            have hle := (G.mattrRank_spec X α j _ ⟨_, hm⟩).2.2 _ hm
            have hpos := (G.mattrRank_spec X α j _ (hY N)).1
            omega
          obtain ⟨n, hn, hnU⟩ := ih _ hlt (N + 1) rfl
          exact ⟨n, by omega, hnU⟩
        · exact ⟨N + 1, by omega, hm⟩
        · exact absurd hm (hreach (N + 1))
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · show ∃ᶠ k in Filter.atTop, G.prio (p k) = j
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn, hU⟩ := hvisit _ N rfl
      exact ⟨n, hn, hUj _ hU⟩
    · rintro m (hm : ∃ᶠ k in Filter.atTop, G.prio (p k) = m)
      obtain ⟨k, hk⟩ := hm.exists
      rw [← hk]
      exact G.prio_le_of_mattr X α j _ (hY k)

/-- `acceptFatal` preserves the invariant and extends the solution. -/
theorem Game.acceptFatal_inv [Finite V] (G : Game V) (X : Set V) (hsub : G.IsSubgame X)
    {j : ℕ} {U : Set V} {r : Solution V} (hr : G.ImplInv X r) (hUj : ∀ u ∈ U, G.prio u = j)
    (hUY : U ⊆ G.mattr X (Player.ofPrio j) j (U ∪ r.win (Player.ofPrio j))) :
    G.ImplInv X (G.acceptFatal X j U (G.mattr X (Player.ofPrio j) j (U ∪ r.win (Player.ofPrio j))) r) ∧
      r.Extends (G.acceptFatal X j U
        (G.mattr X (Player.ofPrio j) j (U ∪ r.win (Player.ofPrio j))) r) := by
  set α := Player.ofPrio j
  set Y := G.mattr X α j (U ∪ r.win α)
  set r1 : Solution V :=
    { win := Function.update r.win α (r.win α ∪ Y)
      strat := Function.update r.strat α (G.fatalStrat X j U Y (r.win α) (r.strat α)) }
  have h1 : G.SoundPartial X r1 := by
    intro k
    by_cases hk : k = α
    · subst hk
      simpa [r1] using G.isClosedWinningRegion_fatal X hsub (hr.1 α) (hr.2 α) hUj hUY
    · simpa [r1, Function.update_of_ne hk] using hr.1 k
  have hext1 : r.Extends r1 := by
    intro k
    by_cases hk : k = α
    · subst hk; simp [r1]
    · simp [r1, Function.update_of_ne hk]
  rw [G.acceptFatal_eq]
  obtain ⟨hs, hcl, hext⟩ := G.attrWithTau_sound X hsub α h1
  refine ⟨⟨hs, fun k => ?_⟩, hext1.trans hext⟩
  by_cases hk : k = α
  · subst hk; exact hcl
  · have hw : r1.win k = r.win k := Function.update_of_ne hk _ _
    rw [G.attrWithTau_win_ne X hk, hw]
    exact hr.2 k

/-- The `while` loop preserves the invariant and extends the solution, as long as the candidate
    set consists of priority-`j` nodes. -/
theorem Game.fatalLoop_inv [Finite V] (G : Game V) (X : Set V) (hsub : G.IsSubgame X) (j : ℕ) :
    ∀ fuel prev U r, G.ImplInv X r → (∀ u ∈ U, G.prio u = j) →
      G.ImplInv X (G.fatalLoop X j fuel prev U r) ∧ r.Extends (G.fatalLoop X j fuel prev U r) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ r hr _; exact ⟨hr, Solution.Extends.refl r⟩
  | succ fuel ih =>
    intro prev U r hr hUj
    simp only [Game.fatalLoop]
    split_ifs with h1 h2
    · exact ⟨hr, Solution.Extends.refl r⟩
    · exact G.acceptFatal_inv X hsub hr hUj h2
    · exact ih _ _ r hr fun u hu => hUj u hu.1

/-- Contract for `FatalAttractorOriginal`. -/
theorem Game.fatalAttractorOriginalSound (G : Game V) [Finite V] (X : Set V) (js : List ℕ)
    (r : Solution V) : G.FatalAttractorOriginalSound X js r := by
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
  have hfold : ∀ (js : List ℕ) (r : Solution V), G.ImplInv X r →
      G.ImplInv X (js.foldl (fun r j =>
        G.fatalLoop X j (Nat.card V + 1) ∅
          ({u | u ∈ X ∧ G.prio u = j} \ r.win (Player.ofPrio j).opp) r) r) ∧
      r.Extends (js.foldl (fun r j =>
        G.fatalLoop X j (Nat.card V + 1) ∅
          ({u | u ∈ X ∧ G.prio u = j} \ r.win (Player.ofPrio j).opp) r) r) := by
    intro js
    induction js with
    | nil => intro r hr; exact ⟨hr, Solution.Extends.refl r⟩
    | cons j js ih =>
      intro r hr
      obtain ⟨h1, he⟩ := G.fatalLoop_inv X hsub j _ _ _ r hr fun u (hu : u ∈ {u | u ∈ X ∧ G.prio u = j} \ _) => hu.1.2
      obtain ⟨h2, he'⟩ := ih _ h1
      exact ⟨h2, he.trans he'⟩
  obtain ⟨hf, hef⟩ := hfold js _ hinv
  exact ⟨hf.1, (he0.trans he1).trans hef⟩

end MercLib.ParityGame
