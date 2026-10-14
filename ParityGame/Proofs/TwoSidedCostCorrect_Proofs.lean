module

public import ParityGame.Proofs.TwoSidedCostCorrect_Win_Proofs
public import ParityGame.Proofs.TwoSidedCostCorrect_Fuel_Proofs

@[expose] public section TwoSidedCostCorrectProofs

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/TwoSidedCostCorrect_Pins.lean`.

Functional correctness of `solve`. The proof is split over
`TwoSidedCostCorrect_{Order,Graph,Tree,Lift,Win}_Proofs` (termination with explicit fuel,
`solveTerminates`, is in `TwoSidedCostCorrect_Fuel_Proofs`):
* Order: the program's value comparison is a total preorder and agrees with `LexLE` on the
  interleaved tuples `tup`.
* Graph: `explore`/`reachSet` compute reachability (fuel `n + 1` suffices).
* Tree: the program's levels, child lists (numbering by least vertex, `Ctx.nb`), chain bound
  (`≥` the library's) and tree navigation (`prog` sound, and least for the library's chain
  leaves with the program numbering).
* Lift: the lifting invariant `LInv` w.r.t. a bound `ν`: choices are alive successors, alive
  vertices off the queue are consistent, values stay below `ν`. Acceleration: the set found by
  `sccLoop` has only odd-maximum kept cycles, so `|M|` Bellman–Ford rounds keep it below `ν`.
* Win: consistent values form a progress measure (completion, certification); the bound `ν` is
  the chain-tree measure of the winning region (`Game.chainTreeCompleteBy` with `Ctx.nb`).
* Here: the attractor is `Game.attr`, one removal is two `Game.RemovalStep`s
  (`Game.simultaneousRemoval`), and the outer loop keeps `Game.AlgInv`.

Rather than the least fixpoint, completion uses any pre-fixpoint bound: an empty queue makes the
current values a fixpoint-like labelling below the chain-tree measure of the winning region,
which is all that is needed. -/

variable {n : ℕ}

/-! ### Players -/

theorem toPlayer_not (b : Bool) : toPlayer (!b) = (toPlayer b).opp := by
  cases b <;> rfl

theorem toPlayer_inj {a b : Bool} (h : toPlayer a = toPlayer b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem toPlayer_eq_or (b : Bool) (i : Player) : toPlayer b = i ∨ (toPlayer b).opp = i := by
  cases b <;> cases i <;> simp [toPlayer, Player.opp]

/-! ### The attractor -/

/-- Does the pass attract `u` into `A`? -/
def attracts (G : PGame n) (alive : VSet n) (player : Bool) (A : VSet n) (u : Fin n) : Bool :=
  if G.owner u == player then ((G.succ u).filter alive).any A
  else ((G.succ u).filter alive).any A && ((G.succ u).filter alive).all A

theorem attrStep_ret (G : PGame n) (alive : VSet n) (player : Bool) (A : VSet n) (u : Fin n) :
    (attrStep G alive player A u).ret = if (alive u && !A u) = true then
      (if attracts G alive player A u = true then Function.update A u true else A) else A := by
  unfold attrStep attracts
  simp only [ret_bind]
  split <;> simp

theorem attracts_mono (G : PGame n) (alive : VSet n) (player : Bool) {A A' : VSet n}
    (hA : ∀ v, A v = true → A' v = true) (u : Fin n) (h : attracts G alive player A u = true) :
    attracts G alive player A' u = true := by
  unfold attracts at h ⊢
  split_ifs at h ⊢
  · simp only [List.any_eq_true] at h ⊢
    obtain ⟨w, hw, hAw⟩ := h
    exact ⟨w, hw, hA w hAw⟩
  · simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h ⊢
    obtain ⟨⟨w, hw, hAw⟩, hall⟩ := h
    exact ⟨⟨w, hw, hA w hAw⟩, fun x hx => hA x (hall x hx)⟩

/-- A pass adds every alive vertex attracted by its input. -/
theorem attrPass_sup (G : PGame n) (alive : VSet n) (player : Bool) (A : VSet n) (u : Fin n)
    (hu : alive u = true) (ha : attracts G alive player A u = true) :
    (attrPass G alive player A).ret u = true := by
  unfold attrPass
  rw [ret_foldlM]
  have mono : ∀ (L : List (Fin n)) (B : VSet n) (x : Fin n), B x = true →
      (L.foldl (fun b a => (attrStep G alive player b a).ret) B) x = true := by
    intro L
    induction L with
    | nil => intro B x h; exact h
    | cons y L ih =>
      intro B x h
      apply ih
      dsimp only
      rw [attrStep_ret]
      split
      · split
        · by_cases hxy : x = y
          · subst hxy; simp
          · rw [Function.update_of_ne hxy]; exact h
        · exact h
      · exact h
  have key : ∀ (L : List (Fin n)) (B : VSet n), (∀ x, A x = true → B x = true) → u ∈ L →
      (L.foldl (fun b a => (attrStep G alive player b a).ret) B) u = true := by
    intro L
    induction L with
    | nil => intro _ _ h; simp at h
    | cons y L ih =>
      intro B hB hmem
      rw [List.foldl_cons]
      rcases List.mem_cons.1 hmem with rfl | hmem
      · apply mono
        rw [attrStep_ret]
        by_cases hBu : B u = true
        · split
          · split <;> simp_all
          · exact hBu
        · rw [ite_eq_left (by simp [hu, hBu]), ite_eq_left (attracts_mono G alive player hB u ha)]
          simp
      · apply ih _ _ hmem
        intro x hx
        rw [attrStep_ret]
        split
        · split
          · by_cases hxy : x = y
            · subst hxy; simp
            · rw [Function.update_of_ne hxy]; exact hB x hx
          · exact hB x hx
        · exact hB x hx
  exact key _ A (fun _ h => h) (List.mem_finRange u)

/-- A property of the input that holds for every attracted alive vertex holds after a pass. -/
theorem attrPass_sub (G : PGame n) (alive : VSet n) (player : Bool) (P : Fin n → Prop)
    (hP : ∀ (B : VSet n) u, (∀ v, B v = true → P v) → alive u = true →
      attracts G alive player B u = true → P u) (A : VSet n) (hA : ∀ v, A v = true → P v) :
    ∀ v, (attrPass G alive player A).ret v = true → P v := by
  unfold attrPass
  rw [ret_foldlM]
  have key : ∀ (L : List (Fin n)) (B : VSet n), (∀ v, B v = true → P v) →
      ∀ v, (L.foldl (fun b a => (attrStep G alive player b a).ret) B) v = true → P v := by
    intro L
    induction L with
    | nil => intro B hB; exact hB
    | cons y L ih =>
      intro B hB
      rw [List.foldl_cons]
      apply ih
      intro v hv
      rw [attrStep_ret] at hv
      split at hv
      · rename_i hy
        split at hv
        · rename_i hat
          by_cases hvy : v = y
          · subst hvy
            exact hP B v hB (by simp at hy; exact hy.1) hat
          · rw [Function.update_of_ne hvy] at hv; exact hB v hv
        · exact hB v hv
      · exact hB v hv
  exact key _ A hA

theorem iterT_fix_of_fix (f : VSet n → TimeM ℕ (VSet n)) (A : VSet n) (hA : (f A).ret = A) :
    ∀ k, (iterT f k A).ret = A
  | 0 => rfl
  | k + 1 => by simp only [iterT, ret_bind, hA]; exact iterT_fix_of_fix f A hA k

/-- After `k` passes with `k + |A| > n`, a fixpoint has been reached. -/
theorem attr_iter_fix (G : PGame n) (alive : VSet n) (player : Bool) :
    ∀ (k : ℕ) (A : VSet n), n < k + A.count →
      (attrPass G alive player (iterT (attrPass G alive player) k A).ret).ret =
        (iterT (attrPass G alive player) k A).ret
  | 0, A, h => absurd h (by have := count_le A; omega)
  | k + 1, A, h => by
    simp only [iterT, ret_bind]
    by_cases hfix : (attrPass G alive player A).ret = A
    · rw [hfix, iterT_fix_of_fix _ A hfix]; exact hfix
    · apply attr_iter_fix G alive player k
      have hsub : ∀ v, A v = true → (attrPass G alive player A).ret v = true :=
        fun v hv => attrPass_mono G alive player A v hv
      obtain ⟨v, hv⟩ : ∃ v, (attrPass G alive player A).ret v ≠ A v := by
        by_contra hall
        push Not at hall
        exact hfix (funext hall)
      have hv1 : (attrPass G alive player A).ret v = true ∧ A v = false := by
        cases hA : A v
        · cases hp : (attrPass G alive player A).ret v
          · rw [hp, hA] at hv; exact absurd rfl hv
          · exact ⟨rfl, rfl⟩
        · rw [hsub v hA, hA] at hv; exact absurd rfl hv
      have := count_lt (attrPass G alive player A).ret A hsub v hv1.1 hv1.2
      omega

theorem toGame_owner (G : PGame n) (h : G.Total) (v : Fin n) :
    (G.toGame h).owner v = toPlayer (G.owner v) := rfl

theorem toGame_edge (G : PGame n) (h : G.Total) (v w : Fin n) :
    (G.toGame h).edge v w ↔ w ∈ G.succ v := Iff.rfl

/-- The program's attractor is the library's attractor (headline). -/
theorem attractorComputesAttr (G : PGame n) (h : G.Total) : AttractorComputesAttr G h := by
  intro alive player target hX
  set X := alive.toSet
  set U := alive.toSet ∩ target.toSet
  set i := toPlayer player
  have hUX : U ⊆ X := fun _ hv => hv.1
  have hA0 : (materialize fun v => alive v && target v) = fun v => alive v && target v :=
    materialize_eq _
  have hret : (attractor G alive player target).ret =
      (iterT (attrPass G alive player) (n + 1) (fun v => alive v && target v)).ret := by
    simp only [attractor, ret_bind, hA0]
  have howner : ∀ u, ((G.owner u == player) = true) ↔ (G.toGame h).owner u = i := by
    intro u
    rw [toGame_owner]
    constructor
    · intro hu; simp at hu; rw [hu]
    · intro hu; simpa using toPlayer_inj hu
  ext v
  simp only [VSet.toSet, Set.mem_ofPred_eq]
  rw [hret]
  constructor
  · -- everything attracted is in the attractor
    have key : ∀ (k : ℕ) (A : VSet n), (∀ v, A v = true → v ∈ (G.toGame h).attr X i U) →
        ∀ v, (iterT (attrPass G alive player) k A).ret v = true → v ∈ (G.toGame h).attr X i U := by
      intro k
      induction k with
      | zero => intro A hA; exact hA
      | succ k ih =>
        intro A hA
        simp only [iterT, ret_bind]
        apply ih
        apply attrPass_sub G alive player _ _ A hA
        intro B u hB hu hat
        unfold attracts at hat
        split at hat
        · rename_i hown
          simp only [List.any_eq_true, List.mem_filter] at hat
          obtain ⟨w, ⟨hw, -⟩, hBw⟩ := hat
          exact (G.toGame h).mem_attr_of_owner X i U hu ((howner u).1 hown) hw (hB w hBw)
        · rename_i hown
          simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter] at hat
          refine (G.toGame h).mem_attr_of_opp X i U hu (fun ho => hown ((howner u).2 ho))
            fun w hwX he => hB w (hat.2 w ⟨he, hwX⟩)
    exact key (n + 1) _ (fun v hv => (G.toGame h).subset_attr X i U (by
      simp only [Bool.and_eq_true] at hv; exact ⟨hv.1, hv.2⟩)) v
  · -- the final set is closed, so it contains every stage
    rintro ⟨k, hk⟩
    set F := (iterT (attrPass G alive player) (n + 1) (fun v => alive v && target v)).ret
    have hfix : (attrPass G alive player F).ret = F :=
      attr_iter_fix G alive player (n + 1) _ (by omega)
    have hclosed : ∀ u, alive u = true → attracts G alive player F u = true → F u = true := by
      intro u hu ha
      have := attrPass_sup G alive player F u hu ha
      rwa [hfix] at this
    have h0 : ∀ v, v ∈ U → F v = true := by
      intro v hv
      exact iterT_mono _ v (fun A h' => attrPass_mono G alive player A v h') _ _
        (by simp only [Bool.and_eq_true]; exact ⟨hv.1, hv.2⟩)
    have hstage : ∀ k, ∀ v ∈ (G.toGame h).attrStage X i U k, F v = true := by
      intro k
      induction k with
      | zero => exact h0
      | succ k ih =>
        intro v hv
        simp only [Game.attrStage, Set.mem_union, Set.mem_ofPred_eq] at hv
        rcases hv with hv | ⟨hvX, hv⟩
        · exact ih v hv
        · apply hclosed v hvX
          unfold attracts
          rcases hv with ⟨ho, w, hw, he⟩ | ⟨ho, hall⟩
          · rw [ite_eq_left ((howner v).2 ho)]
            simp only [List.any_eq_true, List.mem_filter]
            exact ⟨w, ⟨he, (G.toGame h).attrStage_subset X i U hUX k hw⟩, ih w hw⟩
          · rw [ite_eq_right (fun h' => ho ((howner v).1 h'))]
            obtain ⟨w, hwX, he⟩ := hX v hvX
            simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_filter]
            exact ⟨⟨w, ⟨he, hwX⟩, ih w (hall w hwX he)⟩,
              fun x ⟨hx, hxX⟩ => ih x (hall x hxX hx)⟩
    exact hstage k v hk


theorem mkLifter_X (G : PGame n) (alive : VSet n) (p : Bool) :
    (mkLifter G alive p).ret.1.X = alive.toSet := rfl

/-! ### The outer state as an `AlgState` -/

/-- The library state of the outer loop: the dead vertices are decided (for the player named by
    `winner`), the alive ones form the undecided subgame. -/
def algOf (alive winner : VSet n) : AlgState (Fin n) :=
  ⟨fun i => {v | alive v = false ∧ toPlayer (winner v) = i}, alive.toSet⟩

/-- `w` names the winner of every vertex. -/
def Done (G : PGame n) (h : G.Total) (w : VSet n) : Prop :=
  ∀ v i, toPlayer (w v) = i ↔ (G.toGame h).Wins Set.univ i v

theorem algState_ext {V : Type*} {s t : AlgState V} (h1 : ∀ i, s.won i = t.won i)
    (h2 : s.rest = t.rest) : s = t := by
  cases s; cases t
  simp only [AlgState.mk.injEq] at h1 h2 ⊢
  exact ⟨funext h1, h2⟩

theorem attr_empty {V : Type*} (G : Game V) {X : Set V} (hX : G.IsSubgame X) (i : Player) :
    G.attr X i ∅ = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro v ⟨k, hk⟩
  induction k generalizing v with
  | zero => exact hk
  | succ k ih =>
    simp only [Game.attrStage, Set.mem_union, Set.mem_ofPred_eq] at hk
    rcases hk with hk | ⟨hvX, ⟨-, w, hw, -⟩ | ⟨-, hall⟩⟩
    · exact ih v hk
    · exact ih w hw
    · obtain ⟨w, hwX, he⟩ := hX v hvX
      exact ih w (hall w hwX he)

theorem algInv_remove {V : Type*} [Finite V] (G : Game V) (s : AlgState V) (hs : G.AlgInv s)
    (i : Player) {M : Type} (C : Codomain M) (D : Set V) (μ : V → M) (σ : Strategy V)
    (hpm : (G.forPlayer i).IsProgressMeasure s.rest C D μ σ) : G.AlgInv (s.remove G i D) := by
  by_cases hne : D.Nonempty
  · exact G.algInvStep _ _ hs ⟨i, M, C, μ, σ, D, hne, hpm, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have : s.remove G i ∅ = s := by
      apply algState_ext
      · intro j
        simp only [AlgState.remove, attr_empty G hs.1, Set.union_empty]
        split <;> rfl
      · simp [AlgState.remove, attr_empty G hs.1]
    rw [this]; exact hs

/-- The program's Even attractor in `removal`. -/
def rmA0 (G : PGame n) (alive cert0 : VSet n) : VSet n := (attractor G alive false cert0).ret

/-- The alive vertices after removing the Even attractor. -/
def rmAlive1 (G : PGame n) (alive cert0 : VSet n) : VSet n :=
  fun v => alive v && !rmA0 G alive cert0 v

/-- The program's Odd attractor in `removal`. -/
def rmA1 (G : PGame n) (alive cert0 cert1 : VSet n) : VSet n :=
  (attractor G (rmAlive1 G alive cert0) true cert1).ret

theorem removal_ret (G : PGame n) (alive winner cert0 cert1 : VSet n) :
    (removal G alive winner cert0 cert1).ret =
      ((fun v => rmAlive1 G alive cert0 v && !rmA1 G alive cert0 cert1 v),
        (fun v => if rmA0 G alive cert0 v = true then false else
          if rmA1 G alive cert0 cert1 v = true then true else winner v)) := by
  simp only [removal, ret_bind, ret_pure, materialize_eq]
  rfl

/-- One round's removal of both certified sets keeps the algorithm invariant (two
    `Game.RemovalStep`s, justified by `Game.simultaneousRemoval`). -/
theorem removal_inv (G : PGame n) (h : G.Total) (alive winner cert0 cert1 : VSet n)
    (hinv : (G.toGame h).AlgInv (algOf alive winner))
    {M₀ M₁ : Type} (C₀ : Codomain M₀) (μ₀ : Fin n → M₀) (σ₀ : Strategy (Fin n))
    (C₁ : Codomain M₁) (μ₁ : Fin n → M₁) (σ₁ : Strategy (Fin n))
    (hpm0 : (G.toGame h).IsProgressMeasure alive.toSet C₀ cert0.toSet μ₀ σ₀)
    (hpm1 : (G.toGame h).dual.IsProgressMeasure alive.toSet C₁ cert1.toSet μ₁ σ₁) :
    (G.toGame h).AlgInv (algOf (removal G alive winner cert0 cert1).ret.1
      (removal G alive winner cert0 cert1).ret.2) := by
  have hX : (G.toGame h).IsSubgame alive.toSet := hinv.1
  have hs1 : (G.toGame h).AlgInv ((algOf alive winner).remove (G.toGame h) .zero cert0.toSet) :=
    algInv_remove (G.toGame h) _ hinv .zero C₀ cert0.toSet μ₀ σ₀ hpm0
  have hpm1' := (G.toGame h).simultaneousRemoval alive.toSet C₀ cert0.toSet μ₀ σ₀ C₁ cert1.toSet
    μ₁ σ₁ hX hpm0 hpm1
  have hs2 : (G.toGame h).AlgInv (((algOf alive winner).remove (G.toGame h) .zero
      cert0.toSet).remove (G.toGame h) .one cert1.toSet) :=
    algInv_remove (G.toGame h) _ hs1 .one C₁ cert1.toSet μ₁ σ₁ hpm1'
  have hA0set : (rmA0 G alive cert0).toSet = (G.toGame h).attr alive.toSet .zero cert0.toSet := by
    rw [rmA0, attractorComputesAttr G h alive false cert0 hX]
    congr 1
    exact Set.inter_eq_right.2 hpm0.1
  have mA : ∀ v, v ∈ (G.toGame h).attr alive.toSet .zero cert0.toSet ↔ rmA0 G alive cert0 v = true :=
    fun v => by rw [← hA0set]; rfl
  have hA0X : ∀ v, rmA0 G alive cert0 v = true → alive v = true := fun v hv =>
    (G.toGame h).attr_subset _ .zero _ hpm0.1 ((mA v).2 hv)
  have halive1set : (rmAlive1 G alive cert0).toSet =
      alive.toSet \ (G.toGame h).attr alive.toSet .zero cert0.toSet := by
    ext v
    rw [Set.mem_sdiff, mA]
    simp [rmAlive1, VSet.toSet]
  have hX1 : (G.toGame h).IsSubgame (rmAlive1 G alive cert0).toSet := by
    rw [halive1set]; exact hs1.1
  have hA1set : (rmA1 G alive cert0 cert1).toSet = (G.toGame h).attr
      (alive.toSet \ (G.toGame h).attr alive.toSet .zero cert0.toSet) .one cert1.toSet := by
    rw [rmA1, attractorComputesAttr G h _ true cert1 hX1, halive1set]
    congr 1
    exact Set.inter_eq_right.2 hpm1'.1
  have mB : ∀ v, v ∈ (G.toGame h).attr (alive.toSet \ (G.toGame h).attr alive.toSet .zero
      cert0.toSet) .one cert1.toSet ↔ rmA1 G alive cert0 cert1 v = true :=
    fun v => by rw [← hA1set]; rfl
  have hA1X : ∀ v, rmA1 G alive cert0 cert1 v = true → rmAlive1 G alive cert0 v = true :=
    fun v hv => by
      have := (G.toGame h).attr_subset _ .one _ hpm1'.1 ((mB v).2 hv)
      rw [← halive1set] at this
      exact this
  rw [removal_ret]
  convert hs2 using 1
  apply algState_ext
  · intro j
    ext v
    show (_ ∧ _) ↔ v ∈ (if j = .one then _ else _)
    have mW : ∀ j', v ∈ (algOf alive winner).won j' ↔
        alive v = false ∧ toPlayer (winner v) = j' := fun _ => Iff.rfl
    have mR : v ∈ (algOf alive winner).rest ↔ alive v = true := Iff.rfl
    by_cases ha0 : rmA0 G alive cert0 v = true
    · have hal := hA0X v ha0
      have ha1 : rmA1 G alive cert0 cert1 v = false := by
        cases h' : rmA1 G alive cert0 cert1 v
        · rfl
        · have := hA1X v h'; simp [rmAlive1, ha0] at this
      have ma : v ∈ (G.toGame h).attr (algOf alive winner).rest .zero cert0.toSet := (mA v).2 ha0
      have mb : v ∉ (G.toGame h).attr ((algOf alive winner).rest \ (G.toGame h).attr
          (algOf alive winner).rest .zero cert0.toSet) .one cert1.toSet := fun hb => by
        rw [(mB v).1 hb] at ha1; cases ha1
      cases j <;> simp [AlgState.remove, ha0, ha1, hal, rmAlive1, toPlayer, ma, mb, mW]
    · simp only [Bool.not_eq_true] at ha0
      have ma : v ∉ (G.toGame h).attr (algOf alive winner).rest .zero cert0.toSet := fun ha => by
        rw [(mA v).1 ha] at ha0; cases ha0
      by_cases ha1 : rmA1 G alive cert0 cert1 v = true
      · have hal := hA1X v ha1
        simp only [rmAlive1, Bool.and_eq_true] at hal
        have mb : v ∈ (G.toGame h).attr ((algOf alive winner).rest \ (G.toGame h).attr
            (algOf alive winner).rest .zero cert0.toSet) .one cert1.toSet := (mB v).2 ha1
        cases j <;> simp [AlgState.remove, ha0, ha1, hal.1, rmAlive1, toPlayer, ma, mb, mW]
      · simp only [Bool.not_eq_true] at ha1
        have mb : v ∉ (G.toGame h).attr ((algOf alive winner).rest \ (G.toGame h).attr
            (algOf alive winner).rest .zero cert0.toSet) .one cert1.toSet := fun hb => by
          rw [(mB v).1 hb] at ha1; cases ha1
        cases j <;> simp [AlgState.remove, ha0, ha1, rmAlive1, ma, mb, mW]
  · ext v
    change (rmAlive1 G alive cert0 v && !rmA1 G alive cert0 cert1 v) = true ↔
      v ∈ (alive.toSet \ (G.toGame h).attr alive.toSet .zero cert0.toSet) \
        (G.toGame h).attr (alive.toSet \ (G.toGame h).attr alive.toSet .zero cert0.toSet) .one
          cert1.toSet
    rw [Set.mem_sdiff, Set.mem_sdiff, mA, mB]
    simp [rmAlive1, VSet.toSet]

/-! ### Completion -/

theorem complete_ret (c : Ctx n) (st : LState n) (w : VSet n) :
    (complete c st w).ret = fun v =>
      if c.alive v = true then (if (st.measure v).isSome = true then c.p else !c.p) else w v := by
  simp only [complete, ret_bind, ret_pure, materialize_eq]

/-- A lifter whose queue is empty decides the whole subgame. -/
theorem complete_correct (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total) (W : VSet n)
    (hinv : (c.G.toGame h).AlgInv (algOf c.alive W)) {ν : Fin n → Val}
    {E : Fin n → Fin n → Prop} (_hB : Bound c ν E)
    (hW : ∀ v, (c.G.toGame h).Wins c.X (toPlayer c.p) v → ν v ≠ none) (st : LState n)
    (hL : LInv c ν st) (hq : st.queue = []) : Done c.G h (complete c st W).ret := by
  set Gt := c.G.toGame h
  have hX : Gt.IsSubgame c.X := hinv.1
  have hsound := complete_sound c hc h hX st.measure hL.len
    (fun v hv => hL.queue v hv (by rw [hq]; simp))
  intro v i
  rw [complete_ret]
  dsimp only
  by_cases hv : c.alive v = true
  · rw [ite_eq_left hv]
    have hrest : ∀ j, Gt.Wins c.X j v ↔ Gt.Wins Set.univ j v := hinv.2.2 v hv
    have hdet := Gt.wins_or_wins hX hv (toPlayer c.p)
    by_cases hm : (st.measure v).isSome = true
    · rw [ite_eq_left hm]
      have hwin : Gt.Wins c.X (toPlayer c.p) v := hsound v hv (by simpa [Option.isSome_iff_ne_none] using hm)
      constructor
      · rintro rfl; exact (hrest _).1 hwin
      · intro hi
        rcases toPlayer_eq_or c.p i with h' | h'
        · exact h'
        · subst h'
          exact (Gt.not_wins_both hwin ((hrest _).2 hi)).elim
    · rw [ite_eq_right hm, toPlayer_not]
      have hnone : st.measure v = none := by simpa using hm
      have hnwin : ¬ Gt.Wins c.X (toPlayer c.p) v := by
        intro hw
        have := hL.le v
        rw [hnone, VLe.top_iff] at this
        exact hW v hw this
      have hopp : Gt.Wins c.X (toPlayer c.p).opp v := hdet.resolve_left hnwin
      constructor
      · rintro rfl; exact (hrest _).1 hopp
      · intro hi
        rcases toPlayer_eq_or c.p i with h' | h'
        · subst h'; exact (hnwin ((hrest _).2 hi)).elim
        · exact h'
  · rw [ite_eq_right hv]
    have := hinv.2.1 i v
    simp only [algOf, Set.mem_ofPred_eq, VSet.toSet] at this
    rw [show c.alive v = false by simpa using hv] at this
    simpa using this

/-! ### The rounds of one restart -/

/-- What an outcome guarantees: winners for `done`, the invariant for `next`. -/
def OutcomeOK (G : PGame n) (h : G.Total) : Outcome n → Prop
  | .done s => Done G h s.winner
  | .next s => (G.toGame h).AlgInv (algOf s.alive s.winner)
  | .oof _ => True

theorem certified_pm' (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total) (st : LState n)
    (hlen : ∀ v x, st.measure v = some x → x.length = c.height) :
    ∃ σ, ((c.G.toGame h).forPlayer (toPlayer c.p)).IsProgressMeasure c.alive.toSet (c.cod h)
      (certified c st).ret.toSet (lab st.measure) σ :=
  ⟨_, certified_pm c hc h st hlen⟩

theorem roundLoop_ok (G : PGame n) (h : G.Total) (rem fuel : ℕ) (A W : VSet n)
    (hinv : (G.toGame h).AlgInv (algOf A W))
    {ν₀ ν₁ : Fin n → Val} {E₀ E₁ : Fin n → Fin n → Prop}
    (hB0 : Bound (mkLifter G A false).ret.1 ν₀ E₀) (hB1 : Bound (mkLifter G A true).ret.1 ν₁ E₁)
    (hW0 : ∀ v, (G.toGame h).Wins A.toSet .zero v → ν₀ v ≠ none)
    (hW1 : ∀ v, (G.toGame h).Wins A.toSet .one v → ν₁ v ≠ none) :
    ∀ (f : ℕ) (s : SState n) (l0 l1 : LState n), s.alive = A → s.winner = W →
      LInv (mkLifter G A false).ret.1 ν₀ l0 → LInv (mkLifter G A true).ret.1 ν₁ l1 →
      OutcomeOK G h (roundLoop G rem fuel (mkLifter G A false).ret.1 (mkLifter G A true).ret.1 f
        s l0 l1).ret := by
  set c0 := (mkLifter G A false).ret.1 with hc0
  set c1 := (mkLifter G A true).ret.1 with hc1
  have hc0a : c0.alive = A := mkLifter_alive G A false
  have hc1a : c1.alive = A := mkLifter_alive G A true
  have hl0 : c0.LevelsOK := mkLifter_levelsOK G A false
  have hl1 : c1.LevelsOK := mkLifter_levelsOK G A true
  have hinv0 : (c0.G.toGame h).AlgInv (algOf c0.alive W) := by rw [hc0a]; exact hinv
  have hinv1 : (c1.G.toGame h).AlgInv (algOf c1.alive W) := by rw [hc1a]; exact hinv
  intro f
  induction f with
  | zero => intro s l0 l1 _ _ _ _; simp [roundLoop, OutcomeOK]
  | succ f ih =>
    intro s l0 l1 hsa hsw hL0 hL1
    rw [roundLoop.eq_2]
    simp only [ret_bind]
    obtain ⟨hr0, hr0q⟩ := run_inv hB0 rem fuel l0 hL0
    obtain ⟨hr1, hr1q⟩ := run_inv hB1 rem fuel l1 hL1
    split
    · simp [OutcomeOK]
    · split
      · rename_i hq
        simp only [ret_bind, ret_pure, OutcomeOK]
        rw [hsw]
        exact complete_correct c0 hl0 h W hinv0 hB0 (fun v hv => hW0 v (by rw [← hc0a]; exact hv))
          _ hr0 (hr0q hq)
      · simp only [ret_bind]
        split
        · simp [OutcomeOK]
        · split
          · rename_i hq
            simp only [ret_bind, ret_pure, OutcomeOK]
            rw [hsw]
            exact complete_correct c1 hl1 h W hinv1 hB1
              (fun v hv => hW1 v (by rw [← hc1a]; exact hv)) _ hr1 (hr1q hq)
          · simp only [ret_bind]
            split
            · exact ih _ _ _ (by simp [hsa]) (by simp [hsw]) hr0 hr1
            · simp only [ret_bind, ret_pure, OutcomeOK]
              obtain ⟨σ0, hpm0⟩ := certified_pm' c0 hl0 h _ hr0.len
              obtain ⟨σ1, hpm1⟩ := certified_pm' c1 hl1 h _ hr1.len
              rw [hc0a] at hpm0
              rw [hc1a] at hpm1
              rw [hsa, hsw]
              exact removal_inv G h A W _ _ hinv (c0.cod h) _ σ0 (c1.cod h) _ σ1 hpm0 hpm1

/-! ### The outer loop and the headline -/

theorem outer_ok (G : PGame n) (h : G.Total) (fuel : ℕ) :
    ∀ (k : ℕ) (s : SState n), (G.toGame h).AlgInv (algOf s.alive s.winner) →
      (outer G fuel k s).ret.2 = true → Done G h (outer G fuel k s).ret.1.winner
  | 0, s, _, h2 => by simp [outer] at h2
  | k + 1, s, hinv, h2 => by
    rw [outer.eq_2] at h2 ⊢
    simp only [ret_bind] at h2 ⊢
    by_cases hrem : s.alive.count = 0
    · simp only [hrem, beq_self_eq_true, ↓reduceIte, ret_pure] at h2 ⊢
      have hdead : ∀ v, s.alive v = false := fun v => count_eq_zero _ hrem v
      intro v i
      have := hinv.2.1 i v
      simp only [algOf, Set.mem_ofPred_eq, VSet.toSet, hdead v, true_and] at this
      simpa using this
    · have hrem' : (s.alive.count == 0) = false := by simpa using hrem
      simp only [hrem', Bool.false_eq_true, ↓reduceIte, ret_bind] at h2 ⊢
      set s1 : SState n := { s with restarts := s.restarts + 1 }
      have hinv1 : (G.toGame h).AlgInv (algOf s1.alive s1.winner) := hinv
      have hX : (G.toGame h).IsSubgame s1.alive.toSet := hinv.1
      obtain ⟨ν₀, E₀, hB0, hW0⟩ := exists_bound (mkLifter G s1.alive false).ret.1
        (mkLifter_levelsOK G s1.alive false) h (by rw [mkLifter_X]; exact hX)
      obtain ⟨ν₁, E₁, hB1, hW1⟩ := exists_bound (mkLifter G s1.alive true).ret.1
        (mkLifter_levelsOK G s1.alive true) h (by rw [mkLifter_X]; exact hX)
      have hok := roundLoop_ok G h s1.alive.count fuel s1.alive s1.winner hinv1 hB0 hB1
        (fun v hv => hW0 v (by rw [mkLifter_X]; exact hv))
        (fun v hv => hW1 v (by rw [mkLifter_X]; exact hv)) fuel s1 _ _ rfl rfl
        (mkLifter_inv G s1.alive false hB0) (mkLifter_inv G s1.alive true hB1)
      generalize (roundLoop G s1.alive.count fuel (mkLifter G s1.alive false).ret.1
        (mkLifter G s1.alive true).ret.1 fuel s1 (mkLifter G s1.alive false).ret.2
        (mkLifter G s1.alive true).ret.2).ret = o at hok h2 ⊢
      cases o with
      | done s' => simpa [OutcomeOK] using hok
      | oof s' => simp at h2
      | next s' =>
        simp only at h2 ⊢
        exact outer_ok G h fuel k s' hok h2

/-- Functional correctness of the solver (headline). -/
theorem solveCorrect (G : PGame n) (fuel : ℕ) : SolveCorrect G fuel := by
  intro h w hw
  simp only [solve, ret_bind, ret_pure] at hw
  split at hw
  · rename_i h2
    simp only [Option.some.injEq] at hw
    subst hw
    apply outer_ok G h fuel (n + 1) _ _ h2
    have : algOf (fun _ => true : VSet n) (fun _ => false) = AlgState.init := by
      apply algState_ext
      · intro i; ext v; simp [algOf, AlgState.init]
      · ext v; simp [algOf, AlgState.init, VSet.toSet]
    simp only
    rw [this]
    exact (G.toGame h).algInvInit
  · cases hw

/-! ### The intermediate headlines -/

theorem levelsCorrect (c : Ctx n) (h : c.G.Total) : LevelsCorrect c h := fun hc =>
  ⟨height_eq c hc h, level_eq c hc h, depthOf_eq c hc h⟩

theorem childrenComplete (c : Ctx n) (h : c.G.Total) : ChildrenComplete c h :=
  c.compNumbering h

theorem chainBoundDominates (c : Ctx n) (h : c.G.Total) : ChainBoundDominates c h :=
  fun R hR q => chainBound_ge c h R hR q

theorem progSound (c : Ctx n) : ProgSound c := fun v x r hr hx => prog_sound c v x r hr hx

theorem progLeast (c : Ctx n) (h : c.G.Total) : ProgLeast c h :=
  fun hc v aw av hav hle hlt x hx hxw => prog_least c hc h v aw av hav hle hlt x hx hxw

theorem liftingCorrect (G : PGame n) (h : G.Total) (alive : VSet n) (p : Bool) :
    LiftingCorrect G h alive p := by
  intro hX
  set c := (mkLifter G alive p).ret.1
  have hca : c.alive = alive := mkLifter_alive G alive p
  have hcl : c.LevelsOK := mkLifter_levelsOK G alive p
  obtain ⟨ν, E, hB, hW⟩ := exists_bound c hcl h (by rw [mkLifter_X]; exact hX)
  refine ⟨LInv c ν, mkLifter_inv G alive p hB, fun b f st hst => (run_inv hB b f st hst).1,
    fun b f st hst => (run_inv hB b f st hst).2, fun st hst hq v hv => ?_, fun st hst => ?_⟩
  · have hsound := complete_sound c hcl h (by rw [mkLifter_X]; exact hX) st.measure hst.len
      (fun v hv => hst.queue v hv (by rw [hq]; simp))
    constructor
    · intro hm
      have := hsound v (by rw [hca]; exact hv) (by simpa [Option.isSome_iff_ne_none] using hm)
      rwa [mkLifter_X] at this
    · intro hw
      have hne := hW v (by rw [mkLifter_X]; exact hw)
      have := hst.le v
      cases hm : st.measure v with
      | none => rw [hm, VLe.top_iff] at this; exact absurd this hne
      | some x => simp
  · obtain ⟨σ, hpm⟩ := certified_pm' c hcl h st hst.len
    rw [hca] at hpm
    exact ⟨c.cod h, lab st.measure, σ, hpm⟩

end ParityGame.TwoSidedCost

end TwoSidedCostCorrectProofs
