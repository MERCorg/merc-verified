module

public import ParityGame.Proofs.TwoSidedCostCorrect_Graph_Proofs
public import ParityGame.Proofs.TwoSidedAlgorithm_Proofs

@[expose] public section TwoSidedCostCorrectTreeProofs

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

The program's chain tree against the library's (`ParityGame.TwoSidedLifting`): the lifting
player's game `Ctx.game`, the levels, the weak components (`Ctx.nb` lists every component), the
chain bound (the program's longest-path bound is at least the library's), the regions of a
path, and tree navigation (`nextAux`, `prog`). -/

variable {n : ℕ}

/-! ### The lifting player's game -/

section Game

variable (c : Ctx n) (h : c.G.Total)

theorem Ctx.game_prio (v : Fin n) : (c.game h).prio v = c.prio v := by
  unfold Ctx.game Ctx.prio
  cases hp : c.p <;> simp [toPlayer, Game.forPlayer, Game.dual, PGame.toGame]

theorem Ctx.game_edge (v w : Fin n) : (c.game h).edge v w ↔ w ∈ c.G.succ v := by
  unfold Ctx.game
  cases c.p <;> simp [toPlayer, Game.forPlayer, Game.dual, PGame.toGame]

theorem Ctx.game_owner (v : Fin n) : (c.game h).owner v = .zero ↔ c.mine v = true := by
  unfold Ctx.game Ctx.mine
  cases hp : c.p <;> cases ho : c.G.owner v <;>
    simp [toPlayer, Game.forPlayer, Game.dual, PGame.toGame, ho, Player.opp]

theorem Ctx.mem_X (v : Fin n) : v ∈ c.X ↔ c.alive v = true := Iff.rfl

end Game

theorem mem_succT (c : Ctx n) (v w : Fin n) :
    w ∈ (succT c v).ret ↔ w ∈ c.G.succ v ∧ c.alive w = true := by
  simp [succT, List.mem_filter]

theorem mem_predT (c : Ctx n) (v u : Fin n) :
    u ∈ (predT c v).ret ↔ c.alive u = true ∧ v ∈ c.G.succ u := by
  simp [predT, List.mem_filter]

/-! ### Small list and fold facts -/

theorem foldl_update {α β : Type} [DecidableEq α] (F : α → β) :
    ∀ (l : List α) (b : α → β) (u : α),
      (l.foldl (fun b x => Function.update b x (F x)) b) u = if u ∈ l then F u else b u
  | [], b, u => by simp
  | x :: l, b, u => by
    rw [List.foldl_cons, foldl_update F l]
    by_cases hu : u ∈ l
    · simp [hu]
    · by_cases hux : u = x
      · subst hux; simp
      · simp [hu, hux]

theorem foldl_update_eq {α β : Type} [DecidableEq α] (F : α → β) (l : List α) (b : α → β)
    (hl : ∀ u, u ∈ l) : l.foldl (fun b x => Function.update b x (F x)) b = F := by
  funext u
  rw [foldl_update, if_pos (hl u)]

theorem le_foldr_max {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (x : α), x ∈ l → f x ≤ l.foldr (fun w a => max (f w) a) 0
  | [], x, hx => by simp at hx
  | y :: l, x, hx => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (le_foldr_max f l x hx).trans (le_max_right _ _)

theorem foldr_max_le {α : Type} (f : α → ℕ) (B : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ B) → l.foldr (fun w a => max (f w) a) 0 ≤ B
  | [], _ => by simp
  | y :: l, h => by
    rw [List.foldr_cons]
    exact max_le (h y (by simp)) (foldr_max_le f B l fun x hx => h x (by simp [hx]))

theorem length_filter_finRange (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = (Finset.univ.filter fun x => p x = true).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext x
  simp

/-! ### Levels -/

theorem prio_lt_d (G : PGame n) (v : Fin n) : G.prio v < G.d := by
  unfold PGame.d
  have : G.prio v ≤ ((List.finRange n).map G.prio).foldr max 0 :=
    le_foldr_max (f := id) _ _ (List.mem_map.2 ⟨v, List.mem_finRange v, rfl⟩) |>.trans_eq
      (by simp [List.foldr_map])
  omega

/-- The levels list of `mkLevels`. -/
theorem mkLevels_ret (G : PGame n) (p : Bool) (alive : VSet n) :
    (mkLevels G p alive).ret.1 = (List.range (G.d + 1)).reverse.filter fun q =>
      q % 2 == 1 && (List.finRange n).any fun v => alive v && G.prio v + (if p then 1 else 0) == q :=
  rfl

theorem mkLifter_levelsOK (G : PGame n) (alive : VSet n) (p : Bool) :
    (mkLifter G alive p).ret.1.LevelsOK := rfl

section Levels

variable (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total)
include hc

theorem levels_sortedGT : c.levels.SortedGT := by
  rw [hc, mkLevels_ret]
  have : ((List.range (c.G.d + 1)).reverse).SortedGT :=
    List.sortedGT_reverse.2 (List.sortedLT_range _)
  exact (List.sortedGT_iff_pairwise.1 this).filter _ |>.sortedGT

theorem mem_levels (q : ℕ) : q ∈ c.levels ↔ q ∈ (c.game h).oddPrios c.X := by
  rw [Game.mem_oddPrios, hc, mkLevels_ret]
  simp only [List.mem_filter, List.mem_reverse, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, List.mem_finRange, true_and, Set.mem_image]
  constructor
  · rintro ⟨-, hodd, v, hv, rfl⟩
    refine ⟨⟨v, hv, ?_⟩, hodd⟩
    rw [Ctx.game_prio]; rfl
  · rintro ⟨⟨v, hv, rfl⟩, hodd⟩
    rw [Ctx.game_prio] at hodd ⊢
    refine ⟨?_, hodd, v, hv, rfl⟩
    have := prio_lt_d c.G v
    unfold Ctx.prio; split <;> omega

theorem levels_eq_sort :
    c.levels = (((c.game h).oddPrios c.X).sort fun a b => a ≤ b).reverse :=
  List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT (fun q => by
    rw [mem_levels c hc h, Finset.mem_sort]) (levels_sortedGT c hc)
    (Finset.sortedLT_sort _)

theorem height_eq : c.height = (c.game h).height c.X := by
  unfold Ctx.height Game.height
  rw [levels_eq_sort c hc h, List.length_reverse, Finset.length_sort]

theorem level_eq (l : ℕ) : c.level l = (c.game h).level c.X l := by
  unfold Ctx.level Game.level
  split_ifs with hl
  · rw [levels_eq_sort c hc h, Finset.orderEmbOfFin_apply]
    have hlen := Finset.length_sort (s := (c.game h).oddPrios c.X) (fun a b => a ≤ b)
    rw [List.getD_eq_getElem _ _ (by rw [List.length_reverse]; omega), List.getElem_reverse]
    congr 1
    simp only [hlen]
  · rw [List.getD_eq_default]
    rw [levels_eq_sort c hc h, List.length_reverse, Finset.length_sort]
    omega

omit hc in
theorem levels_eq_map : c.levels = (List.range c.height).map c.level := by
  apply List.ext_getElem
  · simp [Ctx.height]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Ctx.level]
    rw [List.getD_eq_getElem]

theorem depthOf_eq (v : Fin n) :
    depthOf c v = (c.game h).levelDepth c.X ((c.game h).prio v) := by
  classical
  unfold depthOf Game.levelDepth
  rw [← height_eq c hc h, Ctx.game_prio]
  conv_lhs => rw [levels_eq_map c]
  rw [List.filter_map, List.length_map]
  have hodd : ∀ l < c.height, c.level l % 2 = 1 := by
    intro l hl
    rw [level_eq c hc h]
    exact (c.game h).level_odd c.X (by rw [← height_eq c hc h]; exact hl)
  have : (List.range c.height).filter ((fun q => if c.prio v % 2 == 0 then decide (c.prio v < q)
      else decide (c.prio v ≤ q)) ∘ c.level) =
      (List.range c.height).filter fun l => decide (c.prio v ≤ (c.game h).level c.X l) := by
    apply List.filter_congr
    intro l hl
    rw [List.mem_range] at hl
    have := hodd l hl
    simp only [Function.comp, level_eq c hc h] at this ⊢
    split_ifs with he <;> simp only [decide_eq_decide] <;> simp at he <;> omega
  rw [this]
  rw [show (Finset.range c.height).filter (fun l => c.prio v ≤ (c.game h).level c.X l) =
    ⟨((List.range c.height).filter fun l => decide (c.prio v ≤ (c.game h).level c.X l) : List ℕ),
      (List.nodup_range).filter _⟩ by ext; simp]
  rfl

end Levels

/-! ### Weak components -/

/-- An edge of the program graph between two vertices of `S`. -/
def UE (c : Ctx n) (S : VSet n) (x y : Fin n) : Prop :=
  S x = true ∧ S y = true ∧ y ∈ c.G.succ x

theorem rtg_symm {α : Type} {r : α → α → Prop} (hs : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (hs _ _ hbc)).trans ih

theorem eqvGen_UE_mem {c : Ctx n} {S : VSet n} {x y : Fin n}
    (h : Relation.EqvGen (UE c S) x y) : x = y ∨ (S x = true ∧ S y = true) := by
  induction h with
  | rel a b h => exact Or.inr ⟨h.1, h.2.1⟩
  | refl => exact Or.inl rfl
  | symm a b _ ih =>
    rcases ih with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h.2, h.1⟩
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with rfl | h1
    · exact ih2
    · rcases ih2 with rfl | h2
      · exact Or.inr h1
      · exact Or.inr ⟨h1.1, h2.2⟩

theorem mem_undirected (c : Ctx n) (S : VSet n) (x y : Fin n) :
    y ∈ (undirected c S x).ret ↔
      ((y ∈ c.G.succ x ∧ c.alive y = true) ∨ (c.alive y = true ∧ x ∈ c.G.succ y)) ∧
        S y = true := by
  simp only [undirected, ret_bind, ret_tick, ret_pure, List.mem_filter, List.mem_append]
  rw [mem_succT, mem_predT]

/-- The search of `weakComponents` from a root of `S` finds exactly its component. -/
theorem reach_undirected (c : Ctx n) (S : VSet n) (hS : ∀ v, S v = true → c.alive v = true)
    {r : Fin n} (hr : S r = true) (z : Fin n) :
    (reachSet (undirected c S) S r).ret z = true ↔ Relation.EqvGen (UE c S) r z := by
  rw [reachSet_iff]
  constructor
  · intro h
    suffices Relation.EqvGen (UE c S) r z ∧ S z = true from this.1
    induction h with
    | refl => exact ⟨Relation.EqvGen.refl _, hr⟩
    | tail _ hst ih =>
      obtain ⟨hy, hSy⟩ := hst
      rw [mem_undirected] at hy
      refine ⟨Relation.EqvGen.trans _ _ _ ih.1 ?_, hSy⟩
      rcases hy.1 with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact Relation.EqvGen.rel _ _ ⟨ih.2, hSy, h1⟩
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hSy, ih.2, h1⟩)
  · intro h
    let Rs : Fin n → Fin n → Prop := fun a b => UE c S a b ∨ UE c S b a
    have h1 : Relation.ReflTransGen Rs r z := by
      clear hr
      induction h with
      | rel a b h => exact Relation.ReflTransGen.single (Or.inl h)
      | refl => exact Relation.ReflTransGen.refl
      | symm a b _ ih => exact rtg_symm (fun a b h => h.symm) ih
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) h1
    refine ⟨?_, ?_⟩
    · rw [mem_undirected]
      rcases hab with ⟨ha, hb, he⟩ | ⟨hb, ha, he⟩
      · exact ⟨Or.inl ⟨he, hS b hb⟩, hb⟩
      · exact ⟨Or.inr ⟨hS b hb, he⟩, hb⟩
    · rcases hab with ⟨-, hb, -⟩ | ⟨hb, -, -⟩ <;> exact hb

theorem wcStep_ret (c : Ctx n) (S : VSet n) (acc : VSet n × List (VSet n)) (root : Fin n) :
    (wcStep c S acc root).ret = if (S root && !acc.1 root) = true then
      (materialize fun v => acc.1 v || (reachSet (undirected c S) S root).ret v,
        acc.2 ++ [(reachSet (undirected c S) S root).ret]) else acc := by
  unfold wcStep
  simp only [ret_bind, ret_tick]
  split <;> simp

/-- The fold invariant of `weakComponents`. -/
def WCInv (c : Ctx n) (S : VSet n) (acc : VSet n × List (VSet n)) : Prop :=
  (∀ K ∈ acc.2, ∃ r, S r = true ∧ ∀ z, K z = true ↔ Relation.EqvGen (UE c S) r z) ∧
  (∀ z, acc.1 z = true → ∃ K ∈ acc.2, K z = true)

theorem wc_fold (c : Ctx n) (S : VSet n) (hS : ∀ v, S v = true → c.alive v = true) :
    ∀ (l : List (Fin n)) (acc : VSet n × List (VSet n)), WCInv c S acc →
      WCInv c S (l.foldl (fun b a => (wcStep c S b a).ret) acc) ∧
      (∀ u ∈ l, S u = true → (l.foldl (fun b a => (wcStep c S b a).ret) acc).1 u = true) ∧
      (∀ u, acc.1 u = true → (l.foldl (fun b a => (wcStep c S b a).ret) acc).1 u = true)
  | [], acc, h => ⟨h, by simp, fun _ h => h⟩
  | x :: l, acc, h => by
    simp only [List.foldl_cons]
    have hstep : WCInv c S (wcStep c S acc x).ret ∧
        (S x = true → (wcStep c S acc x).ret.1 x = true) ∧
        (∀ u, acc.1 u = true → (wcStep c S acc x).ret.1 u = true) := by
      rw [wcStep_ret]
      split
      · rename_i hx
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hx
        refine ⟨⟨fun K hK => ?_, fun z hz => ?_⟩, fun _ => ?_, fun u hu => ?_⟩
        · simp only [List.mem_append, List.mem_singleton] at hK
          rcases hK with hK | rfl
          · exact h.1 K hK
          · exact ⟨x, hx.1, reach_undirected c S hS hx.1⟩
        · simp only [materialize_apply, Bool.or_eq_true] at hz
          rcases hz with hz | hz
          · obtain ⟨K, hK, hKz⟩ := h.2 z hz
            exact ⟨K, by simp [hK], hKz⟩
          · exact ⟨_, by simp, hz⟩
        · simp only [materialize_apply, Bool.or_eq_true]
          right
          exact (reach_undirected c S hS hx.1 x).2 (Relation.EqvGen.refl _)
        · simp [hu]
      · rename_i hx
        refine ⟨h, fun hSx => ?_, fun u hu => hu⟩
        simpa [hSx] using hx
    obtain ⟨ih1, ih2, ih3⟩ := wc_fold c S hS l _ hstep.1
    refine ⟨ih1, fun u hu hSu => ?_, fun u hu => ih3 u (hstep.2.2 u hu)⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ih3 u (hstep.2.1 hSu)
    · exact ih2 u hu hSu

/-- Every vertex of `S` has its component among the computed weak components. -/
theorem weakComponents_cover (c : Ctx n) (S : VSet n) (hS : ∀ v, S v = true → c.alive v = true)
    {v : Fin n} (hv : S v = true) :
    ∃ K ∈ (weakComponents c S).ret, ∀ z, K z = true ↔ Relation.EqvGen (UE c S) v z := by
  have hret : (weakComponents c S).ret =
      ((List.finRange n).foldl (fun b a => (wcStep c S b a).ret) (VSet.empty, [])).2 := by
    simp [weakComponents, ret_foldlM]
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := wc_fold c S hS (List.finRange n) (VSet.empty, [])
    ⟨by simp, by simp [VSet.empty]⟩
  obtain ⟨K, hK, hKv⟩ := h2 v (h3 v (List.mem_finRange v) hv)
  obtain ⟨r, -, hr⟩ := h1 K hK
  refine ⟨K, hret ▸ hK, fun z => ?_⟩
  rw [hr]
  have hrv := (hr v).1 hKv
  exact ⟨fun h => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hrv) h,
    fun h => Relation.EqvGen.trans _ _ _ hrv h⟩

/-- Every computed weak component lies inside `S`. -/
theorem weakComponents_sub (c : Ctx n) (S : VSet n) (hS : ∀ v, S v = true → c.alive v = true) :
    ∀ K ∈ (weakComponents c S).ret, ∀ z, K z = true → S z = true := by
  have hret : (weakComponents c S).ret =
      ((List.finRange n).foldl (fun b a => (wcStep c S b a).ret) (VSet.empty, [])).2 := by
    simp [weakComponents, ret_foldlM]
  obtain ⟨⟨h1, -⟩, -, -⟩ := wc_fold c S hS (List.finRange n) (VSet.empty, [])
    ⟨by simp, by simp [VSet.empty]⟩
  intro K hK z hz
  obtain ⟨r, hr, hrz⟩ := h1 K (hret ▸ hK)
  rcases eqvGen_UE_mem ((hrz z).1 hz) with rfl | h
  · exact hr
  · exact h.2

theorem materialize_eq (S : VSet n) : materialize S = S := funext (materialize_apply S)

theorem children_ret (c : Ctx n) (l : ℕ) (R : VSet n) :
    (children c l R).ret = if (weakComponents c (fun v => R v && decide (c.prio v < c.level l))).ret.isEmpty
      then [VSet.empty] else (weakComponents c (fun v => R v && decide (c.prio v < c.level l))).ret := by
  simp only [children, ret_bind, ret_pure, materialize_eq]

theorem children_ne_nil (c : Ctx n) (l : ℕ) (R : VSet n) : (children c l R).ret ≠ [] := by
  rw [children_ret]
  split
  · simp
  · rename_i h; simpa using h

theorem children_sub (c : Ctx n) (l : ℕ) (R : VSet n) (hR : ∀ v, R v = true → c.alive v = true) :
    ∀ K ∈ (children c l R).ret, ∀ z, K z = true → R z = true := by
  rw [children_ret]
  split
  · simp [VSet.empty]
  · intro K hK z hz
    have := weakComponents_sub c _ (fun v hv => hR v (by simp at hv; exact hv.1)) K hK z hz
    simp at this
    exact this.1

/-- The context with the single level `q` (used by `Ctx.nb`). -/
def Ctx.atLevel (c : Ctx n) (q : ℕ) : Ctx n := { c with levels := [q], levels_le := by simp }

open scoped Classical in
theorem Ctx.nb_eq (c : Ctx n) (R : Set (Fin n)) (q : ℕ) :
    c.nb R q = ((children (c.atLevel q) 0 (fun v => decide (v ∈ R))).ret).map VSet.toSet := rfl

theorem children_atLevel (c : Ctx n) (l : ℕ) (R : VSet n) :
    (children c l R).ret = (children (c.atLevel (c.level l)) 0 R).ret := rfl

open scoped Classical in
theorem toSet_decide (R : VSet n) :
    (fun v => decide (v ∈ R.toSet)) = R := by
  funext v
  simp [VSet.toSet]

theorem Ctx.nb_toSet (c : Ctx n) (l : ℕ) (R : VSet n) :
    c.nb R.toSet (c.level l) = ((children c l R).ret).map VSet.toSet := by
  rw [Ctx.nb_eq, toSet_decide]
  rfl

/-- `Ctx.nb` lists every component (`Game.CompNumbering`). -/
theorem Ctx.compNumbering (c : Ctx n) (h : c.G.Total) :
    (c.game h).CompNumbering c.X c.nb := by
  classical
  intro R hR q K hK
  obtain ⟨v, hvR, hvq, rfl⟩ := hK
  rw [Ctx.nb_eq]
  set S : VSet n := fun v => decide (v ∈ R) && decide ((c.atLevel q).prio v < (c.atLevel q).level 0)
    with hSdef
  have hS : ∀ v, S v = true → (c.atLevel q).alive v = true := by
    intro v hv
    simp only [hSdef, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hR hv.1
  have hprio : ∀ v, (c.atLevel q).prio v = (c.game h).prio v := fun v => by
    rw [Ctx.game_prio]; rfl
  have hlev : (c.atLevel q).level 0 = q := rfl
  have hvS : S v = true := by simp [hSdef, hvR, hprio, hlev, hvq]
  obtain ⟨K', hK', hK'z⟩ := weakComponents_cover (c.atLevel q) S hS hvS
  have hrel : UE (c.atLevel q) S = (c.game h).LowEdge R q := by
    funext a b
    apply propext
    simp only [UE, Game.LowEdge, hSdef, Bool.and_eq_true, decide_eq_true_eq, hprio, hlev,
      Ctx.game_edge]
    constructor
    · rintro ⟨⟨ha, hpa⟩, ⟨hb, hpb⟩, he⟩; exact ⟨ha, hb, hpa, hpb, he⟩
    · rintro ⟨ha, hb, hpa, hpb, he⟩; exact ⟨⟨ha, hpa⟩, ⟨hb, hpb⟩, he⟩
  rw [children_ret]
  have hne : (weakComponents (c.atLevel q) S).ret.isEmpty = false := by
    cases hl : (weakComponents (c.atLevel q) S).ret with
    | nil => rw [hl] at hK'; simp at hK'
    | cons => rfl
  simp only [show (fun v => decide (v ∈ R) && decide ((c.atLevel q).prio v < (c.atLevel q).level 0))
    = S from rfl, hne, Bool.false_eq_true, ↓reduceIte, List.mem_map]
  refine ⟨K', hK', ?_⟩
  ext z
  simp only [VSet.toSet, Set.mem_setOf_eq, hK'z, hrel]
  rfl

/-! ### The chain bound -/

theorem iterT_ret_succ {α : Type} (f : α → TimeM ℕ α) :
    ∀ (k : ℕ) (a : α), (iterT f (k + 1) a).ret = (f (iterT f k a).ret).ret
  | 0, a => by simp [iterT]
  | k + 1, a => by
    rw [iterT, ret_bind, iterT_ret_succ f k]
    simp [iterT]

theorem rstep_succIn (c : Ctx n) (S : VSet n) (x y : Fin n) :
    RStep (succIn c S) S x y ↔ (y ∈ c.G.succ x ∧ c.alive y = true) ∧ S y = true := by
  simp only [RStep, succIn, ret_bind, ret_pure, List.mem_filter, mem_succT]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h2⟩

theorem chainRound_ret (S : VSet n) (reach : Fin n → VSet n) (weight best : Fin n → ℕ) :
    (chainRound S reach weight best).ret = fun u => weight u +
      ((List.finRange n).filter fun w => S w && reach u w && !reach w u).foldr
        (fun w a => max (best w) a) 0 := by
  funext u
  unfold chainRound
  rw [ret_foldlM]
  rw [show (fun b a => (chainEntry S reach weight best b a).ret) = fun b a => Function.update b a
    (weight a + ((List.finRange n).filter fun w => S w && reach a w && !reach w a).foldr
      (fun w a => max (best w) a) 0) from rfl, foldl_update]
  simp

theorem chainBound_ret (c : Ctx n) (R : VSet n) (q : ℕ) :
    (chainBound c R q).ret =
      ((List.finRange n).filter fun v => R v && decide (c.prio v ≤ q)).foldr (fun u a => max
        ((iterT (chainRound (fun v => R v && decide (c.prio v ≤ q))
          (fun u => (reachSet (succIn c fun v => R v && decide (c.prio v ≤ q))
            (fun v => R v && decide (c.prio v ≤ q)) u).ret)
          (fun u => ((List.finRange n).filter fun x => (R x && decide (c.prio x ≤ q)) &&
            (reachSet (succIn c fun v => R v && decide (c.prio v ≤ q))
              (fun v => R v && decide (c.prio v ≤ q)) u).ret x &&
            (reachSet (succIn c fun v => R v && decide (c.prio v ≤ q))
              (fun v => R v && decide (c.prio v ≤ q)) x).ret u && c.prio x == q).length))
          (n + 1) (fun _ => 0)).ret u) a) 0 := by
  simp only [chainBound, ret_bind, ret_pure, materialize_eq, ret_foldlM, weightStep, reachStep]
  rw [foldl_update_eq _ _ _ List.mem_finRange, foldl_update_eq _ _ _ List.mem_finRange]

section DP

variable (c : Ctx n) (S : VSet n) (q : ℕ) (hS : ∀ v, S v = true → c.alive v = true)
  (rc : Fin n → VSet n)
  (hrc : ∀ u x, rc u x = true ↔ Relation.ReflTransGen (RStep (succIn c S) S) u x)

/-- The number of priority-`q` positions of a path. -/
def qcnt (a : ℕ → Fin n) (len : ℕ) : ℕ :=
  ((Finset.range (len + 1)).filter fun i => c.prio (a i) = q).card

/-- The `k`-th Jacobi iterate of the chain-bound DP. -/
def dpB (wt : Fin n → ℕ) (k : ℕ) : Fin n → ℕ := (iterT (chainRound S rc wt) k (fun _ => 0)).ret

include hS hrc in
theorem path_reach {a : ℕ → Fin n} {len : ℕ} (haS : ∀ i ≤ len, S (a i) = true)
    (hedge : ∀ i < len, a (i + 1) ∈ c.G.succ (a i)) :
    ∀ j ≤ len, ∀ i, j ≤ i → i ≤ len → rc (a j) (a i) = true := by
  intro j _ i hji hi
  rw [hrc]
  induction i, hji using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ i hji ih =>
    refine (ih (by omega)).tail ?_
    rw [rstep_succIn]
    exact ⟨⟨hedge i (by omega), hS _ (haS _ hi)⟩, haS _ hi⟩

theorem qcnt_split (a : ℕ → Fin n) (len j : ℕ) (hj : j ≤ len) :
    qcnt c q a len = ((Finset.range j).filter fun i => c.prio (a i) = q).card +
      qcnt c q (fun i => a (j + i)) (len - j) := by
  unfold qcnt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    show len + 1 = j + (len - j + 1) by omega, Finset.sum_range_add]

include hS hrc in
theorem dp_ge (wt : Fin n → ℕ)
    (hwt : ∀ u, wt u = ((List.finRange n).filter fun x =>
      S x && rc u x && rc x u && c.prio x == q).length) :
    ∀ (k : ℕ) (u : Fin n), S u = true → (Finset.univ.filter fun x => rc u x = true).card ≤ k →
      ∀ (len : ℕ) (a : ℕ → Fin n), a 0 = u → (∀ i ≤ len, S (a i) = true) →
      (∀ i < len, a (i + 1) ∈ c.G.succ (a i)) →
      (∀ i ≤ len, ∀ j ≤ len, c.prio (a i) = q → a i = a j → i = j) →
      qcnt c q a len ≤ dpB S rc wt k u := by
  intro k
  induction k with
  | zero =>
    intro u _ hcard
    exfalso
    have : u ∈ Finset.univ.filter fun x => rc u x = true := by
      simp [(hrc u u).2 Relation.ReflTransGen.refl]
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at this
    simp at this
  | succ k ih =>
    intro u hu hcard len a ha0 haS hedge hinj
    have hreach := path_reach c S hS rc hrc haS hedge
    unfold dpB
    rw [iterT_ret_succ, chainRound_ret]
    dsimp only
    -- positions in the strongly connected set of `u` are bounded by the weight
    have hpre : ∀ j ≤ len + 1, (∀ i < j, rc (a i) u = true) →
        ((Finset.range j).filter fun i => c.prio (a i) = q).card ≤ wt u := by
      intro j hj hall
      rw [hwt, length_filter_finRange]
      apply Finset.card_le_card_of_injOn a
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨⟨haS i (by omega), ?_⟩, hall i hi.1⟩, hi.2⟩
        rw [← ha0]; exact hreach 0 (by omega) i (by omega) (by omega)
      · intro x hx y hy hxy
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
        exact hinj x (by omega) y (by omega) hx.2 hxy
    by_cases hall : ∀ i ≤ len, rc (a i) u = true
    · have := hpre (len + 1) le_rfl (fun i hi => hall i (by omega))
      unfold qcnt
      omega
    · push Not at hall
      classical
      have hex : ∃ j, j ≤ len ∧ rc (a j) u = false := by
        obtain ⟨j, hj, hj'⟩ := hall
        exact ⟨j, hj, by simpa using hj'⟩
      let j := Nat.find hex
      have hj : j ≤ len ∧ rc (a j) u = false := Nat.find_spec hex
      have hjmin : ∀ i < j, rc (a i) u = true := fun i hi => by
        by_contra hne
        exact Nat.find_min hex hi ⟨by omega, by simpa using hne⟩
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · exfalso
          have := hj.2
          rw [h0, ha0, (hrc u u).2 Relation.ReflTransGen.refl] at this
          cases this
        · exact h0
      rw [qcnt_split c q a len j hj.1]
      have h1 := hpre j (by omega) hjmin
      -- the rest of the path starts in a later strongly connected set
      have hlater : a j ∈ (List.finRange n).filter fun w => S w && rc u w && !rc w u := by
        simp only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true]
        refine ⟨⟨haS j hj.1, ?_⟩, hj.2⟩
        rw [← ha0]; exact hreach 0 (by omega) j (by omega) hj.1
      have hsub : (Finset.univ.filter fun x => rc (a j) x = true) ⊂
          (Finset.univ.filter fun x => rc u x = true) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨u, by simp [(hrc u u).2 Relation.ReflTransGen.refl], ?_⟩
          simpa using hj.2
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rw [hrc] at hx ⊢
          have : rc u (a j) = true := by rw [← ha0]; exact hreach 0 (by omega) j (by omega) hj.1
          rw [hrc] at this
          exact this.trans hx
      have h2 := ih (a j) (haS j hj.1) (by have := Finset.card_lt_card hsub; omega) (len - j)
        (fun i => a (j + i)) rfl (fun i hi => haS _ (by omega))
        (fun i hi => by rw [show j + (i + 1) = j + i + 1 by omega]; exact hedge _ (by omega))
        (fun i hi i' hi' hq he => by have := hinj (j + i) (by omega) (j + i') (by omega) hq he; omega)
      have h3 := le_foldr_max (dpB S rc wt k) _ _ hlater
      unfold dpB at h2 h3
      omega

end DP

/-- The program's chain bound is at least the library's (for a region of alive vertices). -/
theorem chainBound_ge (c : Ctx n) (h : c.G.Total) (R : VSet n)
    (hR : ∀ v, R v = true → c.alive v = true) (q : ℕ) :
    (c.game h).chainBound R.toSet q ≤ (chainBound c R q).ret := by
  set S : VSet n := fun v => R v && decide (c.prio v ≤ q) with hSdef
  have hS : ∀ v, S v = true → c.alive v = true := fun v hv => hR v (by
    simp only [hSdef, Bool.and_eq_true] at hv; exact hv.1)
  set rc : Fin n → VSet n := fun u => (reachSet (succIn c S) S u).ret with hrcdef
  have hrc : ∀ u x, rc u x = true ↔ Relation.ReflTransGen (RStep (succIn c S) S) u x :=
    fun u x => reachSet_iff _ _ _ _
  rw [chainBound_ret]
  apply csSup_le'
  rintro m ⟨len, a, ha, hedge, hinj, rfl⟩
  have haS : ∀ i ≤ len, S (a i) = true := fun i hi => by
    obtain ⟨h1, h2⟩ := ha i hi
    rw [Ctx.game_prio] at h2
    simp [hSdef, h1, VSet.toSet] at h1 ⊢
    exact ⟨h1, h2⟩
  have hk := dp_ge c S q hS rc hrc _ (fun u => rfl) (n + 1) (a 0) (haS 0 (by omega))
    (by have := Finset.card_le_univ (Finset.univ.filter fun x => rc (a 0) x = true)
        simp at this ⊢; omega) len a rfl haS
    (fun i hi => (Ctx.game_edge c h _ _).1 (hedge i hi))
    (fun i hi j hj hq he => hinj i hi j hj (by rw [Ctx.game_prio]; exact hq) he)
  refine le_trans ?_ (le_trans hk (le_foldr_max _ _ (a 0) (by
    simp only [List.mem_filter, List.mem_finRange, true_and]; exact haS 0 (by omega))))
  unfold qcnt
  apply le_of_eq
  congr 1
  ext i
  simp [Ctx.game_prio]

/-! ### Regions of a path -/

theorem regionsOf_cons_cons (c : Ctx n) (l : ℕ) (R : VSet n) (x y : ℕ × ℕ)
    (rest : List (ℕ × ℕ)) :
    (regionsOf c l R (x :: y :: rest)).ret =
      R :: (regionsOf c (l + 1) ((children c l R).ret.getD y.1 VSet.empty) (y :: rest)).ret := by
  obtain ⟨k, cnt⟩ := y
  simp [regionsOf]

/-- The region selected from `R0` by the component indices `idx 1, idx 2, …`. -/
def progRegion (c : Ctx n) (R0 : VSet n) (idx : ℕ → ℕ) : ℕ → VSet n
  | 0 => R0
  | l + 1 => (children c l (progRegion c R0 idx l)).ret.getD (idx (l + 1)) VSet.empty

theorem progRegion_congr (c : Ctx n) (R0 : VSet n) {idx idx' : ℕ → ℕ} :
    ∀ j, (∀ i, 1 ≤ i → i ≤ j → idx i = idx' i) → progRegion c R0 idx j = progRegion c R0 idx' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [progRegion]
    rw [progRegion_congr c R0 j (fun i h1 h2 => h i h1 (by omega)), h (j + 1) (by omega) le_rfl]

theorem regionsOf_spec (c : Ctx n) (R0 : VSet n) (idx : ℕ → ℕ) :
    ∀ (P : List (ℕ × ℕ)) (l : ℕ),
      (∀ i, 1 ≤ i → i < P.length → (P.getD i (0, 0)).1 = idx (l + i)) →
      ∀ j < P.length, (regionsOf c l (progRegion c R0 idx l) P).ret.getD j VSet.empty =
        progRegion c R0 idx (l + j)
  | [], l, _, j, hj => by simp at hj
  | [x], l, _, j, hj => by
    simp only [List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    simp [regionsOf]
  | x :: y :: rest, l, hidx, j, hj => by
    rw [regionsOf_cons_cons]
    have hy : y.1 = idx (l + 1) := by
      have := hidx 1 le_rfl (by simp)
      simpa using this
    have hR' : (children c l (progRegion c R0 idx l)).ret.getD y.1 VSet.empty =
        progRegion c R0 idx (l + 1) := by
      rw [hy]; rfl
    rw [hR']
    rcases j with _ | j
    · simp
    · rw [List.getD_cons_succ, regionsOf_spec c R0 idx (y :: rest) (l + 1) (fun i hi1 hi2 => by
        have := hidx (i + 1) (by omega) (by simp only [List.length_cons] at hi2 ⊢; omega)
        rw [show l + (i + 1) = l + 1 + i by omega] at this
        simpa using this) j (by simp only [List.length_cons] at hj ⊢; omega)]
      congr 1
      omega

theorem toSet_empty : (VSet.empty : VSet n).toSet = ∅ := by
  ext; simp [VSet.toSet, VSet.empty]

theorem getD_mem_or {α : Type} (L : List α) (i : ℕ) (d : α) : L.getD i d ∈ L ∨ L.getD i d = d := by
  by_cases hi : i < L.length
  · left; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · right; exact List.getD_eq_default _ _ (by omega)

theorem progRegion_sub (c : Ctx n) (idx : ℕ → ℕ) :
    ∀ l v, progRegion c c.alive idx l v = true → c.alive v = true
  | 0, v, hv => hv
  | l + 1, v, hv => by
    simp only [progRegion] at hv
    rcases getD_mem_or (children c l (progRegion c c.alive idx l)).ret (idx (l + 1))
      VSet.empty with hm | he
    · exact progRegion_sub c idx l v (children_sub c l _ (progRegion_sub c idx l) _ hm v hv)
    · rw [he] at hv; simp [VSet.empty] at hv

theorem progRegion_toSet (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total) (a : ℕ → ℕ) :
    ∀ l, (progRegion c c.alive (fun i => a (2 * i)) l).toSet =
      (c.game h).leafRegionBy c.X c.nb a l
  | 0 => rfl
  | l + 1 => by
    show ((children c l _).ret.getD (a (2 * (l + 1))) VSet.empty).toSet =
      (c.nb ((c.game h).leafRegionBy c.X c.nb a l) ((c.game h).level c.X l)).getD
        (a (2 * (l + 1))) ∅
    rw [← progRegion_toSet c hc h a l, ← level_eq c hc h, Ctx.nb_toSet, ← toSet_empty,
      List.getD_map]

/-! ### Tuples of lists -/

theorem tup_concat_lt (P : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    ∀ i < 2 * P.length, tup (P ++ [x]) i = tup P i :=
  tup_eq_of_getD fun l hl => List.getD_append _ _ _ _ hl

theorem tup_concat_fst (P : List (ℕ × ℕ)) (x : ℕ × ℕ) : tup (P ++ [x]) (2 * P.length) = x.1 := by
  rw [tup_even, List.getD_append_right _ _ _ _ le_rfl]; simp

theorem tup_concat_snd (P : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    tup (P ++ [x]) (2 * P.length + 1) = x.2 := by
  rw [tup_odd, List.getD_append_right _ _ _ _ le_rfl]; simp

theorem tup_pad (P : List (ℕ × ℕ)) (m : ℕ) : tup (P ++ List.replicate m (0, 0)) = tup P := by
  funext i
  unfold tup
  have : ∀ l, (P ++ List.replicate m (0, 0)).getD l (0, 0) = P.getD l (0, 0) := by
    intro l
    by_cases hl : l < P.length
    · exact List.getD_append _ _ _ _ hl
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default P _ (by omega)]
      by_cases hl' : l - P.length < m
      · rw [List.getD_replicate _ hl']
      · rw [List.getD_eq_default _ _ (by simp; omega)]
  simp only [this]

theorem tup_take (x : List (ℕ × ℕ)) (d : ℕ) : ∀ i < 2 * d, tup (x.take d) i = tup x i :=
  tup_eq_of_getD fun l hl => by
    by_cases hlx : l < x.length
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hlx,
        List.getElem_take]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- A tuple that is strictly below another at some position (equal before it) is below it at
    every depth. -/
theorem lexLE_of_lt_at {f g : ℕ → ℕ} {p : ℕ} (hpre : ∀ j < p, f j = g j) (hp : f p < g p) :
    ∀ m, LexLE m f g := by
  intro m
  rw [lexLE_iff]
  intro i _ hi
  rcases Nat.lt_trichotomy i p with h | rfl | h
  · exact (hpre i h).le
  · exact hp.le
  · exact absurd (hi p h) hp.ne

/-- The first position where a tuple strictly below another (at depth `m`) differs. -/
theorem exists_first_lt {m : ℕ} {f g : ℕ → ℕ} (h : ¬ LexLE m g f) :
    ∃ p < m, (∀ j < p, f j = g j) ∧ f p < g p := by
  rw [lexLE_iff] at h
  push Not at h
  obtain ⟨p, hp, hpre, hlt⟩ := h
  exact ⟨p, hp, fun j hj => (hpre j hj).symm, hlt⟩

/-! ### Tree navigation -/

theorem nextAux_ret_concat (c : Ctx n) (regs : List (VSet n)) (f : ℕ) (P : List (ℕ × ℕ))
    (k cnt : ℕ) :
    (nextAux c regs (f + 1) (P ++ [(k, cnt)])).ret =
      if cnt < (chainBound c (regs.getD P.length VSet.empty) (c.level P.length)).ret then
        some (P ++ [(k, cnt + 1)])
      else if 0 < P.length then
        (if k + 1 < (children c (P.length - 1) (regs.getD (P.length - 1) VSet.empty)).ret.length
          then some (P ++ [(k + 1, 0)]) else (nextAux c regs f P).ret)
      else (nextAux c regs f P).ret := by
  rw [nextAux]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append,
    List.length_singleton, Nat.add_sub_cancel, ret_bind, List.dropLast_concat]
  split_ifs <;> simp_all [List.set_append_right] <;> (split_ifs <;> first | rfl | omega)

theorem nextAux_ret_nil (c : Ctx n) (regs : List (VSet n)) (f : ℕ) :
    (nextAux c regs f []).ret = none := by
  cases f <;> simp [nextAux]

theorem nextAux_ret_zero (c : Ctx n) (regs : List (VSet n)) (P : List (ℕ × ℕ)) :
    (nextAux c regs 0 P).ret = none := by
  simp [nextAux]

/-- Soundness of `nextAux`: the result is no longer than the path and strictly above it. -/
theorem nextAux_sound (c : Ctx n) (regs : List (VSet n)) :
    ∀ (f : ℕ) (P nx : List (ℕ × ℕ)), (nextAux c regs f P).ret = some nx →
      nx.length ≤ P.length ∧ ¬ LexLE (2 * P.length) (tup nx) (tup P)
  | 0, P, nx, h => by rw [nextAux_ret_zero] at h; cases h
  | f + 1, P, nx, h => by
    rcases List.eq_nil_or_concat P with rfl | ⟨P', ⟨k, cnt⟩, rfl⟩
    · rw [nextAux_ret_nil] at h; cases h
    rw [List.concat_eq_append] at h ⊢
    rw [nextAux_ret_concat] at h
    have hstrict : ∀ x : ℕ × ℕ, (k < x.1 ∨ (k = x.1 ∧ cnt < x.2)) →
        ¬ LexLE (2 * (P' ++ [(k, cnt)]).length) (tup (P' ++ [x])) (tup (P' ++ [(k, cnt)])) := by
      intro x hx hle
      rw [lexLE_iff] at hle
      simp only [List.length_append, List.length_singleton] at hle
      rcases hx with hx | ⟨hx1, hx2⟩
      · have := hle (2 * P'.length) (by omega) (fun j hj => by
          rw [tup_concat_lt _ _ j hj, tup_concat_lt _ _ j hj])
        rw [tup_concat_fst, tup_concat_fst] at this
        simp at this; omega
      · have := hle (2 * P'.length + 1) (by omega) (fun j hj => by
          rcases Nat.lt_or_ge j (2 * P'.length) with hj' | hj'
          · rw [tup_concat_lt _ _ j hj', tup_concat_lt _ _ j hj']
          · obtain rfl : j = 2 * P'.length := by omega
            rw [tup_concat_fst, tup_concat_fst]; exact hx1.symm)
        rw [tup_concat_snd, tup_concat_snd] at this
        simp at this; omega
    split_ifs at h
    · cases h
      exact ⟨by simp, hstrict _ (Or.inr ⟨rfl, by simp⟩)⟩
    · cases h
      exact ⟨by simp, hstrict _ (Or.inl (by simp))⟩
    all_goals
      obtain ⟨h1, h2⟩ := nextAux_sound c regs f P' nx h
      refine ⟨by simp; omega, fun hle => h2 ?_⟩
      have := LexLE.mono (show 2 * P'.length ≤ 2 * (P' ++ [(k, cnt)]).length by simp) hle
      exact (lexLE_congr (fun i _ => rfl) (fun i hi => tup_concat_lt _ _ i hi)).1 this

section Least

variable (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total)

/-- The regions recorded for a path agree with the library's leaf regions for every chain leaf
    whose component indices agree with the path. -/
def RegsOK (regs : List (VSet n)) (a : ℕ → ℕ) (P : List (ℕ × ℕ)) : Prop :=
  ∀ j < P.length, (∀ i, 1 ≤ i → i ≤ j → a (2 * i) = (P.getD i (0, 0)).1) →
    (regs.getD j VSet.empty).toSet = (c.game h).leafRegionBy c.X c.nb a j ∧
      ∀ v, regs.getD j VSet.empty v = true → c.alive v = true

include hc in
theorem regsOK_regionsOf (a : ℕ → ℕ) (P : List (ℕ × ℕ)) :
    RegsOK c h (regionsOf c 0 c.alive P).ret a P := by
  intro j hj hidx
  have hreg := regionsOf_spec c c.alive (fun i => (P.getD i (0, 0)).1) P 0
    (fun i _ _ => by simp) j hj
  simp only [zero_add] at hreg
  rw [show c.alive = progRegion c c.alive (fun i => (P.getD i (0, 0)).1) 0 from rfl, hreg,
    progRegion_congr c c.alive j (idx' := fun i => a (2 * i)) (fun i h1 h2 => (hidx i h1 h2).symm)]
  exact ⟨progRegion_toSet c hc h a j, progRegion_sub c _ j⟩

theorem regsOK_dropLast {regs : List (VSet n)} {a : ℕ → ℕ} {P : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hr : RegsOK c h regs a (P ++ [x])) : RegsOK c h regs a P := by
  intro j hj hidx
  exact hr j (by simp; omega) fun i h1 h2 => by
    rw [hidx i h1 h2, List.getD_append _ _ _ _ (by omega)]

theorem tup_concat_lt' {P : List (ℕ × ℕ)} {d : ℕ} (hd : P.length = d) (x : ℕ × ℕ) :
    ∀ i < 2 * d, tup (P ++ [x]) i = tup P i := hd ▸ tup_concat_lt P x

theorem tup_concat_fst' {P : List (ℕ × ℕ)} {d : ℕ} (hd : P.length = d) (x : ℕ × ℕ) :
    tup (P ++ [x]) (2 * d) = x.1 := hd ▸ tup_concat_fst P x

theorem tup_concat_snd' {P : List (ℕ × ℕ)} {d : ℕ} (hd : P.length = d) (x : ℕ × ℕ) :
    tup (P ++ [x]) (2 * d + 1) = x.2 := hd ▸ tup_concat_snd P x

include hc in
/-- Leastness of `nextAux`: for a chain leaf `a` strictly above the path (at the path's depth),
    `nextAux` finds a node, and it is below `a` at every depth. -/
theorem nextAux_least (a : ℕ → ℕ) (ha : (c.game h).IsChainLeafBy c.X c.nb a)
    (regs : List (VSet n)) :
    ∀ (f : ℕ) (P : List (ℕ × ℕ)), P.length ≤ c.height → P.length ≤ f → RegsOK c h regs a P →
      ¬ LexLE (2 * P.length) a (tup P) →
      ∃ nx, (nextAux c regs f P).ret = some nx ∧ ∀ m, LexLE m (tup nx) a
  | f, [], _, _, _, hlt => absurd (Or.inl fun i hi => by simp at hi) hlt
  | 0, _ :: _, _, hf, _, _ => by simp at hf
  | f + 1, x :: xs, hlen, hf, hregs, hlt => by
    obtain ⟨P', ⟨k, cnt⟩, hP⟩ : ∃ P' y, x :: xs = P' ++ [y] := by
      rcases List.eq_nil_or_concat (x :: xs) with h' | ⟨P', y, h'⟩
      · simp at h'
      · exact ⟨P', y, by rw [h', List.concat_eq_append]⟩
    rw [hP] at hlen hf hregs hlt ⊢
    simp only [List.length_append, List.length_singleton] at hlen hf hlt
    obtain ⟨d, hd⟩ : ∃ d, P'.length = d := ⟨_, rfl⟩
    rw [hd] at hlen hf hlt
    obtain ⟨hleaf0, hleafk, hleafc, -⟩ := id ha
    have hh : (c.game h).height c.X = c.height := (height_eq c hc h).symm
    obtain ⟨p, hp, hpre, hplt⟩ := exists_first_lt hlt
    have hgetd : ((P' ++ [(k, cnt)]).getD d (0, 0)) = (k, cnt) := by
      rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hd]
    -- indices of the path agree with the leaf's up to `j` when `2 j < p`
    have hidx_lt : ∀ j, 2 * j < p → ∀ i, 1 ≤ i → i ≤ j →
        a (2 * i) = ((P' ++ [(k, cnt)]).getD i (0, 0)).1 := by
      intro j hpj i _ hi
      have := hpre (2 * i) (by omega)
      rw [tup_even] at this
      exact this.symm
    -- the program's bound at depth `d` dominates the leaf's counter when indices agree
    have hcnt : (∀ i, 1 ≤ i → i ≤ d → a (2 * i) = ((P' ++ [(k, cnt)]).getD i (0, 0)).1) →
        a (2 * d + 1) ≤ (chainBound c (regs.getD d VSet.empty) (c.level d)).ret := by
      intro hidx
      obtain ⟨hR, hRsub⟩ := hregs d (by simp [hd]) hidx
      refine le_trans (hleafc d (by omega)) ?_
      rw [← hR, ← level_eq c hc h]
      exact chainBound_ge c h _ hRsub _
    -- if the first difference is the counter at depth `d`, it exceeds the program's bound
    have hC : p = 2 * d + 1 → cnt < (chainBound c (regs.getD d VSet.empty) (c.level d)).ret := by
      intro hpd
      subst hpd
      have h1 := hcnt (fun i h1 h2 => by
        rcases Nat.lt_or_ge i d with hid | hid
        · exact hidx_lt d (by omega) i h1 (by omega)
        · obtain rfl : i = d := by omega
          have := hpre (2 * i) (by omega)
          rw [tup_concat_fst' hd] at this
          rw [hgetd]
          exact this.symm)
      rw [tup_concat_snd' hd] at hplt
      simp only at hplt
      omega
    -- a node `P' ++ [y]` below `a` at depth `d + 1` is below it everywhere
    have hfin : ∀ y : ℕ × ℕ, LexLE (2 * (d + 1)) (tup (P' ++ [y])) a →
        ∀ m, LexLE m (tup (P' ++ [y])) a := fun y hy =>
      lexLE_of_zero_tail hy (fun i hi => tup_zero_tail _ i (by simp; omega))
    have hcases : p < 2 * d ∨ p = 2 * d ∨ p = 2 * d + 1 := by omega
    have hA : p < 2 * d → ∀ y : ℕ × ℕ, ∀ m, LexLE m (tup (P' ++ [y])) a := by
      intro hpd y
      refine lexLE_of_lt_at (p := p) (fun j hj => ?_) ?_
      · rw [tup_concat_lt' hd _ j (by omega), ← hpre j hj, tup_concat_lt' hd _ j (by omega)]
      · rw [tup_concat_lt' hd _ p hpd, ← tup_concat_lt' hd (k, cnt) p hpd]; exact hplt
    rw [nextAux_ret_concat, hd]
    split_ifs with hb hd0 hsib
    · -- increment the counter
      refine ⟨_, rfl, ?_⟩
      rcases hcases with hpd | rfl | rfl
      · exact hA hpd _
      · refine lexLE_of_lt_at (p := 2 * d) (fun j hj => ?_) ?_
        · rw [tup_concat_lt' hd _ j hj, ← hpre j hj, tup_concat_lt' hd _ j hj]
        · rw [tup_concat_fst' hd]; rw [tup_concat_fst' hd] at hplt; exact hplt
      · apply hfin
        rw [lexLE_iff]
        intro i hi hpi
        rcases Nat.lt_or_ge i (2 * d) with hi' | hi'
        · rw [tup_concat_lt' hd _ i hi', ← tup_concat_lt' hd (k, cnt) i hi', hpre i (by omega)]
        · rcases (show i = 2 * d ∨ i = 2 * d + 1 by omega) with rfl | rfl
          · rw [tup_concat_fst' hd, ← hpre (2 * d) (by omega), tup_concat_fst' hd]
          · rw [tup_concat_snd' hd]; rw [tup_concat_snd' hd] at hplt; simp at hplt ⊢; omega
    · -- next sibling
      refine ⟨_, rfl, ?_⟩
      rcases hcases with hpd | rfl | rfl
      · exact hA hpd _
      · rw [tup_concat_fst' hd] at hplt
        simp only at hplt
        rcases Nat.lt_or_ge (k + 1) (a (2 * d)) with hk | hk
        · refine lexLE_of_lt_at (p := 2 * d) (fun j hj => ?_) ?_
          · rw [tup_concat_lt' hd _ j hj, ← hpre j hj, tup_concat_lt' hd _ j hj]
          · rw [tup_concat_fst' hd]; exact hk
        · apply hfin
          rw [lexLE_iff]
          intro i hi hpi
          rcases Nat.lt_or_ge i (2 * d) with hi' | hi'
          · rw [tup_concat_lt' hd _ i hi', ← tup_concat_lt' hd (k, cnt) i hi', hpre i (by omega)]
          · rcases (show i = 2 * d ∨ i = 2 * d + 1 by omega) with rfl | rfl
            · rw [tup_concat_fst' hd]; simp; omega
            · rw [tup_concat_snd' hd]; simp
      · exact absurd (hC rfl) hb
    all_goals
      -- recursion on the shorter path
      have hshort : ¬ LexLE (2 * d) a (tup P') := by
        rcases hcases with hpd | rfl | rfl
        · intro hle
          rw [lexLE_iff] at hle
          have := hle p hpd (fun j hj => by
            rw [← tup_concat_lt' hd (k, cnt) j (by omega)]; exact (hpre j hj).symm)
          rw [← tup_concat_lt' hd (k, cnt) p hpd] at this
          omega
        · exfalso
          rw [tup_concat_fst' hd] at hplt
          simp only at hplt
          rcases Nat.eq_zero_or_pos d with hd0' | hd0'
          · rw [hd0', mul_zero, hleaf0] at hplt; omega
          · have hsib' : ¬ k + 1 <
                (children c (d - 1) (regs.getD (d - 1) VSet.empty)).ret.length := by
              first | exact hsib | exact absurd hd0' hd0
            have hk := hleafk (d - 1) (by omega)
            obtain ⟨hR, -⟩ := hregs (d - 1) (by simp; omega) (hidx_lt (d - 1) (by omega))
            rw [← hR, ← level_eq c hc h, Ctx.nb_toSet, List.length_map,
              show d - 1 + 1 = d by omega] at hk
            have hne := children_ne_nil c (d - 1) (regs.getD (d - 1) VSet.empty)
            have : 1 ≤ (children c (d - 1) (regs.getD (d - 1) VSet.empty)).ret.length := by
              cases hl : (children c (d - 1) (regs.getD (d - 1) VSet.empty)).ret
              · exact absurd hl hne
              · simp
            rw [max_eq_right this] at hk
            omega
        · exact absurd (hC rfl) hb
      have hd1 : 1 ≤ d := by
        by_contra h0
        exact hshort (Or.inl fun i hi => by omega)
      exact nextAux_least a ha regs f P' (by omega) (by omega) (regsOK_dropLast c h hregs)
        (by rw [hd]; exact hshort)

end Least

/-! ### `prog` -/

theorem leftmost_ret (c : Ctx n) (pre : List (ℕ × ℕ)) :
    (leftmost c pre).ret = pre ++ List.replicate (c.height - pre.length) (0, 0) := by
  simp [leftmost]

theorem nextNode_ret (c : Ctx n) (pre : List (ℕ × ℕ)) :
    (nextNode c pre).ret = (nextAux c (regionsOf c 0 c.alive pre).ret pre.length pre).ret := by
  simp [nextNode]

theorem prog_ret_none (c : Ctx n) (v : Fin n) : (prog c v none).ret = none := by
  simp [prog]

theorem prog_ret_even (c : Ctx n) (v : Fin n) (x : List (ℕ × ℕ)) (hv : c.prio v % 2 = 0) :
    (prog c v (some x)).ret = some ((leftmost c (x.take (depthOf c v))).ret) := by
  simp [prog, hv]

theorem prog_ret_odd (c : Ctx n) (v : Fin n) (x : List (ℕ × ℕ)) (hv : c.prio v % 2 = 1) :
    (prog c v (some x)).ret =
      ((nextNode c (x.take (depthOf c v))).ret).map fun nx => (leftmost c nx).ret := by
  simp only [prog, ret_bind, hv]
  simp only [show ((1 : ℕ) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, ret_bind]
  split <;> simp_all

theorem prog_len (c : Ctx n) (v : Fin n) (t : Val) (r : List (ℕ × ℕ))
    (h : (prog c v t).ret = some r) : r.length = c.height := by
  have hd := depthOf_le c v
  cases t with
  | none => rw [prog_ret_none] at h; cases h
  | some x =>
    rcases Nat.mod_two_eq_zero_or_one (c.prio v) with hv | hv
    · rw [prog_ret_even c v x hv] at h
      cases h
      rw [leftmost_ret]
      simp only [List.length_append, List.length_take, List.length_replicate]
      omega
    · rw [prog_ret_odd c v x hv] at h
      obtain ⟨nx, hnx, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [nextNode_ret] at hnx
      have := (nextAux_sound c _ _ _ _ hnx).1
      rw [leftmost_ret]
      simp only [List.length_append, List.length_replicate, List.length_take] at this ⊢
      omega

/-- Soundness of `prog`: its result progresses from the target at the depth of `v`, strictly for
    odd priorities. -/
theorem prog_sound (c : Ctx n) (v : Fin n) (x r : List (ℕ × ℕ))
    (h : (prog c v (some x)).ret = some r) (hx : c.height ≤ x.length) :
    LexLE (2 * depthOf c v) (tup x) (tup r) ∧
      (c.prio v % 2 = 1 → ¬ LexLE (2 * depthOf c v) (tup r) (tup x)) := by
  have hd := depthOf_le c v
  have htake := tup_take x (depthOf c v)
  rcases Nat.mod_two_eq_zero_or_one (c.prio v) with hv | hv
  · rw [prog_ret_even c v x hv] at h
    cases h
    rw [leftmost_ret, tup_pad]
    refine ⟨(lexLE_congr (fun i _ => rfl) (fun i hi => (htake i hi).symm)).1 (LexLE.refl _ _),
      fun h' => by omega⟩
  · rw [prog_ret_odd c v x hv] at h
    obtain ⟨nx, hnx, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [nextNode_ret] at hnx
    have hs := (nextAux_sound c _ _ _ _ hnx).2
    rw [List.length_take, min_eq_left (by omega)] at hs
    rw [leftmost_ret, tup_pad]
    have hns : ¬ LexLE (2 * depthOf c v) (tup nx) (tup x) := fun hle =>
      hs ((lexLE_congr (fun i _ => rfl) (fun i hi => (htake i hi).symm)).1 hle)
    exact ⟨(lexLE_total _ _ _).resolve_right hns, fun _ => hns⟩

/-- Leastness of `prog`: if the chain leaf `aw` progresses (at `v`'s depth) to the chain leaf
    `av`, then `prog` applied to any value below `aw` gives a value below `av`. -/
theorem prog_least (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total) (v : Fin n) (aw av : ℕ → ℕ)
    (hav : (c.game h).IsChainLeafBy c.X c.nb av)
    (hle : LexLE (2 * depthOf c v) aw av)
    (hlt : c.prio v % 2 = 1 → ¬ LexLE (2 * depthOf c v) av aw)
    (x : List (ℕ × ℕ)) (hx : x.length = c.height) (hxw : LexLE (2 * c.height) (tup x) aw) :
    ∃ r, (prog c v (some x)).ret = some r ∧ ∀ m, LexLE m (tup r) av := by
  have hd := depthOf_le c v
  have htake := tup_take x (depthOf c v)
  have hxw' : LexLE (2 * depthOf c v) (tup x) aw := LexLE.mono (by omega) hxw
  rcases Nat.mod_two_eq_zero_or_one (c.prio v) with hv | hv
  · rw [prog_ret_even c v x hv]
    refine ⟨_, rfl, ?_⟩
    rw [leftmost_ret, tup_pad]
    apply lexLE_of_zero_tail (m := 2 * depthOf c v)
    · exact (lexLE_congr (fun i hi => (htake i hi).symm) (fun i _ => rfl)).1 (hxw'.trans hle)
    · intro i hi
      exact tup_zero_tail _ i (by rw [List.length_take]; omega)
  · rw [prog_ret_odd c v x hv, nextNode_ret]
    have hnot : ¬ LexLE (2 * (x.take (depthOf c v)).length) av (tup (x.take (depthOf c v))) := by
      rw [List.length_take, min_eq_left (by omega)]
      intro hle'
      have := (lexLE_congr (fun i _ => rfl) (fun i hi => htake i hi)).1 hle'
      exact hlt hv (this.trans hxw')
    obtain ⟨nx, hnx, hnle⟩ := nextAux_least c hc h av hav _ _ _
      (by rw [List.length_take]; omega) le_rfl (regsOK_regionsOf c hc h av _) hnot
    rw [hnx]
    refine ⟨_, rfl, ?_⟩
    simp only [leftmost_ret, tup_pad]
    exact hnle

end ParityGame.TwoSidedCost

end TwoSidedCostCorrectTreeProofs
