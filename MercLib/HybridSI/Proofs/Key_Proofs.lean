module

public import MercLib.HybridSI.Proofs.Lasso_Proofs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section HybridSIKeyProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Keys from the point of view of a player `i`: `kf G f i x` is the key for Even and its
componentwise negation for Odd, so that player `i` always prefers larger values. Its components
are `rI` (reward of the cycle maximum), `sI` (signed sum over `bSet`) and `eI` (signed steps), with
the one-step recursions along the profile. `top_dominates`: a sum of distinct signed powers
`± 2^rank` has the sign of its greatest term. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### Ranks -/

theorem rank_eq_card (x : V) : rank x = (Finset.univ.filter (· < x)).card := by
  unfold rank univList
  rw [← List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).filter _), List.toFinset_filter,
    Finset.sort_toFinset]
  rfl

theorem rank_lt_rank {x y : V} (h : x < y) : rank x < rank y := by
  rw [rank_eq_card, rank_eq_card]
  refine Finset.card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.trans h
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ x, h⟩)
    simp at this

theorem rank_lt_rank_iff {x y : V} : rank x < rank y ↔ x < y := by
  constructor
  · intro h
    by_contra h'
    rcases (not_lt.1 h').lt_or_eq with h'' | h''
    · exact absurd (rank_lt_rank h'') (by omega)
    · subst h''; omega
  · exact rank_lt_rank

theorem rank_injective : Injective (rank : V → ℕ) := by
  intro x y h
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact absurd (rank_lt_rank h') (by omega)
  · exact absurd (rank_lt_rank h') (by omega)

/-! ### Signed sums of powers of two -/

/-- `δ` is a signed power of two at every vertex. -/
def SignedPow (δ : V → ℤ) : Prop := ∀ y, δ y = 2 ^ rank y ∨ δ y = -(2 ^ rank y)

theorem abs_sum_lt_of_lt (δ : V → ℤ) (hδ : SignedPow δ) (D : Finset V) (t : V)
    (hD : ∀ y ∈ D, y < t) : |∑ y ∈ D, δ y| < 2 ^ rank t := by
  have h1 : |∑ y ∈ D, δ y| ≤ ∑ y ∈ D, (2 : ℤ) ^ rank y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    rcases hδ y with h | h <;> simp [h]
  have h2 : ∑ y ∈ D, (2 : ℤ) ^ rank y ≤ ∑ j ∈ Finset.range (rank t), (2 : ℤ) ^ j := by
    rw [← Finset.sum_image (f := fun j => (2 : ℤ) ^ j) (fun x _ y _ h => rank_injective h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun _ _ _ => by positivity)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (rank_lt_rank (hD y hy))
  have h3 : ∑ j ∈ Finset.range (rank t), (2 : ℤ) ^ j < 2 ^ rank t := by
    have := geom_sum_mul_add 1 (rank t) (R := ℤ)
    norm_num at this
    omega
  omega

/-- A sum of distinct signed powers of two has the sign of its greatest term. -/
theorem top_dominates (δ : V → ℤ) (hδ : SignedPow δ) (D : Finset V) (t : V) (ht : t ∈ D)
    (hmax : ∀ y ∈ D, y ≤ t) : (0 < ∑ y ∈ D, δ y ↔ 0 < δ t) ∧ ∑ y ∈ D, δ y ≠ 0 := by
  rw [← Finset.add_sum_erase D δ ht]
  have hr := abs_sum_lt_of_lt δ hδ (D.erase t) t fun y hy =>
    lt_of_le_of_ne (hmax y (Finset.mem_of_mem_erase hy)) (Finset.ne_of_mem_erase hy)
  have hpos : (0 : ℤ) < 2 ^ rank t := by positivity
  rw [abs_lt] at hr
  rcases hδ t with h | h <;> rw [h] <;> constructor <;> omega

/-- Comparing two signed sums over sets decides the comparison of their parts at or above any
    threshold `m` in the same direction. -/
theorem upper_le_of_le (δ : V → ℤ) (hδ : SignedPow δ) (A B : Finset V) (m : V)
    (h : ∑ y ∈ A, δ y ≤ ∑ y ∈ B, δ y) :
    ∑ y ∈ A.filter (m ≤ ·), δ y ≤ ∑ y ∈ B.filter (m ≤ ·), δ y := by
  classical
  -- the difference as a sum over the symmetric difference
  let ε : V → ℤ := fun y => if y ∈ B then δ y else -δ y
  have hε : SignedPow ε := fun y => by
    simp only [ε]; split_ifs
    · exact hδ y
    · rcases hδ y with h | h <;> rw [h] <;> simp
  have hdiff : ∀ X Y : Finset V, X ⊆ A → Y ⊆ B → (∀ y ∈ A, y ∈ X ↔ y ∈ Y ∨ y ∉ B) →
      True := fun _ _ _ _ _ => trivial
  clear hdiff
  have split : ∀ P : V → Prop, [DecidablePred P] →
      ∑ y ∈ B.filter P, δ y - ∑ y ∈ A.filter P, δ y =
        ∑ y ∈ (symmDiff A B).filter P, ε y := by
    intro P _
    have hB : B.filter P = (B \ A).filter P ∪ (A ∩ B).filter P := by
      ext y; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hA : A.filter P = (A \ B).filter P ∪ (A ∩ B).filter P := by
      ext y; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hS : (symmDiff A B).filter P = (A \ B).filter P ∪ (B \ A).filter P := by
      ext y; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_symmDiff]
      tauto
    have d1 : Disjoint ((B \ A).filter P) ((A ∩ B).filter P) := by
      rw [Finset.disjoint_left]; intro y h1 h2
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter] at h1 h2; tauto
    have d2 : Disjoint ((A \ B).filter P) ((A ∩ B).filter P) := by
      rw [Finset.disjoint_left]; intro y h1 h2
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter] at h1 h2; tauto
    have d3 : Disjoint ((A \ B).filter P) ((B \ A).filter P) := by
      rw [Finset.disjoint_left]; intro y h1 h2
      simp only [Finset.mem_filter, Finset.mem_sdiff] at h1 h2; tauto
    rw [hB, hA, hS, Finset.sum_union d1, Finset.sum_union d2, Finset.sum_union d3]
    have e1 : ∑ y ∈ (A \ B).filter P, ε y = -∑ y ∈ (A \ B).filter P, δ y := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_filter, Finset.mem_sdiff] at hy
      simp [ε, hy.1.2]
    have e2 : ∑ y ∈ (B \ A).filter P, ε y = ∑ y ∈ (B \ A).filter P, δ y := by
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_filter, Finset.mem_sdiff] at hy
      simp [ε, hy.1.1]
    rw [e1, e2]; ring
  have hall := split (fun _ => True)
  simp only [Finset.filter_true] at hall
  have hup := split (m ≤ ·)
  by_cases hD : (symmDiff A B).filter (m ≤ ·) = ∅
  · rw [hD, Finset.sum_empty] at hup
    omega
  · obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image ((symmDiff A B).filter (m ≤ ·)) id
      (Finset.nonempty_iff_ne_empty.2 hD)
    simp only [id] at hmax
    have htD : t ∈ symmDiff A B := (Finset.mem_filter.1 ht).1
    have hmt : m ≤ t := (Finset.mem_filter.1 ht).2
    -- `t` is also the greatest element of the whole symmetric difference
    have hmax' : ∀ y ∈ symmDiff A B, y ≤ t := by
      intro y hy
      by_cases hmy : m ≤ y
      · exact hmax y (Finset.mem_filter.2 ⟨hy, hmy⟩)
      · exact (le_of_lt (lt_of_not_ge hmy)).trans hmt
    have hd1 := top_dominates ε hε _ t htD hmax'
    have hd2 := top_dominates ε hε _ t ht hmax
    have : 0 < ∑ y ∈ symmDiff A B, ε y := lt_of_le_of_ne (by omega) (Ne.symm hd1.2)
    have := hd2.1.2 (hd1.1.1 this)
    omega

/-! ### Keys for a player -/

/-- Componentwise negation of a key. -/
def negK (κ : Key) : Key := toLex (-(ofLex κ).1, toLex (-(ofLex (ofLex κ).2).1, -(ofLex (ofLex κ).2).2))

/-- Player `i`'s view of a key: the key itself for Even, its negation for Odd. -/
def kfor (i : Player) (κ : Key) : Key := match i with
  | .zero => κ
  | .one => negK κ

theorem lex_le_iff (a b : ℤ) (c d : Lex (ℤ × ℤ)) :
    (toLex (a, c) : Key) ≤ toLex (b, d) ↔ a < b ∨ (a = b ∧ c ≤ d) := Prod.Lex.toLex_le_toLex

theorem lex2_le_iff (a b c d : ℤ) :
    (toLex (a, c) : Lex (ℤ × ℤ)) ≤ toLex (b, d) ↔ a < b ∨ (a = b ∧ c ≤ d) :=
  Prod.Lex.toLex_le_toLex

theorem negK_le_negK (κ κ' : Key) : negK κ ≤ negK κ' ↔ κ' ≤ κ := by
  have e : ∀ κ : Key,
      κ = toLex ((ofLex κ).1, toLex ((ofLex (ofLex κ).2).1, (ofLex (ofLex κ).2).2)) := fun _ => rfl
  generalize ha : (ofLex κ).1 = a
  generalize hb : (ofLex (ofLex κ).2).1 = b
  generalize hc : (ofLex (ofLex κ).2).2 = c
  generalize ha' : (ofLex κ').1 = a'
  generalize hb' : (ofLex (ofLex κ').2).1 = b'
  generalize hc' : (ofLex (ofLex κ').2).2 = c'
  have hk : κ = toLex (a, toLex (b, c)) := by rw [e κ, ha, hb, hc]
  have hk' : κ' = toLex (a', toLex (b', c')) := by rw [e κ', ha', hb', hc']
  subst hk hk'
  simp only [negK, ofLex_toLex, lex_le_iff, lex2_le_iff]
  omega

/-- `p` favours player `i`. -/
def Good (i : Player) (p : ℕ) : Prop := Player.ofPrio p = i

instance (i : Player) (p : ℕ) : Decidable (Good i p) := by unfold Good; infer_instance

variable (G : Game V) (f : V → V)

/-- Player `i`'s signed weight of a vertex. -/
def wI (i : Player) (y : V) : ℤ := if Good i (G.prio y) then 2 ^ rank y else -(2 ^ rank y)

/-- Player `i`'s reward of a cycle maximum. -/
def rI (i : Player) (l : V) : ℤ := if Good i (G.prio l) then (rank l : ℤ) + 1 else -((rank l : ℤ) + 1)

/-- Player `i`'s signed step count. -/
def eI (i : Player) (l : V) (k : ℕ) : ℤ := if Good i (G.prio l) then -(k : ℤ) else k

theorem wI_signed (i : Player) : SignedPow (wI G i) := fun y => by
  unfold wI; split_ifs <;> simp

theorem good_zero_iff (p : ℕ) : Good .zero p ↔ p % 2 = 0 := by
  unfold Good Player.ofPrio; split_ifs with h <;> simp [h]

theorem good_one_iff (p : ℕ) : Good .one p ↔ ¬ p % 2 = 0 := by
  unfold Good Player.ofPrio; split_ifs with h <;> simp [h]

/-- Player `i`'s view of the key of `x`, in components. -/
theorem kfor_key (i : Player) (x : V) :
    kfor i (key G f x) = toLex (rI G i (cycMax f x),
      toLex (∑ y ∈ bSet f x, wI G i y, eI G i (cycMax f x) (stepsTo f x))) := by
  cases i
  · have hs : (bSet f x).sum (weight G) = ∑ y ∈ bSet f x, wI G .zero y :=
      Finset.sum_congr rfl fun y _ => by simp only [weight, wI, good_zero_iff]
    simp only [kfor, key]
    rw [hs]
    simp only [rI, eI, good_zero_iff]
  · have hs : -(bSet f x).sum (weight G) = ∑ y ∈ bSet f x, wI G .one y := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [weight, wI, good_one_iff]
      split_ifs <;> ring
    simp only [kfor, key, negK, ofLex_toLex]
    rw [hs]
    simp only [rI, eI, good_one_iff]
    split_ifs <;> simp

/-! ### One-step recursions of the components -/

variable {G f}

theorem rI_pos_iff (i : Player) (l : V) : 0 < rI G i l ↔ Good i (G.prio l) := by
  unfold rI; split_ifs with h <;> simp [h]

theorem rI_inj {i : Player} {l l' : V} (h : rI G i l = rI G i l') (hpos : 0 < rI G i l) : l = l' := by
  have hl := (rI_pos_iff i l).1 hpos
  have hl' : Good i (G.prio l') := (rI_pos_iff i l').1 (h ▸ hpos)
  unfold rI at h
  rw [ite_eq_left hl, ite_eq_left hl'] at h
  exact rank_injective (by omega)

theorem sum_bSet_self {x : V} (h : x = cycMax f x) (i : Player) :
    ∑ y ∈ bSet f x, wI G i y = 0 := by
  rw [bSet_eq_empty h, Finset.sum_empty]

theorem sum_bSet_apply {x : V} (h : x ≠ cycMax f x) (i : Player) :
    ∑ y ∈ bSet f x, wI G i y =
      ∑ y ∈ bSet f (f x), wI G i y + if cycMax f x < x then wI G i x else 0 := by
  rw [bSet_apply h]
  split_ifs with hlt
  · rw [Finset.sum_insert (not_mem_bSet_apply hlt), add_comm]
  · simp

/-- The part of the signed sum at or above `m`, along one step. -/
theorem upper_bSet_apply {x m : V} (h : x ≠ cycMax f x) (i : Player) :
    ∑ y ∈ (bSet f x).filter (m ≤ ·), wI G i y =
      ∑ y ∈ (bSet f (f x)).filter (m ≤ ·), wI G i y +
        if cycMax f x < x ∧ m ≤ x then wI G i x else 0 := by
  rw [bSet_apply h]
  split_ifs with hlt hlt' hlt'
  · rw [Finset.filter_insert, ite_eq_left hlt'.2,
      Finset.sum_insert (fun hx => not_mem_bSet_apply hlt (Finset.mem_filter.1 hx).1), add_comm]
  · rw [Finset.filter_insert, ite_eq_right (fun hm => hlt' ⟨hlt, hm⟩), add_zero]
  · exact absurd hlt'.1 hlt
  · rw [add_zero]

end MercLib.HybridSI

end HybridSIKeyProofs
