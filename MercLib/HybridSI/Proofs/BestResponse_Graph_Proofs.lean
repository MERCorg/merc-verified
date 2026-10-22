module

public import MercLib.HybridSI.BestResponse
public import MercLib.HybridSI.Proofs.Correctness_Proofs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section HybridSIBestResponseGraphProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Generic facts behind `bestResponse`: tables (`mat`), timed iteration (`iterT`), backward
reachability (`reachFrom` computes `Reach`, by stabilisation of a monotone chain of sets), and
Bellman–Ford (`bfVal` is a fixpoint of `bfRound` when every simple cycle avoiding the targets is
negative, `NegCyc`: a strict increase in round `|V| + 1` would give a chain of `|V| + 1` strict
increases along edges, which repeats a vertex, and the cycle in between cannot pay for it). -/

open Function Cslib.Algorithms.Lean

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### Tables and loops -/

theorem mat_eq {α : Type*} (d : α) (f : V → α) : mat d f = f :=
  funext fun v => look_tabulate f d v

theorem matV_eq (f : V → V) : matV f = f := funext fun v => look_tabulate f v v

theorem ret_iterT {α : Type*} (f : α → TimeM ℕ α) :
    ∀ (k : ℕ) (a : α), (iterT f k a).ret = (fun a => (f a).ret)^[k] a
  | 0, _ => rfl
  | k + 1, a => by
    simp only [iterT, TimeM.ret_bind, iterate_succ_apply]
    exact ret_iterT f k _

theorem time_iterT_le {α : Type*} (f : α → TimeM ℕ α) (K : ℕ) (hf : ∀ a, (f a).time ≤ K) :
    ∀ (k : ℕ) (a : α), (iterT f k a).time ≤ k * K
  | 0, _ => by simp [iterT]
  | k + 1, a => by
    simp only [iterT, TimeM.time_bind]
    have := time_iterT_le f K hf k (f a).ret
    have := hf a
    rw [Nat.succ_mul]; omega

/-! ### Reachability -/

variable (nb : V → List V)

/-- `u` reaches `x` along `nb`-edges whose sources lie in `S`. -/
def Reach (S : V → Bool) (u x : V) : Prop :=
  Relation.ReflTransGen (fun a b => S a = true ∧ b ∈ nb a) u x

theorem reachRound_apply (S X : V → Bool) (v : V) :
    reachRound nb S X v = (X v || (S v && (nb v).any X)) := by
  unfold reachRound; rw [mat_eq]

/-- The `j`-th reachability iterate. -/
abbrev reachIt (S : V → Bool) (x : V) (j : ℕ) : V → Bool :=
  (reachRound nb S)^[j] fun v => decide (v = x)

theorem reachIt_succ (S : V → Bool) (x : V) (j : ℕ) :
    reachIt nb S x (j + 1) = reachRound nb S (reachIt nb S x j) := by
  simp only [reachIt, iterate_succ_apply']

theorem reachIt_le_succ (S : V → Bool) (x : V) (j : ℕ) (v : V) (h : reachIt nb S x j v = true) :
    reachIt nb S x (j + 1) v = true := by
  rw [reachIt_succ, reachRound_apply, h, Bool.true_or]

theorem reachIt_mono (S : V → Bool) (x : V) {j k : ℕ} (hjk : j ≤ k) (v : V)
    (h : reachIt nb S x j v = true) : reachIt nb S x k v = true := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact reachIt_le_succ nb S x k v ih

theorem reachIt_zero (S : V → Bool) (x v : V) : reachIt nb S x 0 v = true ↔ v = x := by
  simp [reachIt]

/-- One unfolding of an iterate. -/
theorem reachIt_cases (S : V → Bool) (x : V) (j : ℕ) (v : V)
    (h : reachIt nb S x (j + 1) v = true) :
    reachIt nb S x j v = true ∨ (S v = true ∧ ∃ w ∈ nb v, reachIt nb S x j w = true) := by
  rw [reachIt_succ, reachRound_apply] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨h1, w, hw, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, w, hw, h2⟩

theorem reachIt_sound (S : V → Bool) (x : V) :
    ∀ (j : ℕ) (v : V), reachIt nb S x j v = true → Reach nb S v x
  | 0, v, h => by rw [(reachIt_zero nb S x v).1 h]; exact Relation.ReflTransGen.refl
  | j + 1, v, h => by
    rcases reachIt_cases nb S x j v h with h | ⟨h1, w, hw, h2⟩
    · exact reachIt_sound S x j v h
    · exact Relation.ReflTransGen.head ⟨h1, hw⟩ (reachIt_sound S x j w h2)

/-- The iterates stabilise within `|V|` rounds. -/
theorem reachIt_stable (S : V → Bool) (x : V) :
    reachIt nb S x (Fintype.card V + 1) = reachIt nb S x (Fintype.card V) := by
  classical
  let F : ℕ → Finset V := fun j => Finset.univ.filter fun v => reachIt nb S x j v = true
  have hsub : ∀ j, F j ⊆ F (j + 1) := fun j v hv => by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact reachIt_le_succ nb S x j v hv
  -- once two consecutive iterates agree, all later ones do
  have hfix : ∀ j, reachIt nb S x (j + 1) = reachIt nb S x j →
      ∀ k, reachIt nb S x (j + k) = reachIt nb S x j := by
    intro j hj k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, reachIt_succ, ih, ← reachIt_succ, hj]
  by_contra hne
  have hgrow : ∀ j ≤ Fintype.card V, j + 1 ≤ (F j).card := by
    intro j hj
    induction j with
    | zero =>
      exact Finset.card_pos.2 ⟨x, by
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; exact (reachIt_zero nb S x x).2 rfl⟩
    | succ j ih =>
      have ih := ih (by omega)
      have hne' : F j ≠ F (j + 1) := by
        intro he
        apply hne
        have heq : reachIt nb S x (j + 1) = reachIt nb S x j := by
          funext v
          have := congrArg (v ∈ ·) he
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at this
          cases h1 : reachIt nb S x (j + 1) v <;> cases h2 : reachIt nb S x j v <;> simp_all
        have h1 := hfix j heq (Fintype.card V + 1 - j)
        have h2 := hfix j heq (Fintype.card V - j)
        rw [show j + (Fintype.card V + 1 - j) = Fintype.card V + 1 by omega] at h1
        rw [show j + (Fintype.card V - j) = Fintype.card V by omega] at h2
        rw [h1, h2]
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub j, hne'⟩)
      omega
  have := hgrow (Fintype.card V) le_rfl
  have := Finset.card_le_univ (F (Fintype.card V))
  omega

theorem reachFrom_eq (S : V → Bool) (x : V) :
    reachFrom nb S x = reachIt nb S x (Fintype.card V) := rfl

theorem reachFrom_iff (S : V → Bool) (x v : V) : reachFrom nb S x v = true ↔ Reach nb S v x := by
  refine ⟨reachIt_sound nb S x _ v, fun h => ?_⟩
  rw [reachFrom_eq]
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact reachIt_mono nb S x (Nat.zero_le _) x ((reachIt_zero nb S x x).2 rfl)
  | @head a b hab _ ih =>
    rw [← reachIt_stable, reachIt_succ, reachRound_apply]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
    exact Or.inr ⟨hab.1, b, hab.2, ih⟩

theorem ret_reachFromT (S : V → Bool) (x : V) : (reachFromT nb S x).ret = reachFrom nb S x := by
  unfold reachFromT reachFrom
  rw [ret_iterT]
  rfl

theorem time_reachFromT (S : V → Bool) (x : V) :
    (reachFromT nb S x).time ≤ Fintype.card V * roundCost nb := by
  unfold reachFromT
  exact time_iterT_le _ _ (fun a => by simp) _ _

/-! ### Maxima over lists -/

theorem le_foldr_max (f : V → WithBot ℤ) : ∀ (ws : List V) (w : V), w ∈ ws →
    f w ≤ ws.foldr (fun w a => max (f w) a) ⊥
  | [], _, h => absurd h List.not_mem_nil
  | x :: ws, w, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max f ws w h).trans (le_max_right _ _)

theorem foldr_max_le (f : V → WithBot ℤ) (b : WithBot ℤ) :
    ∀ (ws : List V), (∀ w ∈ ws, f w ≤ b) → ws.foldr (fun w a => max (f w) a) ⊥ ≤ b
  | [], _ => bot_le
  | x :: ws, h => by
    simp only [List.foldr_cons]
    exact max_le (h x List.mem_cons_self) (foldr_max_le f b ws fun w hw => h w (List.mem_cons_of_mem _ hw))

theorem foldr_max_cases (f : V → WithBot ℤ) : ∀ (ws : List V),
    ws.foldr (fun w a => max (f w) a) ⊥ = ⊥ ∨ ∃ w ∈ ws, ws.foldr (fun w a => max (f w) a) ⊥ = f w
  | [] => Or.inl rfl
  | x :: ws => by
    simp only [List.foldr_cons]
    rcases foldr_max_cases f ws with h | ⟨w, hw, h⟩
    · rw [h]; exact Or.inr ⟨x, List.mem_cons_self, by simp⟩
    · rcases le_total (f x) (ws.foldr (fun w a => max (f w) a) ⊥) with hle | hle
      · rw [max_eq_right hle, h]; exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
      · rw [max_eq_left hle]; exact Or.inr ⟨x, List.mem_cons_self, rfl⟩

theorem argmaxBy_spec (D : V → WithBot ℤ) (d : V) : ∀ (ws : List V), ws ≠ [] →
    argmaxBy D d ws ∈ ws ∧ ∀ w ∈ ws, D w ≤ D (argmaxBy D d ws) := by
  have key : ∀ (ws : List V) (b : V),
      (ws.foldl (fun b x => if D b < D x then x else b) b = b ∨
        ws.foldl (fun b x => if D b < D x then x else b) b ∈ ws) ∧
      D b ≤ D (ws.foldl (fun b x => if D b < D x then x else b) b) ∧
      ∀ w ∈ ws, D w ≤ D (ws.foldl (fun b x => if D b < D x then x else b) b) := by
    intro ws
    induction ws with
    | nil => intro b; simp
    | cons x ws ih =>
      intro b
      simp only [List.foldl_cons]
      obtain ⟨h1, h2, h3⟩ := ih (if D b < D x then x else b)
      by_cases hb : D b < D x
      · simp only [hb, ite_true] at h1 h2 h3 ⊢
        refine ⟨?_, le_of_lt (lt_of_lt_of_le hb h2), ?_⟩
        · rcases h1 with h | h
          · rw [h]; exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem _ h)
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact h2
          · exact h3 w hw
      · simp only [hb, ite_false] at h1 h2 h3 ⊢
        refine ⟨?_, h2, ?_⟩
        · rcases h1 with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact (not_lt.1 hb).trans h2
          · exact h3 w hw
  intro ws hws
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hws
  obtain ⟨h1, h2, h3⟩ := key (x :: xs) x
  refine ⟨?_, fun w hw => h3 w hw⟩
  rcases h1 with h | h
  · simp only [argmaxBy, List.headD_cons]; rw [h]; exact List.mem_cons_self
  · exact h

/-! ### Bellman–Ford -/

variable (tgt : V → Bool) (c : V → ℤ)

/-- The `j`-th Bellman–Ford iterate. -/
abbrev bfIt (j : ℕ) : V → WithBot ℤ := (bfRound nb tgt c)^[j] (bfInit tgt)

theorem bfRound_apply (D : V → WithBot ℤ) (v : V) : bfRound nb tgt c D v =
    if tgt v then 0 else (nb v).foldr (fun w a => max ((c v : WithBot ℤ) + D w) a) ⊥ := by
  unfold bfRound; rw [mat_eq]

theorem bfIt_succ (j : ℕ) : bfIt nb tgt c (j + 1) = bfRound nb tgt c (bfIt nb tgt c j) := by
  simp only [bfIt, iterate_succ_apply']

theorem bfRound_mono {D D' : V → WithBot ℤ} (h : ∀ v, D v ≤ D' v) (v : V) :
    bfRound nb tgt c D v ≤ bfRound nb tgt c D' v := by
  rw [bfRound_apply, bfRound_apply]
  split_ifs
  · exact le_rfl
  · refine foldr_max_le _ _ _ fun w hw => ?_
    exact (add_le_add_right (h w) _).trans (le_foldr_max (fun w => (c v : WithBot ℤ) + D' w) _ w hw)

theorem bfIt_le_succ : ∀ (j : ℕ) (v : V), bfIt nb tgt c j v ≤ bfIt nb tgt c (j + 1) v
  | 0, v => by
    rw [bfIt_succ, bfRound_apply]
    simp only [bfIt, iterate_zero, id, bfInit]
    split_ifs <;> simp
  | j + 1, v => by
    rw [bfIt_succ nb tgt c (j + 1)]
    conv_lhs => rw [bfIt_succ nb tgt c j]
    exact bfRound_mono nb tgt c (bfIt_le_succ j) v

theorem bfIt_mono {j k : ℕ} (hjk : j ≤ k) (v : V) : bfIt nb tgt c j v ≤ bfIt nb tgt c k v := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (bfIt_le_succ nb tgt c k v)

theorem bfIt_tgt (j : ℕ) (v : V) (h : tgt v = true) : bfIt nb tgt c j v = 0 := by
  cases j with
  | zero => simp [bfIt, bfInit, h]
  | succ j => rw [bfIt_succ, bfRound_apply, ite_eq_left h]

/-- A strict increase in round `j + 2` comes from a strict increase in round `j + 1` at a
    successor. -/
theorem bfIt_step (j : ℕ) (u : V) (h : bfIt nb tgt c (j + 1) u < bfIt nb tgt c (j + 2) u) :
    ∃ w ∈ nb u, tgt u = false ∧
      bfIt nb tgt c (j + 2) u = (c u : WithBot ℤ) + bfIt nb tgt c (j + 1) w ∧
      bfIt nb tgt c j w < bfIt nb tgt c (j + 1) w := by
  have ht : tgt u = false := by
    by_contra ht
    simp only [Bool.not_eq_false] at ht
    rw [bfIt_tgt nb tgt c _ u ht, bfIt_tgt nb tgt c _ u ht] at h
    exact lt_irrefl _ h
  have hfold := bfRound_apply nb tgt c (bfIt nb tgt c (j + 1)) u
  rw [ite_eq_right (by simp [ht]), ← bfIt_succ] at hfold
  rcases foldr_max_cases (fun w => (c u : WithBot ℤ) + bfIt nb tgt c (j + 1) w) (nb u) with
    h0 | ⟨w, hw, hmax⟩
  · rw [hfold, h0] at h; exact absurd h (not_lt_bot)
  refine ⟨w, hw, ht, hfold.trans hmax, ?_⟩
  by_contra hnot
  have hle : bfIt nb tgt c (j + 1) w ≤ bfIt nb tgt c j w := not_lt.1 hnot
  have h1 := bfRound_apply nb tgt c (bfIt nb tgt c j) u
  rw [ite_eq_right (by simp [ht]), ← bfIt_succ] at h1
  have : (c u : WithBot ℤ) + bfIt nb tgt c (j + 1) w ≤ bfIt nb tgt c (j + 1) u := by
    rw [h1]
    exact (add_le_add_right hle _).trans
      (le_foldr_max (fun w => (c u : WithBot ℤ) + bfIt nb tgt c j w) _ w hw)
  rw [hfold, hmax] at h
  exact absurd (lt_of_lt_of_le h this) (lt_irrefl _)

/-- A chain of strict increases. -/
theorem bfIt_chain : ∀ (j : ℕ) (u : V), bfIt nb tgt c j u < bfIt nb tgt c (j + 1) u →
    ∃ s : ℕ → V, s 0 = u ∧ ∀ i ≤ j,
      bfIt nb tgt c (j - i) (s i) < bfIt nb tgt c (j + 1 - i) (s i) ∧
      (i < j → s (i + 1) ∈ nb (s i) ∧ tgt (s i) = false ∧
        bfIt nb tgt c (j + 1 - i) (s i) = (c (s i) : WithBot ℤ) + bfIt nb tgt c (j - i) (s (i + 1)))
  | 0, u, h => ⟨fun _ => u, rfl, fun i hi => by
      obtain rfl : i = 0 := by omega
      exact ⟨h, fun h => absurd h (lt_irrefl 0)⟩⟩
  | j + 1, u, h => by
    obtain ⟨w, hw, ht, heq, hlt⟩ := bfIt_step nb tgt c j u h
    obtain ⟨s', hs0, hs⟩ := bfIt_chain j w hlt
    refine ⟨fun i => match i with | 0 => u | k + 1 => s' k, rfl, fun i hi => ?_⟩
    rcases i with _ | i
    · refine ⟨h, fun _ => ?_⟩
      simp only [hs0]
      exact ⟨hw, ht, heq⟩
    · obtain ⟨h1, h2⟩ := hs i (by omega)
      simp only [show j + 1 - (i + 1) = j - i by omega, show j + 1 + 1 - (i + 1) = j + 1 - i by omega]
      exact ⟨h1, fun hi' => h2 (by omega)⟩

/-- Every simple cycle avoiding the targets has negative weight. -/
def NegCyc : Prop :=
  ∀ (s : ℕ → V) (a b : ℕ), a < b → s b = s a →
    (∀ k, a ≤ k → k < b → s (k + 1) ∈ nb (s k) ∧ tgt (s k) = false) →
    Set.InjOn s (Set.Ico a b) → ∑ k ∈ Finset.Ico a b, c (s k) < 0

theorem bfVal_eq : bfVal nb tgt c = bfIt nb tgt c (Fintype.card V) := rfl

/-- Bellman–Ford has converged after `|V|` rounds. -/
theorem bfVal_fix (hneg : NegCyc nb tgt c) : bfRound nb tgt c (bfVal nb tgt c) = bfVal nb tgt c := by
  classical
  set N := Fintype.card V
  funext v
  rw [bfVal_eq, ← bfIt_succ]
  by_contra hne
  have hlt : bfIt nb tgt c N v < bfIt nb tgt c (N + 1) v :=
    lt_of_le_of_ne (bfIt_le_succ nb tgt c N v) (Ne.symm hne)
  obtain ⟨s, -, hs⟩ := bfIt_chain nb tgt c N v hlt
  -- a repetition among `s 0, …, s N`
  have hrep : ∃ b, b ≤ N ∧ ∃ a < b, s a = s b := by
    obtain ⟨a, b, hab, e⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (N + 1) => s i) (by simp [N])
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b, by omega, a, h, e⟩
    · exact ⟨a, by omega, b, h, e.symm⟩
  let b := Nat.find hrep
  obtain ⟨hbN, a, hab, hsab⟩ := Nat.find_spec hrep
  have hinj : Set.InjOn s (Set.Ico a b) := by
    intro k1 hk1 k2 hk2 e
    simp only [Set.mem_Ico] at hk1 hk2
    by_contra hk
    rcases lt_or_gt_of_ne hk with h | h
    · exact Nat.find_min hrep (show k2 < b by omega) ⟨by omega, k1, h, e⟩
    · exact Nat.find_min hrep (show k1 < b by omega) ⟨by omega, k2, h, e.symm⟩
  have hedge : ∀ k, a ≤ k → k < b → s (k + 1) ∈ nb (s k) ∧ tgt (s k) = false :=
    fun k _ hk => let h := (hs k (by omega)).2 (by omega); ⟨h.1, h.2.1⟩
  have hsum := hneg s a b hab hsab.symm hedge hinj
  -- telescoping along the chain
  have htel : ∀ k, a ≤ k → k ≤ b → bfIt nb tgt c (N + 1 - a) (s a) =
      ((∑ i ∈ Finset.Ico a k, c (s i) : ℤ) : WithBot ℤ) + bfIt nb tgt c (N + 1 - k) (s k) := by
    intro k hak hkb
    induction k, hak using Nat.le_induction with
    | base => simp
    | succ k hak ih =>
      rw [ih (by omega), ((hs k (by omega)).2 (by omega)).2.2, Finset.sum_Ico_succ_top hak,
        show N - k = N + 1 - (k + 1) by omega, ← add_assoc, WithBot.coe_add]
  have h1 := htel b hab.le le_rfl
  rw [← hsab] at h1
  have h2 : bfIt nb tgt c (N + 1 - b) (s a) ≤ bfIt nb tgt c (N - a) (s a) :=
    bfIt_mono nb tgt c (by omega) _
  have h3 : bfIt nb tgt c (N + 1 - a) (s a) ≤ bfIt nb tgt c (N - a) (s a) := by
    rw [h1]
    refine le_trans ?_ h2
    generalize bfIt nb tgt c (N + 1 - b) (s a) = X
    induction X using WithBot.recBotCoe with
    | bot => simp
    | coe x => rw [← WithBot.coe_add, WithBot.coe_le_coe]; omega
  exact absurd (lt_of_lt_of_le (hs a (by omega)).1 h3) (lt_irrefl _)

theorem ret_bfValT : (bfValT nb tgt c).ret = bfVal nb tgt c := by
  unfold bfValT bfVal
  rw [ret_iterT]
  rfl

theorem time_bfValT : (bfValT nb tgt c).time ≤ Fintype.card V * roundCost nb := by
  unfold bfValT
  exact time_iterT_le _ _ (fun a => by simp) _ _

end MercLib.HybridSI

end HybridSIBestResponseGraphProofs
