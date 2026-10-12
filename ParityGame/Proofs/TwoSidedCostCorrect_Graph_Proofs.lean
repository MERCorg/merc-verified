module

public import ParityGame.Proofs.TwoSidedCostCorrect_Order_Proofs

@[expose] public section TwoSidedCostCorrectGraphProofs

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

Graph searches of `ParityGame.TwoSidedCost`: `pushNew`, the depth-first `explore` (state
invariants, soundness, and completeness with fuel `n + 1`: every pop finishes one more vertex),
and `reachSet` = reflexive-transitive closure. -/

variable {n : ℕ}

/-! ### `pushNew` -/

theorem pushNew_spec (ok : VSet n) : ∀ (ys : List (Fin n)) (seen : VSet n) (st : List (Fin n)),
    ∃ new : List (Fin n), (pushNew ok ys seen st).2 = new ++ st ∧ new.Nodup ∧
      (∀ z, z ∈ new ↔ z ∈ ys ∧ ok z = true ∧ seen z = false) ∧
      (∀ z, (pushNew ok ys seen st).1 z = true ↔ seen z = true ∨ (z ∈ ys ∧ ok z = true))
  | [], seen, st => ⟨[], by simp [pushNew]⟩
  | y :: ys, seen, st => by
    by_cases hy : (ok y && !seen y) = true
    · have hy' : ok y = true ∧ seen y = false := by simpa using hy
      obtain ⟨new, h1, h2, h3, h4⟩ := pushNew_spec ok ys (Function.update seen y true) (y :: st)
      refine ⟨new ++ [y], ?_, ?_, ?_, ?_⟩
      · simp only [pushNew, hy, ↓reduceIte, h1, List.append_assoc, List.cons_append,
          List.nil_append]
      · rw [List.nodup_append]
        refine ⟨h2, by simp, fun a ha b hb => ?_⟩
        simp only [List.mem_singleton] at hb
        subst hb
        have := ((h3 a).1 ha).2.2
        intro hab; subst hab; simp at this
      · intro z
        rw [List.mem_append, h3, List.mem_singleton, List.mem_cons]
        by_cases hz : z = y
        · subst hz; simp [hy']
        · rw [Function.update_of_ne hz]; simp [hz]
      · intro z
        simp only [pushNew, hy, ↓reduceIte]
        rw [h4]
        by_cases hz : z = y
        · subst hz; simp [hy']
        · rw [Function.update_of_ne hz]; simp [hz]
    · obtain ⟨new, h1, h2, h3, h4⟩ := pushNew_spec ok ys seen st
      have hy' : ok y = true → seen y = true := by
        intro h; simp only [h, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hy
        simpa using hy
      refine ⟨new, by simp only [pushNew, hy, Bool.false_eq_true, ↓reduceIte, h1], h2,
        fun z => ?_, fun z => ?_⟩
      · rw [h3, List.mem_cons]
        constructor
        · rintro ⟨h, h', h''⟩; exact ⟨Or.inr h, h', h''⟩
        · rintro ⟨rfl | h, h', h''⟩
          · rw [hy' h'] at h''; cases h''
          · exact ⟨h, h', h''⟩
      · simp only [pushNew, hy, Bool.false_eq_true, ↓reduceIte]
        rw [h4, List.mem_cons]
        constructor
        · rintro (h | ⟨h, h'⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h, h'⟩
        · rintro (h | ⟨rfl | h, h'⟩)
          · exact Or.inl h
          · exact Or.inl (hy' h')
          · exact Or.inr ⟨h, h'⟩

/-! ### `explore` -/

section Explore

variable {σ : Type} (nbrs : σ → Fin n → TimeM ℕ (σ × List (Fin n))) (ok : VSet n)

theorem explore_ret_zero (s : σ) (seen : VSet n) (stack : List (Fin n)) :
    (explore nbrs ok 0 s seen stack).ret = (s, seen) := by
  simp [explore]

theorem explore_ret_nil (k : ℕ) (s : σ) (seen : VSet n) :
    (explore nbrs ok (k + 1) s seen []).ret = (s, seen) := by
  simp [explore]

theorem explore_ret_cons (k : ℕ) (s : σ) (seen : VSet n) (x : Fin n) (stack : List (Fin n)) :
    (explore nbrs ok (k + 1) s seen (x :: stack)).ret =
      (explore nbrs ok k (nbrs s x).ret.1 (pushNew ok (nbrs s x).ret.2 seen stack).1
        (pushNew ok (nbrs s x).ret.2 seen stack).2).ret := by
  simp [explore]

/-- A state invariant of the neighbour function holds for the final state. -/
theorem explore_state (P : σ → Prop) (hP : ∀ s x, P s → P (nbrs s x).ret.1) :
    ∀ (k : ℕ) (s : σ) (seen : VSet n) (stack : List (Fin n)), P s →
      P (explore nbrs ok k s seen stack).ret.1
  | 0, s, seen, stack, h => by rw [explore_ret_zero]; exact h
  | k + 1, s, seen, [], h => by rw [explore_ret_nil]; exact h
  | k + 1, s, seen, x :: stack, h => by
    rw [explore_ret_cons]
    exact explore_state P hP k _ _ _ (hP s x h)

/-- Soundness: a property of the initial seen set and stack that propagates along accepted
    neighbours holds for every finally seen vertex. -/
theorem explore_sound (Q : Fin n → Prop)
    (hQ : ∀ s x, Q x → ∀ y ∈ (nbrs s x).ret.2, ok y = true → Q y) :
    ∀ (k : ℕ) (s : σ) (seen : VSet n) (stack : List (Fin n)), (∀ z, seen z = true → Q z) →
      (∀ z ∈ stack, Q z) → ∀ z, (explore nbrs ok k s seen stack).ret.2 z = true → Q z
  | 0, s, seen, stack, h1, _ => by rw [explore_ret_zero]; exact h1
  | k + 1, s, seen, [], h1, _ => by rw [explore_ret_nil]; exact h1
  | k + 1, s, seen, x :: stack, h1, h2 => by
    rw [explore_ret_cons]
    obtain ⟨new, e1, -, e3, e4⟩ := pushNew_spec ok (nbrs s x).ret.2 seen stack
    have hx : Q x := h2 x (by simp)
    apply explore_sound Q hQ k
    · intro z hz
      rcases (e4 z).1 hz with h | ⟨h, h'⟩
      · exact h1 z h
      · exact hQ s x hx z h h'
    · intro z hz
      rw [e1, List.mem_append] at hz
      rcases hz with hz | hz
      · obtain ⟨h, h', -⟩ := (e3 z).1 hz
        exact hQ s x hx z h h'
      · exact h2 z (by simp [hz])

/-- The seen set only grows. -/
theorem explore_mono :
    ∀ (k : ℕ) (s : σ) (seen : VSet n) (stack : List (Fin n)) (z : Fin n), seen z = true →
      (explore nbrs ok k s seen stack).ret.2 z = true
  | 0, s, seen, stack, z, h => by rw [explore_ret_zero]; exact h
  | k + 1, s, seen, [], z, h => by rw [explore_ret_nil]; exact h
  | k + 1, s, seen, x :: stack, z, h => by
    rw [explore_ret_cons]
    obtain ⟨new, -, -, -, e4⟩ := pushNew_spec ok (nbrs s x).ret.2 seen stack
    exact explore_mono k _ _ _ z ((e4 z).2 (Or.inl h))

open scoped Classical in
/-- The finished vertices: seen and no longer on the stack. -/
noncomputable def finished (seen : VSet n) (stack : List (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun z => seen z = true ∧ z ∉ stack

/-- Completeness: with enough fuel (more than the number of unfinished vertices), when the
    neighbours do not depend on the state, the final seen set is closed under accepted
    neighbours. -/
theorem explore_closed (N : Fin n → List (Fin n)) (hN : ∀ s x, (nbrs s x).ret.2 = N x) :
    ∀ (k : ℕ) (s : σ) (seen : VSet n) (stack : List (Fin n)),
      n < k + (finished seen stack).card → stack.Nodup → (∀ z ∈ stack, seen z = true) →
      (∀ x, seen x = true → x ∉ stack → ∀ y ∈ N x, ok y = true → seen y = true) →
      ∀ x, (explore nbrs ok k s seen stack).ret.2 x = true → ∀ y ∈ N x, ok y = true →
        (explore nbrs ok k s seen stack).ret.2 y = true
  | 0, s, seen, stack, hk, _, _, _ => by
    exfalso
    have := Finset.card_le_univ (finished seen stack)
    simp at this hk
    omega
  | k + 1, s, seen, [], _, _, _, hcl => by
    rw [explore_ret_nil]
    exact fun x hx y hy hok => hcl x hx (by simp) y hy hok
  | k + 1, s, seen, x :: stack, hk, hnd, hsub, hcl => by
    rw [explore_ret_cons]
    obtain ⟨new, e1, e2, e3, e4⟩ := pushNew_spec ok (nbrs s x).ret.2 seen stack
    rw [hN] at e1 e3 e4 ⊢
    have hxs : x ∉ stack := (List.nodup_cons.1 hnd).1
    have hxseen : seen x = true := hsub x (by simp)
    have hnew_unseen : ∀ z ∈ new, seen z = false := fun z hz => ((e3 z).1 hz).2.2
    have hfin : finished (pushNew ok (N x) seen stack).1 (pushNew ok (N x) seen stack).2 =
        insert x (finished seen (x :: stack)) := by
      ext z
      simp only [finished, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        List.mem_cons, not_or, e1, List.mem_append, e4]
      by_cases hzx : z = x
      · subst hzx
        refine ⟨fun _ => Or.inl rfl, fun _ => ⟨Or.inl hxseen, fun h => ?_, hxs⟩⟩
        have := hnew_unseen z h
        rw [hxseen] at this; cases this
      · constructor
        · rintro ⟨h1, h2, h3⟩
          right
          rcases h1 with h1 | ⟨h1, h1'⟩
          · exact ⟨h1, hzx, h3⟩
          · by_cases hs : seen z = true
            · exact ⟨hs, hzx, h3⟩
            · exact absurd ((e3 z).2 ⟨h1, h1', by simpa using hs⟩) h2
        · rintro (rfl | ⟨h1, -, h3⟩)
          · exact absurd rfl hzx
          · exact ⟨Or.inl h1, (fun h => by rw [hnew_unseen z h] at h1; cases h1), h3⟩
    have hxfin : x ∉ finished seen (x :: stack) := by simp [finished]
    apply explore_closed N hN k
    · rw [hfin, Finset.card_insert_of_notMem hxfin]; omega
    · rw [e1, List.nodup_append]
      refine ⟨e2, (List.nodup_cons.1 hnd).2, fun a ha b hb hab => ?_⟩
      subst hab
      have := hnew_unseen a ha
      rw [hsub a (by simp [hb])] at this; cases this
    · intro z hz
      rw [e4]
      rw [e1, List.mem_append] at hz
      rcases hz with hz | hz
      · obtain ⟨h1, h2, -⟩ := (e3 z).1 hz
        exact Or.inr ⟨h1, h2⟩
      · exact Or.inl (hsub z (by simp [hz]))
    · intro z hz hzs y hy hok
      rw [e4] at hz ⊢
      rw [e1, List.mem_append, not_or] at hzs
      by_cases hzx : z = x
      · subst hzx; exact Or.inr ⟨hy, hok⟩
      · rcases hz with hz | ⟨h1, h2⟩
        · exact Or.inl (hcl z hz (by simp [hzx, hzs.2]) y hy hok)
        · by_cases hs : seen z = true
          · exact Or.inl (hcl z hs (by simp [hzx, hzs.2]) y hy hok)
          · exact absurd ((e3 z).2 ⟨h1, h2, by simpa using hs⟩) hzs.1

end Explore

/-! ### Reachability -/

/-- One accepted step of a search: `y` is a neighbour of `x` accepted by `ok`. -/
def RStep (nbrs : Fin n → TimeM ℕ (List (Fin n))) (ok : VSet n) (x y : Fin n) : Prop :=
  y ∈ (nbrs x).ret ∧ ok y = true

/-- `reachSet` computes the reflexive-transitive closure of accepted steps. -/
theorem reachSet_iff (nbrs : Fin n → TimeM ℕ (List (Fin n))) (ok : VSet n) (v z : Fin n) :
    (reachSet nbrs ok v).ret z = true ↔ Relation.ReflTransGen (RStep nbrs ok) v z := by
  let nb : Unit → Fin n → TimeM ℕ (Unit × List (Fin n)) :=
    fun _ x => do let ys ← nbrs x; return ((), ys)
  have hnb : ∀ s x, (nb s x).ret.2 = (nbrs x).ret := fun _ _ => rfl
  have hret : (reachSet nbrs ok v).ret = (explore nb ok (n + 1) () (VSet.single v) [v]).ret.2 :=
    rfl
  rw [hret]
  constructor
  · intro hz
    refine explore_sound nb ok (fun z => Relation.ReflTransGen (RStep nbrs ok) v z) ?_ (n + 1) ()
      (VSet.single v) [v] ?_ ?_ z hz
    · intro s x hx y hy hok
      exact hx.tail ⟨by rwa [hnb s x] at hy, hok⟩
    · intro z hz
      simp only [VSet.single, decide_eq_true_eq] at hz
      subst hz; exact Relation.ReflTransGen.refl
    · intro z hz
      simp only [List.mem_singleton] at hz
      subst hz; exact Relation.ReflTransGen.refl
  · intro h
    have hcl := explore_closed nb ok (fun x => (nbrs x).ret) hnb (n + 1) () (VSet.single v) [v]
      (by have := Finset.card_le_univ (finished (VSet.single v) [v]); omega) (by simp)
      (by simp [VSet.single]) (by
        intro x hx hxs
        simp only [VSet.single, decide_eq_true_eq] at hx
        subst hx; simp at hxs)
    induction h with
    | refl => exact explore_mono nb ok _ _ _ _ v (by simp [VSet.single])
    | tail _ hst ih => exact hcl _ ih _ hst.1 hst.2

end ParityGame.TwoSidedCost

end TwoSidedCostCorrectGraphProofs
