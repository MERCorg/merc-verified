module

public import ParityGame.TwoSidedCost
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section TwoSidedCostProofs

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/TwoSidedCost_Pins.lean`.

All bounds are polynomials in `N = n + m + d + 2` (`PGame.size`). Every loop is either a fold
over a list of known length or a fuel-driven recursion, so the per-operation bounds follow by
induction from uniform per-iteration bounds. The lifting loop is the only amortised argument: an
unsuccessful pop is paid for by the queue (potential `E · |queue|`), and every successful lift
or accelerated raise pays for its own work and for the at most `n + 1` queue entries it adds. A
round that does not finish has made at least `budget ≥ 1` steps of player `0`, which pays for the
two certifications of that round. -/

variable {n : ℕ}

/-! ### Generic loop lemmas -/

theorem time_foldlM_le {α β : Type} (f : β → α → TimeM ℕ β) (K : ℕ) :
    ∀ (xs : List α) (b : β), (∀ b, ∀ a ∈ xs, (f b a).time ≤ K) →
      (xs.foldlM f b).time ≤ xs.length * K := by
  intro xs
  induction xs with
  | nil => intro b _; simp
  | cons a xs ih =>
    intro b h
    simp only [List.foldlM_cons, time_bind, List.length_cons]
    have h1 := h b a (by simp)
    have h2 := ih (f b a).ret (fun b a ha => h b a (by simp [ha]))
    rw [Nat.succ_mul]; omega

theorem ret_foldlM {α β : Type} (f : β → α → TimeM ℕ β) :
    ∀ (xs : List α) (b : β), (xs.foldlM f b).ret = xs.foldl (fun b a => (f b a).ret) b := by
  intro xs
  induction xs with
  | nil => intro b; simp
  | cons a xs ih => intro b; simp [List.foldlM_cons, ih]

theorem time_filterT_le {α : Type} (p : α → TimeM ℕ Bool) (K : ℕ) :
    ∀ (xs : List α), (∀ a ∈ xs, (p a).time ≤ K) → (filterT p xs).time ≤ xs.length * K := by
  intro xs
  induction xs with
  | nil => intro _; simp [filterT]
  | cons a xs ih =>
    intro h
    simp only [filterT, time_bind, time_pure, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun a ha => h a (by simp [ha]))
    rw [Nat.succ_mul]; omega

theorem length_filterT_le {α : Type} (p : α → TimeM ℕ Bool) :
    ∀ (xs : List α), (filterT p xs).ret.length ≤ xs.length := by
  intro xs
  induction xs with
  | nil => simp [filterT]
  | cons a xs ih =>
    simp only [filterT, ret_bind, ret_pure, List.length_cons]
    split <;> (try simp only [List.length_cons]) <;> omega

theorem time_iterT_le {α : Type} (f : α → TimeM ℕ α) (K : ℕ) (hf : ∀ a, (f a).time ≤ K) :
    ∀ (k : ℕ) (a : α), (iterT f k a).time ≤ k * K := by
  intro k
  induction k with
  | zero => intro a; simp [iterT]
  | succ k ih =>
    intro a
    simp only [iterT, time_bind]
    have := ih (f a).ret
    have := hf a
    rw [Nat.succ_mul]; omega

theorem time_explore_le {σ : Type} (nbrs : σ → Fin n → TimeM ℕ (σ × List (Fin n))) (ok : VSet n)
    (K L : ℕ) (hK : ∀ s x, (nbrs s x).time ≤ K) (hL : ∀ s x, (nbrs s x).ret.2.length ≤ L) :
    ∀ (f : ℕ) (s : σ) (seen : VSet n) (st : List (Fin n)),
      (explore nbrs ok f s seen st).time ≤ f * (1 + K + L) := by
  intro f
  induction f with
  | zero => intro s seen st; simp [explore]
  | succ f ih =>
    intro s seen st
    cases st with
    | nil => simp [explore]
    | cons x st =>
      simp only [explore, time_bind, time_tick]
      have h1 := hK s x
      have h2 := hL s x
      have h3 := ih (nbrs s x).ret.1 (pushNew ok (nbrs s x).ret.2 seen st).1
        (pushNew ok (nbrs s x).ret.2 seen st).2
      rw [Nat.succ_mul]; omega

/-! ### Size facts -/

theorem le_sum_of_mem' : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.sum := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    simp only [List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · have := ih x hx; omega

theorem deg_le_m (G : PGame n) (v : Fin n) : (G.succ v).length ≤ G.m := by
  unfold PGame.m
  exact le_sum_of_mem' _ _ (List.mem_map.2 ⟨v, List.mem_finRange v, rfl⟩)

theorem n_succ_le_N (c : Ctx n) : n + 1 ≤ c.N := by
  simp only [Ctx.N, PGame.size]; omega

theorem m_succ_le_N (c : Ctx n) : c.G.m + 1 ≤ c.N := by
  simp only [Ctx.N, PGame.size]; omega

theorem nm_le_N (c : Ctx n) : n + c.G.m ≤ c.N := by
  simp only [Ctx.N, PGame.size]; omega

theorem height_succ_le_N (c : Ctx n) : c.height + 1 ≤ c.N := by
  have := c.levels_le
  simp only [Ctx.N, PGame.size, Ctx.height]; omega

theorem deg_succ_le_N (c : Ctx n) (v : Fin n) : (c.G.succ v).length + 1 ≤ c.N := by
  have := deg_le_m c.G v; have := m_succ_le_N c; omega

theorem one_le_N (c : Ctx n) : 1 ≤ c.N := by
  have := n_succ_le_N c; omega

theorem N_le_pow (c : Ctx n) {i j : ℕ} (h : i ≤ j) : c.N ^ i ≤ c.N ^ j :=
  Nat.pow_le_pow_right (one_le_N c) h

/-! ### Primitive operations -/

theorem time_succT (c : Ctx n) (v : Fin n) : (succT c v).time ≤ c.N := by
  simp only [succT, time_bind, time_tick, time_pure]
  have := deg_succ_le_N c v; omega

theorem length_succT (c : Ctx n) (v : Fin n) : (succT c v).ret.length ≤ c.N := by
  simp only [succT, ret_bind, ret_pure]
  have := List.length_filter_le c.alive (c.G.succ v)
  have := deg_succ_le_N c v; omega

theorem time_predT (c : Ctx n) (v : Fin n) : (predT c v).time ≤ c.N := by
  simp only [predT, time_bind, time_tick, time_pure]
  have := nm_le_N c; omega

theorem length_predT (c : Ctx n) (v : Fin n) : (predT c v).ret.length ≤ n := by
  simp only [predT, ret_bind, ret_pure]
  refine Nat.le_trans (List.length_filter_le _ _) ?_
  simp

theorem time_keptT (c : Ctx n) (ch : Fin n → Option (Fin n)) (u : Fin n) :
    (keptT c ch u).time ≤ c.N := by
  unfold keptT
  split
  · exact time_succT c u
  · simp only [time_bind, time_tick, time_pure]; have := one_le_N c; omega

theorem length_keptT (c : Ctx n) (ch : Fin n → Option (Fin n)) (u : Fin n) :
    (keptT c ch u).ret.length ≤ c.N := by
  unfold keptT
  split
  · exact length_succT c u
  · simp only [ret_bind, ret_pure]
    have := one_le_N c
    cases ch u <;> simp; omega

theorem time_reachSet (c : Ctx n) (nbrs : Fin n → TimeM ℕ (List (Fin n))) (ok : VSet n)
    (v : Fin n) (K L : ℕ) (hK : ∀ x, (nbrs x).time ≤ K) (hL : ∀ x, (nbrs x).ret.length ≤ L) :
    (reachSet nbrs ok v).time ≤ c.N * (1 + K + L) := by
  simp only [reachSet, time_bind, time_pure]
  have := time_explore_le (fun (_ : Unit) x => do let ys ← nbrs x; return ((), ys)) ok K L
    (fun _ x => by simpa using hK x) (fun _ x => by simpa using hL x) (n + 1) ()
    (VSet.single v) [v]
  have h2 : (n + 1) * (1 + K + L) ≤ c.N * (1 + K + L) :=
    Nat.mul_le_mul_right _ (n_succ_le_N c)
  omega

/-! ### The chain tree -/

theorem time_undirected (c : Ctx n) (S : VSet n) (x : Fin n) :
    (undirected c S x).time ≤ 4 * c.N := by
  simp only [undirected, time_bind, time_tick, time_pure]
  have := time_succT c x; have := time_predT c x
  have := length_succT c x; have := length_predT c x; have := n_succ_le_N c
  omega

theorem length_undirected (c : Ctx n) (S : VSet n) (x : Fin n) :
    (undirected c S x).ret.length ≤ 2 * c.N := by
  simp only [undirected, ret_bind, ret_pure]
  have := List.length_filter_le S ((succT c x).ret ++ (predT c x).ret)
  have := length_succT c x; have := length_predT c x; have := n_succ_le_N c
  simp only [List.length_append] at *
  omega

theorem time_wcStep (c : Ctx n) (S : VSet n) (acc : VSet n × List (VSet n)) (root : Fin n) :
    (wcStep c S acc root).time ≤ 9 * c.N ^ 2 := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  simp only [wcStep, time_bind, time_tick]
  split
  · simp only [time_bind, time_tick, time_pure]
    have := time_reachSet c (undirected c S) S root (4 * c.N) (2 * c.N)
      (time_undirected c S) (length_undirected c S)
    nlinarith
  · simp only [time_pure]; nlinarith

/-- `n * (K * N^k) ≤ K * N^(k+1)`. -/
theorem n_mul_le (c : Ctx n) (K k : ℕ) : n * (K * c.N ^ k) ≤ K * c.N ^ (k + 1) := by
  have : n * (K * c.N ^ k) ≤ c.N * (K * c.N ^ k) :=
    Nat.mul_le_mul_right _ (by have := n_succ_le_N c; omega)
  have : c.N * (K * c.N ^ k) = K * c.N ^ (k + 1) := by ring
  omega

theorem time_weakComponents (c : Ctx n) (S : VSet n) :
    (weakComponents c S).time ≤ 9 * c.N ^ 3 := by
  simp only [weakComponents, time_bind, time_pure]
  have h := time_foldlM_le (wcStep c S) (9 * c.N ^ 2) (List.finRange n) (VSet.empty, [])
    (fun b a _ => time_wcStep c S b a)
  simp only [List.length_finRange] at h
  have := n_mul_le c 9 2
  simp only [Nat.reduceAdd] at this
  omega

theorem time_children (c : Ctx n) (l : ℕ) (R : VSet n) :
    (children c l R).time ≤ 10 * c.N ^ 3 := by
  simp only [children, time_bind, time_tick, time_pure]
  have := time_weakComponents c (materialize fun v => R v && decide (c.prio v < c.level l))
  have := n_succ_le_N c
  have : c.N ≤ c.N ^ 3 := by simpa using N_le_pow c (i := 1) (j := 3) (by omega)
  omega

theorem time_chainRound (S : VSet n) (reach : Fin n → VSet n) (weight best : Fin n → ℕ) :
    (chainRound S reach weight best).time ≤ n * n := by
  unfold chainRound
  have := time_foldlM_le (chainEntry S reach weight best) n (List.finRange n) (fun _ => 0) (by
    intro b a _
    simp only [chainEntry, time_bind, time_tick, time_pure]; omega)
  simpa using this

theorem time_succIn (c : Ctx n) (S : VSet n) (x : Fin n) : (succIn c S x).time ≤ 2 * c.N := by
  simp only [succIn, time_bind, time_tick, time_pure]
  have := time_succT c x; have := length_succT c x; omega

theorem length_succIn (c : Ctx n) (S : VSet n) (x : Fin n) : (succIn c S x).ret.length ≤ c.N := by
  simp only [succIn, ret_bind, ret_pure]
  exact Nat.le_trans (List.length_filter_le _ _) (length_succT c x)

theorem time_chainBound (c : Ctx n) (R : VSet n) (q : ℕ) :
    (chainBound c R q).time ≤ 8 * c.N ^ 3 := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  simp only [chainBound, time_bind, time_tick, time_pure]
  generalize (materialize fun v => R v && decide (c.prio v ≤ q)) = S
  have h1 := time_foldlM_le (reachStep c S) (4 * c.N ^ 2) (List.finRange n) (fun _ => VSet.empty)
    (by
      intro b a _
      simp only [reachStep, time_bind, time_pure]
      have := time_reachSet c (succIn c S) S a (2 * c.N) c.N (time_succIn c S) (length_succIn c S)
      nlinarith)
  generalize (List.foldlM (reachStep c S) (fun _ => VSet.empty) (List.finRange n)) = reach at *
  have h2 := time_foldlM_le (weightStep c S q reach.ret) n (List.finRange n) (fun _ => 0) (by
    intro b a _
    simp only [weightStep, time_bind, time_tick, time_pure]; omega)
  generalize (List.foldlM (weightStep c S q reach.ret) (fun _ => 0) (List.finRange n)) = weight
    at *
  have h3 := time_iterT_le (chainRound S reach.ret weight.ret) (n * n)
    (time_chainRound S reach.ret weight.ret) (n + 1) (fun _ => 0)
  simp only [List.length_finRange] at h1 h2
  have e1 := n_mul_le c 4 2
  simp only [Nat.reduceAdd] at e1
  have e2 : n * n ≤ c.N ^ 3 := by
    have : n * n ≤ c.N * c.N := Nat.mul_le_mul (by omega) (by omega)
    have : c.N * c.N ≤ c.N * c.N * c.N := Nat.le_mul_of_pos_right _ (by omega)
    have : c.N * c.N * c.N = c.N ^ 3 := by ring
    omega
  have e3 : (n + 1) * (n * n) ≤ c.N ^ 3 := by
    have : (n + 1) * (n * n) ≤ c.N * (c.N * c.N) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    have : c.N * (c.N * c.N) = c.N ^ 3 := by ring
    omega
  have e4 : c.N ≤ c.N ^ 3 := by simpa using N_le_pow c (i := 1) (j := 3) (by omega)
  omega

theorem time_regionsOf (c : Ctx n) :
    ∀ (path : List (ℕ × ℕ)) (l : ℕ) (R : VSet n),
      (regionsOf c l R path).time ≤ path.length * (11 * c.N ^ 3) := by
  intro path
  induction path with
  | nil => intro l R; simp [regionsOf]
  | cons x rest ih =>
    intro l R
    match rest, ih with
    | [], _ => simp [regionsOf]
    | (k, k') :: rest', ih =>
      rw [regionsOf.eq_3]
      simp only [time_bind, time_tick, time_pure]
      have := time_children c l R
      have := ih (l + 1) ((children c l R).ret.getD k VSet.empty)
      have := one_le_N c
      have : 1 ≤ c.N ^ 3 := Nat.one_le_pow _ _ (by omega)
      simp only [List.length_cons] at *
      rw [Nat.succ_mul]
      omega

theorem time_nextAux (c : Ctx n) (regs : List (VSet n)) :
    ∀ (f : ℕ) (path : List (ℕ × ℕ)), (nextAux c regs f path).time ≤ f * (19 * c.N ^ 3) := by
  intro f
  induction f with
  | zero => intro path; simp [nextAux]
  | succ f ih =>
    intro path
    have hb := fun R q => time_chainBound c R q
    have hc := fun l R => time_children c l R
    have hh := height_succ_le_N c
    have : c.N ≤ c.N ^ 3 := by simpa using N_le_pow c (i := 1) (j := 3) (by omega)
    have ih' := fun p => ih p
    unfold nextAux
    split
    · simp
    · simp only [time_bind, time_tick]
      rw [Nat.succ_mul]
      split
      · simp only [time_pure]
        have := hb (regs.getD (path.length - 1) VSet.empty) (c.level (path.length - 1))
        omega
      · split
        · simp only [time_bind]
          split
          · simp only [time_pure]
            have := hb (regs.getD (path.length - 1) VSet.empty) (c.level (path.length - 1))
            have := hc (path.length - 1 - 1) (regs.getD (path.length - 1 - 1) VSet.empty)
            omega
          · have := hb (regs.getD (path.length - 1) VSet.empty) (c.level (path.length - 1))
            have := hc (path.length - 1 - 1) (regs.getD (path.length - 1 - 1) VSet.empty)
            have := ih' path.dropLast
            omega
        · have := hb (regs.getD (path.length - 1) VSet.empty) (c.level (path.length - 1))
          have := ih' path.dropLast
          omega

theorem time_nextNode (c : Ctx n) (pre : List (ℕ × ℕ)) :
    (nextNode c pre).time ≤ pre.length * (30 * c.N ^ 3) := by
  simp only [nextNode, time_bind]
  have := time_regionsOf c pre 0 c.alive
  have := time_nextAux c (regionsOf c 0 c.alive pre).ret pre.length pre
  rw [show 30 * c.N ^ 3 = 11 * c.N ^ 3 + 19 * c.N ^ 3 by ring, Nat.mul_add]
  omega

theorem time_leftmost (c : Ctx n) (pre : List (ℕ × ℕ)) : (leftmost c pre).time ≤ c.N := by
  simp only [leftmost, time_bind, time_tick, time_pure]
  have := height_succ_le_N c; omega

theorem time_lexCmp : ∀ (k : ℕ) (a b : List (ℕ × ℕ)), (lexCmp k a b).time ≤ k := by
  intro k
  induction k with
  | zero => intro a b; simp [lexCmp]
  | succ k ih =>
    intro a b
    match a, b with
    | [], [] => simp [lexCmp]
    | [], _ :: _ => simp [lexCmp]
    | _ :: _, [] => simp [lexCmp]
    | x :: xs, y :: ys =>
      simp only [lexCmp, time_bind, time_tick]
      split
      · have := ih xs ys; omega
      · simp

theorem time_cmpVal (c : Ctx n) (a b : Val) : (cmpVal c a b).time ≤ c.N := by
  have := height_succ_le_N c
  match a, b with
  | none, none => simp [cmpVal]
  | none, some _ => simp [cmpVal]
  | some _, none => simp [cmpVal]
  | some a, some b =>
    simp only [cmpVal]
    have := time_lexCmp c.height a b; omega

theorem depthOf_le (c : Ctx n) (v : Fin n) : depthOf c v ≤ c.height :=
  List.length_filter_le _ _

theorem time_prog (c : Ctx n) (v : Fin n) (t : Val) : (prog c v t).time ≤ 32 * c.N ^ 4 := by
  have hh := height_succ_le_N c
  have hN := one_le_N c
  have h4 : c.N ≤ c.N ^ 4 := by simpa using N_le_pow c (i := 1) (j := 4) (by omega)
  simp only [prog, time_bind, time_tick]
  split
  · simp only [time_pure]; omega
  · rename_i t
    have hpre : (t.take (depthOf c v)).length ≤ c.height := by
      have := depthOf_le c v; simp only [List.length_take]; omega
    split
    · simp only [time_bind, time_pure]
      have := time_leftmost c (t.take (depthOf c v)); omega
    · simp only [time_bind]
      have hn := time_nextNode c (t.take (depthOf c v))
      have : (t.take (depthOf c v)).length * (30 * c.N ^ 3) ≤ 30 * c.N ^ 4 := by
        have : (t.take (depthOf c v)).length * (30 * c.N ^ 3) ≤ c.N * (30 * c.N ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
        have : c.N * (30 * c.N ^ 3) = 30 * c.N ^ 4 := by ring
        omega
      split
      · simp only [time_pure]; omega
      · simp only [time_bind, time_pure]
        have := time_leftmost c (by assumption); omega

/-! ### Lifting: evaluation -/

theorem N_mul_le (c : Ctx n) {a : ℕ} (K k j : ℕ) (ha : a ≤ c.N) (hj : k + 1 = j) :
    a * (K * c.N ^ k) ≤ K * c.N ^ j := by
  subst hj
  have : a * (K * c.N ^ k) ≤ c.N * (K * c.N ^ k) := Nat.mul_le_mul_right _ ha
  have : c.N * (K * c.N ^ k) = K * c.N ^ (k + 1) := by ring
  omega

theorem length_succT_le_deg (c : Ctx n) (v : Fin n) :
    (succT c v).ret.length ≤ (c.G.succ v).length := by
  simp only [succT, ret_bind, ret_pure]
  exact List.length_filter_le _ _

theorem time_evalStep (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n))
    (acc : Option (Val × Fin n)) (w : Fin n) :
    (evalStep c μ v allowed acc w).time ≤ 34 * c.N ^ 4 := by
  have hN := one_le_N c
  have h4 : c.N ≤ c.N ^ 4 := by simpa using N_le_pow c (i := 1) (j := 4) (by omega)
  have hp := time_prog c v (μ w)
  simp only [evalStep, time_bind, time_tick]
  split
  · simp only [time_bind]
    split
    · simp only [time_pure]; omega
    · simp only [time_bind, time_pure]
      have := time_cmpVal c (prog c v (μ w)).ret (by assumption)
      omega
  · simp only [time_pure]; omega

theorem time_evaluate (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n)) :
    (evaluate c μ v allowed).time ≤ ((c.G.succ v).length + 1) * (35 * c.N ^ 4) := by
  have hN := one_le_N c
  have h1 : 1 ≤ c.N ^ 4 := Nat.one_le_pow _ _ (by omega)
  simp only [evaluate, time_bind, time_pure]
  have hf := time_foldlM_le (evalStep c μ v allowed) (34 * c.N ^ 4) (succT c v).ret none
    (fun b a _ => time_evalStep c μ v allowed b a)
  have hl := length_succT_le_deg c v
  have hs : (succT c v).time = (c.G.succ v).length + 1 := by simp [succT]
  have : (succT c v).ret.length * (34 * c.N ^ 4) ≤ (c.G.succ v).length * (34 * c.N ^ 4) :=
    Nat.mul_le_mul_right _ hl
  have : (c.G.succ v).length + 1 ≤ ((c.G.succ v).length + 1) * c.N ^ 4 :=
    Nat.le_mul_of_pos_right _ (by omega)
  have : ((c.G.succ v).length + 1) * (35 * c.N ^ 4) =
      ((c.G.succ v).length + 1) * c.N ^ 4 + (c.G.succ v).length * (34 * c.N ^ 4) +
        34 * c.N ^ 4 := by ring
  omega

theorem time_evaluate' (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n)) :
    (evaluate c μ v allowed).time ≤ 35 * c.N ^ 5 :=
  Nat.le_trans (time_evaluate c μ v allowed) (N_mul_le c 35 4 5 (deg_succ_le_N c v) rfl)

theorem time_currentChoice (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n))
    (x : Fin n) : (currentChoice c μ ch x).time ≤ 36 * c.N ^ 5 := by
  have hN := one_le_N c
  have h1 : 1 ≤ c.N ^ 5 := Nat.one_le_pow _ _ (by omega)
  have := time_evaluate' c μ x none
  simp only [currentChoice, time_bind, time_tick]
  split
  · simp only [time_pure]; omega
  · simp only [time_bind, time_pure]; omega

theorem length_foldl_requeue : ∀ (l : List (Fin n)) (st : LState n),
    (l.foldl requeue st).queue.length ≤ st.queue.length + l.length := by
  intro l
  induction l with
  | nil => intro st; simp
  | cons a l ih =>
    intro st
    simp only [List.foldl_cons, List.length_cons]
    have := ih (requeue st a)
    have : (requeue st a).queue.length ≤ st.queue.length + 1 := by
      unfold requeue; split <;> simp
    omega

theorem time_requeuePreds (c : Ctx n) (st : LState n) (v : Fin n) :
    (requeuePreds c st v).time ≤ 2 * c.N := by
  simp only [requeuePreds, time_bind, time_tick, time_pure]
  have := time_predT c v; have := length_predT c v; have := n_succ_le_N c; omega

theorem queue_requeuePreds (c : Ctx n) (st : LState n) (v : Fin n) :
    (requeuePreds c st v).ret.queue.length ≤ st.queue.length + n := by
  simp only [requeuePreds, ret_bind, ret_pure]
  have := length_foldl_requeue (predT c v).ret st
  have := length_predT c v; omega

/-! ### Lifting: acceleration -/

theorem time_pumpTest (c : Ctx n) (μ : Fin n → Val) (v : Fin n) :
    ∀ (k : ℕ) (ch : Fin n → Option (Fin n)) (x : Fin n),
      (pumpTest c μ v k ch x).time ≤ k * (36 * c.N ^ 5) := by
  intro k
  induction k with
  | zero => intro ch x; simp [pumpTest]
  | succ k ih =>
    intro ch x
    simp only [pumpTest, time_bind]
    have := time_currentChoice c μ ch x
    rw [Nat.succ_mul]
    split
    · simp only [time_pure]; omega
    · split
      · simp only [time_pure]; omega
      · have := ih (currentChoice c μ ch x).ret.1 (by assumption); omega

theorem time_fwdNbrs (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (x : Fin n) :
    (fwdNbrs c μ ch x).time ≤ 37 * c.N ^ 5 := by
  have hN := one_le_N c
  have h5 : c.N ≤ c.N ^ 5 := by simpa using N_le_pow c (i := 1) (j := 5) (by omega)
  unfold fwdNbrs
  split
  · simp only [time_bind, time_pure, ret_pure]
    have := time_keptT c ch x; omega
  · simp only [time_bind, time_pure, ret_pure]
    have := time_currentChoice c μ ch x
    have := time_keptT c (currentChoice c μ ch x).ret.1 x
    omega

theorem length_fwdNbrs (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (x : Fin n) :
    (fwdNbrs c μ ch x).ret.2.length ≤ c.N := by
  unfold fwdNbrs
  split <;> simp only [ret_bind, ret_pure] <;> exact length_keptT c _ x

theorem time_keptEdge (c : Ctx n) (ch : Fin n → Option (Fin n)) (fwd : VSet n) (x u : Fin n) :
    (keptEdge c ch fwd x u).time ≤ 2 * c.N := by
  unfold keptEdge
  split
  · simp only [time_bind, time_tick, time_pure]
    have := time_keptT c ch u; have := length_keptT c ch u; omega
  · simp

theorem time_bwdNbrs (c : Ctx n) (ch : Fin n → Option (Fin n)) (fwd : VSet n) (x : Fin n) :
    (bwdNbrs c ch fwd () x).time ≤ 3 * c.N ^ 2 := by
  have hN := one_le_N c
  simp only [bwdNbrs, time_bind, time_pure]
  have h1 := time_predT c x
  have h2 := time_filterT_le (keptEdge c ch fwd x) (2 * c.N) (predT c x).ret
    (fun u _ => time_keptEdge c ch fwd x u)
  have h3 : (predT c x).ret.length * (2 * c.N) ≤ 2 * c.N ^ 2 := by
    simpa using N_mul_le c 2 1 2 (by have := length_predT c x; have := n_succ_le_N c; omega) rfl
  have : c.N ≤ c.N ^ 2 := by simpa using N_le_pow c (i := 1) (j := 2) (by omega)
  omega

theorem length_bwdNbrs (c : Ctx n) (ch : Fin n → Option (Fin n)) (fwd : VSet n) (x : Fin n) :
    (bwdNbrs c ch fwd () x).ret.2.length ≤ c.N := by
  simp only [bwdNbrs, ret_bind, ret_pure]
  have := length_filterT_le (keptEdge c ch fwd x) (predT c x).ret
  have := length_predT c x; have := n_succ_le_N c; omega

theorem time_keptNbrs (c : Ctx n) (ch : Fin n → Option (Fin n)) (x : Fin n) :
    (keptNbrs c ch () x).time ≤ c.N := by
  simp only [keptNbrs, time_bind, time_pure]; have := time_keptT c ch x; omega

theorem length_keptNbrs (c : Ctx n) (ch : Fin n → Option (Fin n)) (x : Fin n) :
    (keptNbrs c ch () x).ret.2.length ≤ c.N := by
  simp only [keptNbrs, ret_bind, ret_pure]; exact length_keptT c ch x

theorem time_ecmStep (c : Ctx n) (ch : Fin n → Option (Fin n)) (M bad : VSet n) (u : Fin n) :
    (ecmStep c ch M bad u).time ≤ 7 * c.N ^ 2 := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  simp only [ecmStep, time_bind, time_tick]
  split
  · simp only [time_bind, time_tick, time_pure]
    have := time_keptT c ch u; have := length_keptT c ch u
    have := time_explore_le (keptNbrs c ch)
      (materialize fun w => M w && decide (c.prio w ≤ c.prio u))
      c.N c.N (fun _ x => time_keptNbrs c ch x) (fun _ x => length_keptNbrs c ch x) (n + 1) ()
      (pushNew (materialize fun w => M w && decide (c.prio w ≤ c.prio u)) (keptT c ch u).ret
        VSet.empty []).1
      (pushNew (materialize fun w => M w && decide (c.prio w ≤ c.prio u)) (keptT c ch u).ret
        VSet.empty []).2
    nlinarith
  · simp only [time_pure]; nlinarith

theorem time_evenCycleMaxima (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) :
    (evenCycleMaxima c ch M).time ≤ 7 * c.N ^ 3 := by
  unfold evenCycleMaxima
  have := time_foldlM_le (ecmStep c ch M) (7 * c.N ^ 2) (List.finRange n) VSet.empty
    (fun b a _ => time_ecmStep c ch M b a)
  have := N_mul_le c 7 2 3 (a := n) (by have := n_succ_le_N c; omega) rfl
  simp only [List.length_finRange] at *
  omega

theorem count_le (S : VSet n) : S.count ≤ n := by
  unfold VSet.count
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem time_sccLoop (c : Ctx n) (μ : Fin n → Val) (v : Fin n) :
    ∀ (k : ℕ) (ch : Fin n → Option (Fin n)) (allowed : Option (VSet n)),
      (sccLoop c μ v k ch allowed).time ≤ k * (56 * c.N ^ 6) := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  have h36 : c.N ^ 3 ≤ c.N ^ 6 := N_le_pow c (by omega)
  have h16 : c.N ≤ c.N ^ 6 := by simpa using N_le_pow c (i := 1) (j := 6) (by omega)
  intro k
  induction k with
  | zero => intro ch allowed; simp [sccLoop]
  | succ k ih =>
    intro ch allowed
    simp only [sccLoop, time_bind, time_tick]
    have hf := time_explore_le (fwdNbrs c μ) (fun y => (allowed.map fun a => a y).getD true)
      (37 * c.N ^ 5) c.N (time_fwdNbrs c μ) (length_fwdNbrs c μ) (n + 1) ch (VSet.single v) [v]
    have hf' : (n + 1) * (1 + 37 * c.N ^ 5 + c.N) ≤ 39 * c.N ^ 6 := by
      have : 1 + 37 * c.N ^ 5 + c.N ≤ 39 * c.N ^ 5 := by
        have : c.N ≤ c.N ^ 5 := by simpa using N_le_pow c (i := 1) (j := 5) (by omega)
        omega
      exact Nat.le_trans (Nat.mul_le_mul_left _ this) (N_mul_le c 39 5 6 hn rfl)
    generalize explore (fwdNbrs c μ) _ (n + 1) ch (VSet.single v) [v] = fw at *
    have hb := time_explore_le (bwdNbrs c fw.ret.1 fw.ret.2) (fun _ => true)
      (3 * c.N ^ 2) c.N (fun _ x => time_bwdNbrs c fw.ret.1 fw.ret.2 x)
      (fun _ x => length_bwdNbrs c fw.ret.1 fw.ret.2 x) (n + 1) () (VSet.single v) [v]
    have hb' : (n + 1) * (1 + 3 * c.N ^ 2 + c.N) ≤ 5 * c.N ^ 3 := by
      have : 1 + 3 * c.N ^ 2 + c.N ≤ 5 * c.N ^ 2 := by
        have : c.N ≤ c.N ^ 2 := by simpa using N_le_pow c (i := 1) (j := 2) (by omega)
        omega
      exact Nat.le_trans (Nat.mul_le_mul_left _ this) (N_mul_le c 5 2 3 hn rfl)
    generalize explore (bwdNbrs c fw.ret.1 fw.ret.2) _ (n + 1) () (VSet.single v) [v] = bw at *
    have hk := time_keptT c fw.ret.1 v
    have hkl := length_keptT c fw.ret.1 v
    have he := time_evenCycleMaxima c fw.ret.1 bw.ret.2
    rw [show (k + 1) * (56 * c.N ^ 6) = k * (56 * c.N ^ 6) + 56 * c.N ^ 6 by ring]
    split
    · simp only [time_pure]; omega
    · simp only [time_bind, time_tick]
      split
      · simp only [time_pure]; omega
      · split
        · simp only [time_pure]; omega
        · have := ih fw.ret.1 (some (materialize fun u =>
            bw.ret.2 u && !(evenCycleMaxima c fw.ret.1 bw.ret.2).ret u))
          omega

theorem time_exitStep (c : Ctx n) (μ : Fin n → Val) (M : VSet n) (s : Fin n) (acc : Val)
    (w : Fin n) : (exitStep c μ M s acc w).time ≤ 34 * c.N ^ 4 := by
  have hN := one_le_N c
  have h4 : c.N ≤ c.N ^ 4 := by simpa using N_le_pow c (i := 1) (j := 4) (by omega)
  simp only [exitStep, time_bind, time_tick]
  split
  · simp only [time_pure]; omega
  · simp only [time_bind, time_pure]
    have := time_prog c s (μ w)
    have := time_cmpVal c (prog c s (μ w)).ret acc
    omega

theorem time_exitBound (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (s : Fin n) : (exitBound c μ ch M s).time ≤ 35 * c.N ^ 5 := by
  have hN := one_le_N c
  have h5 : c.N ≤ c.N ^ 5 := by simpa using N_le_pow c (i := 1) (j := 5) (by omega)
  simp only [exitBound, time_bind]
  have := time_keptT c ch s
  have := time_foldlM_le (exitStep c μ M s) (34 * c.N ^ 4) (keptT c ch s).ret none
    (fun b a _ => time_exitStep c μ M s b a)
  have := N_mul_le c 34 4 5 (length_keptT c ch s) rfl
  omega

theorem time_initStep (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (b : Fin n → Val) (s : Fin n) : (initStep c μ ch M b s).time ≤ 36 * c.N ^ 5 := by
  have hN := one_le_N c
  have h5 : 1 ≤ c.N ^ 5 := Nat.one_le_pow _ _ (by omega)
  simp only [initStep, time_bind, time_tick]
  split
  · simp only [time_bind, time_pure]; have := time_exitBound c μ ch M s; omega
  · simp only [time_pure]; omega

theorem time_bfEdge (c : Ctx n) (M : VSet n) (s : Fin n) (acc : (Fin n → Val) × Bool)
    (w : Fin n) : (bfEdge c M s acc w).time ≤ 34 * c.N ^ 4 := by
  have hN := one_le_N c
  have h4 : c.N ≤ c.N ^ 4 := by simpa using N_le_pow c (i := 1) (j := 4) (by omega)
  simp only [bfEdge, time_bind, time_tick]
  split
  · simp only [time_bind, time_pure]
    have := time_prog c s (acc.1 w)
    have := time_cmpVal c (prog c s (acc.1 w)).ret (acc.1 s)
    omega
  · simp only [time_pure]; omega

theorem time_bfStep (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (acc : (Fin n → Val) × Bool) (s : Fin n) : (bfStep c ch M acc s).time ≤ 36 * c.N ^ 5 := by
  have hN := one_le_N c
  have h5 : c.N ≤ c.N ^ 5 := by simpa using N_le_pow c (i := 1) (j := 5) (by omega)
  simp only [bfStep, time_bind, time_tick]
  split
  · simp only [time_bind]
    have := time_keptT c ch s
    have := time_foldlM_le (bfEdge c M s) (34 * c.N ^ 4) (keptT c ch s).ret acc
      (fun b a _ => time_bfEdge c M s b a)
    have := N_mul_le c 34 4 5 (length_keptT c ch s) rfl
    omega
  · simp only [time_pure]; omega

theorem time_bfRound (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (b : Fin n → Val) :
    (bfRound c ch M b).time ≤ 36 * c.N ^ 6 := by
  unfold bfRound
  have := time_foldlM_le (bfStep c ch M) (36 * c.N ^ 5) (List.finRange n) (b, false)
    (fun b a _ => time_bfStep c ch M b a)
  have := N_mul_le c 36 5 6 (a := n) (by have := n_succ_le_N c; omega) rfl
  simp only [List.length_finRange] at *
  omega

theorem time_bfLoop (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) :
    ∀ (k : ℕ) (b : Fin n → Val), (bfLoop c ch M k b).time ≤ k * (36 * c.N ^ 6) := by
  intro k
  induction k with
  | zero => intro b; simp [bfLoop]
  | succ k ih =>
    intro b
    simp only [bfLoop, time_bind]
    have := time_bfRound c ch M b
    rw [Nat.succ_mul]
    split
    · have := ih (bfRound c ch M b).ret.1; omega
    · simp only [time_pure]; omega

theorem time_raiseStep (c : Ctx n) (M : VSet n) (b : Fin n → Val) (acc : LState n × ℕ)
    (s : Fin n) : (raiseStep c M b acc s).time ≤ 4 * c.N := by
  simp only [raiseStep, time_bind, time_tick]
  split
  · simp only [time_bind]
    have := time_cmpVal c (b s) (acc.1.measure s)
    split
    · simp only [time_bind, time_pure]
      have := time_requeuePreds c
        ⟨Function.update acc.1.measure s (b s), acc.1.choice, acc.1.queue, acc.1.inq, acc.1.steps⟩ s
      have := one_le_N c
      omega
    · simp only [time_pure]; have := one_le_N c; omega
  · simp only [time_pure]; have := one_le_N c; omega

theorem queue_requeue (st : LState n) (v : Fin n) :
    (requeue st v).queue.length ≤ st.queue.length + 1 := by
  unfold requeue; split <;> simp

theorem queue_raiseStep (c : Ctx n) (M : VSet n) (b : Fin n → Val) (acc : LState n × ℕ)
    (s : Fin n) (q0 : ℕ) (h : acc.1.queue.length ≤ q0 + acc.2 * (n + 1)) :
    (raiseStep c M b acc s).ret.1.queue.length ≤ q0 + (raiseStep c M b acc s).ret.2 * (n + 1) := by
  simp only [raiseStep, ret_bind]
  split
  · simp only [ret_bind]
    split
    · simp only [ret_bind, ret_pure]
      have h1 := queue_requeuePreds c
        ⟨Function.update acc.1.measure s (b s), acc.1.choice, acc.1.queue, acc.1.inq, acc.1.steps⟩ s
      have h2 := queue_requeue (requeuePreds c
        ⟨Function.update acc.1.measure s (b s), acc.1.choice, acc.1.queue, acc.1.inq, acc.1.steps⟩
          s).ret s
      dsimp only at h1
      rw [Nat.succ_mul]
      omega
    · simp only [ret_pure]; exact h
  · simp only [ret_pure]; exact h

theorem time_raise (c : Ctx n) (M : VSet n) (b : Fin n → Val) (st : LState n) :
    (raise c M b st).time ≤ 4 * c.N ^ 2 := by
  unfold raise
  have := time_foldlM_le (raiseStep c M b) (4 * c.N) (List.finRange n) (st, 0)
    (fun x a _ => time_raiseStep c M b x a)
  have := N_mul_le c 4 1 2 (a := n) (by have := n_succ_le_N c; omega) rfl
  simp only [List.length_finRange, pow_one] at *
  omega

theorem queue_raise (c : Ctx n) (M : VSet n) (b : Fin n → Val) (st : LState n) :
    (raise c M b st).ret.1.queue.length ≤ st.queue.length + (raise c M b st).ret.2 * (n + 1) := by
  unfold raise
  rw [ret_foldlM]
  suffices ∀ (l : List (Fin n)) (acc : LState n × ℕ),
      acc.1.queue.length ≤ st.queue.length + acc.2 * (n + 1) →
      (l.foldl (fun x a => (raiseStep c M b x a).ret) acc).1.queue.length ≤
        st.queue.length + (l.foldl (fun x a => (raiseStep c M b x a).ret) acc).2 * (n + 1) from
    this _ _ (by simp)
  intro l
  induction l with
  | nil => intro acc h; simpa using h
  | cons a l ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (queue_raiseStep c M b acc a _ h)

theorem time_accelRaise (c : Ctx n) (st : LState n) (M : VSet n) :
    (accelRaise c st M).time ≤ 80 * c.N ^ 7 := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  have h67 : c.N ^ 6 ≤ c.N ^ 7 := N_le_pow c (by omega)
  have h27 : c.N ^ 2 ≤ c.N ^ 7 := N_le_pow c (by omega)
  have h17 : c.N ≤ c.N ^ 7 := by simpa using N_le_pow c (i := 1) (j := 7) (by omega)
  simp only [accelRaise, time_bind, time_tick]
  have hi := time_foldlM_le (initStep c st.measure st.choice M) (36 * c.N ^ 5)
    (List.finRange n) (fun _ => none) (fun b a _ => time_initStep c st.measure st.choice M b a)
  have hi' := N_mul_le c 36 5 6 (a := n) (by omega) rfl
  simp only [List.length_finRange] at hi
  generalize List.foldlM (initStep c st.measure st.choice M) (fun _ => none) (List.finRange n) = b0
    at *
  have hl := time_bfLoop c st.choice M M.count b0.ret
  have hl' := N_mul_le c 36 6 7 (a := M.count) (by have := count_le M; omega) rfl
  have hr := time_raise c M (bfLoop c st.choice M M.count b0.ret).ret st
  omega

theorem time_accelerate (c : Ctx n) (st : LState n) (v : Fin n) :
    (accelerate c st v).time ≤ 175 * c.N ^ 7 := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  have hp := time_pumpTest c st.measure v n st.choice v
  have hp' := N_mul_le c 36 5 6 (a := n) (by omega) rfl
  have h67 : c.N ^ 6 ≤ c.N ^ 7 := N_le_pow c (by omega)
  simp only [accelerate, time_bind]
  split
  · simp only [time_pure]; omega
  · simp only [time_bind]
    have hs := time_sccLoop c st.measure v (n + 1) (pumpTest c st.measure v n st.choice v).ret.1
      none
    have hs' := N_mul_le c 56 6 7 hn rfl
    split
    · simp only [time_pure]; omega
    · rename_i M _
      generalize ({ st with choice := _ } : LState n) = st' at *
      have := time_accelRaise c st' M
      omega

theorem queue_accelRaise (c : Ctx n) (st : LState n) (M : VSet n) :
    (accelRaise c st M).ret.1.queue.length ≤
      st.queue.length + (accelRaise c st M).ret.2 * (n + 1) := by
  simp only [accelRaise, ret_bind]
  exact queue_raise c _ _ _

theorem queue_accelerate (c : Ctx n) (st : LState n) (v : Fin n) :
    (accelerate c st v).ret.1.queue.length ≤
      st.queue.length + (accelerate c st v).ret.2 * (n + 1) := by
  simp only [accelerate, ret_bind]
  split
  · simp
  · simp only [ret_bind]
    split
    · simp
    · exact queue_accelRaise c _ _

/-! ### The lifting loop -/

theorem runLoop_potential (c : Ctx n) (B K : ℕ) (hK : 250 * c.N ^ 7 ≤ K) :
    ∀ (f : ℕ) (st : LState n),
      (runLoop c B f st).time + 37 * c.N ^ 5 * (runLoop c B f st).ret.1.queue.length +
          K * st.steps ≤
        37 * c.N ^ 5 * st.queue.length + K * (runLoop c B f st).ret.1.steps := by
  intro f
  induction f with
  | zero => intro st; simp [runLoop]
  | succ f ih =>
    intro st
    unfold runLoop
    split
    · simp
    · split
      · simp
      · rename_i v q hq
        simp only [time_bind, time_tick, ret_bind]
        have hN := one_le_N c
        have hn := n_succ_le_N c
        have h15 : c.N ≤ c.N ^ 5 := by simpa using N_le_pow c (i := 1) (j := 5) (by omega)
        have h57 : c.N ^ 5 ≤ c.N ^ 7 := N_le_pow c (by omega)
        have h67 : c.N ^ 6 ≤ c.N ^ 7 := N_le_pow c (by omega)
        have hE := time_evaluate' c st.measure v none
        have hC := time_cmpVal c (evaluate c st.measure v none).ret.1 (st.measure v)
        have hlen : st.queue.length = q.length + 1 := by rw [hq]; simp
        have hEn : 37 * c.N ^ 5 * (n + 1) ≤ 37 * c.N ^ 6 := by
          have := N_mul_le c 37 5 6 hn rfl; rw [Nat.mul_comm]; exact this
        generalize evaluate c st.measure v none = ev at *
        generalize cmpVal c ev.ret.1 (st.measure v) = o at *
        split
        · simp only [time_bind, ret_bind]
          set st3 : LState n := ⟨Function.update st.measure v ev.ret.1,
            Function.update st.choice v ev.ret.2, q, Function.update st.inq v false, st.steps + 1⟩
            with hs3
          have hR := time_requeuePreds c st3 v
          have hRq := queue_requeuePreds c st3 v
          have q3 : st3.queue = q := by rw [hs3]
          rw [q3] at hRq
          generalize (requeuePreds c st3 v).ret = st4 at *
          have hA := time_accelerate c st4 v
          have hAq := queue_accelerate c st4 v
          generalize accelerate c st4 v = a at *
          have hih := ih ⟨a.ret.1.measure, a.ret.1.choice, a.ret.1.queue, a.ret.1.inq,
            st.steps + 1 + a.ret.2⟩
          generalize runLoop c B f ⟨a.ret.1.measure, a.ret.1.choice, a.ret.1.queue, a.ret.1.inq,
            st.steps + 1 + a.ret.2⟩ = r at *
          simp only at hih hRq
          have k1 : 37 * c.N ^ 5 * a.ret.1.queue.length ≤
              37 * c.N ^ 5 * (q.length + n + a.ret.2 * (n + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
          have k2 : 37 * c.N ^ 5 * (a.ret.2 * (n + 1)) ≤ K * a.ret.2 := by
            rw [Nat.mul_comm K, ← Nat.mul_assoc, Nat.mul_comm (37 * c.N ^ 5) a.ret.2,
              Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ (by omega)
          nlinarith
        · have hih := ih ⟨st.measure, Function.update st.choice v ev.ret.2, q,
            Function.update st.inq v false, st.steps⟩
          generalize runLoop c B f ⟨st.measure, Function.update st.choice v ev.ret.2, q,
            Function.update st.inq v false, st.steps⟩ = r at *
          simp only at hih
          nlinarith

theorem runLoop_steps_mono (c : Ctx n) (B : ℕ) :
    ∀ (f : ℕ) (st : LState n), st.steps ≤ (runLoop c B f st).ret.1.steps := by
  intro f
  induction f with
  | zero => intro st; simp [runLoop]
  | succ f ih =>
    intro st
    unfold runLoop
    split
    · simp
    · split
      · simp
      · simp only [ret_bind]
        split
        · simp only [ret_bind]
          refine Nat.le_trans ?_ (ih _)
          simp only; omega
        · refine Nat.le_trans ?_ (ih _)
          simp only; omega

theorem runLoop_budget (c : Ctx n) (B : ℕ) :
    ∀ (f : ℕ) (st : LState n), (runLoop c B f st).ret.2.1 = false →
      (runLoop c B f st).ret.2.2 = false → B ≤ (runLoop c B f st).ret.1.steps := by
  intro f
  induction f with
  | zero => intro st _ h; simp [runLoop] at h
  | succ f ih =>
    intro st
    rw [runLoop.eq_2]
    split
    · intro _ _; simpa
    · split
      · simp
      · simp only [ret_bind]
        split
        · simp only [ret_bind]; exact ih _
        · exact ih _

/-! ### Certification -/

theorem time_certLoop (c : Ctx n) (μ : Fin n → Val) :
    ∀ (k : ℕ) (dom queued : VSet n) (q : List (Fin n)),
      (certLoop c μ k dom queued q).time ≤ k * (41 * c.N ^ 5) := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  have h15 : c.N ≤ c.N ^ 5 := by simpa using N_le_pow c (i := 1) (j := 5) (by omega)
  intro k
  induction k with
  | zero => intro dom queued q; simp [certLoop]
  | succ k ih =>
    intro dom queued q
    cases q with
    | nil => simp [certLoop]
    | cons v q =>
      simp only [certLoop, time_bind, time_tick]
      rw [Nat.succ_mul]
      split
      · have := ih dom (Function.update queued v false) q; omega
      · simp only [time_bind, time_tick]
        have hs := time_succT c v
        have hsl := length_succT c v
        have hev := time_evaluate' c μ v (some dom)
        have hp := time_predT c v
        have hpl := length_predT c v
        split
        · simp only [time_bind, time_pure, ret_pure, time_tick, Bool.false_eq_true, ↓reduceIte]
          have := ih (Function.update dom v false)
            ((predT c v).ret.foldl (certPush (Function.update dom v false))
              (Function.update queued v false, q)).1
            ((predT c v).ret.foldl (certPush (Function.update dom v false))
              (Function.update queued v false, q)).2
          omega
        · simp only [time_bind, time_pure, ret_pure]
          have hc := time_cmpVal c (μ v) (evaluate c μ v (some dom)).ret.1
          split
          · have := ih dom (Function.update queued v false) q; omega
          · simp only [time_bind, time_tick]
            have := ih (Function.update dom v false)
              ((predT c v).ret.foldl (certPush (Function.update dom v false))
                (Function.update queued v false, q)).1
              ((predT c v).ret.foldl (certPush (Function.update dom v false))
                (Function.update queued v false, q)).2
            omega

theorem time_certified (c : Ctx n) (st : LState n) :
    (certified c st).time ≤ 43 * c.N ^ 7 := by
  have hN := one_le_N c
  have hn := n_succ_le_N c
  simp only [certified, time_bind, time_tick, time_pure]
  have h := time_certLoop c st.measure (n * n + n + 1)
    (materialize fun v => c.alive v && (st.measure v).isSome)
    (materialize fun v => c.alive v && (st.measure v).isSome)
    ((List.finRange n).filter (materialize fun v => c.alive v && (st.measure v).isSome))
  have hf : n * n + n + 1 ≤ c.N * c.N := by nlinarith
  have : (n * n + n + 1) * (41 * c.N ^ 5) ≤ c.N * c.N * (41 * c.N ^ 5) :=
    Nat.mul_le_mul_right _ hf
  have : c.N * c.N * (41 * c.N ^ 5) = 41 * c.N ^ 7 := by ring
  have h17 : c.N ≤ c.N ^ 7 := by simpa using N_le_pow c (i := 1) (j := 7) (by omega)
  omega

/-! ### Attractor, lifter construction, completion, removal -/

theorem time_attrPass (G : PGame n) (alive : VSet n) (player : Bool) (A : VSet n) :
    (attrPass G alive player A).time ≤ n * (G.m + 1) := by
  unfold attrPass
  have := time_foldlM_le (attrStep G alive player) (G.m + 1) (List.finRange n) A (by
    intro b u _
    simp only [attrStep, time_bind, time_tick]
    have := deg_le_m G u
    split <;> simp <;> omega)
  simpa using this

theorem time_attractor (G : PGame n) (alive : VSet n) (player : Bool) (target : VSet n) :
    (attractor G alive player target).time ≤ 2 * G.size ^ 3 := by
  simp only [attractor, time_bind, time_tick]
  have := time_iterT_le (attrPass G alive player) (n * (G.m + 1)) (time_attrPass G alive player)
    (n + 1) (materialize fun v => alive v && target v)
  have h1 : n + 1 ≤ G.size := by simp only [PGame.size]; omega
  have h2 : G.m + 1 ≤ G.size := by simp only [PGame.size]; omega
  have : (n + 1) * (n * (G.m + 1)) ≤ G.size * (G.size * G.size) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) h2)
  have : G.size * (G.size * G.size) = G.size ^ 3 := by ring
  have : n ≤ G.size ^ 3 := by
    have : G.size ≤ G.size ^ 3 := by
      simpa using Nat.pow_le_pow_right (n := G.size) (by omega) (show 1 ≤ 3 by omega)
    omega
  omega

theorem time_removal (G : PGame n) (alive winner cert0 cert1 : VSet n) :
    (removal G alive winner cert0 cert1).time ≤ 6 * G.size ^ 3 := by
  simp only [removal, time_bind, time_tick, time_pure]
  have := time_attractor G alive false cert0
  have := time_attractor G (materialize fun v => alive v && !(attractor G alive false cert0).ret v)
    true cert1
  have h1 : n + 1 ≤ G.size := by simp only [PGame.size]; omega
  have : G.size ≤ G.size ^ 3 := by
    simpa using Nat.pow_le_pow_right (n := G.size) (by omega) (show 1 ≤ 3 by omega)
  omega

theorem time_complete (c : Ctx n) (st : LState n) (w : VSet n) : (complete c st w).time = n := by
  simp [complete]

theorem time_mkLifter (G : PGame n) (alive : VSet n) (p : Bool) :
    (mkLifter G alive p).time ≤ 3 * G.size ^ 2 := by
  have hl : (mkLevels G p alive).time = (G.d + 1) * (n + 1) := by simp [mkLevels]
  simp only [mkLifter, time_bind, time_tick, time_pure]
  have := time_leftmost ⟨G, p, alive, _, (mkLevels G p alive).ret.2⟩ []
  simp only [Ctx.N] at this
  have h1 : n + 1 ≤ G.size := by simp only [PGame.size]; omega
  have h2 : G.d + 1 ≤ G.size := by simp only [PGame.size]; omega
  have : (G.d + 1) * (n + 1) ≤ G.size * G.size := Nat.mul_le_mul h2 h1
  have : G.size * G.size = G.size ^ 2 := by ring
  have : G.size ≤ G.size ^ 2 := by
    simpa using Nat.pow_le_pow_right (n := G.size) (by omega) (show 1 ≤ 2 by omega)
  omega

/-! ### Rounds and restarts -/

theorem run_facts (G : PGame n) (c : Ctx n) (hc : c.G = G) (rem fuel : ℕ) (hrem : 1 ≤ rem)
    (l : LState n) :
    (run c rem fuel l).time + 37 * G.size ^ 5 * (run c rem fuel l).ret.1.queue.length +
        250 * G.size ^ 7 * l.steps ≤
      37 * G.size ^ 5 * l.queue.length + 250 * G.size ^ 7 * (run c rem fuel l).ret.1.steps ∧
    l.steps ≤ (run c rem fuel l).ret.1.steps ∧
    ((run c rem fuel l).ret.2.1 = false → (run c rem fuel l).ret.2.2 = false →
      l.steps + 1 ≤ (run c rem fuel l).ret.1.steps) := by
  have hN : c.N = G.size := by simp [Ctx.N, hc]
  unfold run
  refine ⟨?_, runLoop_steps_mono c _ fuel l, fun h1 h2 => ?_⟩
  · have := runLoop_potential c (l.steps + rem) (250 * c.N ^ 7) le_rfl fuel l
    rwa [hN] at this
  · have := runLoop_budget c (l.steps + rem) fuel l h1 h2
    omega

theorem roundLoop_state_restarts (G : PGame n) (rem fuel : ℕ) (c0 c1 : Ctx n) :
    ∀ (f : ℕ) (s : SState n) (l0 l1 : LState n),
      (roundLoop G rem fuel c0 c1 f s l0 l1).ret.state.restarts = s.restarts := by
  intro f
  induction f with
  | zero => intro s l0 l1; simp [roundLoop, Outcome.state]
  | succ f ih =>
    intro s l0 l1
    rw [roundLoop.eq_2]
    simp only [ret_bind]
    split
    · simp [Outcome.state]
    · split
      · simp [Outcome.state]
      · simp only [ret_bind]
        split
        · simp [Outcome.state]
        · split
          · simp [Outcome.state]
          · simp only [ret_bind]
            split
            · rw [ih]
            · simp [Outcome.state]

theorem roundLoop_potential (G : PGame n) (rem fuel : ℕ) (c0 c1 : Ctx n) (h0 : c0.G = G)
    (h1 : c1.G = G) (hrem : 1 ≤ rem) :
    ∀ (f : ℕ) (s : SState n) (l0 l1 : LState n),
      (roundLoop G rem fuel c0 c1 f s l0 l1).time +
          340 * G.size ^ 7 * (s.steps + l0.steps + l1.steps) ≤
        93 * G.size ^ 7 + 37 * G.size ^ 5 * (l0.queue.length + l1.queue.length) +
          340 * G.size ^ 7 * (roundLoop G rem fuel c0 c1 f s l0 l1).ret.state.steps := by
  have hN0 : c0.N = G.size := by simp [Ctx.N, h0]
  have hN1 : c1.N = G.size := by simp [Ctx.N, h1]
  have hNn : n + 1 ≤ G.size := by simp only [PGame.size]; omega
  have h17 : G.size ≤ G.size ^ 7 := by
    simpa using Nat.pow_le_pow_right (n := G.size) (by omega) (show 1 ≤ 7 by omega)
  have h37 : G.size ^ 3 ≤ G.size ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  intro f
  induction f with
  | zero => intro s l0 l1; simp [roundLoop, Outcome.state]
  | succ f ih =>
    intro s l0 l1
    rw [roundLoop.eq_2]
    simp only [time_bind, ret_bind]
    obtain ⟨p0, m0, b0⟩ := run_facts G c0 h0 rem fuel hrem l0
    generalize run c0 rem fuel l0 = r0 at *
    have m0' := Nat.mul_le_mul_left (90 * G.size ^ 7) m0
    have z0 := Nat.zero_le (37 * G.size ^ 5 * r0.ret.1.queue.length)
    have z1 := Nat.zero_le (37 * G.size ^ 5 * l1.queue.length)
    split
    · simp only [time_pure, ret_pure, Outcome.state]; linarith
    · split
      · simp only [time_bind, time_pure, ret_bind, ret_pure, Outcome.state, time_complete]
        linarith
      · simp only [time_bind, ret_bind]
        have b0' := b0 (by simpa using ‹¬r0.ret.2.1 = true›) (by simpa using ‹¬r0.ret.2.2 = true›)
        have b0'' := Nat.mul_le_mul_left (90 * G.size ^ 7) b0'
        obtain ⟨p1, m1, b1⟩ := run_facts G c1 h1 rem fuel hrem l1
        generalize run c1 rem fuel l1 = r1 at *
        have m1' := Nat.mul_le_mul_left (90 * G.size ^ 7) m1
        have z2 := Nat.zero_le (37 * G.size ^ 5 * r1.ret.1.queue.length)
        split
        · simp only [time_pure, ret_pure, Outcome.state]; linarith
        · split
          · simp only [time_bind, time_pure, ret_bind, ret_pure, Outcome.state, time_complete]
            linarith
          · simp only [time_bind, time_tick, ret_bind]
            have hc0 := time_certified c0 r0.ret.1
            have hc1 := time_certified c1 r1.ret.1
            rw [hN0] at hc0; rw [hN1] at hc1
            split
            · have := ih { s with rounds := s.rounds + 1 } r0.ret.1 r1.ret.1
              simp only at this
              linarith
            · simp only [time_bind, time_pure, ret_bind, ret_pure, Outcome.state]
              have := time_removal G s.alive s.winner (certified c0 r0.ret.1).ret
                (certified c1 r1.ret.1).ret
              linarith

theorem mkLifter_facts (G : PGame n) (alive : VSet n) (p : Bool) :
    (mkLifter G alive p).ret.1.G = G ∧ (mkLifter G alive p).ret.2.steps = 0 ∧
      (mkLifter G alive p).ret.2.queue.length ≤ n := by
  refine ⟨by simp [mkLifter], by simp [mkLifter], ?_⟩
  simp only [mkLifter, ret_bind, ret_pure]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem outer_bound (G : PGame n) (fuel : ℕ) :
    ∀ (k : ℕ) (s : SState n),
      (outer G fuel k s).time + 340 * G.size ^ 7 * s.steps ≤
          k * (175 * G.size ^ 7) + 340 * G.size ^ 7 * (outer G fuel k s).ret.1.steps ∧
        (outer G fuel k s).ret.1.restarts ≤ s.restarts + k := by
  have hNn : n + 1 ≤ G.size := by simp only [PGame.size]; omega
  have h17 : G.size ≤ G.size ^ 7 := by
    simpa using Nat.pow_le_pow_right (n := G.size) (by omega) (show 1 ≤ 7 by omega)
  have h27 : G.size ^ 2 ≤ G.size ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h67 : G.size ^ 6 ≤ G.size ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq : 37 * G.size ^ 5 * (n + n) ≤ 74 * G.size ^ 6 := by
    have : 37 * G.size ^ 5 * (n + n) ≤ 37 * G.size ^ 5 * (2 * G.size) :=
      Nat.mul_le_mul_left _ (by omega)
    have : 37 * G.size ^ 5 * (2 * G.size) = 74 * G.size ^ 6 := by ring
    omega
  intro k
  induction k with
  | zero => intro s; simp [outer]
  | succ k ih =>
    intro s
    rw [outer.eq_2, show (k + 1) * (175 * G.size ^ 7) = k * (175 * G.size ^ 7) + 175 * G.size ^ 7
      by ring]
    simp only [time_bind, time_tick, ret_bind]
    split
    · simp only [time_pure, ret_pure]; constructor <;> omega
    · simp only [time_bind, ret_bind]
      obtain ⟨g0, s0, q0⟩ := mkLifter_facts G s.alive false
      obtain ⟨g1, s1, q1⟩ := mkLifter_facts G s.alive true
      have t0 := time_mkLifter G s.alive false
      have t1 := time_mkLifter G s.alive true
      have hrem : 1 ≤ s.alive.count := by
        rename_i h; simp only [beq_iff_eq] at h; omega
      have hR := roundLoop_potential G s.alive.count fuel _ _ g0 g1 hrem fuel
        { s with restarts := s.restarts + 1 } (mkLifter G s.alive false).ret.2
        (mkLifter G s.alive true).ret.2
      have hr := roundLoop_state_restarts G s.alive.count fuel (mkLifter G s.alive false).ret.1
        (mkLifter G s.alive true).ret.1 fuel { s with restarts := s.restarts + 1 }
        (mkLifter G s.alive false).ret.2 (mkLifter G s.alive true).ret.2
      rw [s0, s1] at hR
      simp only [Nat.add_zero] at hR
      have hq' : 37 * G.size ^ 5 * ((mkLifter G s.alive false).ret.2.queue.length +
          (mkLifter G s.alive true).ret.2.queue.length) ≤ 37 * G.size ^ 5 * (n + n) :=
        Nat.mul_le_mul_left _ (by omega)
      generalize roundLoop G s.alive.count fuel _ _ fuel _ _ _ = o at *
      match ho : o.ret with
      | .done s' =>
        simp only [Outcome.state, ho] at hR hr ⊢
        simp only [time_pure, ret_pure]
        constructor <;> omega
      | .oof s' =>
        simp only [Outcome.state, ho] at hR hr ⊢
        simp only [time_pure, ret_pure]
        constructor <;> omega
      | .next s' =>
        simp only [Outcome.state, ho] at hR hr ⊢
        obtain ⟨i1, i2⟩ := ih s'
        constructor <;> omega

/-! ### Headlines -/

theorem navigationCost (c : Ctx n) : NavigationCost c := by
  refine ⟨time_leftmost c, time_cmpVal c, fun pre h => ?_, time_prog c⟩
  have := time_nextNode c pre
  have := N_mul_le c 30 3 4 (a := pre.length) (by have := height_succ_le_N c; omega) rfl
  omega

theorem regionInfoCost (c : Ctx n) : RegionInfoCost c :=
  ⟨time_weakComponents c, time_children c, time_chainBound c⟩

theorem evaluateCost (c : Ctx n) : EvaluateCost c := time_evaluate c

theorem accelerateCost (c : Ctx n) : AccelerateCost c :=
  fun st v => ⟨time_accelerate c st v, queue_accelerate c st v⟩

theorem liftingAmortised (c : Ctx n) : LiftingAmortised c :=
  fun B f st => runLoop_potential c B (250 * c.N ^ 7) le_rfl f st

theorem certifiedCost (c : Ctx n) : CertifiedCost c := time_certified c

theorem attractorCost (G : PGame n) : AttractorCost G := time_attractor G

theorem solveTimeBound (G : PGame n) (fuel : ℕ) : SolveTimeBound G fuel := by
  unfold SolveTimeBound costPoly
  simp only [solve, time_bind, time_pure, ret_bind, ret_pure]
  obtain ⟨h1, h2⟩ := outer_bound G fuel (n + 1) ⟨fun _ => true, fun _ => false, 0, 0, 0⟩
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at h1 h2
  refine ⟨?_, h2⟩
  generalize (outer G fuel (n + 1) ⟨fun _ => true, fun _ => false, 0, 0, 0⟩) = r at *
  have : (r.ret.1.steps + n + 1) * (340 * G.size ^ 7) =
      340 * G.size ^ 7 * r.ret.1.steps + (n + 1) * (340 * G.size ^ 7) := by ring
  have : (n + 1) * (175 * G.size ^ 7) ≤ (n + 1) * (340 * G.size ^ 7) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem solvePolyOfSteps (G : PGame n) (fuel : ℕ) (Q : ℕ → ℕ) : SolvePolyOfSteps G fuel Q := by
  intro h
  refine Nat.le_trans (solveTimeBound G fuel).1 (Nat.mul_le_mul_right _ ?_)
  omega

/-! ### Progress of restarts -/

@[simp] theorem materialize_apply (S : VSet n) (i : Fin n) : materialize S i = S i := by
  simp [materialize]

theorem filter_length_lt (S T : VSet n) (hTS : ∀ v, T v = true → S v = true) :
    ∀ (l : List (Fin n)), (l.filter T).length ≤ (l.filter S).length ∧
      (∀ v ∈ l, S v = true → T v = false → (l.filter T).length < (l.filter S).length) := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hS : S a = true <;> by_cases hT : T a = true
    · simp only [List.filter_cons, hS, hT, ↓reduceIte, List.length_cons, List.mem_cons]
      refine ⟨by omega, fun v hv h1 h2 => ?_⟩
      rcases hv with rfl | hv
      · simp [hT] at h2
      · have := ih2 v hv h1 h2; omega
    · simp only [List.filter_cons, hS, hT, ↓reduceIte, List.length_cons, List.mem_cons,
        Bool.false_eq_true]
      refine ⟨by omega, fun v _ _ _ => by omega⟩
    · exact absurd (hTS a hT) hS
    · simp only [List.filter_cons, hS, hT, ↓reduceIte, List.mem_cons, Bool.false_eq_true]
      refine ⟨ih1, fun v hv h1 h2 => ?_⟩
      rcases hv with rfl | hv
      · simp [hS] at h1
      · exact ih2 v hv h1 h2

theorem count_lt (S T : VSet n) (hTS : ∀ v, T v = true → S v = true) (v : Fin n)
    (hS : S v = true) (hT : T v = false) : T.count < S.count :=
  (filter_length_lt S T hTS (List.finRange n)).2 v (List.mem_finRange v) hS hT

theorem certified_sub (c : Ctx n) (st : LState n) (v : Fin n)
    (h : (certified c st).ret v = true) : c.alive v = true := by
  simp only [certified, ret_bind, ret_pure] at h
  generalize (certLoop _ _ _ _ _ _).ret = r at h
  cases r with
  | some D => simp only [materialize_apply, Bool.and_eq_true] at h; exact h.1
  | none => simp [VSet.empty] at h

theorem attrPass_mono (G : PGame n) (alive : VSet n) (player : Bool) (A : VSet n) (v : Fin n)
    (h : A v = true) : (attrPass G alive player A).ret v = true := by
  unfold attrPass
  rw [ret_foldlM]
  suffices ∀ (l : List (Fin n)) (B : VSet n), B v = true →
      (l.foldl (fun b a => (attrStep G alive player b a).ret) B) v = true from this _ _ h
  intro l
  induction l with
  | nil => intro B hB; simpa using hB
  | cons u l ih =>
    intro B hB
    simp only [List.foldl_cons]
    apply ih
    have key : ∀ (P : Prop) [Decidable P],
        (if P then Function.update B u true else B) v = true := by
      intro P _
      split
      · by_cases hvu : v = u
        · subst hvu; simp
        · rw [Function.update_of_ne hvu]; exact hB
      · exact hB
    simp only [attrStep, ret_bind]
    split
    · simp only [ret_pure]; exact key _
    · simpa using hB

theorem iterT_mono (f : VSet n → TimeM ℕ (VSet n)) (v : Fin n)
    (hf : ∀ A, A v = true → (f A).ret v = true) :
    ∀ (k : ℕ) (A : VSet n), A v = true → (iterT f k A).ret v = true := by
  intro k
  induction k with
  | zero => intro A h; simpa [iterT] using h
  | succ k ih => intro A h; simp only [iterT, ret_bind]; exact ih _ (hf A h)

theorem attractor_sup (G : PGame n) (alive : VSet n) (player : Bool) (target : VSet n) (v : Fin n)
    (ha : alive v = true) (ht : target v = true) :
    (attractor G alive player target).ret v = true := by
  simp only [attractor, ret_bind]
  exact iterT_mono _ v (fun A h => attrPass_mono G alive player A v h) _ _ (by simp [ha, ht])

theorem removal_progress (G : PGame n) (alive winner cert0 cert1 : VSet n)
    (h0 : ∀ v, cert0 v = true → alive v = true) (h1 : ∀ v, cert1 v = true → alive v = true)
    (hne : cert0.count ≠ 0 ∨ cert1.count ≠ 0) :
    (removal G alive winner cert0 cert1).ret.1.count < alive.count := by
  have hex : ∃ v, cert0 v = true ∨ cert1 v = true := by
    rcases hne with h | h
    · obtain ⟨v, hv⟩ : ∃ v, v ∈ (List.finRange n).filter cert0 :=
        List.exists_mem_of_length_pos (by unfold VSet.count at h; omega)
      exact ⟨v, Or.inl (List.mem_filter.1 hv).2⟩
    · obtain ⟨v, hv⟩ : ∃ v, v ∈ (List.finRange n).filter cert1 :=
        List.exists_mem_of_length_pos (by unfold VSet.count at h; omega)
      exact ⟨v, Or.inr (List.mem_filter.1 hv).2⟩
  obtain ⟨v, hv⟩ := hex
  simp only [removal, ret_bind, ret_pure]
  apply count_lt alive _
    (fun u hu => by simp only [materialize_apply, Bool.and_eq_true] at hu; exact hu.1.1) v
  · rcases hv with hv | hv
    · exact h0 v hv
    · exact h1 v hv
  · simp only [materialize_apply, Bool.and_eq_false_iff, Bool.not_eq_false']
    by_cases hA0 : (attractor G alive false cert0).ret v = true
    · left; right; exact hA0
    · rcases hv with hv | hv
      · exact absurd (attractor_sup G alive false cert0 v (h0 v hv) hv) hA0
      · right
        apply attractor_sup _ _ _ _ v _ hv
        simp only [materialize_apply, h1 v hv, Bool.true_and, Bool.not_eq_true']
        simpa using hA0

theorem mkLifter_alive (G : PGame n) (alive : VSet n) (p : Bool) :
    (mkLifter G alive p).ret.1.alive = alive := by
  simp [mkLifter]

theorem roundLoop_progress (G : PGame n) (rem fuel : ℕ) (c0 c1 : Ctx n) (A : VSet n)
    (h0 : c0.alive = A) (h1 : c1.alive = A) :
    ∀ (f : ℕ) (s s' : SState n) (l0 l1 : LState n), s.alive = A →
      (roundLoop G rem fuel c0 c1 f s l0 l1).ret = .next s' → s'.alive.count < A.count := by
  intro f
  induction f with
  | zero => intro s s' l0 l1 _ h; simp [roundLoop] at h
  | succ f ih =>
    intro s s' l0 l1 hs h
    rw [roundLoop.eq_2] at h
    simp only [ret_bind] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [ret_bind] at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [ret_bind] at h
            split at h
            · exact ih _ s' _ _ (by simpa using hs) h
            · simp only [ret_bind, ret_pure, Outcome.next.injEq] at h
              subst h
              rename_i hc
              simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hc
              simp only [hs]
              apply removal_progress
              · intro v hv; rw [← h0]; exact certified_sub c0 _ v hv
              · intro v hv; rw [← h1]; exact certified_sub c1 _ v hv
              · by_cases h' : (certified c0 (run c0 rem fuel l0).ret.1).ret.count = 0
                · exact Or.inr (hc h')
                · exact Or.inl h'

theorem restartProgress (G : PGame n) (fuel : ℕ) : RestartProgress G fuel := by
  intro rem f s s' l0 l1 h
  exact roundLoop_progress G rem fuel _ _ s.alive (mkLifter_alive G s.alive false)
    (mkLifter_alive G s.alive true) f s s' l0 l1 rfl h

theorem outer_some (G : PGame n) (fuel : ℕ)
    (hno : ∀ s s' : SState n, (roundLoop G s.alive.count fuel (mkLifter G s.alive false).ret.1
      (mkLifter G s.alive true).ret.1 fuel s (mkLifter G s.alive false).ret.2
      (mkLifter G s.alive true).ret.2).ret ≠ .oof s') :
    ∀ (k : ℕ) (s : SState n), s.alive.count < k → (outer G fuel k s).ret.2 = true := by
  intro k
  induction k with
  | zero => intro s h; omega
  | succ k ih =>
    intro s hk
    rw [outer.eq_2]
    simp only [ret_bind]
    split
    · simp
    · simp only [ret_bind]
      have hno' := hno { s with restarts := s.restarts + 1 }
      have hp := restartProgress G fuel s.alive.count fuel { s with restarts := s.restarts + 1 }
      simp only at hno' hp
      split
      · simp
      · rename_i s' heq
        exact absurd heq (hno' s')
      · rename_i s' heq
        have := hp s' _ _ heq
        exact ih s' (by omega)

theorem outerFuelSuffices (G : PGame n) (fuel : ℕ) : OuterFuelSuffices G fuel := by
  intro hno
  simp only [solve, ret_bind, ret_pure]
  rw [outer_some G fuel hno (n + 1) _ (by
    have := count_le (n := n) (fun _ => true)
    simp only at this ⊢; omega)]
  simp

end ParityGame.TwoSidedCost
