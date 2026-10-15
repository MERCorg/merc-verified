module

public import MercLib.TwoSided.Proofs.TwoSidedCostCorrect_Win_Proofs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section TwoSidedCostCorrectFuelProofs

namespace MercLib.ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Termination of `solve` with explicit fuel. Every value the program builds is a list of `h` pairs
with entries `≤ n (n + 1)` (child indices `< n`, counters `≤` the chain bound `≤ n (n + 1)`), so
it has a rank below `B ^ (2 h)`, `B = n (n + 1) + 1`, that increases with every lift and every
accelerated raise; the potential `Φ = Σ_v rank (μ v) ≤ n · B ^ (2 h)` bounds the steps of a
restart. A `run` call needs at most `|queue| + (n + 2) · budget` iterations (the queue has no
duplicates, so `|queue| ≤ n`), and every round of a restart that neither finishes nor removes
anything makes at least `budget ≥ 1` steps of player `0`. -/

variable {n : ℕ}

/-! ### Entry bounds -/

/-- The bound on all entries of program values. -/
def ebound (n : ℕ) : ℕ := n * (n + 1)

/-- All entries of a list are at most `ebound n`. -/
def PBnd (n : ℕ) (x : List (ℕ × ℕ)) : Prop := ∀ p ∈ x, p.1 ≤ ebound n ∧ p.2 ≤ ebound n

/-- A value of the right length with bounded entries (or `⊤`). -/
def VOK (c : Ctx n) (t : Val) : Prop := ∀ x, t = some x → x.length = c.height ∧ PBnd n x

theorem weakComponents_length (c : Ctx n) (S : VSet n) : (weakComponents c S).ret.length ≤ n := by
  have key : ∀ (L : List (Fin n)) (acc : VSet n × List (VSet n)),
      (L.foldl (fun b a => (wcStep c S b a).ret) acc).2.length ≤ acc.2.length + L.length := by
    intro L
    induction L with
    | nil => intro acc; simp
    | cons x L ih =>
      intro acc
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      rw [wcStep_ret]
      split <;> simp; omega
  simp only [weakComponents, ret_bind, ret_pure, ret_foldlM]
  have := key (List.finRange n) (VSet.empty, [])
  simpa using this

theorem children_length (c : Ctx n) (l : ℕ) (R : VSet n) :
    (children c l R).ret.length ≤ max 1 n := by
  rw [children_ret]
  split
  · simp
  · exact (weakComponents_length c _).trans (le_max_right _ _)

theorem chainBound_le (c : Ctx n) (R : VSet n) (q : ℕ) :
    (chainBound c R q).ret ≤ ebound n := by
  rw [chainBound_ret]
  apply foldr_max_le
  intro u _
  -- every DP value after `k` rounds is at most `k · n`
  have key : ∀ (k : ℕ) (wt : Fin n → ℕ), (∀ u, wt u ≤ n) → ∀ (S : VSet n)
      (reach : Fin n → VSet n) (u : Fin n),
      (iterT (chainRound S reach wt) k (fun _ => 0)).ret u ≤ k * n := by
    intro k wt hwt S reach
    induction k with
    | zero => intro u; simp [iterT]
    | succ k ih =>
      intro u
      rw [iterT_ret_succ, chainRound_ret]
      dsimp only
      have := foldr_max_le (fun w => (iterT (chainRound S reach wt) k fun _ => 0).ret w) (k * n)
        ((List.finRange n).filter fun w => S w && reach u w && !reach w u) (fun w _ => ih w)
      have := hwt u
      rw [Nat.succ_mul]
      omega
  refine (key (n + 1) _ (fun u => ?_) _ _ u).trans ?_
  · exact (List.length_filter_le _ _).trans (by simp)
  · unfold ebound; rw [Nat.mul_comm]

theorem nextAux_bnd (c : Ctx n) (regs : List (VSet n)) :
    ∀ (f : ℕ) (P nx : List (ℕ × ℕ)), PBnd n P → (nextAux c regs f P).ret = some nx → PBnd n nx
  | 0, P, nx, _, h => by rw [nextAux_ret_zero] at h; cases h
  | f + 1, P, nx, hP, h => by
    rcases List.eq_nil_or_concat P with rfl | ⟨P', ⟨k, cnt⟩, rfl⟩
    · rw [nextAux_ret_nil] at h; cases h
    rw [List.concat_eq_append] at h hP
    have hP' : PBnd n P' := fun p hp => hP p (by simp [hp])
    have hk : k ≤ ebound n ∧ cnt ≤ ebound n := hP (k, cnt) (by simp)
    rw [nextAux_ret_concat] at h
    split_ifs at h with hb hd hs
    · cases h
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hP' p hp
      · simp at hp; subst hp
        have := chainBound_le c (regs.getD P'.length VSet.empty) (c.level P'.length)
        exact ⟨hk.1, by simp only; omega⟩
    · cases h
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hP' p hp
      · simp at hp; subst hp
        have hlen := children_length c (P'.length - 1) (regs.getD (P'.length - 1) VSet.empty)
        have hn : n ≤ n * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
        refine ⟨?_, by simp [ebound]⟩
        simp only
        unfold ebound
        omega
    · exact nextAux_bnd c regs f P' nx hP' h
    · exact nextAux_bnd c regs f P' nx hP' h

theorem pbnd_take (x : List (ℕ × ℕ)) (d : ℕ) (hx : PBnd n x) : PBnd n (x.take d) :=
  fun p hp => hx p (List.mem_of_mem_take hp)

theorem pbnd_leftmost (c : Ctx n) (x : List (ℕ × ℕ)) (hx : PBnd n x) :
    PBnd n (leftmost c x).ret := by
  rw [leftmost_ret]
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hx p hp
  · rw [List.eq_of_mem_replicate hp]; simp

/-- `prog` builds values of length `h` with bounded entries from bounded inputs. -/
theorem prog_ok (c : Ctx n) (v : Fin n) (t : Val) (ht : ∀ x, t = some x → PBnd n x) :
    VOK c (prog c v t).ret := by
  intro r hr
  refine ⟨prog_len c v t r hr, ?_⟩
  cases t with
  | none => rw [prog_ret_none] at hr; cases hr
  | some x =>
    have hx := ht x rfl
    rcases Nat.mod_two_eq_zero_or_one (c.prio v) with hv | hv
    · rw [prog_ret_even c v x hv] at hr
      cases hr
      exact pbnd_leftmost c _ (pbnd_take x _ hx)
    · rw [prog_ret_odd c v x hv] at hr
      obtain ⟨nx, hnx, rfl⟩ := Option.map_eq_some_iff.1 hr
      rw [nextNode_ret] at hnx
      exact pbnd_leftmost c _ (nextAux_bnd c _ _ _ _ (pbnd_take x _ hx) hnx)

theorem evaluate_ok (c : Ctx n) (μ : Fin n → Val) (hμ : ∀ v, VOK c (μ v)) (v : Fin n)
    (allowed : Option (VSet n)) : VOK c (evaluate c μ v allowed).ret.1 := by
  intro x hx
  obtain ⟨-, h2, h3⟩ := evaluate_spec c μ v allowed
  cases he : (evaluate c μ v allowed).ret.2 with
  | none => rw [h2 he] at hx; cases hx
  | some w =>
    rw [(h3 w he).2.2.1] at hx
    exact prog_ok c v _ (fun y hy => (hμ w y hy).2) x hx


/-! ### Ranks and the potential -/

/-- The big-endian base-`B` number formed by the first `m` coordinates of `f`. -/
def enc (B : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => f 0 * B ^ m + enc B (fun i => f (i + 1)) m

theorem enc_lt (B : ℕ) : ∀ (m : ℕ) (f : ℕ → ℕ), (∀ i < m, f i < B) → enc B f m < B ^ m
  | 0, f, _ => by simp [enc]
  | m + 1, f, h => by
    have ih := enc_lt B m (fun i => f (i + 1)) (fun i hi => h (i + 1) (by omega))
    have h0 := h 0 (by omega)
    simp only [enc, pow_succ]
    nlinarith

theorem lexLE_succ {m : ℕ} {f g : ℕ → ℕ} :
    LexLE (m + 1) f g ↔ f 0 < g 0 ∨ (f 0 = g 0 ∧ LexLE m (fun i => f (i + 1)) (fun i => g (i + 1))) := by
  rw [lexLE_iff, lexLE_iff]
  constructor
  · intro h
    rcases Nat.lt_or_ge (f 0) (g 0) with h0 | h0
    · exact Or.inl h0
    have e0 : f 0 = g 0 := le_antisymm (h 0 (by omega) (by simp)) h0
    right
    refine ⟨e0, fun i hi hpre => h (i + 1) (by omega) fun j hj => ?_⟩
    rcases j with _ | j
    · exact e0
    · exact hpre j (by omega)
  · rintro (h0 | ⟨e0, h⟩) i hi hpre
    · rcases i with _ | i
      · exact h0.le
      · exact absurd (hpre 0 (by omega)) h0.ne
    · rcases i with _ | i
      · exact e0.le
      · exact h i (by omega) fun j hj => hpre (j + 1) (by omega)

theorem enc_lt_enc (B : ℕ) : ∀ (m : ℕ) (f g : ℕ → ℕ), (∀ i < m, f i < B) → (∀ i < m, g i < B) →
    ¬ LexLE m g f → enc B f m < enc B g m
  | 0, f, g, _, _, h => absurd (Or.inl fun i hi => by omega) h
  | m + 1, f, g, hf, hg, h => by
    rw [lexLE_succ] at h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    simp only [enc]
    rcases Nat.lt_or_ge (f 0) (g 0) with h0 | h0
    · have := enc_lt B m (fun i => f (i + 1)) (fun i hi => hf (i + 1) (by omega))
      have : (f 0 + 1) * B ^ m ≤ g 0 * B ^ m := Nat.mul_le_mul_right _ h0
      nlinarith
    · have e0 : f 0 = g 0 := le_antisymm (by omega) h0
      have := enc_lt_enc B m _ _ (fun i hi => hf (i + 1) (by omega))
        (fun i hi => hg (i + 1) (by omega)) (h2 e0.symm)
      rw [e0]
      omega

/-- The base of ranks. -/
def rbase (n : ℕ) : ℕ := ebound n + 1

/-- The rank of a value: its tuple as a base-`rbase` number, `⊤` above all. -/
def rank (c : Ctx n) : Val → ℕ
  | none => rbase n ^ (2 * c.height)
  | some x => enc (rbase n) (tup x) (2 * c.height)

theorem tup_lt_rbase (x : List (ℕ × ℕ)) (hx : PBnd n x) (i : ℕ) : tup x i < rbase n := by
  unfold rbase
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [tup_even]
    rcases getD_mem_or x l (0, 0) with h | h
    · have := (hx _ h).1; omega
    · rw [h]; simp
  · rw [tup_odd]
    rcases getD_mem_or x l (0, 0) with h | h
    · have := (hx _ h).2; omega
    · rw [h]; simp

theorem rank_le (c : Ctx n) (t : Val) (ht : VOK c t) : rank c t ≤ rbase n ^ (2 * c.height) := by
  cases t with
  | none => exact le_rfl
  | some x => exact (enc_lt _ _ _ fun i _ => tup_lt_rbase x (ht x rfl).2 i).le

theorem rank_lt (c : Ctx n) (a b : Val) (ha : VOK c a) (hb : VOK c b) (h : ¬ VLe c b a) :
    rank c a < rank c b := by
  cases a with
  | none => exact absurd (VLe.top c b) h
  | some x =>
    cases b with
    | none => exact enc_lt _ _ _ fun i _ => tup_lt_rbase x (ha x rfl).2 i
    | some y =>
      rw [vle_some_iff c (hb y rfl).1 (ha x rfl).1] at h
      exact enc_lt_enc _ _ _ _ (fun i _ => tup_lt_rbase x (ha x rfl).2 i)
        (fun i _ => tup_lt_rbase y (hb y rfl).2 i) h

/-- The potential of a labelling. -/
def pot (c : Ctx n) (μ : Fin n → Val) : ℕ := ∑ v, rank c (μ v)

theorem pot_le (c : Ctx n) (μ : Fin n → Val) (h : ∀ v, VOK c (μ v)) :
    pot c μ ≤ n * rbase n ^ (2 * c.height) := by
  unfold pot
  calc ∑ v, rank c (μ v) ≤ ∑ _v : Fin n, rbase n ^ (2 * c.height) :=
        Finset.sum_le_sum fun v _ => rank_le c _ (h v)
    _ = n * rbase n ^ (2 * c.height) := by simp

theorem pot_update (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (t : Val) (hv : VOK c (μ v))
    (ht : VOK c t) (hlt : ¬ VLe c t (μ v)) : pot c μ + 1 ≤ pot c (Function.update μ v t) := by
  unfold pot
  apply Nat.succ_le_of_lt
  apply Finset.sum_lt_sum
  · intro u _
    by_cases huv : u = v
    · subst huv; rw [Function.update_self]; exact (rank_lt c _ _ hv ht hlt).le
    · rw [Function.update_of_ne huv]
  · exact ⟨v, Finset.mem_univ _, by rw [Function.update_self]; exact rank_lt c _ _ hv ht hlt⟩

/-! ### The fuel invariant -/

/-- The queue has no duplicates and is tracked by `inq`, values are bounded, and every step so
    far has raised the potential. -/
structure FInv (c : Ctx n) (st : LState n) : Prop where
  nodup : st.queue.Nodup
  inq : ∀ v, st.inq v = true ↔ v ∈ st.queue
  ok : ∀ v, VOK c (st.measure v)
  pot : st.steps ≤ pot c st.measure

theorem requeue_nodup (st : LState n) (u : Fin n) (h1 : st.queue.Nodup)
    (h2 : ∀ v, st.inq v = true ↔ v ∈ st.queue) :
    (requeue st u).queue.Nodup ∧ ∀ v, (requeue st u).inq v = true ↔ v ∈ (requeue st u).queue := by
  unfold requeue
  split
  · exact ⟨h1, h2⟩
  · rename_i hu
    have hu' : u ∉ st.queue := fun h => hu ((h2 u).2 h)
    refine ⟨List.nodup_append.2 ⟨h1, by simp, fun a ha b hb hab => ?_⟩, fun v => ?_⟩
    · simp at hb; subst hb; subst hab; exact hu' ha
    · by_cases hvu : v = u
      · subst hvu; simp
      · simp [h2 v, hvu]

theorem foldl_requeue_nodup : ∀ (L : List (Fin n)) (st : LState n), st.queue.Nodup →
    (∀ v, st.inq v = true ↔ v ∈ st.queue) →
    (L.foldl requeue st).queue.Nodup ∧
      ∀ v, (L.foldl requeue st).inq v = true ↔ v ∈ (L.foldl requeue st).queue
  | [], st, h1, h2 => ⟨h1, h2⟩
  | u :: L, st, h1, h2 => by
    obtain ⟨a1, a2⟩ := requeue_nodup st u h1 h2
    exact foldl_requeue_nodup L _ a1 a2

theorem requeuePreds_nodup (c : Ctx n) (st : LState n) (s : Fin n) (h1 : st.queue.Nodup)
    (h2 : ∀ v, st.inq v = true ↔ v ∈ st.queue) :
    (requeuePreds c st s).ret.queue.Nodup ∧
      ∀ v, (requeuePreds c st s).ret.inq v = true ↔ v ∈ (requeuePreds c st s).ret.queue := by
  simp only [requeuePreds, ret_bind, ret_pure]
  exact foldl_requeue_nodup _ st h1 h2

/-- The part of the fuel invariant kept by acceleration, which also raises the potential by the
    number of raised vertices. -/
def QOK (c : Ctx n) (st : LState n) : Prop :=
  st.queue.Nodup ∧ (∀ v, st.inq v = true ↔ v ∈ st.queue) ∧ ∀ v, VOK c (st.measure v)

theorem raiseStep_fuel (c : Ctx n) (M : VSet n) (b : Fin n → Val) (hb : ∀ s, VOK c (b s))
    (acc : LState n × ℕ) (s : Fin n) (h : QOK c acc.1) :
    QOK c (raiseStep c M b acc s).ret.1 ∧
      pot c acc.1.measure + (raiseStep c M b acc s).ret.2 ≤
        pot c (raiseStep c M b acc s).ret.1.measure + acc.2 := by
  rw [raiseStep_ret]
  split
  · rename_i hc
    obtain ⟨-, hgt⟩ := hc
    set st1 : LState n := { acc.1 with measure := Function.update acc.1.measure s (b s) }
    obtain ⟨a1, a2, -, -, -, -⟩ := requeuePreds_spec c st1 s (fun v hv => (h.2.1 v).1 hv)
    obtain ⟨n1, n2⟩ := requeuePreds_nodup c st1 s h.1 h.2.1
    obtain ⟨m1, m2⟩ := requeue_nodup (requeuePreds c st1 s).ret s n1 n2
    have hm : (requeue (requeuePreds c st1 s).ret s).measure = Function.update acc.1.measure s (b s) := by
      unfold requeue; split <;> simp [a1, st1]
    refine ⟨⟨m1, m2, fun v => ?_⟩, ?_⟩
    · rw [hm]
      by_cases hvs : v = s
      · subst hvs; rw [Function.update_self]; exact hb v
      · rw [Function.update_of_ne hvs]; exact h.2.2 v
    · rw [hm]
      have := pot_update c acc.1.measure s (b s) (h.2.2 s) (hb s)
        (by rw [← cmpVal_gt_iff]; exact hgt)
      simp only
      omega
  · exact ⟨h, le_rfl⟩

theorem raise_fuel (c : Ctx n) (M : VSet n) (b : Fin n → Val) (hb : ∀ s, VOK c (b s))
    (st : LState n) (h : QOK c st) :
    QOK c (raise c M b st).ret.1 ∧ pot c st.measure + (raise c M b st).ret.2 ≤
      pot c (raise c M b st).ret.1.measure := by
  unfold raise
  rw [ret_foldlM]
  have key : ∀ (L : List (Fin n)) (acc : LState n × ℕ), QOK c acc.1 →
      pot c st.measure + acc.2 ≤ pot c acc.1.measure →
      QOK c (L.foldl (fun b' a => (raiseStep c M b b' a).ret) acc).1 ∧
        pot c st.measure + (L.foldl (fun b' a => (raiseStep c M b b' a).ret) acc).2 ≤
          pot c (L.foldl (fun b' a => (raiseStep c M b b' a).ret) acc).1.measure := by
    intro L
    induction L with
    | nil => intro acc h1 h2; exact ⟨h1, h2⟩
    | cons s L ih =>
      intro acc h1 h2
      obtain ⟨r1, r2⟩ := raiseStep_fuel c M b hb acc s h1
      rw [List.foldl_cons]
      exact ih _ r1 (by omega)
  exact key _ _ h (by simp)

theorem exitBound_ok (c : Ctx n) (μ : Fin n → Val) (hμ : ∀ v, VOK c (μ v))
    (ch : Fin n → Option (Fin n)) (M : VSet n) (s : Fin n) :
    VOK c (exitBound c μ ch M s).ret := by
  have key : ∀ (L : List (Fin n)) (acc : Val), VOK c acc →
      VOK c (L.foldl (fun b a => (exitStep c μ M s b a).ret) acc) := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons w L ih =>
      intro acc h
      apply ih
      dsimp only
      rw [exitStep_ret]
      split
      · exact h
      · split
        · exact prog_ok c s _ fun x hx => (hμ w x hx).2
        · exact h
  simp only [exitBound, ret_bind, ret_foldlM]
  exact key _ none (fun x hx => by cases hx)

theorem bfRound_ok (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (b : Fin n → Val)
    (hb : ∀ s, VOK c (b s)) : ∀ s, VOK c ((bfRound c ch M b).ret.1 s) := by
  have hedge : ∀ (s : Fin n) (L : List (Fin n)) (acc : (Fin n → Val) × Bool),
      (∀ u, VOK c (acc.1 u)) →
      ∀ u, VOK c ((L.foldl (fun b a => (bfEdge c M s b a).ret) acc).1 u) := by
    intro s L
    induction L with
    | nil => intro acc h; exact h
    | cons w L ih =>
      intro acc h
      apply ih
      intro u
      dsimp only
      rw [bfEdge_ret]
      split
      · split
        · by_cases hus : u = s
          · subst hus; simp only [Function.update_self]
            exact prog_ok c u _ fun x hx => (h w x hx).2
          · simp only [Function.update_of_ne hus]; exact h u
        · exact h u
      · exact h u
  have key : ∀ (L : List (Fin n)) (acc : (Fin n → Val) × Bool), (∀ u, VOK c (acc.1 u)) →
      ∀ u, VOK c ((L.foldl (fun b a => (bfStep c ch M b a).ret) acc).1 u) := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons s L ih =>
      intro acc h
      apply ih
      dsimp only
      rw [bfStep_ret]
      split
      · exact hedge s _ acc h
      · exact h
  simp only [bfRound, ret_foldlM]
  exact key _ _ hb

theorem bfLoop_ok (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) :
    ∀ (k : ℕ) (b : Fin n → Val), (∀ s, VOK c (b s)) → ∀ s, VOK c ((bfLoop c ch M k b).ret s)
  | 0, b, hb => by simpa [bfLoop] using hb
  | k + 1, b, hb => by
    simp only [bfLoop, ret_bind]
    split
    · exact bfLoop_ok c ch M k _ (bfRound_ok c ch M b hb)
    · exact bfRound_ok c ch M b hb

theorem accelerate_fuel (c : Ctx n) (st : LState n) (v : Fin n) (h : QOK c st) :
    QOK c (accelerate c st v).ret.1 ∧
      pot c st.measure + (accelerate c st v).ret.2 ≤ pot c (accelerate c st v).ret.1.measure := by
  simp only [accelerate, ret_bind]
  split
  · exact ⟨h, by simp⟩
  · simp only [ret_bind]
    split
    · exact ⟨h, by simp⟩
    · rename_i M hM
      simp only [accelRaise, ret_bind]
      set st' : LState n := { st with choice := (sccLoop c st.measure v (n + 1)
        (pumpTest c st.measure v n st.choice v).ret.1 none).ret.1 }
      have hb0 : ∀ s, VOK c (((List.finRange n).foldlM (initStep c st'.measure st'.choice M)
          (fun _ => none)).ret s) := by
        intro s
        rw [init_ret]
        split
        · exact exitBound_ok c _ h.2.2 _ _ _
        · intro x hx; cases hx
      exact raise_fuel c M _ (bfLoop_ok c _ M _ _ hb0) st' h

/-- The lifting loop keeps the fuel invariant, and does not run out of fuel when the fuel exceeds
    `|queue| + (n + 2) · (remaining budget)`. -/
theorem runLoop_fuel (c : Ctx n) (B : ℕ) :
    ∀ (k : ℕ) (st : LState n), FInv c st →
      FInv c (runLoop c B k st).ret.1 ∧
      ((st.queue.length + (n + 2) * (B - st.steps) < k ∨ (B ≤ st.steps ∧ 0 < k)) →
        (runLoop c B k st).ret.2.2 = false)
  | 0, st, h => ⟨h, fun hk => by omega⟩
  | k + 1, st, h => by
    rw [runLoop]
    split
    · exact ⟨h, fun _ => rfl⟩
    · rename_i hB
      split
      · exact ⟨h, fun _ => rfl⟩
      · rename_i v q hq
        have hnd := h.nodup
        rw [hq] at hnd
        have hvq : v ∉ q := (List.nodup_cons.1 hnd).1
        have hqnd : q.Nodup := (List.nodup_cons.1 hnd).2
        have hinq' : ∀ u, (Function.update st.inq v false) u = true ↔ u ∈ q := by
          intro u
          by_cases huv : u = v
          · subst huv; simp [hvq]
          · rw [Function.update_of_ne huv, h.inq u, hq]; simp [huv]
        simp only [ret_bind]
        split
        · rename_i hgt
          set e := (evaluate c st.measure v none).ret
          set st3 : LState n := ⟨Function.update st.measure v e.1,
            Function.update st.choice v e.2, q, Function.update st.inq v false, st.steps + 1⟩
          have hlt : ¬ VLe c e.1 (st.measure v) := by
            rw [← cmpVal_gt_iff]; simpa using hgt
          have hpot3 := pot_update c st.measure v e.1 (h.ok v)
            (evaluate_ok c st.measure h.ok v none) hlt
          have hq3 : QOK c st3 := ⟨hqnd, hinq', fun u => by
            by_cases huv : u = v
            · subst huv; simp only [st3, Function.update_self]
              exact evaluate_ok c st.measure h.ok u none
            · simp only [st3, Function.update_of_ne huv]; exact h.ok u⟩
          obtain ⟨n1, n2⟩ := requeuePreds_nodup c st3 v hq3.1 hq3.2.1
          obtain ⟨a1, -, a3, -, -, -⟩ := requeuePreds_spec c st3 v (fun u hu => (hq3.2.1 u).1 hu)
          have hq4 : QOK c (requeuePreds c st3 v).ret := ⟨n1, n2, by rw [a1]; exact hq3.2.2⟩
          obtain ⟨ac1, ac2⟩ := accelerate_fuel c _ v hq4
          rw [a1] at ac2
          have hF : FInv c { (accelerate c (requeuePreds c st3 v).ret v).ret.1 with
              steps := st.steps + 1 + (accelerate c (requeuePreds c st3 v).ret v).ret.2 } :=
            ⟨ac1.1, ac1.2.1, ac1.2.2, by
              have := h.pot
              simp only [st3] at ac2 hpot3 ⊢
              omega⟩
          obtain ⟨r1, r2⟩ := runLoop_fuel c B k _ hF
          refine ⟨r1, fun hk => r2 ?_⟩
          have hlen1 := queue_requeuePreds c st3 v
          have hlen2 := queue_accelerate c (requeuePreds c st3 v).ret v
          simp only [st3] at hlen1 hlen2 ⊢
          rw [hq] at hk
          simp only [List.length_cons] at hk
          by_cases hBs : B ≤ st.steps + 1 + (accelerate c (requeuePreds c st3 v).ret v).ret.2
          · right; exact ⟨hBs, by omega⟩
          · left
            have : (n + 2) * (B - st.steps) = (n + 2) * (B - (st.steps + 1 +
                (accelerate c (requeuePreds c st3 v).ret v).ret.2)) +
                (n + 2) * (1 + (accelerate c (requeuePreds c st3 v).ret v).ret.2) := by
              rw [← Nat.mul_add]; congr 1; omega
            rcases hk with hk | hk
            · nlinarith
            · omega
        · rename_i hgt
          have hF : FInv c ⟨st.measure, Function.update st.choice v
              (evaluate c st.measure v none).ret.2, q, Function.update st.inq v false,
              st.steps⟩ := ⟨hqnd, hinq', h.ok, h.pot⟩
          obtain ⟨r1, r2⟩ := runLoop_fuel c B k _ hF
          refine ⟨r1, fun hk => r2 ?_⟩
          rw [hq] at hk
          simp only [List.length_cons] at hk
          rcases hk with hk | hk
          · left; simp only; omega
          · omega


/-! ### Rounds and the outer loop -/

theorem queue_length_le (st : LState n) (h : st.queue.Nodup) : st.queue.length ≤ n := by
  have := h.length_le_card
  simpa using this

theorem run_no_oof (c : Ctx n) (rem fuel : ℕ) (hrem : rem ≤ n) (hfuel : (n + 2) ^ 2 ≤ fuel)
    (st : LState n) (h : FInv c st) : (run c rem fuel st).ret.2.2 = false := by
  apply (runLoop_fuel c _ fuel st h).2
  left
  have := queue_length_le st h.nodup
  rw [show st.steps + rem - st.steps = rem by omega]
  nlinarith

theorem mkLifter_height (G : PGame n) (alive : VSet n) (p : Bool) :
    (mkLifter G alive p).ret.1.height ≤ G.d + 1 := (mkLifter G alive p).ret.1.levels_le

theorem mkLifter_finv (G : PGame n) (alive : VSet n) (p : Bool) :
    FInv (mkLifter G alive p).ret.1 (mkLifter G alive p).ret.2 := by
  rw [mkLifter_ret]
  refine ⟨(List.nodup_finRange n).filter _, fun v => ?_, fun v x hx => ?_, Nat.zero_le _⟩
  · simp
  · simp only [Option.some.injEq] at hx
    subst hx
    refine ⟨by rw [leftmost_ret]; simp, ?_⟩
    rw [leftmost_ret]
    intro p hp
    simp only [List.nil_append] at hp
    rw [List.eq_of_mem_replicate hp]
    simp

theorem roundLoop_no_oof (G : PGame n) (rem fuel : ℕ) (A : VSet n) (hrem1 : 1 ≤ rem)
    (hrem : rem ≤ n) (hfuel : (n + 2) ^ 2 ≤ fuel) :
    ∀ (f : ℕ) (s : SState n) (l0 l1 : LState n), FInv (mkLifter G A false).ret.1 l0 →
      FInv (mkLifter G A true).ret.1 l1 →
      n * rbase n ^ (2 * (mkLifter G A false).ret.1.height) < l0.steps + f →
      ∀ s', (roundLoop G rem fuel (mkLifter G A false).ret.1 (mkLifter G A true).ret.1 f s l0
        l1).ret ≠ .oof s' := by
  set c0 := (mkLifter G A false).ret.1
  set c1 := (mkLifter G A true).ret.1
  intro f
  induction f with
  | zero =>
    intro s l0 l1 h0 _ hlt
    exfalso
    have := h0.pot
    have := pot_le c0 l0.measure h0.ok
    omega
  | succ f ih =>
    intro s l0 l1 h0 h1 hlt s'
    have hr0 := run_no_oof c0 rem fuel hrem hfuel l0 h0
    have hr1 := run_no_oof c1 rem fuel hrem hfuel l1 h1
    obtain ⟨hF0, -⟩ := runLoop_fuel c0 (l0.steps + rem) fuel l0 h0
    obtain ⟨hF1, -⟩ := runLoop_fuel c1 (l1.steps + rem) fuel l1 h1
    rw [roundLoop.eq_2]
    simp only [ret_bind]
    split
    · rename_i h'; exact absurd h' (by simp [hr0])
    · split
      · simp
      · rename_i hq0
        simp only [ret_bind]
        split
        · rename_i h'; exact absurd h' (by simp [hr1])
        · split
          · simp
          · simp only [ret_bind]
            split
            · have hb := runLoop_budget c0 (l0.steps + rem) fuel l0 (by simpa [run] using hq0)
                (by simpa [run] using hr0)
              exact ih _ _ _ hF0 hF1 (by
                have : l0.steps + rem ≤ (run c0 rem fuel l0).ret.1.steps := hb
                omega) s'
            · simp

/-- With fuel at least `fuelBound G`, no restart runs out of fuel, so the solver returns
    winners (headline). -/
theorem solveTerminates (G : PGame n) (fuel : ℕ) : SolveTerminates G fuel := by
  intro hfuel
  have hpow : (n + 2) ^ 2 ≤ (n + 2) ^ (4 * G.d + 6) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hf2 : (n + 2) ^ 2 ≤ fuel := hpow.trans hfuel
  apply outerFuelSuffices G fuel
  intro s s'
  by_cases hc : s.alive.count = 0
  · -- nothing alive: the first round completes immediately
    have hdead : ∀ v, s.alive v = false := fun v => count_eq_zero _ hc v
    have hq : (mkLifter G s.alive false).ret.2.queue = [] := by
      rw [mkLifter_ret]
      simp [hdead]
    obtain ⟨k, hk⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
      have : 4 ≤ (n + 2) ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega⟩
    rw [hc, hk, roundLoop.eq_2]
    simp only [ret_bind]
    have hrun : (run (mkLifter G s.alive false).ret.1 0 (k + 1)
        (mkLifter G s.alive false).ret.2).ret.2 = (true, false) := by
      simp only [run, Nat.add_zero]
      rw [runLoop]
      simp [hq]
    rw [hrun]
    simp
  · have hrem1 : 1 ≤ s.alive.count := by omega
    have hremn : s.alive.count ≤ n := count_le _
    apply roundLoop_no_oof G _ fuel s.alive hrem1 hremn hf2 fuel s _ _
      (mkLifter_finv G s.alive false) (mkLifter_finv G s.alive true)
    simp only [show (mkLifter G s.alive false).ret.2.steps = 0 from rfl, zero_add]
    have hh := mkLifter_height G s.alive false
    have hb : rbase n ≤ (n + 2) ^ 2 := by unfold rbase ebound; nlinarith
    calc n * rbase n ^ (2 * (mkLifter G s.alive false).ret.1.height)
        ≤ n * ((n + 2) ^ 2) ^ (2 * (G.d + 1)) := by
          apply Nat.mul_le_mul_left
          calc rbase n ^ (2 * (mkLifter G s.alive false).ret.1.height)
              ≤ ((n + 2) ^ 2) ^ (2 * (mkLifter G s.alive false).ret.1.height) :=
                Nat.pow_le_pow_left hb _
            _ ≤ ((n + 2) ^ 2) ^ (2 * (G.d + 1)) :=
                Nat.pow_le_pow_right (by positivity) (by omega)
      _ < (n + 2) * (n + 2) ^ (4 * G.d + 4) := by
          rw [← pow_mul, show 2 * (2 * (G.d + 1)) = 4 * G.d + 4 by ring]
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ ≤ (n + 2) ^ (4 * G.d + 6) := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ fuel := hfuel

end MercLib.ParityGame.TwoSidedCost

end TwoSidedCostCorrectFuelProofs
