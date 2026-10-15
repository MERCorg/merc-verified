module

public import MercLib.TwoSided.Proofs.TwoSidedCostCorrect_Tree_Proofs

@[expose] public section TwoSidedCostCorrectLiftProofs

namespace MercLib.ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The lifting loop of `ParityGame.TwoSidedCost` preserves an invariant (`LInv`): recorded choices
are alive successors, every alive vertex off the queue is consistent (its evaluation is not
above its value), and every value is below a fixed bound `ν` (`Bound`: a pre-fixpoint of the
lifting operator whose progress edges have even cycles, e.g. the chain-tree measure of the
winning region). Acceleration keeps the values below `ν`: the acceleration set has only
odd-maximum kept cycles, so from every member with a proper bound the bound's edges reach an exit
within `|M|` steps, and `|M|` Bellman–Ford rounds (or an earlier stable round) bring the member
below `ν`. -/

variable {n : ℕ}

/-! ### `evaluate` -/

/-- Is `w` allowed by the optional restriction? -/
def allowedAt (allowed : Option (VSet n)) (w : Fin n) : Bool := (allowed.map fun a => a w).getD true

theorem evalStep_ret (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n))
    (acc : Option (Val × Fin n)) (w : Fin n) :
    (evalStep c μ v allowed acc w).ret = if allowedAt allowed w = true then
      (match acc with
        | none => some ((prog c v (μ w)).ret, w)
        | some (cur, cw) =>
          if (if c.mine v = true then (cmpVal c (prog c v (μ w)).ret cur).ret == .lt
            else (cmpVal c (prog c v (μ w)).ret cur).ret != .lt) = true
          then some ((prog c v (μ w)).ret, w) else some (cur, cw))
      else acc := by
  unfold evalStep allowedAt
  simp only [ret_bind]
  split
  · simp only [ret_bind]
    split <;> simp_all
  · simp

/-- The fold invariant of `evaluate` over a prefix `L` of the successors. -/
def EvalInv (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n))
    (L : List (Fin n)) (acc : Option (Val × Fin n)) : Prop :=
  (acc = none ↔ ∀ w ∈ L, allowedAt allowed w = false) ∧
  ∀ val w, acc = some (val, w) → w ∈ L ∧ allowedAt allowed w = true ∧
    val = (prog c v (μ w)).ret ∧
    (c.mine v = true → ∀ w' ∈ L, allowedAt allowed w' = true → VLe c val (prog c v (μ w')).ret) ∧
    (c.mine v = false → ∀ w' ∈ L, allowedAt allowed w' = true → VLe c (prog c v (μ w')).ret val)

theorem evalInv_fold (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n)) :
    ∀ (L : List (Fin n)) (P : List (Fin n)) (acc : Option (Val × Fin n)),
      EvalInv c μ v allowed P acc →
      EvalInv c μ v allowed (P ++ L) (L.foldl (fun b a => (evalStep c μ v allowed b a).ret) acc)
  | [], P, acc, h => by simpa using h
  | w :: L, P, acc, h => by
    rw [List.foldl_cons, show P ++ w :: L = (P ++ [w]) ++ L by simp]
    apply evalInv_fold c μ v allowed L
    rw [evalStep_ret]
    obtain ⟨h1, h2⟩ := h
    split
    · rename_i hw
      cases acc with
      | none =>
        refine ⟨by simp [hw], fun val w' he => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hP : ∀ w'' ∈ P, allowedAt allowed w'' = false := h1.1 rfl
        refine ⟨by simp, hw, rfl, fun _ w'' hw'' ha => ?_, fun _ w'' hw'' ha => ?_⟩
        · rcases List.mem_append.1 hw'' with hw'' | hw''
          · rw [hP w'' hw''] at ha; cases ha
          · simp at hw''; subst hw''; exact VLe.refl _ _
        · rcases List.mem_append.1 hw'' with hw'' | hw''
          · rw [hP w'' hw''] at ha; cases ha
          · simp at hw''; subst hw''; exact VLe.refl _ _
      | some p =>
        obtain ⟨cur, cw⟩ := p
        obtain ⟨hcw, hacw, hcur, hmin, hmax⟩ := h2 cur cw rfl
        dsimp only
        by_cases hb : (if c.mine v = true then (cmpVal c (prog c v (μ w)).ret cur).ret == .lt
            else (cmpVal c (prog c v (μ w)).ret cur).ret != .lt) = true
        · rw [ite_eq_left hb]
          refine ⟨by simp [hw], fun val w' he => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨by simp, hw, rfl, fun hm w'' hw'' ha => ?_, fun hm w'' hw'' ha => ?_⟩
          · rw [ite_eq_left hm, beq_iff_eq, cmpVal_lt_iff] at hb
            rcases List.mem_append.1 hw'' with hw'' | hw''
            · have := hmin hm w'' hw'' ha
              rcases VLe.total c (prog c v (μ w)).ret cur with h' | h'
              · exact h'.trans this
              · exact absurd h' hb
            · simp at hw''; subst hw''; exact VLe.refl _ _
          · rw [ite_eq_right (by simp [hm]), bne_iff_ne, ne_eq, cmpVal_lt_iff, not_not] at hb
            rcases List.mem_append.1 hw'' with hw'' | hw''
            · exact (hmax hm w'' hw'' ha).trans hb
            · simp at hw''; subst hw''; exact VLe.refl _ _
        · rw [ite_eq_right hb]
          refine ⟨by simp [hw], fun val w' he => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨by simp [hcw], hacw, hcur, fun hm w'' hw'' ha => ?_, fun hm w'' hw'' ha => ?_⟩
          · rw [ite_eq_left hm, beq_iff_eq, cmpVal_lt_iff, not_not] at hb
            rcases List.mem_append.1 hw'' with hw'' | hw''
            · exact hmin hm w'' hw'' ha
            · simp at hw''; subst hw''; exact hb
          · rw [ite_eq_right (by simp [hm]), bne_iff_ne, ne_eq, not_not, cmpVal_lt_iff] at hb
            rcases List.mem_append.1 hw'' with hw'' | hw''
            · exact hmax hm w'' hw'' ha
            · simp at hw''; subst hw''
              exact (VLe.total c _ _).resolve_left hb
    · rename_i hw
      refine ⟨⟨fun he w' hw' => ?_, fun hall => h1.2 fun w' hw' => hall w' (by simp [hw'])⟩,
        fun val w' he => ?_⟩
      · rcases List.mem_append.1 hw' with hw' | hw'
        · exact h1.1 he w' hw'
        · simp at hw'; subst hw'; simpa using hw
      · obtain ⟨h3, h4, h5, h6, h7⟩ := h2 val w' he
        have hw' : ∀ w'' ∈ P ++ [w], allowedAt allowed w'' = true → w'' ∈ P := by
          intro w'' hw'' ha
          rcases List.mem_append.1 hw'' with hw'' | hw''
          · exact hw''
          · simp at hw''; subst hw''; simp [ha] at hw
        exact ⟨by simp [h3], h4, h5, fun hm w'' hw'' ha => h6 hm w'' (hw' w'' hw'' ha) ha,
          fun hm w'' hw'' ha => h7 hm w'' (hw' w'' hw'' ha) ha⟩

/-- The semantics of `evaluate`: `none` iff no allowed alive successor; otherwise the result is
    `prog` towards the chosen allowed alive successor, minimal for the lifting player's vertices
    and maximal for the opponent's. -/
theorem evaluate_spec (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n)) :
    ((evaluate c μ v allowed).ret.2 = none ↔
      ∀ w ∈ (succT c v).ret, allowedAt allowed w = false) ∧
    ((evaluate c μ v allowed).ret.2 = none → (evaluate c μ v allowed).ret.1 = none) ∧
    ∀ w, (evaluate c μ v allowed).ret.2 = some w → w ∈ (succT c v).ret ∧
      allowedAt allowed w = true ∧ (evaluate c μ v allowed).ret.1 = (prog c v (μ w)).ret ∧
      (c.mine v = true → ∀ w' ∈ (succT c v).ret, allowedAt allowed w' = true →
        VLe c (evaluate c μ v allowed).ret.1 (prog c v (μ w')).ret) ∧
      (c.mine v = false → ∀ w' ∈ (succT c v).ret, allowedAt allowed w' = true →
        VLe c (prog c v (μ w')).ret (evaluate c μ v allowed).ret.1) := by
  have hinv := evalInv_fold c μ v allowed (succT c v).ret [] none ⟨by simp, by simp⟩
  simp only [List.nil_append] at hinv
  have hev : (evaluate c μ v allowed).ret = match ((succT c v).ret.foldl
      (fun b a => (evalStep c μ v allowed b a).ret) none) with
      | some (val, w) => (val, some w)
      | none => (none, none) := by
    simp only [evaluate, ret_bind, ret_foldlM]
    rfl
  rw [hev]
  obtain ⟨h1, h2⟩ := hinv
  generalize ((succT c v).ret.foldl (fun b a => (evalStep c μ v allowed b a).ret) none) = r at h1 h2
  cases r with
  | none => exact ⟨by simpa using h1, fun _ => rfl, fun w hw => by simp at hw⟩
  | some p =>
    obtain ⟨val, w⟩ := p
    refine ⟨by simpa using h1, fun h => by simp at h, fun w' hw' => ?_⟩
    simp only [Option.some.injEq] at hw'
    subst hw'
    exact h2 val w rfl

/-- `evaluate` only reads the values of the alive successors. -/
theorem evaluate_congr (c : Ctx n) (μ μ' : Fin n → Val) (v : Fin n) (allowed : Option (VSet n))
    (h : ∀ w ∈ (succT c v).ret, μ w = μ' w) :
    (evaluate c μ v allowed).ret = (evaluate c μ' v allowed).ret := by
  have key : ∀ (L : List (Fin n)), (∀ w ∈ L, μ w = μ' w) → ∀ acc,
      L.foldl (fun b a => (evalStep c μ v allowed b a).ret) acc =
        L.foldl (fun b a => (evalStep c μ' v allowed b a).ret) acc := by
    intro L
    induction L with
    | nil => intro _ _; rfl
    | cons w L ih =>
      intro hL acc
      simp only [List.foldl_cons]
      rw [evalStep_ret, evalStep_ret, hL w (by simp)]
      exact ih (fun w' hw' => hL w' (by simp [hw'])) _
  simp only [evaluate, ret_bind, ret_foldlM, ret_pure]
  rw [key _ h]

theorem evaluate_len (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (allowed : Option (VSet n)) :
    ∀ x, (evaluate c μ v allowed).ret.1 = some x → x.length = c.height := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := evaluate_spec c μ v allowed
  cases hw : (evaluate c μ v allowed).ret.2 with
  | none => rw [h2 hw] at hx; cases hx
  | some w =>
    rw [(h3 w hw).2.2.1] at hx
    exact prog_len c v _ x hx

/-! ### The bound and the invariant -/

/-- `ν` is a bound for lifting in the context `c`, with progress edges `E`: values have the
    right length, proper values sit on alive vertices, every vertex with a proper bound has an
    `E`-successor (all alive successors for the opponent's vertices), `prog` along an `E`-edge
    stays below the bound, and every `E`-cycle has an even maximum. -/
structure Bound (c : Ctx n) (ν : Fin n → Val) (E : Fin n → Fin n → Prop) : Prop where
  len : ∀ v x, ν v = some x → x.length = c.height
  alive : ∀ v, ν v ≠ none → c.alive v = true
  edge : ∀ v w, E v w → w ∈ c.G.succ v ∧ c.alive w = true ∧ ν v ≠ none ∧ ν w ≠ none
  good : ∀ v w, E v w → ∀ t : Val, (∀ x, t = some x → x.length = c.height) → VLe c t (ν w) →
    VLe c (prog c v t).ret (ν v)
  ex : ∀ v, ν v ≠ none → ∃ w, E v w
  theirs : ∀ v w, ν v ≠ none → c.mine v = false → w ∈ c.G.succ v → c.alive w = true → E v w
  cyc : ∀ (k : ℕ) (f : ℕ → Fin n), 0 < k → f k = f 0 → (∀ i < k, E (f i) (f (i + 1))) →
    ∀ i < k, (∀ j < k, c.prio (f j) ≤ c.prio (f i)) → c.prio (f i) % 2 = 0

/-- Recorded choices are alive successors. -/
def ChInv (c : Ctx n) (ch : Fin n → Option (Fin n)) : Prop :=
  ∀ x y, ch x = some y → y ∈ c.G.succ x ∧ c.alive y = true

/-- The lifting invariant for the bound `ν`. -/
structure LInv (c : Ctx n) (ν : Fin n → Val) (st : LState n) : Prop where
  choice : ChInv c st.choice
  queue : ∀ v, c.alive v = true → v ∉ st.queue →
    VLe c (evaluate c st.measure v none).ret.1 (st.measure v)
  inq : ∀ v, st.inq v = true → v ∈ st.queue
  le : ∀ v, VLe c (st.measure v) (ν v)
  len : ∀ v x, st.measure v = some x → x.length = c.height

theorem allowedAt_none (w : Fin n) : allowedAt (none : Option (VSet n)) w = true := rfl

/-- The lifted value of a vertex stays below the bound. -/
theorem evaluate_le_bound {c : Ctx n} {ν : Fin n → Val} {E : Fin n → Fin n → Prop}
    (hB : Bound c ν E) {μ : Fin n → Val} (hle : ∀ v, VLe c (μ v) (ν v))
    (hlen : ∀ v x, μ v = some x → x.length = c.height) (v : Fin n) :
    VLe c (evaluate c μ v none).ret.1 (ν v) := by
  by_cases hv : ν v = none
  · rw [hv]; exact VLe.top _ _
  obtain ⟨w, hw⟩ := hB.ex v hv
  obtain ⟨hwsucc, hwalive, -, -⟩ := hB.edge v w hw
  have hws : w ∈ (succT c v).ret := (mem_succT c v w).2 ⟨hwsucc, hwalive⟩
  obtain ⟨h1, -, h3⟩ := evaluate_spec c μ v none
  cases he : (evaluate c μ v none).ret.2 with
  | none => exact absurd ((h1.1 he) w hws) (by simp [allowedAt_none])
  | some w' =>
    obtain ⟨hw's, -, hval, hmin, -⟩ := h3 w' he
    cases hm : c.mine v with
    | true =>
      exact (hmin hm w hws (allowedAt_none w)).trans
        (hB.good v w hw _ (hlen w) (hle w))
    | false =>
      obtain ⟨hs, ha⟩ := (mem_succT c v w').1 hw's
      rw [hval]
      exact hB.good v w' (hB.theirs v w' hv hm hs ha) _ (hlen w') (hle w')

/-! ### Re-queueing -/

theorem requeue_spec (st : LState n) (u : Fin n) (hinq : ∀ v, st.inq v = true → v ∈ st.queue) :
    (requeue st u).measure = st.measure ∧ (requeue st u).choice = st.choice ∧
    (requeue st u).steps = st.steps ∧
    (∀ x ∈ st.queue, x ∈ (requeue st u).queue) ∧ u ∈ (requeue st u).queue ∧
    (∀ v, (requeue st u).inq v = true → v ∈ (requeue st u).queue) := by
  unfold requeue
  split
  · rename_i h
    exact ⟨rfl, rfl, rfl, fun x hx => hx, hinq u h, hinq⟩
  · refine ⟨rfl, rfl, rfl, fun x hx => by simp [hx], by simp, fun v hv => ?_⟩
    by_cases hvu : v = u
    · subst hvu; simp
    · simp only [Function.update_of_ne hvu] at hv
      simp [hinq v hv]

theorem foldl_requeue_spec : ∀ (L : List (Fin n)) (st : LState n),
    (∀ v, st.inq v = true → v ∈ st.queue) →
    (L.foldl requeue st).measure = st.measure ∧ (L.foldl requeue st).choice = st.choice ∧
    (L.foldl requeue st).steps = st.steps ∧
    (∀ x ∈ st.queue, x ∈ (L.foldl requeue st).queue) ∧ (∀ u ∈ L, u ∈ (L.foldl requeue st).queue) ∧
    (∀ v, (L.foldl requeue st).inq v = true → v ∈ (L.foldl requeue st).queue)
  | [], st, h => ⟨rfl, rfl, rfl, fun _ hx => hx, by simp, h⟩
  | u :: L, st, h => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := requeue_spec st u h
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := foldl_requeue_spec L (requeue st u) a6
    simp only [List.foldl_cons]
    refine ⟨b1.trans a1, b2.trans a2, b3.trans a3, fun x hx => b4 x (a4 x hx), fun x hx => ?_, b6⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact b4 x a5
    · exact b5 x hx

theorem requeuePreds_spec (c : Ctx n) (st : LState n) (s : Fin n)
    (hinq : ∀ v, st.inq v = true → v ∈ st.queue) :
    (requeuePreds c st s).ret.measure = st.measure ∧ (requeuePreds c st s).ret.choice = st.choice ∧
    (requeuePreds c st s).ret.steps = st.steps ∧
    (∀ x ∈ st.queue, x ∈ (requeuePreds c st s).ret.queue) ∧
    (∀ u, c.alive u = true → s ∈ c.G.succ u → u ∈ (requeuePreds c st s).ret.queue) ∧
    (∀ v, (requeuePreds c st s).ret.inq v = true → v ∈ (requeuePreds c st s).ret.queue) := by
  simp only [requeuePreds, ret_bind, ret_pure]
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := foldl_requeue_spec (predT c s).ret st hinq
  exact ⟨b1, b2, b3, b4, fun u ha hs => b5 u ((mem_predT c s u).2 ⟨ha, hs⟩), b6⟩

/-- Changing the value of `s` and re-queueing its predecessors keeps every other alive vertex
    off the queue consistent. -/
theorem update_consistent (c : Ctx n) (st : LState n) (s : Fin n) (x : Val)
    (hq : ∀ v, c.alive v = true → v ∉ st.queue → v ≠ s →
      VLe c (evaluate c st.measure v none).ret.1 (st.measure v))
    (hinq : ∀ v, st.inq v = true → v ∈ st.queue) :
    ∀ u, c.alive u = true → u ∉ (requeuePreds c { st with measure := Function.update st.measure s x } s).ret.queue →
      u ≠ s →
      VLe c (evaluate c (Function.update st.measure s x) u none).ret.1
        (Function.update st.measure s x u) := by
  intro u hu hnq hus
  obtain ⟨-, -, -, h4, h5, -⟩ := requeuePreds_spec c { st with measure := Function.update st.measure s x } s hinq
  have hsu : s ∉ c.G.succ u := fun h => hnq (h5 u hu h)
  rw [evaluate_congr c (Function.update st.measure s x) st.measure u none (fun w hw => by
    have : w ≠ s := fun h => hsu (h ▸ ((mem_succT c u w).1 hw).1)
    rw [Function.update_of_ne this]), Function.update_of_ne hus]
  exact hq u hu (fun h => hnq (h4 u h)) hus


/-! ### Choices during acceleration -/

/-- `ch'` keeps every choice recorded in `ch`. -/
def ChExt (ch ch' : Fin n → Option (Fin n)) : Prop := ∀ x y, ch x = some y → ch' x = some y

theorem ChExt.refl (ch : Fin n → Option (Fin n)) : ChExt ch ch := fun _ _ h => h

theorem ChExt.trans {ch ch' ch'' : Fin n → Option (Fin n)} (h1 : ChExt ch ch') (h2 : ChExt ch' ch'') :
    ChExt ch ch'' := fun x y h => h2 x y (h1 x y h)

theorem currentChoice_spec (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (x : Fin n)
    (hch : ChInv c ch) :
    ChInv c (currentChoice c μ ch x).ret.1 ∧ ChExt ch (currentChoice c μ ch x).ret.1 ∧
      ∀ y, (currentChoice c μ ch x).ret.2 = some y → (currentChoice c μ ch x).ret.1 x = some y := by
  unfold currentChoice
  simp only [ret_bind]
  split
  · rename_i w hw
    exact ⟨hch, ChExt.refl _, fun y hy => by simp at hy; subst hy; simpa using hw⟩
  · rename_i hx
    simp only [ret_bind, ret_pure]
    obtain ⟨-, -, h3⟩ := evaluate_spec c μ x none
    refine ⟨fun x' y hy => ?_, fun x' y hy => ?_, fun y hy => by simp [hy]⟩
    · by_cases hxx : x' = x
      · subst hxx
        rw [Function.update_self] at hy
        exact (mem_succT c x' y).1 (h3 y hy).1
      · rw [Function.update_of_ne hxx] at hy
        exact hch x' y hy
    · by_cases hxx : x' = x
      · subst hxx; rw [hx] at hy; cases hy
      · rw [Function.update_of_ne hxx]; exact hy

theorem pumpTest_spec (c : Ctx n) (μ : Fin n → Val) (v : Fin n) :
    ∀ (k : ℕ) (ch : Fin n → Option (Fin n)) (x : Fin n), ChInv c ch →
      ChInv c (pumpTest c μ v k ch x).ret.1 ∧ ChExt ch (pumpTest c μ v k ch x).ret.1
  | 0, ch, x, h => ⟨h, ChExt.refl _⟩
  | k + 1, ch, x, h => by
    obtain ⟨h1, h2, -⟩ := currentChoice_spec c μ ch x h
    rw [pumpTest]
    simp only [ret_bind]
    split
    · exact ⟨h1, h2⟩
    · split
      · exact ⟨h1, h2⟩
      · obtain ⟨h3, h4⟩ := pumpTest_spec c μ v k _ _ h1
        exact ⟨h3, h2.trans h4⟩

theorem pumpTest_self (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (k : ℕ)
    (ch : Fin n → Option (Fin n)) (hch : ChInv c ch) :
    (pumpTest c μ v k ch v).ret.2 = true → (pumpTest c μ v k ch v).ret.1 v ≠ none := by
  cases k with
  | zero => simp [pumpTest]
  | succ k =>
    obtain ⟨h1, -, h3⟩ := currentChoice_spec c μ ch v hch
    rw [pumpTest]
    simp only [ret_bind]
    split
    · simp
    · rename_i y hy
      have hv := h3 y hy
      split
      · intro _; simp [hv]
      · intro _
        have := (pumpTest_spec c μ v k _ y h1).2 v y hv
        simp [this]

theorem keptT_ret (c : Ctx n) (ch : Fin n → Option (Fin n)) (u : Fin n) :
    (keptT c ch u).ret = if c.mine u = true then (succT c u).ret else (ch u).toList := by
  unfold keptT
  split <;> simp_all

theorem mem_keptT (c : Ctx n) (ch : Fin n → Option (Fin n)) (u w : Fin n) :
    w ∈ (keptT c ch u).ret ↔
      (c.mine u = true ∧ w ∈ c.G.succ u ∧ c.alive w = true) ∨ (c.mine u = false ∧ ch u = some w) := by
  rw [keptT_ret]
  cases hm : c.mine u
  · simp [Option.mem_toList]
  · simp [mem_succT]

theorem fwdNbrs_state (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (x : Fin n)
    (hch : ChInv c ch) :
    ChInv c (fwdNbrs c μ ch x).ret.1 ∧ ChExt ch (fwdNbrs c μ ch x).ret.1 := by
  simp only [fwdNbrs]
  split
  · exact ⟨hch, ChExt.refl _⟩
  · simp only [ret_bind, ret_pure]
    obtain ⟨h1, h2, -⟩ := currentChoice_spec c μ ch x hch
    exact ⟨h1, h2⟩

theorem filterT_ret {α : Type} (p : α → TimeM ℕ Bool) :
    ∀ xs : List α, (filterT p xs).ret = xs.filter fun x => (p x).ret
  | [] => rfl
  | x :: xs => by
    simp only [filterT, ret_bind, ret_pure, filterT_ret p xs, List.filter_cons]

theorem keptEdge_ret (c : Ctx n) (ch : Fin n → Option (Fin n)) (fwd : VSet n) (x u : Fin n) :
    (keptEdge c ch fwd x u).ret = (fwd u && (keptT c ch u).ret.contains x) := by
  unfold keptEdge
  split <;> simp_all

/-- The vertices found by the backward search have a kept edge (or are the start). -/
theorem bw_kept (c : Ctx n) (ch : Fin n → Option (Fin n)) (fwd : VSet n) (v : Fin n) :
    ∀ u, (explore (bwdNbrs c ch fwd) (fun _ => true) (n + 1) () (VSet.single v) [v]).ret.2 u = true →
      u = v ∨ ∃ x, x ∈ (keptT c ch u).ret := by
  apply explore_sound
  · intro s x _ y hy _
    right
    refine ⟨x, ?_⟩
    simp only [bwdNbrs, ret_bind, ret_pure, filterT_ret, List.mem_filter, keptEdge_ret,
      Bool.and_eq_true, List.contains_iff_mem] at hy
    exact hy.2.2
  · intro z hz; left; simpa [VSet.single] using hz
  · intro z hz; left; simpa using hz

/-- Every kept cycle inside `M` has an odd maximum. -/
def KeptOdd (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) : Prop :=
  ∀ (k : ℕ) (f : ℕ → Fin n), 0 < k → f k = f 0 → (∀ i < k, M (f i) = true) →
    (∀ i < k, f (i + 1) ∈ (keptT c ch (f i)).ret) →
    ∀ i < k, (∀ j < k, c.prio (f j) ≤ c.prio (f i)) → c.prio (f i) % 2 = 1

theorem ecmStep_mono (c : Ctx n) (ch : Fin n → Option (Fin n)) (M bad : VSet n) (u x : Fin n)
    (h : bad x = true) : (ecmStep c ch M bad u).ret x = true := by
  unfold ecmStep
  simp only [ret_bind]
  split
  · simp only [ret_bind, ret_pure]
    split
    · by_cases hxu : x = u
      · subst hxu; simp
      · rw [Function.update_of_ne hxu]; exact h
    · exact h
  · exact h

/-- If `u` is an even member of `M` on a kept cycle inside `{w ∈ M | prio w ≤ prio u}`, the step
    for `u` marks it. -/
theorem ecmStep_marks (c : Ctx n) (ch : Fin n → Option (Fin n)) (M bad : VSet n) (u : Fin n)
    (hu : M u = true) (hev : c.prio u % 2 = 0)
    (hcyc : ∃ y ∈ (keptT c ch u).ret, M y = true ∧ c.prio y ≤ c.prio u ∧
      Relation.ReflTransGen (fun a b => b ∈ (keptT c ch a).ret ∧ M b = true ∧ c.prio b ≤ c.prio u)
        y u) :
    (ecmStep c ch M bad u).ret u = true := by
  unfold ecmStep
  simp only [ret_bind]
  rw [ite_eq_left (by simp [hu, hev])]
  simp only [ret_bind, ret_pure]
  set S : VSet n := materialize fun w => M w && decide (c.prio w ≤ c.prio u) with hS
  obtain ⟨new, e1, e2, e3, e4⟩ := pushNew_spec S (keptT c ch u).ret VSet.empty []
  have hN : ∀ s x, (keptNbrs c ch s x).ret.2 = (keptT c ch x).ret := fun _ _ => rfl
  have hcl := explore_closed (keptNbrs c ch) S (fun x => (keptT c ch x).ret) hN (n + 1) ()
    (pushNew S (keptT c ch u).ret VSet.empty []).1 (pushNew S (keptT c ch u).ret VSet.empty []).2
    (by have := Finset.card_le_univ (finished (pushNew S (keptT c ch u).ret VSet.empty []).1
          (pushNew S (keptT c ch u).ret VSet.empty []).2); simp at this ⊢; omega)
    (by rw [e1]; simpa using e2)
    (by
      intro z hz
      rw [e1, List.append_nil] at hz
      obtain ⟨h1, h2, -⟩ := (e3 z).1 hz
      exact (e4 z).2 (Or.inr ⟨h1, h2⟩))
    (by
      intro x hx hxs
      exfalso
      rcases (e4 x).1 hx with h | ⟨h1, h2⟩
      · simp [VSet.empty] at h
      · exact hxs (by rw [e1, List.append_nil]; exact (e3 x).2 ⟨h1, h2, rfl⟩))
  obtain ⟨y, hy, hyM, hyp, hpath⟩ := hcyc
  have hyS : S y = true := by simp [hS, hyM, hyp]
  have hyseen : (explore (keptNbrs c ch) S (n + 1) () (pushNew S (keptT c ch u).ret VSet.empty []).1
      (pushNew S (keptT c ch u).ret VSet.empty []).2).ret.2 y = true :=
    explore_mono _ _ _ _ _ _ y ((e4 y).2 (Or.inr ⟨hy, hyS⟩))
  have : (explore (keptNbrs c ch) S (n + 1) () (pushNew S (keptT c ch u).ret VSet.empty []).1
      (pushNew S (keptT c ch u).ret VSet.empty []).2).ret.2 u = true := by
    have key : ∀ z, Relation.ReflTransGen
        (fun a b => b ∈ (keptT c ch a).ret ∧ M b = true ∧ c.prio b ≤ c.prio u) y z →
        (explore (keptNbrs c ch) S (n + 1) () (pushNew S (keptT c ch u).ret VSet.empty []).1
          (pushNew S (keptT c ch u).ret VSet.empty []).2).ret.2 z = true := by
      intro z hz
      induction hz with
      | refl => exact hyseen
      | tail _ hst ih =>
        exact hcl _ ih _ hst.1 (by simp [hS, hst.2.1, hst.2.2])
    exact key u hpath
  simp [this]

theorem ecm_fold_mono (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) :
    ∀ (L : List (Fin n)) (bad : VSet n) (x : Fin n), bad x = true →
      (L.foldl (fun b a => (ecmStep c ch M b a).ret) bad) x = true
  | [], _, _, h => h
  | u :: L, bad, x, h => ecm_fold_mono c ch M L _ x (ecmStep_mono c ch M bad u x h)

theorem ecm_fold_marks (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (u : Fin n)
    (hu : M u = true) (hev : c.prio u % 2 = 0)
    (hcyc : ∃ y ∈ (keptT c ch u).ret, M y = true ∧ c.prio y ≤ c.prio u ∧
      Relation.ReflTransGen (fun a b => b ∈ (keptT c ch a).ret ∧ M b = true ∧ c.prio b ≤ c.prio u)
        y u) :
    ∀ (L : List (Fin n)) (bad : VSet n), u ∈ L →
      (L.foldl (fun b a => (ecmStep c ch M b a).ret) bad) u = true
  | [], _, h => by simp at h
  | x :: L, bad, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact ecm_fold_mono c ch M L _ _ (ecmStep_marks c ch M bad _ hu hev hcyc)
    · exact ecm_fold_marks c ch M u hu hev hcyc L _ h

theorem count_eq_zero (S : VSet n) (h : S.count = 0) (u : Fin n) : S u = false := by
  unfold VSet.count at h
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  simpa using h u (List.mem_finRange u)

/-- No even cycle maxima: every kept cycle inside `M` has an odd maximum. -/
theorem keptOdd_of_ecm (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (h : (evenCycleMaxima c ch M).ret.count = 0) : KeptOdd c ch M := by
  intro k f hk hfk hM hkept i hi hmax
  by_contra hodd
  have hev : c.prio (f i) % 2 = 0 := by omega
  have hfold : (evenCycleMaxima c ch M).ret =
      (List.finRange n).foldl (fun b a => (ecmStep c ch M b a).ret) VSet.empty := by
    simp [evenCycleMaxima, ret_foldlM]
  have hmark := ecm_fold_marks c ch M (f i) (hM i hi) hev ?_ (List.finRange n) VSet.empty
    (List.mem_finRange _)
  · rw [← hfold, count_eq_zero _ h] at hmark
    cases hmark
  -- the cycle from `f (i+1)` back to `f i`, rotated
  let g : ℕ → Fin n := fun j => f ((i + 1 + j) % k)
  have hg : ∀ j, g j = f ((i + 1 + j) % k) := fun _ => rfl
  have hfper : ∀ j, f (j % k) = f j ∨ k ≤ j := fun j => by
    rcases Nat.lt_or_ge j k with hj | hj
    · left; rw [Nat.mod_eq_of_lt hj]
    · right; exact hj
  have hstep : ∀ j, g (j + 1) ∈ (keptT c ch (g j)).ret := by
    intro j
    have hmk : (i + 1 + j) % k < k := Nat.mod_lt _ hk
    have e : (i + 1 + (j + 1)) % k = ((i + 1 + j) % k + 1) % k := by
      rw [Nat.mod_add_mod, ← Nat.add_assoc]
    rw [hg, hg, e]
    rcases Nat.lt_or_ge ((i + 1 + j) % k + 1) k with h' | h'
    · rw [Nat.mod_eq_of_lt h']; exact hkept _ hmk
    · have hk' : (i + 1 + j) % k + 1 = k := by omega
      have h2 := hkept _ hmk
      rw [hk'] at h2
      rw [hk', Nat.mod_self, ← hfk]
      exact h2
  have hgM : ∀ j, M (g j) = true ∧ c.prio (g j) ≤ c.prio (f i) := fun j =>
    ⟨hM _ (Nat.mod_lt _ hk), hmax _ (Nat.mod_lt _ hk)⟩
  have hgend : g (k - 1) = f i := by
    rw [hg, show i + 1 + (k - 1) = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  refine ⟨g 0, ?_, (hgM 0).1, (hgM 0).2, ?_⟩
  · have h1 := hstep (k - 1)
    rw [show k - 1 + 1 = k by omega, hgend] at h1
    have hgk : g k = g 0 := by
      rw [hg, hg, show i + 1 + k = i + 1 + 0 + k by omega, Nat.add_mod_right]
    rw [hgk] at h1
    exact h1
  · have : ∀ j, Relation.ReflTransGen
        (fun a b => b ∈ (keptT c ch a).ret ∧ M b = true ∧ c.prio b ≤ c.prio (f i)) (g 0) (g j) := by
      intro j
      induction j with
      | zero => exact Relation.ReflTransGen.refl
      | succ j ih => exact ih.tail ⟨hstep j, (hgM (j + 1)).1, (hgM (j + 1)).2⟩
    have h' := this (k - 1)
    rw [hgend] at h'
    exact h'

theorem count_beq_zero (S : VSet n) (h : (S.count == 0) = true) : S.count = 0 := by
  simpa using h

/-- The acceleration set found by `sccLoop`: no even kept cycles, and every opponent member has
    a recorded choice. -/
theorem sccLoop_spec (c : Ctx n) (μ : Fin n → Val) (v : Fin n) :
    ∀ (k : ℕ) (ch : Fin n → Option (Fin n)) (allowed : Option (VSet n)), ChInv c ch →
      ch v ≠ none →
      ChInv c (sccLoop c μ v k ch allowed).ret.1 ∧
      ∀ M, (sccLoop c μ v k ch allowed).ret.2 = some M →
        KeptOdd c (sccLoop c μ v k ch allowed).ret.1 M ∧
        ∀ s, M s = true → c.mine s = false → (sccLoop c μ v k ch allowed).ret.1 s ≠ none
  | 0, ch, _, h, _ => ⟨h, fun M hM => by simp [sccLoop] at hM⟩
  | k + 1, ch, allowed, h, hv => by
    have hfw := explore_state (fwdNbrs c μ) (fun y => (allowed.map fun a => a y).getD true)
      (fun s => ChInv c s ∧ ChExt ch s)
      (fun s x hs => ⟨(fwdNbrs_state c μ s x hs.1).1, hs.2.trans (fwdNbrs_state c μ s x hs.1).2⟩)
      (n + 1) ch (VSet.single v) [v] ⟨h, ChExt.refl _⟩
    set ch' := (explore (fwdNbrs c μ) (fun y => (allowed.map fun a => a y).getD true) (n + 1) ch
      (VSet.single v) [v]).ret.1 with hch'
    have hv' : ch' v ≠ none := by
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hv
      rw [hfw.2 v y hy]; simp
    have hopp : ∀ s, (explore (bwdNbrs c ch' (explore (fwdNbrs c μ)
        (fun y => (allowed.map fun a => a y).getD true) (n + 1) ch (VSet.single v) [v]).ret.2)
        (fun _ => true) (n + 1) () (VSet.single v) [v]).ret.2 s = true → c.mine s = false →
        ch' s ≠ none := by
      intro s hs hm
      rcases bw_kept c ch' _ v s hs with rfl | ⟨x, hx⟩
      · exact hv'
      · rw [mem_keptT] at hx
        rcases hx with ⟨hm', -⟩ | ⟨-, hx⟩
        · rw [hm] at hm'; cases hm'
        · rw [hx]; simp
    simp only [sccLoop, ret_bind]
    rw [← hch']
    split
    · exact ⟨hfw.1, fun M hM => by simp at hM⟩
    · simp only [ret_bind]
      split
      · rename_i hc0
        refine ⟨hfw.1, fun M hM => ?_⟩
        simp only [ret_pure, Option.some.injEq] at hM
        subst hM
        exact ⟨keptOdd_of_ecm c ch' _ (count_beq_zero _ hc0), hopp⟩
      · split
        · exact ⟨hfw.1, fun M hM => by simp at hM⟩
        · exact sccLoop_spec c μ v k ch' _ hfw.1 hv'


/-! ### Bellman–Ford -/

/-- All proper values of a labelling have length `h`. -/
def LenOK (c : Ctx n) (b : Fin n → Val) : Prop := ∀ s x, b s = some x → x.length = c.height

theorem exitStep_ret (c : Ctx n) (μ : Fin n → Val) (M : VSet n) (s : Fin n) (acc : Val)
    (w : Fin n) :
    (exitStep c μ M s acc w).ret = if M w = true then acc else
      (if ((cmpVal c (prog c s (μ w)).ret acc).ret == .lt) = true then (prog c s (μ w)).ret
        else acc) := by
  unfold exitStep
  simp only [ret_bind]
  split <;> simp

theorem exitBound_spec (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (s : Fin n) :
    (∀ x, (exitBound c μ ch M s).ret = some x → x.length = c.height) ∧
    ∀ w ∈ (keptT c ch s).ret, M w = false → VLe c (exitBound c μ ch M s).ret (prog c s (μ w)).ret := by
  have key : ∀ (L : List (Fin n)) (acc : Val) (P : List (Fin n)),
      (∀ x, acc = some x → x.length = c.height) →
      (∀ w ∈ P, M w = false → VLe c acc (prog c s (μ w)).ret) →
      (∀ x, (L.foldl (fun b a => (exitStep c μ M s b a).ret) acc) = some x → x.length = c.height) ∧
      ∀ w ∈ P ++ L, M w = false →
        VLe c (L.foldl (fun b a => (exitStep c μ M s b a).ret) acc) (prog c s (μ w)).ret := by
    intro L
    induction L with
    | nil => intro acc P h1 h2; simpa using ⟨h1, h2⟩
    | cons w L ih =>
      intro acc P h1 h2
      rw [List.foldl_cons, show P ++ w :: L = (P ++ [w]) ++ L by simp]
      apply ih
      · rw [exitStep_ret]
        split
        · exact h1
        · split
          · exact prog_len c s _
          · exact h1
      · intro w' hw' hM
        rw [exitStep_ret]
        rcases List.mem_append.1 hw' with hw' | hw'
        · split
          · exact h2 w' hw' hM
          · split
            · rename_i _ hlt
              rw [beq_iff_eq, cmpVal_lt_iff] at hlt
              exact ((VLe.total c _ _).resolve_left hlt).trans (h2 w' hw' hM)
            · exact h2 w' hw' hM
        · simp at hw'; subst hw'
          rw [ite_eq_right (by simp [hM])]
          split
          · exact VLe.refl _ _
          · rename_i hlt
            rw [beq_iff_eq, cmpVal_lt_iff, not_not] at hlt
            exact hlt
  have := key (keptT c ch s).ret none [] (by simp) (by simp)
  simp only [exitBound, ret_bind, ret_foldlM, List.nil_append] at this ⊢
  exact this

theorem initStep_ret (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (b : Fin n → Val) (s : Fin n) :
    (initStep c μ ch M b s).ret =
      if M s = true then Function.update b s (exitBound c μ ch M s).ret else b := by
  unfold initStep
  simp only [ret_bind]
  split <;> simp

theorem foldl_cond_update {β : Type} (M : VSet n) (F : Fin n → β) :
    ∀ (L : List (Fin n)) (b : Fin n → β) (u : Fin n),
      (L.foldl (fun b a => if M a = true then Function.update b a (F a) else b) b) u =
        if u ∈ L ∧ M u = true then F u else b u
  | [], b, u => by simp
  | x :: L, b, u => by
    rw [List.foldl_cons, foldl_cond_update M F L]
    by_cases hu : u ∈ L ∧ M u = true
    · simp [hu]
    · rw [ite_eq_right hu]
      by_cases hux : u = x
      · subst hux
        by_cases hM : M u = true
        · simp [hM]
        · simp [hM]
      · split <;> simp_all

theorem init_ret (c : Ctx n) (μ : Fin n → Val) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (s : Fin n) :
    ((List.finRange n).foldlM (initStep c μ ch M) (fun _ => none)).ret s =
      if M s = true then (exitBound c μ ch M s).ret else none := by
  rw [ret_foldlM]
  simp only [initStep_ret]
  rw [foldl_cond_update M (fun s => (exitBound c μ ch M s).ret)]
  simp

theorem bfEdge_ret (c : Ctx n) (M : VSet n) (s : Fin n) (acc : (Fin n → Val) × Bool) (w : Fin n) :
    (bfEdge c M s acc w).ret = if M w = true then
      (if ((cmpVal c (prog c s (acc.1 w)).ret (acc.1 s)).ret == .lt) = true then
        (Function.update acc.1 s (prog c s (acc.1 w)).ret, true) else acc) else acc := by
  unfold bfEdge
  simp only [ret_bind]
  split <;> simp

theorem bfStep_ret (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n)
    (acc : (Fin n → Val) × Bool) (s : Fin n) :
    (bfStep c ch M acc s).ret = if M s = true then
      (keptT c ch s).ret.foldl (fun b a => (bfEdge c M s b a).ret) acc else acc := by
  unfold bfStep
  simp only [ret_bind]
  split <;> simp [ret_foldlM]

/-- The invariant of one Bellman–Ford round started from `b`, after relaxing the pairs `D`. -/
def BFInv (c : Ctx n) (b : Fin n → Val) (D : Fin n → Fin n → Prop)
    (acc : (Fin n → Val) × Bool) : Prop :=
  (∀ u, VLe c (acc.1 u) (b u)) ∧ LenOK c acc.1 ∧ (acc.2 = false → acc.1 = b) ∧
  ∀ s w, D s w → ∃ t, VLe c t (b w) ∧ (∀ x, t = some x → x.length = c.height) ∧
    (acc.2 = false → t = b w) ∧ VLe c (acc.1 s) (prog c s t).ret

theorem bfEdge_inv (c : Ctx n) (M : VSet n) (b : Fin n → Val) (D : Fin n → Fin n → Prop)
    (s w : Fin n) (acc : (Fin n → Val) × Bool) (h : BFInv c b D acc) :
    BFInv c b (fun s' w' => D s' w' ∨ (s' = s ∧ w' = w ∧ M w = true)) (bfEdge c M s acc w).ret := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [bfEdge_ret]
  by_cases hM : M w = true
  · rw [ite_eq_left hM]
    by_cases hlt : ((cmpVal c (prog c s (acc.1 w)).ret (acc.1 s)).ret == .lt) = true
    · rw [ite_eq_left hlt]
      rw [beq_iff_eq, cmpVal_lt_iff] at hlt
      have hlt' : VLe c (prog c s (acc.1 w)).ret (acc.1 s) := (VLe.total c _ _).resolve_left hlt
      refine ⟨fun u => ?_, fun u x hx => ?_, fun h => by simp at h, fun s' w' hD => ?_⟩
      · by_cases hus : u = s
        · subst hus; simp only [Function.update_self]; exact hlt'.trans (h1 u)
        · simp only [Function.update_of_ne hus]; exact h1 u
      · by_cases hus : u = s
        · subst hus; simp only [Function.update_self] at hx; exact prog_len c u _ x hx
        · simp only [Function.update_of_ne hus] at hx; exact h2 u x hx
      · rcases hD with hD | ⟨rfl, rfl, -⟩
        · obtain ⟨t, ht1, ht2, -, ht4⟩ := h4 s' w' hD
          refine ⟨t, ht1, ht2, fun h => by simp at h, ?_⟩
          by_cases hus : s' = s
          · subst hus; simp only [Function.update_self]; exact hlt'.trans ht4
          · simp only [Function.update_of_ne hus]; exact ht4
        · refine ⟨acc.1 w', h1 w', h2 w', fun h => by simp at h, ?_⟩
          simp only [Function.update_self]; exact VLe.refl _ _
    · rw [ite_eq_right hlt]
      rw [beq_iff_eq, cmpVal_lt_iff, not_not] at hlt
      refine ⟨h1, h2, h3, fun s' w' hD => ?_⟩
      rcases hD with hD | ⟨rfl, rfl, -⟩
      · exact h4 s' w' hD
      · exact ⟨acc.1 w', h1 w', h2 w', fun hf => by rw [h3 hf], hlt⟩
  · rw [ite_eq_right hM]
    refine ⟨h1, h2, h3, fun s' w' hD => ?_⟩
    rcases hD with hD | ⟨-, -, hM'⟩
    · exact h4 s' w' hD
    · exact absurd hM' hM

theorem bfStep_inv (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (b : Fin n → Val)
    (D : Fin n → Fin n → Prop) (s : Fin n) (acc : (Fin n → Val) × Bool) (h : BFInv c b D acc) :
    BFInv c b (fun s' w' => D s' w' ∨
      (s' = s ∧ M s = true ∧ w' ∈ (keptT c ch s).ret ∧ M w' = true)) (bfStep c ch M acc s).ret := by
  rw [bfStep_ret]
  by_cases hMs : M s = true
  · rw [ite_eq_left hMs]
    have key : ∀ (L : List (Fin n)) (D' : Fin n → Fin n → Prop) (acc : (Fin n → Val) × Bool),
        BFInv c b D' acc →
        BFInv c b (fun s' w' => D' s' w' ∨ (s' = s ∧ w' ∈ L ∧ M w' = true))
          (L.foldl (fun b a => (bfEdge c M s b a).ret) acc) := by
      intro L
      induction L with
      | nil =>
        intro D' acc h
        refine ⟨h.1, h.2.1, h.2.2.1, fun s' w' hD => ?_⟩
        rcases hD with hD | ⟨-, hw, -⟩
        · exact h.2.2.2 s' w' hD
        · simp at hw
      | cons w L ih =>
        intro D' acc h
        rw [List.foldl_cons]
        have := ih _ _ (bfEdge_inv c M b D' s w acc h)
        refine ⟨this.1, this.2.1, this.2.2.1, fun s' w' hD => this.2.2.2 s' w' ?_⟩
        rcases hD with hD | ⟨rfl, hw, hM⟩
        · exact Or.inl (Or.inl hD)
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact Or.inl (Or.inr ⟨rfl, rfl, hM⟩)
          · exact Or.inr ⟨rfl, hw, hM⟩
    have := key (keptT c ch s).ret D acc h
    refine ⟨this.1, this.2.1, this.2.2.1, fun s' w' hD => this.2.2.2 s' w' ?_⟩
    rcases hD with hD | ⟨rfl, -, hw, hM⟩
    · exact Or.inl hD
    · exact Or.inr ⟨rfl, hw, hM⟩
  · rw [ite_eq_right hMs]
    refine ⟨h.1, h.2.1, h.2.2.1, fun s' w' hD => ?_⟩
    rcases hD with hD | ⟨-, hM, -⟩
    · exact h.2.2.2 s' w' hD
    · exact absurd hM hMs

/-- One Bellman–Ford round: values only decrease, an unchanged round is stable, and every kept
    edge inside `M` has been relaxed. -/
theorem bfRound_spec (c : Ctx n) (ch : Fin n → Option (Fin n)) (M : VSet n) (b : Fin n → Val)
    (hb : LenOK c b) :
    BFInv c b (fun s w => M s = true ∧ w ∈ (keptT c ch s).ret ∧ M w = true)
      (bfRound c ch M b).ret := by
  have key : ∀ (L : List (Fin n)) (D : Fin n → Fin n → Prop) (acc : (Fin n → Val) × Bool),
      BFInv c b D acc →
      BFInv c b (fun s' w' => D s' w' ∨ (s' ∈ L ∧ M s' = true ∧ w' ∈ (keptT c ch s').ret ∧
        M w' = true)) (L.foldl (fun b a => (bfStep c ch M b a).ret) acc) := by
    intro L
    induction L with
    | nil =>
      intro D acc h
      refine ⟨h.1, h.2.1, h.2.2.1, fun s' w' hD => ?_⟩
      rcases hD with hD | ⟨hs, -⟩
      · exact h.2.2.2 s' w' hD
      · simp at hs
    | cons s L ih =>
      intro D acc h
      rw [List.foldl_cons]
      have := ih _ _ (bfStep_inv c ch M b D s acc h)
      refine ⟨this.1, this.2.1, this.2.2.1, fun s' w' hD => this.2.2.2 s' w' ?_⟩
      rcases hD with hD | ⟨hs, hM, hw, hMw⟩
      · exact Or.inl (Or.inl hD)
      · rcases List.mem_cons.1 hs with rfl | hs
        · exact Or.inl (Or.inr ⟨rfl, hM, hw, hMw⟩)
        · exact Or.inr ⟨hs, hM, hw, hMw⟩
  have := key (List.finRange n) (fun _ _ => False) (b, false)
    ⟨fun u => VLe.refl _ _, hb, fun _ => rfl, fun _ _ h => h.elim⟩
  simp only [bfRound, ret_foldlM]
  refine ⟨this.1, this.2.1, this.2.2.1, fun s w hD => this.2.2.2 s w (Or.inr ⟨List.mem_finRange s, hD⟩)⟩

section Reach

variable (c : Ctx n) (ν : Fin n → Val) (E : Fin n → Fin n → Prop) (ch : Fin n → Option (Fin n))
  (M : VSet n)

/-- `s` reaches an exit of `M` along at most `r` bound edges that are kept edges inside `M`. -/
def AReach : ℕ → Fin n → Prop
  | 0, s => M s = true ∧ ν s ≠ none ∧ ∃ w, E s w ∧ w ∈ (keptT c ch s).ret ∧ M w = false
  | r + 1, s => AReach r s ∨
      (M s = true ∧ ν s ≠ none ∧ ∃ w, E s w ∧ w ∈ (keptT c ch s).ret ∧ M w = true ∧ AReach r w)

theorem AReach.mem : ∀ {r : ℕ} {s : Fin n}, AReach c ν E ch M r s → M s = true ∧ ν s ≠ none
  | 0, _, h => ⟨h.1, h.2.1⟩
  | _ + 1, _, Or.inl h => AReach.mem h
  | _ + 1, _, Or.inr h => ⟨h.1, h.2.1⟩

theorem AReach.mono : ∀ {r r' : ℕ} {s : Fin n}, r ≤ r' → AReach c ν E ch M r s →
    AReach c ν E ch M r' s
  | r, 0, s, h, hr => by obtain rfl : r = 0 := by omega
                         exact hr
  | r, r' + 1, s, h, hr => by
    rcases Nat.lt_or_ge r (r' + 1) with h' | h'
    · exact Or.inl (AReach.mono (by omega) hr)
    · obtain rfl : r = r' + 1 := by omega
      exact hr

/-- From every member of `M` with a proper bound, bound edges that are kept edges reach an
    exit (the kept graph inside `M` has no even cycles, the bound's edge graph only even ones). -/
theorem exists_AReach (hB : Bound c ν E) (hch : ChInv c ch) (hodd : KeptOdd c ch M)
    (hopp : ∀ s, M s = true → c.mine s = false → ch s ≠ none) :
    ∀ s, M s = true → ν s ≠ none → ∃ r, AReach c ν E ch M r s := by
  classical
  have hsucc : ∀ s, M s = true → ν s ≠ none → ∃ w, E s w ∧ w ∈ (keptT c ch s).ret := by
    intro s hM hν
    cases hm : c.mine s with
    | true =>
      obtain ⟨w, hw⟩ := hB.ex s hν
      obtain ⟨h1, h2, -⟩ := hB.edge s w hw
      exact ⟨w, hw, (mem_keptT c ch s w).2 (Or.inl ⟨hm, h1, h2⟩)⟩
    | false =>
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hopp s hM hm)
      obtain ⟨h1, h2⟩ := hch s y hy
      exact ⟨y, hB.theirs s y hν hm h1 h2, (mem_keptT c ch s y).2 (Or.inr ⟨hm, hy⟩)⟩
  by_contra hne
  push Not at hne
  obtain ⟨s0, hs0M, hs0ν, hs0⟩ := hne
  let U : Fin n → Prop := fun s => M s = true ∧ ν s ≠ none ∧ ∀ r, ¬ AReach c ν E ch M r s
  have hU : ∀ s, U s → ∃ w, E s w ∧ w ∈ (keptT c ch s).ret ∧ U w := by
    intro s ⟨hM, hν, hr⟩
    obtain ⟨w, hE, hk⟩ := hsucc s hM hν
    refine ⟨w, hE, hk, ?_, (hB.edge s w hE).2.2.2, fun r hrw => hr (r + 1) (Or.inr
      ⟨hM, hν, w, hE, hk, ?_, hrw⟩)⟩
    · by_contra hMw
      exact hr 0 ⟨hM, hν, w, hE, hk, by simpa using hMw⟩
    · by_contra hMw
      exact hr 0 ⟨hM, hν, w, hE, hk, by simpa using hMw⟩
  choose g hg using hU
  let g' : Fin n → Fin n := fun s => if h : U s then g s h else s
  have hg'U : ∀ s, U s → U (g' s) := fun s h => by simp only [g', dite_eq_left h]; exact (hg s h).2.2
  have hiter : ∀ i, U (g'^[i] s0) := by
    intro i
    induction i with
    | zero => exact ⟨hs0M, hs0ν, hs0⟩
    | succ i ih => rw [Function.iterate_succ_apply']; exact hg'U _ ih
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (n + 1) => g'^[i.1] s0) (by simp)
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Fin.ext h)
  wlog hlt : x.1 < y.1 generalizing x y
  · exact this y x hxy.symm hfxy.symm hxy'.symm (by omega)
  let f : ℕ → Fin n := fun t => g'^[x.1 + t] s0
  have hstep : ∀ t, E (f t) (f (t + 1)) ∧ f (t + 1) ∈ (keptT c ch (f t)).ret := by
    intro t
    have hU' := hiter (x.1 + t)
    simp only [f, show x.1 + (t + 1) = (x.1 + t) + 1 by omega, Function.iterate_succ_apply']
    simp only [g', dite_eq_left hU']
    exact ⟨(hg _ hU').1, (hg _ hU').2.1⟩
  set k := y.1 - x.1 with hk
  have hk0 : 0 < k := by omega
  have hfk : f k = f 0 := by
    simp only [f, show x.1 + k = y.1 by omega, add_zero]
    exact hfxy.symm
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range k) (fun t => c.prio (f t))
    ⟨0, by simp; omega⟩
  simp only [Finset.mem_range] at hi hmax
  have h1 := hodd k f hk0 hfk (fun t _ => (hiter (x.1 + t)).1) (fun t _ => (hstep t).2) i hi hmax
  have h2 := hB.cyc k f hk0 hfk (fun t _ => (hstep t).1) i hi hmax
  omega

open scoped Classical in
/-- The members reaching an exit within `r` steps. -/
noncomputable def AFin (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun s => AReach c ν E ch M r s

theorem AFin_mono {r r' : ℕ} (h : r ≤ r') : AFin c ν E ch M r ⊆ AFin c ν E ch M r' := by
  intro s hs
  simp only [AFin, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact AReach.mono c ν E ch M h hs

theorem AFin_step {r : ℕ} (h : AFin c ν E ch M (r + 1) = AFin c ν E ch M r) :
    AFin c ν E ch M (r + 1 + 1) = AFin c ν E ch M (r + 1) := by
  apply le_antisymm _ (AFin_mono c ν E ch M (by omega))
  intro s hs
  simp only [AFin, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  rcases hs with hs | ⟨hM, hν, w, hE, hk, hMw, hw⟩
  · exact hs
  · have hw' : w ∈ AFin c ν E ch M r := by
      rw [← h]; simp only [AFin, Finset.mem_filter, Finset.mem_univ, true_and]; exact hw
    simp only [AFin, Finset.mem_filter, Finset.mem_univ, true_and] at hw'
    exact Or.inr ⟨hM, hν, w, hE, hk, hMw, hw'⟩

theorem AFin_stable {r : ℕ} (h : AFin c ν E ch M (r + 1) = AFin c ν E ch M r) :
    ∀ r', r ≤ r' → AFin c ν E ch M r' = AFin c ν E ch M r := by
  have hs : ∀ r', r ≤ r' → AFin c ν E ch M (r' + 1) = AFin c ν E ch M r' := by
    intro r' hr'
    induction r', hr' using Nat.le_induction with
    | base => exact h
    | succ r' _ ih => exact AFin_step c ν E ch M ih
  intro r' hr'
  induction r', hr' using Nat.le_induction with
  | base => rfl
  | succ r' hr' ih => rw [hs r' hr', ih]

/-- Every member of `M` with a proper bound reaches an exit within `|M| - 1` steps. -/
theorem AReach_count (hB : Bound c ν E) (hch : ChInv c ch) (hodd : KeptOdd c ch M)
    (hopp : ∀ s, M s = true → c.mine s = false → ch s ≠ none) :
    ∀ s, M s = true → ν s ≠ none → AReach c ν E ch M (M.count - 1) s := by
  classical
  have hall := exists_AReach c ν E ch M hB hch hodd hopp
  set Mset : Finset (Fin n) := Finset.univ.filter fun s => M s = true ∧ ν s ≠ none with hMset
  have hsub : ∀ r, AFin c ν E ch M r ⊆ Mset := by
    intro r s hs
    simp only [AFin, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp [hMset, AReach.mem c ν E ch M hs]
  have hcover : ∀ r, AFin c ν E ch M (r + 1) = AFin c ν E ch M r → AFin c ν E ch M r = Mset := by
    intro r h
    apply le_antisymm (hsub r)
    intro s hs
    simp only [hMset, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨r', hr'⟩ := hall s hs.1 hs.2
    have : s ∈ AFin c ν E ch M r' := by simp [AFin, hr']
    rcases Nat.le_total r' r with hle | hle
    · exact AFin_mono c ν E ch M hle this
    · rwa [AFin_stable c ν E ch M h r' hle] at this
  have claim : ∀ r, AFin c ν E ch M r = Mset ∨ r + 1 ≤ (AFin c ν E ch M r).card := by
    intro r
    induction r with
    | zero =>
      by_cases h0 : (AFin c ν E ch M 0).card = 0
      · left
        apply hcover 0
        rw [Finset.card_eq_zero] at h0
        rw [h0]
        apply Finset.eq_empty_of_forall_notMem
        intro s hs
        simp only [AFin, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        rcases hs with hs | ⟨-, -, w, -, -, -, hw⟩
        · have : s ∈ AFin c ν E ch M 0 := by simp [AFin, hs]
          rw [h0] at this; simp at this
        · have : w ∈ AFin c ν E ch M 0 := by simp [AFin, hw]
          rw [h0] at this; simp at this
      · right; omega
    | succ r ih =>
      rcases ih with ih | ih
      · left
        exact le_antisymm (hsub _) (ih ▸ AFin_mono c ν E ch M (Nat.le_succ r))
      · by_cases heq : AFin c ν E ch M (r + 1) = AFin c ν E ch M r
        · left; rw [heq]; exact hcover r heq
        · right
          have hss : AFin c ν E ch M r ⊂ AFin c ν E ch M (r + 1) :=
            Finset.ssubset_iff_subset_ne.2 ⟨AFin_mono c ν E ch M (Nat.le_succ r), Ne.symm heq⟩
          have := Finset.card_lt_card hss
          omega
  intro s hM hν
  have hMcard : Mset.card ≤ M.count := by
    unfold VSet.count
    rw [length_filter_finRange]
    apply Finset.card_le_card
    intro x hx
    simp only [hMset, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  have hsM : s ∈ Mset := by simp [hMset, hM, hν]
  have hpos : 1 ≤ Mset.card := Finset.card_pos.2 ⟨s, hsM⟩
  have hA : AFin c ν E ch M (M.count - 1) = Mset := by
    rcases claim (M.count - 1) with h | h
    · exact h
    · exact Finset.eq_of_subset_of_card_le (hsub _) (by omega)
  have : s ∈ AFin c ν E ch M (M.count - 1) := hA ▸ hsM
  simpa [AFin] using this

end Reach

/-! ### Bellman–Ford keeps the members below the bound -/

section BF

variable {c : Ctx n} {ν : Fin n → Val} {E : Fin n → Fin n → Prop} {ch : Fin n → Option (Fin n)}
  {M : VSet n}

/-- The bounds of all members reaching an exit within `r` steps are below `ν`. -/
def BGood (c : Ctx n) (ν : Fin n → Val) (E : Fin n → Fin n → Prop) (ch : Fin n → Option (Fin n))
    (M : VSet n) (r : ℕ) (b : Fin n → Val) : Prop :=
  ∀ s, AReach c ν E ch M r s → VLe c (b s) (ν s)

theorem bGood_round (hB : Bound c ν E) {r : ℕ} {b : Fin n → Val} (hb : LenOK c b)
    (hg : BGood c ν E ch M r b) : BGood c ν E ch M (r + 1) (bfRound c ch M b).ret.1 := by
  obtain ⟨h1, -, -, h4⟩ := bfRound_spec c ch M b hb
  intro s hs
  rcases hs with hs | ⟨hM, -, w, hE, hk, hMw, hw⟩
  · exact (h1 s).trans (hg s hs)
  · obtain ⟨t, ht1, ht2, -, ht4⟩ := h4 s w ⟨hM, hk, hMw⟩
    exact ht4.trans (hB.good s w hE t ht2 (ht1.trans (hg w hw)))

theorem bGood_stable (hB : Bound c ν E) {b : Fin n → Val} (hb : LenOK c b)
    (hst : (bfRound c ch M b).ret.2 = false) :
    ∀ r, BGood c ν E ch M r b → BGood c ν E ch M (r + 1) b := by
  obtain ⟨-, -, h3, h4⟩ := bfRound_spec c ch M b hb
  intro r hg s hs
  rcases hs with hs | ⟨hM, -, w, hE, hk, hMw, hw⟩
  · exact hg s hs
  · obtain ⟨t, ht1, ht2, ht3, ht4⟩ := h4 s w ⟨hM, hk, hMw⟩
    have htb : t = b w := ht3 hst
    rw [h3 hst] at ht4
    exact ht4.trans (hB.good s w hE t ht2 (htb ▸ hg w hw))

theorem bfLoop_good (hB : Bound c ν E) :
    ∀ (k : ℕ) (b : Fin n → Val) (r : ℕ), LenOK c b → BGood c ν E ch M r b →
      LenOK c (bfLoop c ch M k b).ret ∧ BGood c ν E ch M (r + k) (bfLoop c ch M k b).ret
  | 0, b, r, hb, hg => by simpa [bfLoop] using ⟨hb, hg⟩
  | k + 1, b, r, hb, hg => by
    obtain ⟨-, h2, h3, -⟩ := bfRound_spec c ch M b hb
    simp only [bfLoop, ret_bind]
    split
    · rename_i hch
      have := bfLoop_good hB k _ (r + 1) h2 (bGood_round hB hb hg)
      rw [show r + 1 + k = r + (k + 1) by omega] at this
      exact this
    · rename_i hch
      have hst : (bfRound c ch M b).ret.2 = false := by simpa using hch
      simp only [ret_pure]
      rw [h3 hst]
      refine ⟨hb, ?_⟩
      have : ∀ j, BGood c ν E ch M (r + j) b := by
        intro j
        induction j with
        | zero => exact hg
        | succ j ih => exact bGood_stable hB hb hst _ ih
      exact this _

end BF


/-! ### Raising, acceleration and the lifting loop preserve the invariant -/

theorem LInv.withChoice {c : Ctx n} {ν : Fin n → Val} {st : LState n} (h : LInv c ν st)
    {ch : Fin n → Option (Fin n)} (hch : ChInv c ch) : LInv c ν { st with choice := ch } :=
  ⟨hch, h.queue, h.inq, h.le, h.len⟩

theorem raiseStep_ret (c : Ctx n) (M : VSet n) (b : Fin n → Val) (acc : LState n × ℕ)
    (s : Fin n) :
    (raiseStep c M b acc s).ret = if M s = true ∧ (cmpVal c (b s) (acc.1.measure s)).ret = .gt then
      (requeue (requeuePreds c { acc.1 with measure := Function.update acc.1.measure s (b s) } s).ret
        s, acc.2 + 1) else acc := by
  unfold raiseStep
  simp only [ret_bind]
  split
  · rename_i hM
    simp only [ret_bind]
    split
    · rename_i hgt
      simp only [ret_bind, ret_pure]
      rw [ite_eq_left ⟨hM, by simpa using hgt⟩]
    · rename_i hgt
      simp only [ret_pure]
      rw [ite_eq_right (fun h' => hgt (by simpa using h'.2))]
  · rename_i hM
    simp only [ret_pure]
    rw [ite_eq_right (by simp [hM])]

theorem raiseStep_inv {c : Ctx n} {ν : Fin n → Val} (M : VSet n) (b : Fin n → Val)
    (hb : ∀ s, M s = true → VLe c (b s) (ν s)) (hbl : LenOK c b) (acc : LState n × ℕ) (s : Fin n)
    (h : LInv c ν acc.1) : LInv c ν (raiseStep c M b acc s).ret.1 := by
  rw [raiseStep_ret]
  split
  · rename_i hc
    obtain ⟨hM, -⟩ := hc
    set st1 : LState n := { acc.1 with measure := Function.update acc.1.measure s (b s) } with hst1
    obtain ⟨a1, a2, -, a4, -, a6⟩ := requeuePreds_spec c st1 s h.inq
    obtain ⟨b1, b2, -, b4, b5, b6⟩ := requeue_spec (requeuePreds c st1 s).ret s a6
    refine ⟨?_, fun u hu hnq => ?_, b6, fun u => ?_, fun u x hx => ?_⟩
    · rw [b2, a2]; exact h.choice
    · have hus : u ≠ s := fun he => hnq (he ▸ b5)
      have hnq' : u ∉ (requeuePreds c st1 s).ret.queue := fun h' => hnq (b4 u h')
      rw [b1, a1]
      exact update_consistent c acc.1 s (b s) (fun v hv hvq _ => h.queue v hv hvq) h.inq u hu hnq'
        hus
    · rw [b1, a1]
      by_cases hus : u = s
      · subst hus; simp only [hst1, Function.update_self]; exact hb u hM
      · simp only [hst1, Function.update_of_ne hus]; exact h.le u
    · rw [b1, a1] at hx
      by_cases hus : u = s
      · subst hus; simp only [hst1, Function.update_self] at hx; exact hbl u x hx
      · simp only [hst1, Function.update_of_ne hus] at hx; exact h.len u x hx
  · exact h

theorem raise_inv {c : Ctx n} {ν : Fin n → Val} (M : VSet n) (b : Fin n → Val)
    (hb : ∀ s, M s = true → VLe c (b s) (ν s)) (hbl : LenOK c b) (st : LState n)
    (h : LInv c ν st) : LInv c ν (raise c M b st).ret.1 := by
  unfold raise
  rw [ret_foldlM]
  have key : ∀ (L : List (Fin n)) (acc : LState n × ℕ), LInv c ν acc.1 →
      LInv c ν (L.foldl (fun b' a => (raiseStep c M b b' a).ret) acc).1 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons s L ih =>
      intro acc h
      exact ih _ (raiseStep_inv M b hb hbl acc s h)
  exact key _ _ h

theorem accelRaise_inv {c : Ctx n} {ν : Fin n → Val} {E : Fin n → Fin n → Prop}
    (hB : Bound c ν E) (st : LState n) (M : VSet n) (h : LInv c ν st)
    (hodd : KeptOdd c st.choice M)
    (hopp : ∀ s, M s = true → c.mine s = false → st.choice s ≠ none) :
    LInv c ν (accelRaise c st M).ret.1 := by
  simp only [accelRaise, ret_bind]
  set b0 := ((List.finRange n).foldlM (initStep c st.measure st.choice M) (fun _ => none)).ret
    with hb0
  have hb0s : ∀ s, b0 s = if M s = true then (exitBound c st.measure st.choice M s).ret else none :=
    fun s => init_ret c st.measure st.choice M s
  have hl0 : LenOK c b0 := by
    intro s x hx
    rw [hb0s] at hx
    split at hx
    · exact (exitBound_spec c st.measure st.choice M s).1 x hx
    · cases hx
  have hg0 : BGood c ν E st.choice M 0 b0 := by
    rintro s ⟨hM, -, w, hE, hk, hMw⟩
    rw [hb0s, ite_eq_left hM]
    exact ((exitBound_spec c st.measure st.choice M s).2 w hk hMw).trans
      (hB.good s w hE _ (h.len w) (h.le w))
  obtain ⟨hl, hg⟩ := bfLoop_good (ch := st.choice) (M := M) hB M.count b0 0 hl0 hg0
  apply raise_inv M _ _ hl st h
  intro s hM
  by_cases hν : ν s = none
  · rw [hν]; exact VLe.top _ _
  · exact hg s (AReach.mono c ν E st.choice M (by omega)
      (AReach_count c ν E st.choice M hB h.choice hodd hopp s hM hν))

/-- Acceleration preserves the lifting invariant. -/
theorem accelerate_inv {c : Ctx n} {ν : Fin n → Val} {E : Fin n → Fin n → Prop}
    (hB : Bound c ν E) (st : LState n) (v : Fin n) (h : LInv c ν st) :
    LInv c ν (accelerate c st v).ret.1 := by
  obtain ⟨hp1, -⟩ := pumpTest_spec c st.measure v n st.choice v h.choice
  have hpv := pumpTest_self c st.measure v n st.choice h.choice
  simp only [accelerate, ret_bind]
  split
  · exact h.withChoice hp1
  · rename_i hpt
    have hpv' := hpv (by simpa using hpt)
    obtain ⟨hs1, hs2⟩ := sccLoop_spec c st.measure v (n + 1) _ none hp1 hpv'
    simp only [ret_bind]
    split
    · exact h.withChoice hs1
    · rename_i M hM
      obtain ⟨hodd, hopp⟩ := hs2 M hM
      exact accelRaise_inv hB _ M (h.withChoice hs1) hodd hopp

/-- The state after popping `v` and recording its choice, without a lift. -/
theorem nolift_inv {c : Ctx n} {ν : Fin n → Val} (st : LState n) (v : Fin n) (q : List (Fin n))
    (hq : st.queue = v :: q) (h : LInv c ν st)
    (hgt : (cmpVal c (evaluate c st.measure v none).ret.1 (st.measure v)).ret ≠ .gt) :
    LInv c ν ⟨st.measure, Function.update st.choice v (evaluate c st.measure v none).ret.2, q,
      Function.update st.inq v false, st.steps⟩ := by
  refine ⟨fun x y hxy => ?_, fun u hu hnq => ?_, fun u hu => ?_, h.le, h.len⟩
  · by_cases hxv : x = v
    · subst hxv
      simp only [Function.update_self] at hxy
      exact (mem_succT c x y).1 ((evaluate_spec c st.measure x none).2.2 y hxy).1
    · simp only [Function.update_of_ne hxv] at hxy
      exact h.choice x y hxy
  · by_cases huv : u = v
    · subst huv; exact hgt
    · exact h.queue u hu (by
        rw [hq]; intro h'; rcases List.mem_cons.1 h' with h' | h'
        · exact huv h'
        · exact hnq h')
  · by_cases huv : u = v
    · subst huv; simp at hu
    · simp only [Function.update_of_ne huv] at hu
      have := h.inq u hu
      rw [hq] at this
      rcases List.mem_cons.1 this with h' | h'
      · exact absurd h' huv
      · exact h'

/-- The state after a successful lift of `v` and re-queueing its predecessors. -/
theorem lift_inv {c : Ctx n} {ν : Fin n → Val} {E : Fin n → Fin n → Prop} (hB : Bound c ν E)
    (st : LState n) (v : Fin n) (q : List (Fin n)) (hq : st.queue = v :: q) (h : LInv c ν st) :
    LInv c ν (requeuePreds c ⟨Function.update st.measure v (evaluate c st.measure v none).ret.1,
      Function.update st.choice v (evaluate c st.measure v none).ret.2, q,
      Function.update st.inq v false, st.steps + 1⟩ v).ret := by
  have hinq1 : ∀ u, (Function.update st.inq v false) u = true → u ∈ q := by
    intro u hu
    by_cases huv : u = v
    · subst huv; simp at hu
    · simp only [Function.update_of_ne huv] at hu
      have := h.inq u hu
      rw [hq] at this
      rcases List.mem_cons.1 this with h' | h'
      · exact absurd h' huv
      · exact h'
  have hch1 : ChInv c (Function.update st.choice v (evaluate c st.measure v none).ret.2) := by
    intro x y hxy
    by_cases hxv : x = v
    · subst hxv
      simp only [Function.update_self] at hxy
      exact (mem_succT c x y).1 ((evaluate_spec c st.measure x none).2.2 y hxy).1
    · simp only [Function.update_of_ne hxv] at hxy
      exact h.choice x y hxy
  have hq0 : ∀ u, c.alive u = true → u ∉ q → u ≠ v →
      VLe c (evaluate c st.measure u none).ret.1 (st.measure u) := by
    intro u hu hnq huv
    exact h.queue u hu (by
      rw [hq]; intro h'; rcases List.mem_cons.1 h' with h' | h'
      · exact huv h'
      · exact hnq h')
  obtain ⟨a1, a2, -, a4, a5, a6⟩ := requeuePreds_spec c
    ⟨Function.update st.measure v (evaluate c st.measure v none).ret.1,
      Function.update st.choice v (evaluate c st.measure v none).ret.2, q,
      Function.update st.inq v false, st.steps + 1⟩ v hinq1
  refine ⟨?_, fun u hu hnq => ?_, a6, fun u => ?_, fun u x hx => ?_⟩
  · rw [a2]; exact hch1
  · rw [a1]
    by_cases huv : u = v
    · subst huv
      have hvv : u ∉ c.G.succ u := fun hs => hnq (a5 u hu hs)
      rw [evaluate_congr c (Function.update st.measure u (evaluate c st.measure u none).ret.1)
        st.measure u none (fun w hw => by
          have : w ≠ u := fun h' => hvv (h' ▸ ((mem_succT c u w).1 hw).1)
          rw [Function.update_of_ne this])]
      simp only [Function.update_self]
      exact VLe.refl _ _
    · exact update_consistent c ⟨st.measure, Function.update st.choice v
        (evaluate c st.measure v none).ret.2, q, Function.update st.inq v false, st.steps + 1⟩
        v (evaluate c st.measure v none).ret.1 hq0 hinq1 u hu hnq huv
  · rw [a1]
    by_cases huv : u = v
    · subst huv; simp only [Function.update_self]
      exact evaluate_le_bound hB h.le h.len u
    · simp only [Function.update_of_ne huv]; exact h.le u
  · rw [a1] at hx
    by_cases huv : u = v
    · subst huv; simp only [Function.update_self] at hx
      exact evaluate_len c st.measure u none x hx
    · simp only [Function.update_of_ne huv] at hx; exact h.len u x hx

/-- The lifting loop preserves the invariant, and reports an empty queue only when it is. -/
theorem runLoop_inv {c : Ctx n} {ν : Fin n → Val} {E : Fin n → Fin n → Prop}
    (hB : Bound c ν E) (B : ℕ) :
    ∀ (k : ℕ) (st : LState n), LInv c ν st →
      LInv c ν (runLoop c B k st).ret.1 ∧
        ((runLoop c B k st).ret.2.1 = true → (runLoop c B k st).ret.1.queue = [])
  | 0, st, h => ⟨h, fun h' => by simp [runLoop] at h'⟩
  | k + 1, st, h => by
    rw [runLoop]
    split
    · exact ⟨h, fun h' => by simpa using h'⟩
    · split
      · rename_i hq
        exact ⟨h, fun _ => hq⟩
      · rename_i v q hq
        simp only [ret_bind]
        split
        · apply runLoop_inv hB B k
          have hacc := accelerate_inv hB _ v (lift_inv hB st v q hq h)
          exact ⟨hacc.choice, hacc.queue, hacc.inq, hacc.le, hacc.len⟩
        · rename_i hgt
          apply runLoop_inv hB B k
          exact nolift_inv st v q hq h (by simpa using hgt)

theorem run_inv {c : Ctx n} {ν : Fin n → Val} {E : Fin n → Fin n → Prop}
    (hB : Bound c ν E) (budget fuel : ℕ) (st : LState n) (h : LInv c ν st) :
    LInv c ν (run c budget fuel st).ret.1 ∧
      ((run c budget fuel st).ret.2.1 = true → (run c budget fuel st).ret.1.queue = []) :=
  runLoop_inv hB _ fuel st h

end MercLib.ParityGame.TwoSidedCost

end TwoSidedCostCorrectLiftProofs
