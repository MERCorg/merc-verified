module

public import ParityGame.Proofs.TwoSidedCostCorrect_Lift_Proofs
public import Mathlib.Data.List.GetD

@[expose] public section TwoSidedCostCorrectWinProofs

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

From the program's values to winning: consistent values form a progress measure over the chain
tree codomain (soundness, used for completion and certification), and the chain-tree measure of
the winning region is a `Bound` (completeness: the lifting never exceeds it, so every vertex won
by the lifting player keeps a proper value). -/

variable {n : ℕ}

/-- The codomain of the lifting player's chain tree on the alive vertices. -/
noncomputable def Ctx.cod (c : Ctx n) (h : c.G.Total) : Codomain (ℕ → ℕ) :=
  truncLexCodomain ((c.game h).chainDepth c.X) ((c.game h).chainDepth_antitone c.X)

theorem Ctx.cod_le (c : Ctx n) (h : c.G.Total) (p : ℕ) (a b : ℕ → ℕ) :
    (c.cod h).le p a b ↔ LexLE ((c.game h).chainDepth c.X p) a b := Iff.rfl

/-- The program values as tuples (`⊤` as `0`, never used on the domains below). -/
def lab (μ : Fin n → Val) (v : Fin n) : ℕ → ℕ :=
  match μ v with
  | some x => tup x
  | none => fun _ => 0

theorem lab_some {μ : Fin n → Val} {v : Fin n} {x : List (ℕ × ℕ)} (h : μ v = some x) :
    lab μ v = tup x := by
  simp [lab, h]

theorem vle_some_iff (c : Ctx n) {x y : List (ℕ × ℕ)} (hx : x.length = c.height)
    (hy : y.length = c.height) : VLe c (some x) (some y) ↔ LexLE (2 * c.height) (tup x) (tup y) := by
  unfold VLe
  simp only [cmpVal]
  exact lexCmp_le_iff c.height x y (by omega) (by omega)

/-- A consistent step `prog (μ w) ≤ μ v` is a progress step for the tuples. -/
theorem prog_progress (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total) (μ : Fin n → Val)
    (hlen : ∀ v x, μ v = some x → x.length = c.height) (v w : Fin n) (hv : μ v ≠ none)
    (hle : VLe c (prog c v (μ w)).ret (μ v)) :
    μ w ≠ none ∧ (c.game h).Prog (c.cod h) (lab μ) v w := by
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hv
  cases hw : μ w with
  | none =>
    rw [hw, prog_ret_none, hy] at hle
    exact absurd hle (by simp [VLe, cmpVal])
  | some x =>
    rw [hw] at hle
    refine ⟨by simp, ?_⟩
    cases hr : (prog c v (some x)).ret with
    | none => rw [hr, hy] at hle; exact absurd hle (by simp [VLe, cmpVal])
    | some r =>
      rw [hr, hy, vle_some_iff c (prog_len c v _ r hr) (hlen v y hy)] at hle
      obtain ⟨h1, h2⟩ := prog_sound c v x r hr (by rw [hlen w x hw])
      have hd := depthOf_le c v
      have hdep : (c.game h).chainDepth c.X ((c.game h).prio v) = 2 * depthOf c v := by
        unfold Game.chainDepth; rw [depthOf_eq c hc h]
      have hle' : LexLE (2 * depthOf c v) (tup r) (tup y) := LexLE.mono (by omega) hle
      unfold Game.Prog
      rw [Ctx.cod_le, Ctx.cod_le, hdep, lab_some hw, lab_some hy]
      refine ⟨h1.trans hle', fun hodd h3 => ?_⟩
      rw [Ctx.game_prio] at hodd
      exact h2 hodd (hle'.trans h3)

/-! ### Completion: a fixpoint of the lifting is sound -/

/-- If every alive vertex is consistent, the alive vertices with a proper value are won by the
    lifting player. -/
theorem complete_sound (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total)
    (hX : (c.G.toGame h).IsSubgame c.X) (μ : Fin n → Val)
    (hlen : ∀ v x, μ v = some x → x.length = c.height)
    (hcons : ∀ v, c.alive v = true → VLe c (evaluate c μ v none).ret.1 (μ v)) :
    ∀ v, c.alive v = true → μ v ≠ none → (c.G.toGame h).Wins c.X (toPlayer c.p) v := by
  let D : Set (Fin n) := {v | c.alive v = true ∧ μ v ≠ none}
  let σ : Strategy (Fin n) := fun v => ((evaluate c μ v none).ret.2).getD v
  have hpm : (c.game h).IsProgressMeasure c.X (c.cod h) D (lab μ) σ := by
    refine ⟨fun v hv => hv.1, fun v hv ho => ?_, fun v hv ho w hwX he => ?_⟩
    · rw [Ctx.game_owner] at ho
      obtain ⟨h1, h2, h3⟩ := evaluate_spec c μ v none
      have hle := hcons v hv.1
      cases he : (evaluate c μ v none).ret.2 with
      | none => rw [h2 he] at hle; exact absurd ((VLe.top_iff c _).1 hle) hv.2
      | some w =>
        obtain ⟨hws, -, hval, -, -⟩ := h3 w he
        have hσ : σ v = w := by simp [σ, he]
        rw [hσ]
        rw [hval] at hle
        obtain ⟨hwne, hprog⟩ := prog_progress c hc h μ hlen v w hv.2 hle
        obtain ⟨hsucc, halive⟩ := (mem_succT c v w).1 hws
        exact ⟨⟨halive, hwne⟩, (Ctx.game_edge c h v w).2 hsucc, hprog⟩
    · have hm : c.mine v = false := by
        cases hm : c.mine v
        · rfl
        · exact absurd ((Ctx.game_owner c h v).2 hm) (by rw [ho]; simp)
      obtain ⟨h1, -, h3⟩ := evaluate_spec c μ v none
      have hws : w ∈ (succT c v).ret := (mem_succT c v w).2 ⟨(Ctx.game_edge c h v w).1 he, hwX⟩
      cases hev : (evaluate c μ v none).ret.2 with
      | none => exact absurd ((h1.1 hev) w hws) (by simp [allowedAt_none])
      | some w' =>
        obtain ⟨-, -, -, -, hmax⟩ := h3 w' hev
        have hle := (hmax hm w hws (allowedAt_none w)).trans (hcons v hv.1)
        obtain ⟨hwne, hprog⟩ := prog_progress c hc h μ hlen v w hv.2 hle
        exact ⟨⟨hwX, hwne⟩, hprog⟩
  intro v hv hne
  have hX' : (c.game h).IsSubgame c.X := (Game.forPlayer_isSubgame _ _ _).2 hX
  have := (c.game h).progressMeasureSound c.X (c.cod h) D (lab μ) σ hX' hpm v ⟨hv, hne⟩
  exact ⟨σ, (Game.forPlayer_winsFrom _ _ _ _ _).1 this⟩

/-! ### Certification -/

/-- `v` is consistent for the domain `dom`: the opponent's vertices keep all their alive
    successors in `dom`, and the evaluation restricted to `dom` is not above the value. -/
def Cons (c : Ctx n) (μ : Fin n → Val) (dom : VSet n) (v : Fin n) : Prop :=
  (c.mine v = false → ∀ w ∈ (succT c v).ret, dom w = true) ∧
    VLe c (evaluate c μ v (some dom)).ret.1 (μ v)

theorem evaluate_congr_allowed (c : Ctx n) (μ : Fin n → Val) (v : Fin n) (a a' : Option (VSet n))
    (h : ∀ w ∈ (succT c v).ret, allowedAt a w = allowedAt a' w) :
    (evaluate c μ v a).ret = (evaluate c μ v a').ret := by
  have key : ∀ (L : List (Fin n)), (∀ w ∈ L, allowedAt a w = allowedAt a' w) → ∀ acc,
      L.foldl (fun b x => (evalStep c μ v a b x).ret) acc =
        L.foldl (fun b x => (evalStep c μ v a' b x).ret) acc := by
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

theorem cons_congr (c : Ctx n) (μ : Fin n → Val) (dom dom' : VSet n) (v : Fin n)
    (h : ∀ w ∈ (succT c v).ret, dom w = dom' w) (hc : Cons c μ dom v) : Cons c μ dom' v := by
  refine ⟨fun hm w hw => (h w hw) ▸ hc.1 hm w hw, ?_⟩
  rw [← evaluate_congr_allowed c μ v (some dom) (some dom') (fun w hw => by
    simp [allowedAt, h w hw])]
  exact hc.2

theorem certPush_fold (dom : VSet n) :
    ∀ (ps : List (Fin n)) (Q : VSet n) (L : List (Fin n)), (∀ u, Q u = true → u ∈ L) →
      (∀ u, (ps.foldl (certPush dom) (Q, L)).1 u = true → u ∈ (ps.foldl (certPush dom) (Q, L)).2) ∧
      (∀ u ∈ L, u ∈ (ps.foldl (certPush dom) (Q, L)).2) ∧
      (∀ u ∈ ps, dom u = true → u ∈ (ps.foldl (certPush dom) (Q, L)).2)
  | [], Q, L, h => ⟨h, fun _ hu => hu, by simp⟩
  | x :: ps, Q, L, h => by
    rw [List.foldl_cons]
    unfold certPush
    split
    · rename_i hx
      have h' : ∀ u, (Function.update Q x true) u = true → u ∈ L ++ [x] := by
        intro u hu
        by_cases hux : u = x
        · subst hux; simp
        · rw [Function.update_of_ne hux] at hu; simp [h u hu]
      obtain ⟨a1, a2, a3⟩ := certPush_fold dom ps _ _ h'
      refine ⟨a1, fun u hu => a2 u (by simp [hu]), fun u hu hd => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact a2 u (by simp)
      · exact a3 u hu hd
    · rename_i hx
      obtain ⟨a1, a2, a3⟩ := certPush_fold dom ps Q L h
      refine ⟨a1, a2, fun u hu hd => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · have : Q u = true := by simpa [hd] using hx
        exact a2 u (h u this)
      · exact a3 u hu hd

/-- The removal loop of certification returns a domain on which every vertex is consistent. -/
theorem certLoop_spec (c : Ctx n) (μ : Fin n → Val) (dom0 : VSet n)
    (hdom0 : ∀ v, dom0 v = true → c.alive v = true) :
    ∀ (k : ℕ) (dom queued : VSet n) (q : List (Fin n)),
      (∀ v, dom v = true → v ∉ q → Cons c μ dom v) → (∀ u, queued u = true → u ∈ q) →
      (∀ v, dom v = true → dom0 v = true) →
      ∀ D, (certLoop c μ k dom queued q).ret = some D →
        (∀ v, D v = true → Cons c μ D v) ∧ ∀ v, D v = true → dom0 v = true
  | 0, _, _, _, _, _, _, D, hD => by simp [certLoop] at hD
  | k + 1, dom, queued, [], h1, _, h3, D, hD => by
    simp only [certLoop, ret_pure, Option.some.injEq] at hD
    subst hD
    exact ⟨fun v hv => h1 v hv (by simp), h3⟩
  | k + 1, dom, queued, v :: q, h1, h2, h3, D, hD => by
    rw [certLoop] at hD
    simp only [ret_bind] at hD
    have h2' : ∀ u, (Function.update queued v false) u = true → u ∈ q := by
      intro u hu
      by_cases huv : u = v
      · subst huv; simp at hu
      · rw [Function.update_of_ne huv] at hu
        rcases List.mem_cons.1 (h2 u hu) with h' | h'
        · exact absurd h' huv
        · exact h'
    split at hD
    · rename_i hdv
      apply certLoop_spec c μ dom0 hdom0 k dom _ q _ h2' h3 D hD
      intro u hu huq
      exact h1 u hu (by
        intro h'; rcases List.mem_cons.1 h' with rfl | h'
        · simp [hu] at hdv
        · exact huq h')
    · rename_i hdv
      simp only [ret_bind] at hD
      -- the consistency check
      have hcons : ∀ b, (b = true ↔ Cons c μ dom v) →
          (if b = true then (certLoop c μ k dom (Function.update queued v false) q).ret else
            (certLoop c μ k (Function.update dom v false)
              ((predT c v).ret.foldl (certPush (Function.update dom v false))
                (Function.update queued v false, q)).1
              ((predT c v).ret.foldl (certPush (Function.update dom v false))
                (Function.update queued v false, q)).2).ret) = some D →
          (∀ v, D v = true → Cons c μ D v) ∧ ∀ v, D v = true → dom0 v = true := by
        intro b hb hD'
        split at hD'
        · rename_i hbt
          apply certLoop_spec c μ dom0 hdom0 k dom _ q _ h2' h3 D hD'
          intro u hu huq
          by_cases huv : u = v
          · subst huv; exact hb.1 hbt
          · exact h1 u hu (by
              intro h'; rcases List.mem_cons.1 h' with h' | h'
              · exact huv h'
              · exact huq h')
        · obtain ⟨p1, p2, p3⟩ := certPush_fold (Function.update dom v false) (predT c v).ret
            (Function.update queued v false) q h2'
          apply certLoop_spec c μ dom0 hdom0 k _ _ _ _ p1 _ D hD'
          · intro u hu hunq
            have huv : u ≠ v := by
              intro he; subst he; simp at hu
            rw [Function.update_of_ne huv] at hu
            have huq : u ∉ q := fun h' => hunq (p2 u h')
            have hold := h1 u hu (by
              intro h'; rcases List.mem_cons.1 h' with h' | h'
              · exact huv h'
              · exact huq h')
            have hnp : u ∉ (predT c v).ret := fun hp => hunq (p3 u hp (by
              rw [Function.update_of_ne huv]; exact hu))
            refine cons_congr c μ dom _ u (fun w hw => ?_) hold
            have hwv : w ≠ v := by
              intro he; subst he
              exact hnp ((mem_predT c w u).2 ⟨hdom0 u (h3 u hu), ((mem_succT c u w).1 hw).1⟩)
            rw [Function.update_of_ne hwv]
          · intro u hu
            by_cases huv : u = v
            · subst huv; simp at hu
            · rw [Function.update_of_ne huv] at hu; exact h3 u hu
      split at hD
      · rename_i hleaves
        refine hcons false ⟨(fun h => by cases h), fun hc => ?_⟩ (by simpa using hD)
        exfalso
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true] at hleaves
        obtain ⟨hm, w, hw, hdw⟩ := hleaves
        have := hc.1 (by simpa using hm) w hw
        simp_all
      · rename_i hleaves
        have hall : c.mine v = false → ∀ w ∈ (succT c v).ret, dom w = true := by
          intro hm w hw
          by_contra hdw
          apply hleaves
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true]
          exact ⟨by simpa using hm, w, hw, by simpa using hdw⟩
        simp only [ret_bind] at hD
        split at hD
        · rename_i hb
          refine hcons true ⟨fun _ => ⟨hall, ?_⟩, fun _ => rfl⟩ (by simpa using hD)
          simp only [ret_pure, bne_iff_ne, ne_eq] at hb
          rw [cmpVal_lt_iff, not_not] at hb
          exact hb
        · rename_i hb
          simp only [ret_bind] at hD
          refine hcons false ⟨(fun h => by cases h), fun hc => ?_⟩ (by simpa using hD)
          simp only [ret_pure, bne_iff_ne, ne_eq, not_not] at hb
          have hb' : (cmpVal c (μ v) (evaluate c μ v (some dom)).ret.1).ret = .lt := by
            simpa using hb
          rw [cmpVal_lt_iff] at hb'
          exact absurd hc.2 hb'


theorem allowedAt_some (D : VSet n) (w : Fin n) : allowedAt (some D) w = D w := rfl

/-- Every vertex of the certified set is alive, has a proper value and is consistent for the
    certified set. -/
theorem certified_spec (c : Ctx n) (st : LState n) :
    ∀ v, (certified c st).ret v = true →
      c.alive v = true ∧ st.measure v ≠ none ∧ Cons c st.measure (certified c st).ret v := by
  set dom0 : VSet n := fun v => c.alive v && (st.measure v).isSome with hdom0
  have hd0 : ∀ v, dom0 v = true → c.alive v = true := fun v hv => by
    simp only [hdom0, Bool.and_eq_true] at hv; exact hv.1
  have hret : (certified c st).ret = match (certLoop c st.measure (n * n + n + 1) dom0 dom0
      ((List.finRange n).filter dom0)).ret with
      | some D => fun v => c.alive v && D v
      | none => VSet.empty := by
    simp only [certified, ret_bind, ret_pure, materialize_eq]
    rfl
  have hspec := certLoop_spec c st.measure dom0 hd0 (n * n + n + 1) dom0 dom0
    ((List.finRange n).filter dom0)
    (fun v hv hvq => absurd (List.mem_filter.2 ⟨List.mem_finRange v, hv⟩) hvq)
    (fun u hu => List.mem_filter.2 ⟨List.mem_finRange u, hu⟩) (fun _ h => h)
  rw [hret]
  split
  · rename_i D hD
    obtain ⟨h1, h2⟩ := hspec D hD
    have hDeq : (fun v => c.alive v && D v) = D := by
      funext v
      by_cases hv : D v = true
      · simp [hv, hd0 v (h2 v hv)]
      · simp [hv]
    rw [hDeq]
    intro v hv
    have := h2 v hv
    simp only [hdom0, Bool.and_eq_true, Option.isSome_iff_ne_none] at this
    exact ⟨this.1, this.2, h1 v hv⟩
  · intro v hv; simp [VSet.empty] at hv

/-- The certified set is the domain of a progress measure of the lifting player. -/
theorem certified_pm (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total) (st : LState n)
    (hlen : ∀ v x, st.measure v = some x → x.length = c.height) :
    (c.game h).IsProgressMeasure c.X (c.cod h) (certified c st).ret.toSet (lab st.measure)
      (fun v => ((evaluate c st.measure v (some (certified c st).ret)).ret.2).getD v) := by
  set D := (certified c st).ret with hD
  have hspec := certified_spec c st
  rw [← hD] at hspec
  refine ⟨fun v hv => (hspec v hv).1, fun v hv ho => ?_, fun v hv ho w hwX he => ?_⟩
  · obtain ⟨-, hne, -, hle⟩ := hspec v hv
    obtain ⟨-, h2, h3⟩ := evaluate_spec c st.measure v (some D)
    cases hev : (evaluate c st.measure v (some D)).ret.2 with
    | none => rw [h2 hev] at hle; exact absurd ((VLe.top_iff c _).1 hle) hne
    | some w =>
      obtain ⟨hws, hall, hval, -, -⟩ := h3 w hev
      simp only [hev, Option.getD_some]
      rw [hval] at hle
      obtain ⟨-, hprog⟩ := prog_progress c hc h st.measure hlen v w hne hle
      exact ⟨by simpa [allowedAt_some, VSet.toSet] using hall, (Ctx.game_edge c h v w).2 ((mem_succT c v w).1 hws).1,
        hprog⟩
  · obtain ⟨-, hne, hcons, hle⟩ := hspec v hv
    have hm : c.mine v = false := by
      cases hm : c.mine v
      · rfl
      · exact absurd ((Ctx.game_owner c h v).2 hm) (by rw [ho]; simp)
    have hws : w ∈ (succT c v).ret := (mem_succT c v w).2 ⟨(Ctx.game_edge c h v w).1 he, hwX⟩
    have hwD := hcons hm w hws
    obtain ⟨h1, -, h3⟩ := evaluate_spec c st.measure v (some D)
    cases hev : (evaluate c st.measure v (some D)).ret.2 with
    | none => exact absurd ((h1.1 hev) w hws) (by simp [allowedAt_some, hwD])
    | some w' =>
      obtain ⟨-, -, -, -, hmax⟩ := h3 w' hev
      have hle' := (hmax hm w hws (by simp [allowedAt_some, hwD])).trans hle
      exact ⟨hwD, (prog_progress c hc h st.measure hlen v w hne hle').2⟩

/-! ### The bound: the chain-tree measure of the winning region -/

/-- A chain-tree tuple as a list of `h` pairs. -/
def toL (h : ℕ) (a : ℕ → ℕ) : List (ℕ × ℕ) := (List.range h).map fun l => (a (2 * l), a (2 * l + 1))

theorem toL_length (h : ℕ) (a : ℕ → ℕ) : (toL h a).length = h := by simp [toL]

theorem tup_toL (h : ℕ) (a : ℕ → ℕ) (ha : ∀ i, 2 * h ≤ i → a i = 0) : tup (toL h a) = a := by
  funext i
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [tup_even]
    by_cases hl : l < h
    · rw [List.getD_eq_getElem _ _ (by rw [toL_length]; exact hl)]; simp [toL]
    · rw [List.getD_eq_default _ _ (by rw [toL_length]; omega), ha _ (by omega)]
  · rw [tup_odd]
    by_cases hl : l < h
    · rw [List.getD_eq_getElem _ _ (by rw [toL_length]; exact hl)]; simp [toL]
    · rw [List.getD_eq_default _ _ (by rw [toL_length]; omega), ha _ (by omega)]

/-- For a subgame of alive vertices, the chain-tree measure of the lifting player's winning
    region (Zielonka) gives a `Bound` which is proper on every vertex the player wins. -/
theorem exists_bound (c : Ctx n) (hc : c.LevelsOK) (h : c.G.Total)
    (hX : (c.G.toGame h).IsSubgame c.X) :
    ∃ (ν : Fin n → Val) (E : Fin n → Fin n → Prop), Bound c ν E ∧
      ∀ v, (c.G.toGame h).Wins c.X (toPlayer c.p) v → ν v ≠ none := by
  classical
  have hX' : (c.game h).IsSubgame c.X := (Game.forPlayer_isSubgame _ _ _).2 hX
  have hs := (c.game h).zielonkaAux_strong _ c.X rfl hX'
  have reg := hs.region .zero
  set r := (c.game h).zielonkaAux c.X with hr
  set W := r.win .zero with hW
  set σ := r.strat .zero with hσ
  have hwin : ∀ v ∈ W, (c.game h).WinsFrom c.X .zero σ v := fun v hv => reg.winsFrom hX' hv
  have hcl : ∀ v ∈ W, ∀ w, (c.game h).Step c.X .zero σ v w → w ∈ W := by
    rintro u hu w ⟨-, hwX, he, hst⟩
    cases ho : (c.game h).owner u with
    | zero => rw [hst ho]; exact (reg.mine u hu ho).1
    | one => exact reg.theirs u hu (by rw [ho]; simp) w hwX he
  obtain ⟨μc, hpm, hleaf⟩ := (c.game h).chainTreeCompleteBy c.X (c.cod h) c.nb
    (c.compNumbering h) (fun p a b => Iff.rfl) W σ hwin hcl
  have hh : (c.game h).height c.X = c.height := (height_eq c hc h).symm
  have htup : ∀ v ∈ W, tup (toL c.height (μc v)) = μc v := fun v hv =>
    tup_toL _ _ (fun i hi => (hleaf v hv).2.2.2 i (by rw [hh]; exact hi))
  let ν : Fin n → Val := fun v => if v ∈ W then some (toL c.height (μc v)) else none
  let E : Fin n → Fin n → Prop := fun v w => v ∈ W ∧ w ∈ W ∧ w ∈ c.G.succ v ∧
    c.alive w = true ∧ (c.game h).Prog (c.cod h) μc v w
  have hνW : ∀ v, ν v ≠ none ↔ v ∈ W := fun v => by
    simp only [ν]; split_ifs with hv <;> simp [hv]
  have hdep : ∀ v, (c.game h).chainDepth c.X ((c.game h).prio v) = 2 * depthOf c v := fun v => by
    unfold Game.chainDepth; rw [depthOf_eq c hc h]
  refine ⟨ν, E, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun v ⟨σ', hσ'⟩ => ?_⟩
  · intro v x hx
    simp only [ν] at hx
    split_ifs at hx
    · cases hx; exact toL_length _ _
  · intro v hv
    exact reg.sub ((hνW v).1 hv)
  · rintro v w ⟨hv, hw, hs', ha, -⟩
    exact ⟨hs', ha, (hνW v).2 hv, (hνW w).2 hw⟩
  · rintro v w ⟨hv, hw, -, -, hprog⟩ t ht hle
    simp only [ν, ite_eq_left hw] at hle
    cases t with
    | none => exact absurd hle (by simp [VLe, cmpVal])
    | some x =>
      rw [vle_some_iff c (ht x rfl) (toL_length _ _), htup w hw] at hle
      obtain ⟨hp1, hp2⟩ := hprog
      rw [Ctx.cod_le, hdep] at hp1 hp2
      obtain ⟨r, hr, hrle⟩ := prog_least c hc h v (μc w) (μc v) (hleaf v hv) hp1
        (fun hodd => hp2 (by rw [Ctx.game_prio]; exact hodd)) x (ht x rfl) hle
      simp only [ν, ite_eq_left hv, hr]
      rw [vle_some_iff c (prog_len c v _ r hr) (toL_length _ _), htup v hv]
      exact hrle _
  · intro v hv
    have hvW := (hνW v).1 hv
    cases ho : (c.game h).owner v with
    | zero =>
      obtain ⟨h1, h2, h3⟩ := hpm.2.1 v hvW ho
      exact ⟨σ v, hvW, h1, (Ctx.game_edge c h v _).1 h2, reg.sub h1, h3⟩
    | one =>
      obtain ⟨w, hwX, he⟩ := hX' v (reg.sub hvW)
      obtain ⟨h1, h2⟩ := hpm.2.2 v hvW ho w hwX he
      exact ⟨w, hvW, h1, (Ctx.game_edge c h v w).1 he, hwX, h2⟩
  · intro v w hv hm hs' ha
    have hvW := (hνW v).1 hv
    have ho : (c.game h).owner v = .one := by
      cases ho : (c.game h).owner v
      · rw [(Ctx.game_owner c h v).1 ho] at hm; cases hm
      · rfl
    obtain ⟨h1, h2⟩ := hpm.2.2 v hvW ho w ha ((Ctx.game_edge c h v w).2 hs')
    exact ⟨hvW, h1, hs', ha, h2⟩
  · intro k f hk hfk hE i hi hmax
    have := (c.game h).progCycleEven (c.cod h) μc k f hk hfk (fun j hj => (hE j hj).2.2.2.2) i hi
      (fun j hj => by rw [Ctx.game_prio, Ctx.game_prio]; exact hmax j hj)
    rwa [Ctx.game_prio] at this
  · have := (Game.forPlayer_winsFrom _ _ _ _ _).2 hσ'
    exact (hνW v).2 (by
      have hm := (c.game h).winsFrom_mem_zielonka hX' this
      rw [← hr] at hm
      exact hm)

/-! ### The initial lifter -/

theorem mkLifter_ret (G : PGame n) (alive : VSet n) (p : Bool) :
    (mkLifter G alive p).ret.2 = ⟨fun _ => some ((leftmost (mkLifter G alive p).ret.1 []).ret),
      fun _ => none, (List.finRange n).filter alive, alive, 0⟩ := rfl

theorem mkLifter_inv (G : PGame n) (alive : VSet n) (p : Bool) {ν : Fin n → Val}
    {E : Fin n → Fin n → Prop} (hB : Bound (mkLifter G alive p).ret.1 ν E) :
    LInv (mkLifter G alive p).ret.1 ν (mkLifter G alive p).ret.2 := by
  set c := (mkLifter G alive p).ret.1 with hcdef
  have halive : c.alive = alive := mkLifter_alive G alive p
  rw [mkLifter_ret]
  refine ⟨fun x y h => by simp at h, fun v hv hnq => ?_, fun v hv => ?_, fun v => ?_,
    fun v x hx => ?_⟩
  · exact absurd (List.mem_filter.2 ⟨List.mem_finRange v, by rw [← halive]; exact hv⟩) hnq
  · exact List.mem_filter.2 ⟨List.mem_finRange v, hv⟩
  · cases hν : ν v with
    | none => exact VLe.top _ _
    | some y =>
      rw [vle_some_iff c (by rw [leftmost_ret]; simp; rfl) (hB.len v y hν), leftmost_ret]
      have : tup (([] : List (ℕ × ℕ)) ++ List.replicate (c.height - ([] : List (ℕ × ℕ)).length)
          ((0 : ℕ), (0 : ℕ))) = fun _ => 0 := by
        rw [tup_pad]; funext i; unfold tup; simp
      rw [this]
      exact lexLE_zero_left _ _
  · simp only [Option.some.injEq] at hx
    rw [← hx, leftmost_ret]
    simp
    rfl

end ParityGame.TwoSidedCost

end TwoSidedCostCorrectWinProofs
