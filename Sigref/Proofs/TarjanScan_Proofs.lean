import Sigref.Tarjan

/-!
# Proofs: the primitives of the Tarjan model (`scan`, `popComp`, `finish`, `initNode`)

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

namespace Sigref.Tarjan

open Relation

variable {n : ℕ}

/-- What `scan` does: it consumes a prefix `tc` of the transitions, stops at the first hidden target
that is unvisited (the child), and only lowers `low s` and marks the child. -/
structure ScanRes (g : Graph n) (s : Fin n) (ts : List (Bool × Fin n)) (idx : ℕ) (c : Ctx n)
    (ch : Option (Fin n)) (idx' : ℕ) (c' : Ctx n) : Prop where
  consumed : ∃ tc tr : List (Bool × Fin n), ts = tc ++ tr ∧ idx' = idx + tc.length ∧
    (ch = none → tr = []) ∧
    (∀ v, ch = some v → ∃ pre, tc = pre ++ [(true, v)]) ∧
    (∀ w, (true, w) ∈ tc → c'.disc w ≠ g.unv ∧ (c'.onSt w = true → c'.low s ≤ c'.disc w)) ∧
    (c'.low s = c.low s ∨ ∃ w, (true, w) ∈ tc ∧ c.onSt w = true ∧ c.disc w ≠ g.unv ∧
      c'.low s = c.disc w)
  work : c'.work = c.work
  stk : c'.stk = c.stk
  onSt : c'.onSt = c.onSt
  time : c'.time = c.time
  eq : c'.eq = c.eq
  blk : c'.blk = c.blk
  ri : c'.ri = c.ri
  low_ne : ∀ v, v ≠ s → c'.low v = c.low v
  low_le : c'.low s ≤ c.low s
  disc_ne : ∀ v, ch ≠ some v → c'.disc v = c.disc v
  child : ∀ v, ch = some v → c.disc v = g.unv ∧ c'.disc v = 0

theorem scan_spec (g : Graph n) (s : Fin n) :
    ∀ (ts : List (Bool × Fin n)) (idx : ℕ) (c : Ctx n),
      (∀ v, c.disc v = g.unv → c.onSt v = false) →
      ScanRes g s ts idx c (scan g s ts idx c).1 (scan g s ts idx c).2.1 (scan g s ts idx c).2.2 := by
  intro ts
  induction ts with
  | nil =>
    intro idx c _
    refine ⟨⟨[], [], by simp, by simp [scan], by simp [scan], by simp [scan], by simp, ?_⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, le_rfl, fun _ _ => rfl, ?_⟩
    · simp [scan]
    · intro v hv; simp [scan] at hv
  | cons e ts ih =>
    obtain ⟨h, v⟩ := e
    intro idx c hon
    cases h with
    | false =>
      have hih := ih (idx + 1) c hon
      simp only [scan, Bool.false_eq_true, if_false]
      obtain ⟨tc, tr, h1, h2, h3, h4, h5, h6⟩ := hih.consumed
      refine ⟨⟨(false, v) :: tc, tr, by simp [h1], by simp [h2]; omega, h3, ?_, ?_, ?_⟩,
        hih.work, hih.stk, hih.onSt, hih.time, hih.eq, hih.blk, hih.ri, hih.low_ne, hih.low_le,
        hih.disc_ne, hih.child⟩
      · intro w hw
        obtain ⟨pre, hpre⟩ := h4 w hw
        exact ⟨(false, v) :: pre, by simp [hpre]⟩
      · intro w hw
        apply h5
        simpa using hw
      · rcases h6 with h6 | ⟨w, hw, hw2⟩
        · exact Or.inl h6
        · exact Or.inr ⟨w, by simp [hw], hw2⟩
    | true =>
      have hunv0 : (0 : ℕ) ≠ g.unv := by have := g.unv_gt; omega
      by_cases hd : c.disc v = g.unv
      · simp only [scan, if_true, hd]
        refine ⟨⟨[(true, v)], ts, by simp, by simp, by simp, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ _ => rfl, le_rfl, ?_, ?_⟩
        · intro w hw
          have : v = w := Option.some.inj hw
          subst this
          exact ⟨[], rfl⟩
        · intro w hw
          have hw' : w = v := by simpa using hw
          subst hw'
          simp [hon w hd, hunv0]
        · exact Or.inl rfl
        · intro w hw
          have hwv : w ≠ v := fun h => hw (by rw [h])
          simp [Function.update_of_ne hwv]
        · intro w hw
          have : v = w := Option.some.inj hw
          subst this
          exact ⟨hd, by simp⟩
      · by_cases hc : c.onSt v = true ∧ c.disc v < c.low s
        · have hcond : (c.onSt v && decide (c.disc v < c.low s)) = true := by simp [hc.1, hc.2]
          simp only [scan, if_true, hd, if_false, hcond]
          set c1 : Ctx n := { c with low := Function.update c.low s (c.disc v) } with hc1
          have hih := ih (idx + 1) c1 (fun w hw => hon w hw)
          obtain ⟨tc, tr, h1, h2, h3, h4, h5, h6⟩ := hih.consumed
          have hvnc : ∀ w, (scan g s ts (idx + 1) c1).1 = some w → w ≠ v := by
            intro w hw hwv
            subst hwv
            exact hd (hih.child w hw).1
          refine ⟨⟨(true, v) :: tc, tr, by simp [h1], by simp [h2]; omega, h3, ?_, ?_, ?_⟩,
            hih.work, hih.stk, hih.onSt, hih.time, hih.eq, hih.blk, hih.ri, ?_, ?_, ?_, ?_⟩
          · intro w hw
            obtain ⟨pre, hpre⟩ := h4 w hw
            exact ⟨(true, v) :: pre, by simp [hpre]⟩
          · intro w hw
            rcases List.mem_cons.mp hw with hw | hw
            · have hwv : w = v := by simpa using hw
              subst hwv
              have hdisc : (scan g s ts (idx + 1) c1).2.2.disc w = c.disc w :=
                hih.disc_ne w (fun h => hvnc w h rfl)
              refine ⟨by rw [hdisc]; exact hd, fun _ => ?_⟩
              have := hih.low_le
              rw [hdisc]
              simpa [hc1] using this
            · exact h5 w hw
          · rcases h6 with h6 | ⟨w, hw, hw2, hw3, hw4⟩
            · right
              refine ⟨v, by simp, hc.1, hd, ?_⟩
              simpa [hc1] using h6
            · right
              exact ⟨w, by simp [hw], hw2, hw3, hw4⟩
          · intro w hw
            have := hih.low_ne w hw
            simpa [hc1, Function.update_of_ne hw] using this
          · have := hih.low_le
            simp only [hc1, Function.update_self] at this
            exact this.trans hc.2.le
          · intro w hw
            exact hih.disc_ne w hw
          · intro w hw
            exact hih.child w hw
        · have hcond : ¬ ((c.onSt v && decide (c.disc v < c.low s)) = true) := by
            intro h; apply hc; simpa using h
          simp only [scan, if_true, hd, if_false, hcond, Bool.false_eq_true]
          have hih := ih (idx + 1) c hon
          obtain ⟨tc, tr, h1, h2, h3, h4, h5, h6⟩ := hih.consumed
          have hvnc : ∀ w, (scan g s ts (idx + 1) c).1 = some w → w ≠ v := by
            intro w hw hwv
            subst hwv
            exact hd (hih.child w hw).1
          refine ⟨⟨(true, v) :: tc, tr, by simp [h1], by simp [h2]; omega, h3, ?_, ?_, ?_⟩,
            hih.work, hih.stk, hih.onSt, hih.time, hih.eq, hih.blk, hih.ri, hih.low_ne, hih.low_le,
            hih.disc_ne, hih.child⟩
          · intro w hw
            obtain ⟨pre, hpre⟩ := h4 w hw
            exact ⟨(true, v) :: pre, by simp [hpre]⟩
          · intro w hw
            rcases List.mem_cons.mp hw with hw | hw
            · have hwv : w = v := by simpa using hw
              subst hwv
              have hdisc : (scan g s ts (idx + 1) c).2.2.disc w = c.disc w :=
                hih.disc_ne w (fun h => hvnc w h rfl)
              refine ⟨by rw [hdisc]; exact hd, fun hon' => ?_⟩
              rw [hdisc]
              have honv : c.onSt w = true := by rw [← hih.onSt]; exact hon'
              by_contra hlt
              apply hc
              refine ⟨honv, ?_⟩
              have := hih.low_le
              omega
            · exact h5 w hw
          · rcases h6 with h6 | ⟨w, hw, hw2⟩
            · exact Or.inl h6
            · exact Or.inr ⟨w, by simp [hw], hw2⟩

theorem popComp_spec (s : Fin n) (e : ℕ) :
    ∀ (stk : List (Fin n)) (onSt : Fin n → Bool) (blk : Fin n → ℕ), s ∈ stk →
      ∃ top rest : List (Fin n), stk = top ++ s :: rest ∧ s ∉ top ∧
        ∃ onSt' blk', popComp s e stk onSt blk = some (rest, onSt', blk') ∧
          (∀ u, onSt' u = if u ∈ top ++ [s] then false else onSt u) ∧
          (∀ u, blk' u = if u ∈ top ++ [s] then e else blk u) := by
  intro stk
  induction stk with
  | nil => intro _ _ h; simp at h
  | cons u rest ih =>
    intro onSt blk hs
    by_cases hu : u = s
    · subst hu
      refine ⟨[], rest, by simp, by simp, Function.update onSt u false, Function.update blk u e,
        by simp [popComp], ?_, ?_⟩
      · intro w; by_cases hw : w = u <;> simp [hw]
      · intro w; by_cases hw : w = u <;> simp [hw]
    · have hs' : s ∈ rest := by
        rcases List.mem_cons.mp hs with h | h
        · exact absurd h.symm hu
        · exact h
      obtain ⟨top, rest', h1, h2, onSt', blk', h3, h4, h5⟩ :=
        ih (Function.update onSt u false) (Function.update blk u e) hs'
      refine ⟨u :: top, rest', by simp [h1], ?_, onSt', blk', ?_, ?_, ?_⟩
      · simp [h2, Ne.symm hu]
      · simp only [popComp, hu, if_false]; exact h3
      · intro w
        rw [h4 w]
        by_cases hw : w = u
        · subst hw; simp
        · by_cases hw2 : w ∈ top ++ [s] <;> simp [hw, hw2]
      · intro w
        rw [h5 w]
        by_cases hw : w = u
        · subst hw; simp
        · by_cases hw2 : w ∈ top ++ [s] <;> simp [hw, hw2]

theorem popComp_none (s : Fin n) (e : ℕ) :
    ∀ (stk : List (Fin n)) (onSt : Fin n → Bool) (blk : Fin n → ℕ), s ∉ stk →
      popComp s e stk onSt blk = none := by
  intro stk
  induction stk with
  | nil => intro _ _ _; rfl
  | cons u rest ih =>
    intro onSt blk hs
    have hu : u ≠ s := fun h => hs (by simp [h])
    simp only [popComp, hu, if_false]
    exact ih _ _ (fun h => hs (List.mem_cons_of_mem _ h))

end Sigref.Tarjan
