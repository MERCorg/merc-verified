module

public import MercLib.HybridSI.Proofs.SingleOddStretch_Proofs
public import MercLib.HybridSI.Proofs.SingleOddPoly_Proofs
public import MercLib.HybridSI.Proofs.Bounds_Proofs

@[expose] public section HybridSISingleOddStretchDRProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Theorem DR of `ST_DEC.md` (`HybridSI.SingleOddStretch`).
* `stepsTo_lt_card`: the vertices `f^[i] x`, `i ≤ stepsTo f x`, are distinct (a repetition makes
  the play periodic from there on, and the cycle maximum would be hit earlier), so
  `stepsTo f x < n`.
* `decisive_le_iff`, `decisive_eq_bot`, `decisive_eq_coe`: the decisive element and `DecisiveLe`.
* `run_bound`: a piece `a ≤ k < b` of a stretch without rises. `dec` is non-increasing on it
  (`decisive_antitone`); the iterations with `dec = x` lie in the suffix from the first of them,
  on which `DecisiveLe x` holds, so P4 bounds them by `n` (`decisive_count`). The silent
  iterations lie in the suffix from the first of them, with fixed cycle maxima and `B`-sets; the
  key of `v` changes there only in its length component (`key_le_of_same`, `key_ne_of_same`),
  monotonically (P2) and with at most `n` values (`stepsTo_lt_card`), so at most `n - 1` times
  (`silent_count`). The remaining silent iterations keep all keys and are escape ties (SK) or the
  last iteration `L - 1`.
* `decisiveStretch` (DR): strong induction on `j'`, cutting at the last rise.
* `decisiveStretchBound`, `decisiveIterations`, `riseReduction`: `StretchCount` and arithmetic. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The play from `x` reaches its cycle maximum within `n - 1` steps. -/
theorem stepsTo_lt_card (f : V → V) (x : V) : stepsTo f x < Fintype.card V := by
  have key : ∀ i j : ℕ, i < j → j ≤ stepsTo f x → f^[i] x = f^[j] x → False := by
    intro i j hij hj e
    have hc : IsPeriodicPt f (j - i) (f^[i] x) := by
      show f^[j - i] (f^[i] x) = f^[i] x
      rw [← iterate_add_apply, show j - i + i = j by omega, e]
    obtain ⟨N, hN, eN⟩ := recurs_cycMax (f := f) x i
    have he : f^[(N - i) % (j - i) + i] x = cycMax f x := by
      rw [iterate_add_apply, hc.iterate_mod_apply, ← iterate_add_apply,
        show N - i + i = N by omega, eN]
    have hlt := Nat.mod_lt (N - i) (show 0 < j - i by omega)
    exact (stepsTo_spec (f := f) x).2 _ (by omega) he
  have hinj : Injective (fun i : Fin (stepsTo f x + 1) => f^[i] x) := by
    intro a b hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact key a b h (by omega) hab
    · exact key b a h (by omega) hab.symm
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at this
  omega

theorem decisive_le_iff {ps : ℕ → V → V} {k : ℕ} {x : V} :
    decisive ps k ≤ x ↔ DecisiveLe ps k x := by
  constructor
  · intro h v y hxy
    by_contra hne
    have hy : y ∈ Finset.univ.biUnion fun v => symmDiff (bSet (ps k) v) (bSet (ps (k + 1)) v) := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_symmDiff]
      exact ⟨v, by tauto⟩
    have := (Finset.le_max hy).trans h
    exact absurd (WithBot.coe_le_coe.1 this) (not_le.2 hxy)
  · intro h
    apply Finset.max_le
    intro y hy
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_symmDiff] at hy
    obtain ⟨v, hv⟩ := hy
    by_contra hlt
    have := h v y (lt_of_not_ge fun h' => hlt (WithBot.coe_le_coe.2 h'))
    tauto

theorem decisive_eq_bot {ps : ℕ → V → V} {k : ℕ} (h : decisive ps k = ⊥) (v : V) :
    bSet (ps k) v = bSet (ps (k + 1)) v := by
  rw [decisive, Finset.max_eq_bot] at h
  ext y
  by_contra hne
  have hy : y ∈ Finset.univ.biUnion fun v => symmDiff (bSet (ps k) v) (bSet (ps (k + 1)) v) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_symmDiff]
    exact ⟨v, by tauto⟩
  rw [h] at hy
  simp at hy

theorem decisive_eq_coe {ps : ℕ → V → V} {k : ℕ} {x : V} (h : decisive ps k = x) :
    ∃ v, ¬ (x ∈ bSet (ps k) v ↔ x ∈ bSet (ps (k + 1)) v) := by
  have hx := Finset.mem_of_max h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_symmDiff] at hx
  obtain ⟨v, hv⟩ := hx
  exact ⟨v, by tauto⟩

theorem decisive_antitone {ps : ℕ → V → V} {a b : ℕ}
    (hnr : ∀ k, a < k → k < b → ¬ decisive ps (k - 1) < decisive ps k) :
    ∀ k₁ k₂, a ≤ k₁ → k₁ ≤ k₂ → k₂ < b → decisive ps k₂ ≤ decisive ps k₁ := by
  intro k₁ k₂ h1 h12 h2
  induction k₂, h12 using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have := not_lt.1 (hnr (k + 1) (by omega) h2)
    simp only [Nat.add_sub_cancel] at this
    exact this.trans (ih (by omega))

variable (G : Game V) [DecidableRel G.edge]

theorem key_le_of_same {f g : V → V} {v : V} (hl : cycMax f v = cycMax g v)
    (hb : bSet f v = bSet g v) (h : key G f v ≤ key G g v) :
    (ofLex (ofLex (key G f v)).2).2 ≤ (ofLex (ofLex (key G g v)).2).2 := by
  simp only [key, hl, hb, ofLex_toLex, Prod.Lex.toLex_le_toLex, lt_self_iff_false, true_and,
    false_or] at h ⊢
  exact h

theorem key_ne_of_same {f g : V → V} {v : V} (hl : cycMax f v = cycMax g v)
    (hb : bSet f v = bSet g v) (h : key G f v ≠ key G g v) :
    (ofLex (ofLex (key G f v)).2).2 ≠ (ofLex (ofLex (key G g v)).2).2 := by
  intro he
  apply h
  simp only [key, hl, hb, ofLex_toLex] at he ⊢
  rw [he]

theorem decisive_count {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) {a b : ℕ}
    (hb : b ≤ L) (hst : ∀ k, a ≤ k → k < b → LStable ps k)
    (hnr : ∀ k, a < k → k < b → ¬ decisive ps (k - 1) < decisive ps k) (x : V) :
    ((Finset.Ico a b).filter fun k => decisive ps k = x).card ≤ Fintype.card V := by
  set T := (Finset.Ico a b).filter fun k => decisive ps k = x
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  have hm := Finset.mem_filter.1 (T.min'_mem hne)
  rw [Finset.mem_Ico] at hm
  refine (Finset.card_le_card ?_).trans (decisiveRounds G bf L p ps h (T.min' hne) b x hb
    (fun k h1 h2 => hst k (by omega) h2) (fun k h1 h2 => decisive_le_iff.1 ?_))
  · intro k hk
    have hkT := hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    rw [Finset.mem_Ico] at hk1
    exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨T.min'_le k hkT, hk1.2⟩, decisive_eq_coe hk2⟩
  · rw [← hm.2]; exact decisive_antitone hnr _ _ hm.1.1 h1 h2

theorem silent_count {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) {a b : ℕ}
    (hb : b ≤ L) (hst : ∀ k, a ≤ k → k < b → LStable ps k)
    (hnr : ∀ k, a < k → k < b → ¬ decisive ps (k - 1) < decisive ps k) (v : V) :
    ((Finset.Ico a b).filter fun k =>
      decisive ps k = ⊥ ∧ key G (ps k) v ≠ key G (ps (k + 1)) v).card ≤ Fintype.card V - 1 := by
  set W := (Finset.Ico a b).filter fun k =>
    decisive ps k = ⊥ ∧ key G (ps k) v ≠ key G (ps (k + 1)) v
  set T := (Finset.Ico a b).filter fun k => decisive ps k = ⊥
  have hWT : W ⊆ T := fun k hk => by
    simp only [W, T, Finset.mem_filter] at hk ⊢; exact ⟨hk.1, hk.2.1⟩
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.subset_empty] at hWT; rw [hWT]; simp
  set m := T.min' hne
  have hm := Finset.mem_filter.1 (T.min'_mem hne)
  rw [Finset.mem_Ico] at hm
  have hsil : ∀ k, m ≤ k → k < b → decisive ps k = ⊥ := fun k h1 h2 =>
    le_bot_iff.1 (hm.2 ▸ decisive_antitone hnr m k hm.1.1 h1 h2)
  have hconst : ∀ i, m + i ≤ b →
      cycMax (ps (m + i)) v = cycMax (ps m) v ∧ bSet (ps (m + i)) v = bSet (ps m) v := by
    intro i
    induction i with
    | zero => intro; simp
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [← add_assoc]
      exact ⟨(hst (m + i) (by omega) (by omega) v).symm.trans h1,
        (decisive_eq_bot (hsil (m + i) (by omega) (by omega)) v).symm.trans h2⟩
  set l := cycMax (ps m) v
  set r : ℕ → ℤ := fun i => (ofLex (ofLex (key G (ps (m + i)) v)).2).2
  set S : Finset ℤ := (Finset.range (Fintype.card V)).image fun s : ℕ =>
    if G.prio l % 2 = 0 then -(s : ℤ) else s
  have hS : ∀ i ≤ b - m, r i ∈ S := by
    intro i hi
    have hl := (hconst i (by omega)).1
    refine Finset.mem_image.2 ⟨stepsTo (ps (m + i)) v,
      Finset.mem_range.2 (stepsTo_lt_card _ _), ?_⟩
    simp only [r, key, ofLex_toLex, hl, l]
  have hmono : ∀ i < b - m, r i ≤ r (i + 1) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hconst i (by omega)
    obtain ⟨h1', h2'⟩ := hconst (i + 1) (by omega)
    exact key_le_of_same G (h1.trans h1'.symm) (h2.trans h2'.symm)
      (valuationMonotone G bf L p ps h (m + i) (m + (i + 1)) (by omega) (by omega) v)
  have hch := card_changes_le r (b - m) S hS hmono
  have hScard : S.card ≤ Fintype.card V := Finset.card_image_le.trans (by simp)
  have hsub : W ⊆ ((Finset.range (b - m)).filter fun i => r i ≠ r (i + 1)).image (m + ·) := by
    intro k hk
    have hkT := hWT hk
    have hmk : m ≤ k := T.min'_le k hkT
    obtain ⟨hk1, -, hk3⟩ := by simpa only [W, Finset.mem_filter, Finset.mem_Ico] using hk
    refine Finset.mem_image.2 ⟨k - m, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩,
      Nat.add_sub_cancel' hmk⟩
    obtain ⟨h1, h2⟩ := hconst (k - m) (by omega)
    obtain ⟨h1', h2'⟩ := hconst (k - m + 1) (by omega)
    have e1 : m + (k - m) = k := by omega
    have e2 : m + (k - m + 1) = k + 1 := by omega
    simp only [r, e1, e2]
    rw [e1] at h1 h2
    rw [e2] at h1' h2'
    exact key_ne_of_same G (h1.trans h1'.symm) (h2.trans h2'.symm) hk3
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

theorem mul_two_sub (n : ℕ) : n * n + n * (n - 1) = n * (2 * n - 1) := by
  rcases n with _ | n
  · simp
  · rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.add_sub_cancel]; ring

/-- One piece of a stretch without rises. -/
theorem run_bound (hrel : G.Relabelled) {bf L : ℕ} {p ps : ℕ → V → V}
    (h : RunTrace G bf L p ps) (u : V) (hu : G.owner u = .one) {a b : ℕ} (hb : b ≤ L)
    (hst : ∀ k, a ≤ k → k < b → LStable ps k)
    (hnr : ∀ k, a < k → k < b → ¬ decisive ps (k - 1) < decisive ps k) :
    b - a ≤ Fintype.card V * (2 * Fintype.card V - 1) +
      ((escapeTieRounds G L ps u).filter fun k => a ≤ k ∧ k < b).card +
        (if b < L then 0 else 1) := by
  set N := (Finset.Ico a b).filter fun k => decisive ps k ≠ ⊥
  set S1 := (Finset.Ico a b).filter fun k =>
    decisive ps k = ⊥ ∧ key G (ps k) ≠ key G (ps (k + 1))
  set S2 := (Finset.Ico a b).filter fun k =>
    decisive ps k = ⊥ ∧ key G (ps k) = key G (ps (k + 1))
  set TF := (escapeTieRounds G L ps u).filter fun k => a ≤ k ∧ k < b
  have hN : N.card ≤ Fintype.card V * Fintype.card V := by
    have hsub : N ⊆ Finset.univ.biUnion fun x : V =>
        (Finset.Ico a b).filter fun k => decisive ps k = x := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
      obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.1 hk2
      exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Finset.mem_filter.2 ⟨hk1, hx.symm⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum fun x _ => decisive_count G h hb hst hnr x).trans ?_
    simp
  have hS1 : S1.card ≤ Fintype.card V * (Fintype.card V - 1) := by
    have hsub : S1 ⊆ Finset.univ.biUnion fun v : V => (Finset.Ico a b).filter fun k =>
        decisive ps k = ⊥ ∧ key G (ps k) v ≠ key G (ps (k + 1)) v := by
      intro k hk
      obtain ⟨hk1, hk2, hk3⟩ := Finset.mem_filter.1 hk
      obtain ⟨v, hv⟩ := Function.ne_iff.1 hk3
      exact Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, Finset.mem_filter.2 ⟨hk1, hk2, hv⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum fun v _ => silent_count G h hb hst hnr v).trans ?_
    simp
  have hS2 : S2.card ≤ TF.card + (if b < L then 0 else 1) := by
    set E := (Finset.Ico a b).filter fun k => k + 1 = L
    have hsub : S2 ⊆ TF ∪ E := by
      intro k hk
      obtain ⟨hk1, -, hk3⟩ := Finset.mem_filter.1 hk
      rw [Finset.mem_Ico] at hk1
      by_cases hkL : k + 1 < L
      · exact Finset.mem_union_left _ (Finset.mem_filter.2
          ⟨(sameKeysTie G bf hrel L p ps h k hkL hk3 u hu).1, hk1⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 hk1, by omega⟩)
    have hE : E.card ≤ (if b < L then 0 else 1) := by
      split_ifs with hbL
      · refine le_of_eq (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun k hk => ?_))
        rw [Finset.mem_Ico] at hk; omega
      · refine (Finset.card_le_card (t := {L - 1}) fun k hk => ?_).trans (by simp)
        simp only [E, Finset.mem_filter] at hk
        simp only [Finset.mem_singleton]; omega
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  have hall : Finset.Ico a b ⊆ N ∪ S1 ∪ S2 := by
    intro k hk
    simp only [N, S1, S2, Finset.mem_union, Finset.mem_filter]
    by_cases h1 : decisive ps k = ⊥ <;> by_cases h2 : key G (ps k) = key G (ps (k + 1)) <;>
      tauto
  have hc := (Finset.card_le_card hall).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [Nat.card_Ico] at hc
  have := mul_two_sub (Fintype.card V)
  omega

theorem decisiveStretch_aux (hrel : G.Relabelled) {bf L : ℕ} {p ps : ℕ → V → V}
    (h : RunTrace G bf L p ps) (u : V) (hu : G.owner u = .one) (j : ℕ) :
    ∀ j', j ≤ j' → j' ≤ L → (∀ k, j ≤ k → k < j' → LStable ps k) →
      j' - j ≤ ((riseRounds ps j j').card + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) +
        ((escapeTieRounds G L ps u).filter fun k => j ≤ k ∧ k < j').card +
          (if j' < L then 0 else 1) := by
  intro j'
  induction j' using Nat.strong_induction_on with
  | _ j' ih =>
  intro hjj hj' hst
  by_cases hR : riseRounds ps j j' = ∅
  · rw [hR, Finset.card_empty, zero_add, one_mul]
    refine run_bound G hrel h u hu hj' hst fun k h1 h2 hlt => ?_
    have : k ∈ riseRounds ps j j' := Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨h1, h2⟩, hlt⟩
    rw [hR] at this
    simp at this
  have hne := Finset.nonempty_iff_ne_empty.2 hR
  set R := riseRounds ps j j'
  set r := R.max' hne
  have hr := Finset.max'_mem R hne
  have hrj : j < r ∧ r < j' := by
    have hmem := (Finset.mem_filter.1 hr).1
    rw [Finset.mem_Ioo] at hmem
    exact hmem
  have h1 := ih r hrj.2 hrj.1.le (by omega) fun k h1 h2 => hst k h1 (by omega)
  have h2 := run_bound G hrel h u hu (a := r) (b := j') hj' (fun k h1 h2 => hst k (by omega) h2)
    fun k h1 h2 hlt => absurd (R.le_max' k (Finset.mem_filter.2
      ⟨Finset.mem_Ioo.2 ⟨by omega, h2⟩, hlt⟩)) (by omega)
  have hRs : (riseRounds ps j r).card + 1 ≤ R.card := by
    have hsub : insert r (riseRounds ps j r) ⊆ R := by
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact hr
      · simp only [riseRounds, Finset.mem_filter, Finset.mem_Ioo] at hk
        exact Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨hk.1.1, by omega⟩, hk.2⟩
    have hnot : r ∉ riseRounds ps j r := by simp [riseRounds]
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem hnot] at this
  have hT : ((escapeTieRounds G L ps u).filter fun k => j ≤ k ∧ k < r).card +
      ((escapeTieRounds G L ps u).filter fun k => r ≤ k ∧ k < j').card =
      ((escapeTieRounds G L ps u).filter fun k => j ≤ k ∧ k < j').card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun k _ h1 h2 => by omega)]
    congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hk, h1⟩ | ⟨hk, h1⟩) <;> exact ⟨hk, by omega⟩
    · rintro ⟨hk, h1⟩
      by_cases hkr : k < r
      · exact Or.inl ⟨hk, by omega⟩
      · exact Or.inr ⟨hk, by omega⟩
  simp only [show r < L by omega, ↓reduceIte] at h1
  have hmul : ((riseRounds ps j r).card + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) +
      Fintype.card V * (2 * Fintype.card V - 1) ≤
      (R.card + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- Theorem DR (headline). -/
theorem decisiveStretch (bf : ℕ) : DecisiveStretch G bf := by
  intro hrel L p ps h u hu j j' hj' hst
  rcases Nat.lt_or_ge j' j with hlt | hle
  · omega
  have := decisiveStretch_aux G hrel h u hu j j' hle hj' hst
  split_ifs at this <;> omega

/-- Uniform DR (headline). -/
theorem decisiveStretchBound (bf : ℕ) : DecisiveStretchBound G bf := by
  intro hrel L p ps h u hu r t hr ht j j' hcut
  set j'' := min j' L
  have heq : ((Finset.range L).filter fun k => j ≤ k ∧ k < j') = Finset.Ico j j'' := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, j'']
    omega
  rw [heq, Nat.card_Ico]
  have hst : ∀ k, j ≤ k → k < j'' → LStable ps k := by
    intro k h1 h2 v
    have hk := hcut k h1 (by omega)
    simp only [cycMaxChangeRounds, Finset.mem_filter, Finset.mem_range, not_and, not_exists,
      not_not] at hk
    exact hk (by omega) v
  have hD := decisiveStretch G bf hrel L p ps h u hu j j'' (by omega) hst
  have hR := hr j j'' (by omega) hst
  have hT : ((escapeTieRounds G L ps u).filter fun k => j ≤ k ∧ k < j'').card ≤ t :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans ht
  have hmul : ((riseRounds ps j j'').card + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) ≤
      (r + 1) * (Fintype.card V * (2 * Fintype.card V - 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Iterations from rises and ties (headline). -/
theorem decisiveIterations (bf : ℕ) : DecisiveIterations G bf := by
  intro hrel L p ps h u hu r t hr ht
  exact stretchCount G bf L p ps h _ (decisiveStretchBound G bf hrel L p ps h u hu r t hr ht)

/-- The reduction of `SingleOddRisePoly` to `RiseConjecture` (headline). -/
theorem riseReduction : RiseReduction := by
  intro hc n G _ hG u hu hs L p ps h
  obtain ⟨hr, ht⟩ := hc n G _ hG u hu hs L p ps h
  have hL := decisiveIterations G _ hG L p ps h u hu n n hr ht
  simp only [Fintype.card_fin] at hL
  refine hL.trans ?_
  rcases n with _ | m
  · simp
  · rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, Nat.add_sub_cancel]
    ring_nf; nlinarith [Nat.zero_le m, pow_pos (Nat.succ_pos m) 2]

end MercLib.HybridSI

end HybridSISingleOddStretchDRProofs
