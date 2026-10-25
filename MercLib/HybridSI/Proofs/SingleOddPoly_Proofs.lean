module

public import MercLib.HybridSI.SingleOddPoly
public import MercLib.HybridSI.Proofs.SingleOdd_Proofs
public import MercLib.HybridSI.Proofs.Epoch_Proofs
public import MercLib.HybridSI.Proofs.BestResponse_Proofs

@[expose] public section HybridSISingleOddPolyProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Reduction of the iteration count to escape values (`HybridSI.SingleOddPoly`).
* `epochIterations`: every round `k < L` lies in the epoch starting at `s k`, the last epoch start
  (`0` or a round after an epoch change) at or before `k`; `EpochBound` on the trace shifted to
  `s k` gives `k - s k < n_E`, and `k ↦ (s k, k - s k)` is injective.
* `escapeCount`: the epoch changes that are not escape ties raise the escape value strictly
  (`EscapeMonotone`), so their new escape values are distinct and differ from the first one.
* `escapeClasses`: every escape value lies in the class of its cycle maximum.
* `escapeClassSplit`: with the cycle maximum `l` fixed and `B`-sum `0`, a key is determined by the
  number of steps to `l`, at most `2n` (`stepsTo_le`).
* `singleOddReduction`: `E + 1 ≤ n · (n² + 2n + 1) + n` and `n_E ≤ n`.
* `escapeCutCount`: the changes of the reward of the escape's cycle maximum (`card_changes_le`,
  monotone by MMON) and the iterations before an iteration changing some cycle maximum (P3).
* `segmentCount`: `card_le_segments`, counting the non-final changes outside the cuts by the number
  of cuts before them; changes with the same count lie in one cut-free stretch.
* `segmentReduction`: `E ≤ (n + 1) n² + n²`.
* `stretchCount`: `card_le_segments` with all rounds and the cycle-maximum changes as cuts (P3).
* `downCount`: `card_le_segments` with all rounds and the downward moves as cuts.
* `downReduction`: `L ≤ n² + n (n² + 1)`.
* `stretchReduction`: `L ≤ n(n - 1) + 2n (n(n - 1) + 1) ≤ 2 (n + 1)³`. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-- The escape value is monotone over the states of a trace. -/
theorem escape_mono {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) {u : V}
    (hu : G.owner u = .one) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ L) :
    escape G ps u j ≤ escape G ps u k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    exact (ih (by omega)).trans (escapeMonotone G bf L p ps h k (by omega) u hu)

/-- Iterations per epoch (headline). -/
theorem epochIterations (bf : ℕ) : EpochIterations G bf := by
  intro L p ps h
  set O := oddChangeRounds G L ps
  set starts := insert 0 (O.image (· + 1))
  set s : ℕ → ℕ := fun k => Nat.findGreatest (· ∈ starts) k
  have hs0 : 0 ∈ starts := Finset.mem_insert_self _ _
  have hs_mem : ∀ k, s k ∈ starts := fun k =>
    Nat.findGreatest_spec (P := (· ∈ starts)) (Nat.zero_le k) hs0
  have hs_le : ∀ k, s k ≤ k := fun k => Nat.findGreatest_le k
  -- no epoch change between the start of the epoch and `k`
  have hnone : ∀ k i, s k ≤ i → i < k → i ∉ O := by
    intro k i hi hik hO
    have hmem : i + 1 ∈ starts := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hO)
    have := Nat.le_findGreatest (P := (· ∈ starts)) (show i + 1 ≤ k by omega) hmem
    simp only [s] at hi
    omega
  have hlen : ∀ k < L, k - s k < numEven G := by
    intro k hk
    have hagree : ∀ j ≤ k - s k, ∀ u, G.owner u = .one → ps (s k + j) u = ps (s k) u := by
      intro j
      induction j with
      | zero => intros; rfl
      | succ j ih =>
        intro hj u hu
        have h1 : ps (s k + j) u = ps (s k + j + 1) u := by
          by_contra hne
          exact hnone k (s k + j) (by omega) (by omega)
            (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), u, hu, hne⟩)
        rw [show s k + (j + 1) = s k + j + 1 from rfl, ← h1]
        exact ih (by omega) u hu
    have hb := epochBound G bf (k - s k + 1) (fun j => p (s k + j)) (fun j => ps (s k + j))
      (runTrace_edge G h (s k) (by have := hs_le k; omega))
      (fun j hj => by
        have := hs_le k
        obtain ⟨qt, h1, h2⟩ := h.2.2 (s k + j) (by omega)
        exact ⟨h.2.1 _ (by omega), qt, h1, h2⟩)
      (fun j hj u hu => by have := hs_le k; simpa using hagree j (by omega) u hu)
    omega
  have hinj : Set.InjOn (fun k => (s k, k - s k)) (Finset.range L : Set ℕ) := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    have := hs_le a
    have := hs_le b
    omega
  have hmaps : ∀ k ∈ Finset.range L, (s k, k - s k) ∈ starts ×ˢ Finset.range (numEven G) := by
    intro k hk
    exact Finset.mem_product.2 ⟨hs_mem k, Finset.mem_range.2 (hlen k (Finset.mem_range.1 hk))⟩
  calc L = (Finset.range L).card := (Finset.card_range L).symm
    _ ≤ (starts ×ˢ Finset.range (numEven G)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = starts.card * numEven G := by rw [Finset.card_product, Finset.card_range]
    _ ≤ (O.card + 1) * numEven G := by
        exact Nat.mul_le_mul_right _
          ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1))

/-- Epoch changes and escape values (headline). -/
theorem escapeCount (bf : ℕ) : EscapeCount G bf := by
  intro L p ps h u hu
  set O := oddChangeRounds G L ps
  set S := O.filter fun k => ¬ escape G ps u (k + 1) = escape G ps u k
  have hOL : ∀ k ∈ O, k < L := fun k hk => by
    simpa [O, oddChangeRounds] using (Finset.mem_filter.1 hk).1
  have hlt : ∀ k ∈ S, escape G ps u k < escape G ps u (k + 1) := by
    intro k hk
    obtain ⟨hkO, hne⟩ := Finset.mem_filter.1 hk
    exact lt_of_le_of_ne (escapeMonotone G bf L p ps h k (hOL k hkO) u hu) (Ne.symm hne)
  have hSL : ∀ k ∈ S, k < L := fun k hk => hOL k (Finset.mem_filter.1 hk).1
  have hinj : Set.InjOn (fun k => escape G ps u (k + 1)) (S : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hab' | hab'
    · have := (escape_mono G h hu (show a + 1 ≤ b by omega) (hSL b hb).le).trans_lt (hlt b hb)
      exact absurd hab this.ne
    · have := (escape_mono G h hu (show b + 1 ≤ a by omega) (hSL a ha).le).trans_lt (hlt a ha)
      exact absurd hab.symm this.ne
  have h0 : escape G ps u 0 ∉ S.image fun k => escape G ps u (k + 1) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro k hk he
    exact ((escape_mono G h hu (Nat.zero_le k) (hSL k hk).le).trans_lt (hlt k hk)).ne' he
  have hsub : insert (escape G ps u 0) (S.image fun k => escape G ps u (k + 1)) ⊆
      escapeValues G L ps u := by
    intro x hx
    simp only [escapeValues, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hx ⊢
    rcases hx with rfl | ⟨k, hk, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨k + 1, by have := hSL k hk; omega, rfl⟩
  have hcard : S.card + 1 ≤ (escapeValues G L ps u).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn hinj] at this
  have hsplit : O.card = S.card + (escapeTieRounds G L ps u).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := O)
      (fun k => ¬ escape G ps u (k + 1) = escape G ps u k)]
    simp [S, escapeTieRounds, O]
  omega

/-- Escape classes (headline). -/
theorem escapeClasses : EscapeClasses V := by
  intro G L ps u
  refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_biUnion.2 ⟨cycMax (ps k) (ps k u), Finset.mem_univ _,
    Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨hk, rfl⟩, rfl⟩⟩

/-- Escape class split (headline). -/
theorem escapeClassSplit : EscapeClassSplit V := by
  intro G L ps u l
  set S := escapeClassValues G L ps u l
  rw [← Finset.card_filter_add_card_filter_not (s := S) (fun κ => keySum κ ≠ 0)]
  refine Nat.add_le_add_left ?_ _
  calc (S.filter fun κ => ¬ keySum κ ≠ 0).card
      ≤ ((Finset.range (2 * Fintype.card V + 1)).image fun s : ℕ =>
          (toLex ((if G.prio l % 2 = 0 then (rank l : ℤ) + 1 else -((rank l : ℤ) + 1)),
            toLex ((0 : ℤ), if G.prio l % 2 = 0 then -(s : ℤ) else s)) : Key)).card := by
        apply Finset.card_le_card
        intro κ hκ
        obtain ⟨hκS, h0⟩ := Finset.mem_filter.1 hκ
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hκS
        obtain ⟨-, hl⟩ := Finset.mem_filter.1 hk
        refine Finset.mem_image.2 ⟨stepsTo (ps k) (ps k u),
          Finset.mem_range.2 (by have := stepsTo_le (ps k) (ps k u); omega), ?_⟩
        simp only [not_not, keySum, escape, key, ofLex_toLex] at h0 ⊢
        rw [h0, hl]
    _ ≤ 2 * Fintype.card V + 1 := Finset.card_image_le.trans (by simp)

/-- Cuts (headline). -/
theorem escapeCutCount (bf : ℕ) : EscapeCutCount G bf := by
  intro L p ps h u hu
  set S : Finset ℤ := Finset.univ.image fun x : V => rI G .zero x
  have hScard : S.card ≤ Fintype.card V := Finset.card_image_le.trans (by simp)
  set A := (Finset.range L).filter fun k =>
    rI G .zero (cycMax (ps k) (ps k u)) ≠ rI G .zero (cycMax (ps (k + 1)) (ps (k + 1) u))
  have hA : A.card + 1 ≤ S.card :=
    card_changes_le (fun k => rI G .zero (cycMax (ps k) (ps k u))) L S
      (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (fun k hk => rI_le_of_key_le G (escapeMonotone G bf L p ps h k hk u hu))
  set B := (Finset.range L).filter fun k => k + 1 ∈ cycMaxChangeRounds L ps
  have hB : B.card ≤ (cycMaxChangeRounds L ps).card :=
    Finset.card_le_card_of_injOn (· + 1) (fun k hk => (Finset.mem_filter.1 hk).2)
      (fun a _ b _ hab => by simpa using hab)
  have hsub : escapeCutRounds L ps u ⊆ A ∪ B := by
    intro k hk
    simp only [escapeCutRounds, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkL, hk | hk⟩ := hk
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkL, fun he => hk (rI_injective he)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkL, hk⟩)
  have hC := cycleMaxChanges G bf L p ps h
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le A B
  have hn : Fintype.card V * (Fintype.card V - 1) + Fintype.card V = Fintype.card V ^ 2 := by
    cases Fintype.card V with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel]; ring
  omega

/-- At most `c` elements of `X` in every stretch without an element of `C` give at most
    `|C| + c (|C| + 1)` elements of `X`. -/
theorem card_le_segments (X C : Finset ℕ) (c : ℕ)
    (hseg : ∀ j j', (∀ k, j ≤ k → k < j' → k ∉ C) →
      (X.filter fun k => j ≤ k ∧ k < j').card ≤ c) :
    X.card ≤ C.card + c * (C.card + 1) := by
  set Y := X.filter (· ∉ C)
  have hXY : X.card ≤ C.card + Y.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := X) (· ∈ C)
    have h2 : (X.filter (· ∈ C)).card ≤ C.card :=
      Finset.card_le_card fun k hk => (Finset.mem_filter.1 hk).2
    simp only [Y]
    omega
  set f : ℕ → ℕ := fun k => (C.filter (· < k)).card
  have hfib : ∀ b ∈ Y.image f, (Y.filter fun x => f x = b).card ≤ c := by
    intro b _
    set s := Y.filter fun x => f x = b
    rcases s.eq_empty_or_nonempty with he | hne
    · rw [he]; exact Nat.zero_le _
    have hmin := s.min'_mem hne
    have hmax := s.max'_mem hne
    have hYs : ∀ x ∈ s, x ∈ X ∧ x ∉ C ∧ f x = b := fun x hx => by
      simp only [s, Y, Finset.mem_filter] at hx; exact ⟨hx.1.1, hx.1.2, hx.2⟩
    refine (Finset.card_le_card ?_).trans (hseg (s.min' hne) (s.max' hne + 1) ?_)
    · intro x hx
      exact Finset.mem_filter.2 ⟨(hYs x hx).1, s.min'_le x hx, Nat.lt_succ_of_le (s.le_max' x hx)⟩
    · intro k hjk hkj hkC
      have hkmax : k < s.max' hne := by
        rcases Nat.lt_or_ge k (s.max' hne) with h' | h'
        · exact h'
        · exact absurd (show k = s.max' hne by omega ▸ hkC) (hYs _ hmax).2.1
      have hlt : f (s.min' hne) < f (s.max' hne) := by
        refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, lt_of_lt_of_le hx.2 (s.min'_le _ hmax)⟩
        · have := hsub (Finset.mem_filter.2 ⟨hkC, hkmax⟩)
          simp only [Finset.mem_filter] at this
          omega
      rw [(hYs _ hmin).2.2, (hYs _ hmax).2.2] at hlt
      exact lt_irrefl _ hlt
  have hY := Finset.card_le_mul_card_image Y c hfib
  have himg : (Y.image f).card ≤ C.card + 1 := by
    refine (Finset.card_le_card (t := Finset.range (C.card + 1)) ?_).trans (by simp)
    intro b hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hb
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_filter_le _ _))
  calc X.card ≤ C.card + Y.card := hXY
    _ ≤ C.card + c * (C.card + 1) := by gcongr; exact hY.trans (Nat.mul_le_mul_left _ himg)

/-- Segments (headline). -/
theorem segmentCount (bf : ℕ) : SegmentCount G bf := by
  intro L p ps h u hu hs c hseg
  have hsub : oddChangeRounds G L ps ⊆ nonFinalChanges G L ps u ∪ finalChanges G L ps u := by
    intro k hk
    obtain ⟨hkL, hne⟩ := oddChange_single G h hs hk
    by_cases he : escape G ps u (k + 1) = escape G ps u L
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkL, hne, he⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkL, hne, he⟩)
  have hX := card_le_segments _ _ c hseg
  have hcut := escapeCutCount G bf L p ps h u hu
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 : c * ((escapeCutRounds L ps u).card + 1) ≤ c * Fintype.card V ^ 2 :=
    Nat.mul_le_mul_left _ hcut
  have h3 : (c + 1) * Fintype.card V ^ 2 = c * Fintype.card V ^ 2 + Fintype.card V ^ 2 := by ring
  omega

/-- Stretches (headline). -/
theorem stretchCount (bf : ℕ) : StretchCount G bf := by
  intro L p ps h c hc
  have hX := card_le_segments (Finset.range L) (cycMaxChangeRounds L ps) c hc
  have hC := cycleMaxChanges G bf L p ps h
  rw [Finset.card_range] at hX
  calc L ≤ (cycMaxChangeRounds L ps).card + c * ((cycMaxChangeRounds L ps).card + 1) := hX
    _ ≤ _ := by gcongr

/-- Downward moves (headline). -/
theorem downCount (bf : ℕ) : DownCount G bf := by
  intro L p ps h u c hc
  have hX := card_le_segments (Finset.range L) (downRounds G bf L ps u) c hc
  rwa [Finset.card_range] at hX

/-- The reduction of `SingleOddPoly` to `DownConjecture` (headline). -/
theorem downReduction : DownReduction := by
  intro hc n G _ hG u hu hs L p ps h
  obtain ⟨hb, hd⟩ := hc n G _ hG u hu hs L p ps h
  have hL := downCount G _ L p ps h u n hb
  have h1 : n * ((downRounds G (hbFuel (Fin n)) L ps u).card + 1) ≤ n * (n ^ 2 + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : n ^ 2 + n * (n ^ 2 + 1) ≤ (n + 1) ^ 4 := by nlinarith [Nat.zero_le n, sq_nonneg n]
  omega

/-- The reduction of `SingleOddPoly` to `StretchConjecture` (headline). -/
theorem stretchReduction : StretchReduction := by
  intro hc n G _ hG u hu hs L p ps h
  have hL := stretchCount G _ L p ps h (2 * n) (hc n G _ hG u hu hs L p ps h)
  simp only [Fintype.card_fin] at hL
  refine hL.trans ?_
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le m, sq_nonneg m]

/-- The reduction of `SingleOddPoly` to `SegmentConjecture` (headline). -/
theorem segmentReduction : SegmentReduction := by
  intro hc n G _ hG u hu hs L p ps h
  obtain ⟨hseg, hfin⟩ := hc n G _ hG u hu hs L p ps h
  have hE := segmentCount G _ L p ps h u hu hs n hseg
  simp only [Fintype.card_fin] at hE
  have hev : numEven G ≤ n :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hit := epochIterations G _ L p ps h
  have hE' : (oddChangeRounds G L ps).card + 1 ≤ (n + 1) * n ^ 2 + n ^ 2 + 1 := by omega
  calc L ≤ ((oddChangeRounds G L ps).card + 1) * numEven G := hit
    _ ≤ ((n + 1) * n ^ 2 + n ^ 2 + 1) * n := Nat.mul_le_mul hE' hev
    _ ≤ (n + 1) ^ 4 := by nlinarith [Nat.zero_le n]

/-- The reduction of `SingleOddPoly` to `SingleOddEscapeConjecture` (headline). -/
theorem singleOddReduction : SingleOddReduction := by
  intro hc n G _ hG u hu hs L p ps h
  obtain ⟨hcls, hties⟩ := hc n G _ hG u hu hs L p ps h
  have hE := escapeCount G _ L p ps h u hu
  have hval : (escapeValues G L ps u).card ≤ n * (n ^ 2 + (2 * n + 1)) := by
    refine (escapeClasses G L ps u).trans ?_
    refine (Finset.sum_le_sum fun l _ => (escapeClassSplit G L ps u l).trans
      (Nat.add_le_add (hcls l) (le_of_eq (by simp) : 2 * Fintype.card (Fin n) + 1 ≤ 2 * n + 1))).trans ?_
    simp
  have hev : numEven G ≤ n :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hit := epochIterations G _ L p ps h
  have hE' : (oddChangeRounds G L ps).card + 1 ≤ n * (n ^ 2 + (2 * n + 1)) + n := by omega
  calc L ≤ ((oddChangeRounds G L ps).card + 1) * numEven G := hit
    _ ≤ (n * (n ^ 2 + (2 * n + 1)) + n) * n := Nat.mul_le_mul hE' hev
    _ ≤ (n + 1) ^ 4 := by nlinarith [Nat.zero_le n]

end MercLib.HybridSI

end HybridSISingleOddPolyProofs
