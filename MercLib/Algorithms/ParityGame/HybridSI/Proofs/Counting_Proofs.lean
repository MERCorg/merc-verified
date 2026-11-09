module

public import MercLib.Algorithms.ParityGame.HybridSI.Counting
public import MercLib.Algorithms.ParityGame.HybridSI.Proofs.Epoch_Proofs
public import MercLib.Algorithms.ParityGame.HybridSI.Proofs.Potential_Proofs
import all MercLib.Algorithms.ParityGame.HybridSI.Proofs.Correctness_Proofs
import all MercLib.Algorithms.ParityGame.HybridSI.Proofs.Epoch_Proofs
import all MercLib.Algorithms.ParityGame.HybridSI.Proofs.Filter_Proofs
import all MercLib.Algorithms.ParityGame.HybridSI.Proofs.Improvement_Proofs
import all MercLib.Theory.ParityGame.Proofs.Key_Proofs
import all MercLib.Theory.ParityGame.Proofs.Lasso_Proofs
import all MercLib.Algorithms.ParityGame.HybridSI.Proofs.Potential_Proofs
import all MercLib.Algorithms.ParityGame.HybridSI.Proofs.Termination_Proofs
import all MercLib.Theory.ParityGame.Proofs.Win_Proofs
import all MercLib.Theory.ParityGame.Proofs.Game_Proofs

@[expose] public section HybridSICountingProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Counting iterations along a trace (`HybridSI.Counting`).
* `epochIterations`: every round `k < L` lies in the epoch starting at `s k`, the last epoch start
  (`0` or a round after an epoch change) at or before `k`; `EpochBound` on the trace shifted to
  `s k` gives `k - s k < n_E`, and `k ↦ (s k, k - s k)` is injective.
* `card_le_segments`: at most `c` elements of `X` per stretch without an element of `C` give at
  most `|C| + c (|C| + 1)` elements of `X`.
* `stretchCount`: `card_le_segments` with all rounds and the cycle-maximum changes as cuts (P3).
* `kstarBlock`: the proof of `epochBound` with Odd's moves replaced by the keys `K*`: `epochBound`
  uses the constant Odd moves only to get equal keys of Even's best responses (`hKeq`), and
  `epoch_round` works per iteration. With `Kst = K*_j`, the set `D k` of Even vertices whose move
  under `p k` is `Kst`-maximal grows strictly in each iteration `j ≤ k < j'` and is never all
  Even vertices.
* `kstarCount`: `card_le_segments` with the changes of `K*` as cuts; in a cut-free stretch `K*` is
  constant on the iterations below `L`. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

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

/-- At most `c` elements of `X` in every stretch without an element of `C` give at most
    `|C| + c (|C| + 1)` elements of `X`. -/
private theorem card_le_segments (X C : Finset ℕ) (c : ℕ)
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

/-- Blocks of constant `K*` (headline). -/
theorem kstarBlock (bf : ℕ) : KStarBlock G bf := by
  classical
  intro L p ps h j j' hj' hK
  rcases Nat.lt_or_ge j j' with hjj | hjj
  swap
  · omega
  have hedge := runTrace_edge G h
  have hex : ∀ k, ∃ pstar : V → V, k < L → respond G false bf (ps k) = some pstar := by
    intro k
    by_cases hk : k < L
    · obtain ⟨qt, hqt, -⟩ := h.2.2 k hk
      obtain ⟨pstar, h'⟩ := hbStep_next_pstar G (h.2.1 k hk.le) hqt
      exact ⟨pstar, fun _ => h'⟩
    · exact ⟨id, fun h' => absurd h' hk⟩
  choose pstar hpstar using hex
  have hkof : ∀ k < L, kstarOf G bf ps k = key G (pstar k) := fun k hk => by
    funext v
    simp [kstarOf, hpstar k hk]
  have hKeq : ∀ k, j ≤ k → k < j' → key G (pstar k) = key G (pstar j) := fun k h1 h2 => by
    rw [← hkof k (by omega), ← hkof j (by omega)]
    exact hK k h1 h2
  set Kst := key G (pstar j)
  let E : Finset V := Finset.univ.filter fun v => G.owner v = .zero
  let D : ℕ → Finset V := fun k =>
    Finset.univ.filter fun v => G.owner v = .zero ∧ Mx G Kst v (p k v)
  have hround : ∀ k, j ≤ k → k < j' → D k ⊂ D (k + 1) ∧ D k ⊂ E := by
    intro k hjk hk
    obtain ⟨qt, hqt, hpk⟩ := h.2.2 k (by omega)
    obtain ⟨h1, ⟨v, hvE, hvM, hvM'⟩, ⟨u, huE, huM⟩⟩ :=
      epoch_round G (hedge k (by omega)) (h.2.1 k (by omega)) (hpstar k (by omega)) hqt
    rw [hKeq k hjk hk] at h1 hvM hvM' huM
    have hpk' : ∀ x, p (k + 1) x = look qt x x := fun x => by rw [hpk]
    refine ⟨Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun he => ?_⟩,
      Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun he => ?_⟩⟩
    · simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.1, by rw [hpk']; exact h1 x hx.2⟩
    · have hv : v ∈ D (k + 1) := by
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hvE, by rw [hpk']; exact hvM'⟩
      rw [← he] at hv
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hvM hv.2
    · simp only [D, E, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.1
    · have hu : u ∈ E := by simp [E, huE]
      rw [← he] at hu
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact huM hu.2
  have hcard : ∀ i, j + i + 1 ≤ j' → (D j).card + i ≤ (D (j + i)).card := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have := Finset.card_lt_card (hround (j + i) (by omega) (by omega)).1
      have := ih (by omega)
      rw [show j + (i + 1) = j + i + 1 by omega]
      omega
  have h1 := hcard (j' - j - 1) (by omega)
  have h2 := Finset.card_lt_card (hround (j + (j' - j - 1)) (by omega) (by omega)).2
  have : numEven G = E.card := rfl
  omega

/-- Changes of `K*` (headline). -/
theorem kstarCount (bf : ℕ) : KStarCount G bf := by
  intro L p ps h
  have hX := card_le_segments (Finset.range L) (kstarChangeRounds G bf L ps) (numEven G)
    (fun j j' hcut => by
      set j'' := min j' L
      have heq : ((Finset.range L).filter fun k => j ≤ k ∧ k < j') = Finset.Ico j j'' := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, j'']
        omega
      rw [heq, Nat.card_Ico]
      refine kstarBlock G bf L p ps h j j'' (by omega) fun k h1 h2 => ?_
      induction k, h1 using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        rw [← ih (by omega)]
        have hc := hcut k hk (by omega)
        simp only [kstarChangeRounds, Finset.mem_filter, Finset.mem_range, not_and,
          not_not] at hc
        exact hc (by omega) (by omega))
  rw [Finset.card_range] at hX
  exact hX

end MercLib.HybridSI

end HybridSICountingProofs
