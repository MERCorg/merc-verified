module

public import MercLib.HybridSI.Proofs.SingleOddPoly_Proofs

@[expose] public section HybridSISingleOddPolyKStarProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Blocks of constant `K*` (`HybridSI.SingleOddPoly`, `ST_WORLD.md` §DOWN, Lemma B).
* `kstarBlock`: the proof of `epochBound` with Odd's moves replaced by the keys `K*`: `epochBound`
  uses the constant Odd moves only to get equal keys of Even's best responses (`hKeq`), and
  `epoch_round` works per iteration. With `Kst = K*_j`, the set `D k` of Even vertices whose move
  under `p k` is `Kst`-maximal grows strictly in each iteration `j ≤ k < j'` and is never all
  Even vertices.
* `kstarCount`: `card_le_segments` with the changes of `K*` as cuts; in a cut-free stretch `K*` is
  constant on the iterations below `L`.
* `kChangeReduction`: `L ≤ n² + n (n² + 1) ≤ (n + 1)⁴`. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

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

/-- The reduction of `SingleOddPoly` to `KChangeConjecture` (headline). -/
theorem kChangeReduction : KChangeReduction := by
  intro hc n G _ hG u hu hs L p ps h
  have hC := hc n G _ hG u hu hs L p ps h
  have hL := kstarCount G _ L p ps h
  have hev : numEven G ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hm : numEven G * ((kstarChangeRounds G (hbFuel (Fin n)) L ps).card + 1) ≤
      n * (n ^ 2 + 1) := Nat.mul_le_mul hev (by omega)
  calc L ≤ n ^ 2 + n * (n ^ 2 + 1) := by omega
    _ ≤ (n + 1) ^ 4 := by nlinarith [Nat.zero_le n]

end MercLib.HybridSI

end HybridSISingleOddPolyKStarProofs
