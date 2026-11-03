module

public import MercLib.HybridSI.Potential
public import MercLib.HybridSI.Proofs.Epoch_Proofs
public import MercLib.HybridSI.Proofs.Termination_Proofs
import all MercLib.HybridSI.Proofs.Correctness_Proofs
import all MercLib.HybridSI.Proofs.Epoch_Proofs
import all MercLib.HybridSI.Proofs.Filter_Proofs
import all MercLib.HybridSI.Proofs.Improvement_Proofs
import all MercLib.HybridSI.Proofs.Key_Proofs
import all MercLib.HybridSI.Proofs.Lasso_Proofs
import all MercLib.HybridSI.Proofs.Termination_Proofs
import all MercLib.HybridSI.Proofs.Win_Proofs
import all MercLib.ParityGame.Proofs.Game_Proofs

@[expose] public section HybridSIPotentialProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Potential bounds for H-B runs (`HybridSI.Potential`).
* `runTraceOfRun`: a returning `hbRun` unrolls into a `RunTrace`.
* `valuationMonotone` (P2): one step is the improvement lemma applied to the Odd best responses
  `ps k`, `ps (k + 1)` (Even moves are kept or switched to a strictly better successor in the keys
  of `ps k`, `hbStep_next_spec`).
* `cycleMaxChanges` (P3): per vertex the reward `rI .zero` of the cycle maximum is the first key
  component, hence non-decreasing, and takes at most `n` values; a non-decreasing sequence in a
  set of `s` values changes at most `s - 1` times (`card_changes_le`).
* `entryIterations`: every non-final iteration switches some Even vertex into some Even edge.
* `entryPoly`: `L ≤ n · m_E ≤ n³ ≤ (n + 1)³`. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-! ### Traces -/

/-- The profiles of a trace follow edges. -/
private theorem runTrace_edge {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) :
    ∀ k ≤ L, ∀ v, G.edge v (p k v) := by
  obtain ⟨h0, -, hstep⟩ := h
  intro k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    obtain ⟨qt, hqt, hpk⟩ := hstep k (by omega)
    rw [hpk]
    exact hbStep_next G hqt (ih (by omega))

/-- Traces of runs (headline). -/
theorem runTraceOfRun (bf : ℕ) : RunTraceOfRun G bf := by
  intro fuel
  induction fuel with
  | zero => intro it₀ p₀ it kt _ h; simp [hbRun] at h
  | succ fuel ih =>
    intro it₀ p₀ it kt he h
    unfold hbRun at h
    split at h
    · rename_i ks hstep
      cases h
      obtain ⟨ps, hps, -, -⟩ := hbStep_done G hstep
      refine ⟨0, fun _ => p₀, fun _ => ps, rfl, rfl, ⟨he, fun k _ => hps, fun k hk => ?_⟩, hstep⟩
      omega
    · rename_i qt hstep
      obtain ⟨L, p, ps, hit, hp0, ⟨_, hresp, hst⟩, hdone⟩ :=
        ih (it₀ + 1) _ it kt (hbStep_next G hstep he) h
      obtain ⟨ps₀, hps₀, -⟩ := hbStep_next_spec G hstep
      refine ⟨L + 1, fun k => match k with | 0 => p₀ | k + 1 => p k,
        fun k => match k with | 0 => ps₀ | k + 1 => ps k, by omega, rfl,
        ⟨he, fun k hk => ?_, fun k hk => ?_⟩, hdone⟩
      · rcases k with _ | k
        · exact hps₀
        · exact hresp k (by omega)
      · rcases k with _ | k
        · exact ⟨qt, hstep, by simp only; rw [hp0]⟩
        · exact hst k (by omega)
    · cases h

/-! ### P2: monotonicity of the valuation -/

private theorem runTrace_step_le {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) {k : ℕ}
    (hk : k < L) (v : V) : key G (ps k) v ≤ key G (ps (k + 1)) v := by
  have hedge := runTrace_edge G h
  obtain ⟨-, hresp, hstep⟩ := h
  obtain ⟨qt, hqt, hpk⟩ := hstep k hk
  obtain ⟨ps', hps', hmove, -⟩ := hbStep_next_spec G hqt
  have hps := hresp k (by omega)
  rw [hps] at hps'
  cases hps'
  have hps1 := hresp (k + 1) (by omega)
  obtain ⟨hk0, -, hodd⟩ := respond_spec G true bf _ _ hps
  obtain ⟨hk1, he1, -⟩ := respond_spec G true bf _ _ hps1
  have heven : ∀ u, G.owner u = .zero → ownedBy G true u = false := fun u hu => by
    simp [ownedBy, hu]
  have himp := improvement G (f := ps k) (g := ps (k + 1))
    (fun u hu w hw => by simpa using hodd u ((ownedBy_true_iff G u).2 hu) w hw)
    (fun u _ => he1 (hedge (k + 1) hk) u)
    (fun u hu => by
      rw [hk1 u (heven u hu), hk0 u (heven u hu), hpk]
      rcases hmove u with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.2)
  exact himp.1 v

/-- Monotonicity of the valuation (headline, P2). -/
theorem valuationMonotone (bf : ℕ) : ValuationMonotone G bf := by
  intro L p ps h j k hjk hkL v
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (ih (by omega)).trans (runTrace_step_le G h (by omega) v)

/-! ### P3: changes of the cycle maxima -/

/-- A non-decreasing sequence on `0, …, L` with values in `S` changes at most `|S| - 1` times. -/
private theorem card_changes_le (r : ℕ → ℤ) (L : ℕ) (S : Finset ℤ) (hS : ∀ k ≤ L, r k ∈ S)
    (hmono : ∀ k < L, r k ≤ r (k + 1)) :
    ((Finset.range L).filter fun k => r k ≠ r (k + 1)).card + 1 ≤ S.card := by
  have hle : ∀ j k, j ≤ k → k ≤ L → r j ≤ r k := by
    intro j k hjk hkL
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (ih (by omega)).trans (hmono k (by omega))
  set C := (Finset.range L).filter fun k => r k ≠ r (k + 1)
  have hlt : ∀ k ∈ C, r k < r (k + 1) := fun k hk => by
    simp only [C, Finset.mem_filter, Finset.mem_range] at hk
    exact lt_of_le_of_ne (hmono k hk.1) hk.2
  have hmaps : ∀ k ∈ C, r (k + 1) ∈ S.erase (r 0) := fun k hk => by
    have hkL : k < L := by simp only [C, Finset.mem_filter, Finset.mem_range] at hk; exact hk.1
    refine Finset.mem_erase.2 ⟨fun he => ?_, hS _ (by omega)⟩
    have := hle 0 k (Nat.zero_le _) (by omega)
    have := hlt k hk
    omega
  have hinj : Set.InjOn (fun k => r (k + 1)) C := by
    intro a ha b hb hab
    simp only at hab
    by_contra hne
    have hCL : ∀ k ∈ C, k < L := fun k hk => by
      simp only [C, Finset.mem_filter, Finset.mem_range] at hk; exact hk.1
    rcases lt_or_gt_of_ne hne with h' | h'
    · have h1 := hle (a + 1) b (by omega) (hCL b hb).le
      have h2 := hlt b hb
      omega
    · have h1 := hle (b + 1) a (by omega) (hCL a ha).le
      have h2 := hlt a ha
      omega
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  have h0 := Finset.card_erase_add_one (hS 0 (Nat.zero_le _))
  omega

/-- The first key component is the reward (for Even) of the cycle maximum. -/
private theorem rI_le_of_key_le {f g : V → V} {a b : V} (h : key G f a ≤ key G g b) :
    rI G .zero (cycMax f a) ≤ rI G .zero (cycMax g b) := by
  have ha := kfor_key G f .zero a
  have hb := kfor_key G g .zero b
  simp only [kfor] at ha hb
  rw [ha, hb] at h
  rcases (Prod.Lex.le_iff).1 h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- Changes of the cycle maxima (headline, P3). -/
theorem cycleMaxChanges (bf : ℕ) : CycleMaxChanges G bf := by
  intro L p ps h
  set S : Finset ℤ := Finset.univ.image fun x : V => rI G .zero x
  have hScard : S.card ≤ Fintype.card V := Finset.card_image_le.trans (by simp)
  let C : V → Finset ℕ := fun v => (Finset.range L).filter fun k =>
    rI G .zero (cycMax (ps k) v) ≠ rI G .zero (cycMax (ps (k + 1)) v)
  have hC : ∀ v, (C v).card ≤ Fintype.card V - 1 := fun v => by
    have := card_changes_le (fun k => rI G .zero (cycMax (ps k) v)) L S
      (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (fun k hk => rI_le_of_key_le G (runTrace_step_le G h hk v))
    simp only [C]
    omega
  have hsub : cycMaxChangeRounds L ps ⊆ Finset.univ.biUnion C := by
    intro k hk
    simp only [cycMaxChangeRounds, Finset.mem_filter] at hk
    obtain ⟨hkL, v, hv⟩ := hk
    refine Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, Finset.mem_filter.2 ⟨hkL, fun he => ?_⟩⟩
    exact hv (rI_injective he)
  calc (cycMaxChangeRounds L ps).card ≤ (Finset.univ.biUnion C).card := Finset.card_le_card hsub
    _ ≤ ∑ v, (C v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : V, (Fintype.card V - 1) := Finset.sum_le_sum fun v _ => hC v
    _ = Fintype.card V * (Fintype.card V - 1) := by simp

/-! ### Entries into Even edges -/

/-! ### TOP: changes at the top level -/

/-- With equal rewards of the cycle maxima, the `B`-sums (for Even) compare like the keys. -/
private theorem sum_le_of_key_le {f g : V → V} {a b : V} (h : key G f a ≤ key G g b)
    (hr : rI G .zero (cycMax f a) = rI G .zero (cycMax g b)) :
    ∑ y ∈ bSet f a, wI G .zero y ≤ ∑ y ∈ bSet g b, wI G .zero y := by
  have ha := kfor_key G f .zero a
  have hb := kfor_key G g .zero b
  simp only [kfor] at ha hb
  rw [ha, hb, lex_le_iff, lex2_le_iff] at h
  rcases h with h | ⟨-, h | ⟨h, -⟩⟩
  · omega
  · exact h.le
  · exact h.le

/-- The top-level potential of a vertex: twice the reward of the cycle maximum, plus `1` if the
    membership of the top vertex `t` in `B` is the one Even prefers. -/
private def topPot (t : V) (f : V → V) (v : V) : ℤ :=
  2 * rI G .zero (cycMax f v) +
    if (t ∈ bSet f v) = (0 < wI G .zero t) then 1 else 0

private theorem topPot_mono {t : V} (ht : ∀ x, x ≤ t) {f g : V → V} {v : V}
    (h : key G f v ≤ key G g v) : topPot G t f v ≤ topPot G t g v := by
  have hr := rI_le_of_key_le G h
  unfold topPot
  rcases lt_or_eq_of_le hr with hlt | heq
  · split_ifs <;> omega
  · have hs := upper_le_of_le (wI G .zero) (wI_signed G .zero) _ _ t (sum_le_of_key_le G h heq)
    have hfil : ∀ B : Finset V, ∑ y ∈ B.filter (t ≤ ·), wI G .zero y =
        if t ∈ B then wI G .zero t else 0 := fun B => by
      have : B.filter (t ≤ ·) = if t ∈ B then {t} else ∅ := by
        ext y
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hy, hty⟩
          have := le_antisymm (ht y) hty
          subst this
          simp [hy]
        · intro hy
          split_ifs at hy with hB
          · rw [Finset.mem_singleton] at hy; subst hy; exact ⟨hB, le_rfl⟩
          · simp at hy
      rw [this]; split_ifs <;> simp
    rw [hfil, hfil] at hs
    have hne : wI G .zero t ≠ 0 := by
      have hp : (0 : ℤ) < 2 ^ rank t := by positivity
      rcases wI_signed G .zero t with h' | h' <;> omega
    rw [heq]
    by_cases h1 : t ∈ bSet f v <;> by_cases h2 : t ∈ bSet g v <;>
      by_cases h3 : 0 < wI G .zero t <;> simp_all <;> omega

private theorem topPot_inj {t : V} {f g : V → V} {v : V} (h : topPot G t f v = topPot G t g v) :
    topClass t f v = topClass t g v := by
  unfold topPot at h
  have hr : rI G .zero (cycMax f v) = rI G .zero (cycMax g v) := by split_ifs at h <;> omega
  have hc := rI_injective hr
  rw [hr] at h
  unfold topClass
  rw [hc]
  congr 1
  by_cases h1 : t ∈ bSet f v <;> by_cases h2 : t ∈ bSet g v <;> simp_all <;>
    split_ifs at h <;> omega

/-- Changes at the top level (headline, TOP). -/
theorem topChanges (bf : ℕ) : TopChanges G bf := by
  intro t ht L p ps h
  set S : Finset ℤ := (Finset.univ ×ˢ ({0, 1} : Finset ℤ)).image
    fun xe : V × ℤ => 2 * rI G .zero xe.1 + xe.2
  have hScard : S.card ≤ 2 * Fintype.card V := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product]
    simp [mul_comm]
  have hmem : ∀ k v, topPot G t (ps k) v ∈ S := fun k v => by
    refine Finset.mem_image.2 ⟨(cycMax (ps k) v,
      if (t ∈ bSet (ps k) v) = (0 < wI G .zero t) then 1 else 0), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_univ, true_and]
    split_ifs <;> simp
  let C : V → Finset ℕ := fun v => (Finset.range L).filter fun k =>
    topPot G t (ps k) v ≠ topPot G t (ps (k + 1)) v
  have hC : ∀ v, (C v).card ≤ 2 * Fintype.card V - 1 := fun v => by
    have := card_changes_le (fun k => topPot G t (ps k) v) L S (fun k _ => hmem k v)
      (fun k hk => topPot_mono G ht (runTrace_step_le G h hk v))
    simp only [C]
    omega
  have hsub : topChangeRounds t L ps ⊆ Finset.univ.biUnion C := by
    intro k hk
    simp only [topChangeRounds, Finset.mem_filter] at hk
    obtain ⟨hkL, v, hv⟩ := hk
    exact Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _,
      Finset.mem_filter.2 ⟨hkL, fun he => hv (topPot_inj G he)⟩⟩
  calc (topChangeRounds t L ps).card ≤ (Finset.univ.biUnion C).card := Finset.card_le_card hsub
    _ ≤ ∑ v, (C v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : V, (2 * Fintype.card V - 1) := Finset.sum_le_sum fun v _ => hC v
    _ = Fintype.card V * (2 * Fintype.card V - 1) := by simp

/-! ### P3 per vertex, PXLc -/

/-- Changes of the cycle maximum of one vertex (headline, P3 per vertex). -/
theorem vertexCycMaxChanges (bf : ℕ) : VertexCycMaxChanges G bf := by
  intro L p ps h v
  set S : Finset ℤ := Finset.univ.image fun x : V => rI G .zero x
  have hScard : S.card ≤ Fintype.card V := Finset.card_image_le.trans (by simp)
  have := card_changes_le (fun k => rI G .zero (cycMax (ps k) v)) L S
    (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (fun k hk => rI_le_of_key_le G (runTrace_step_le G h hk v))
  have hsub : ((Finset.range L).filter fun k => cycMax (ps k) v ≠ cycMax (ps (k + 1)) v) ⊆
      (Finset.range L).filter fun k =>
        rI G .zero (cycMax (ps k) v) ≠ rI G .zero (cycMax (ps (k + 1)) v) :=
    Finset.monotone_filter_right _ fun k _ hne he => hne (rI_injective he)
  have := Finset.card_le_card hsub
  omega

/-! ### RED: epoch changes and crossings of sibling pairs -/

end MercLib.HybridSI

end HybridSIPotentialProofs
