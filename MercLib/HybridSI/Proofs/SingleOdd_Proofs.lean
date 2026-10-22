module

public import MercLib.HybridSI.SingleOdd
public import MercLib.HybridSI.Proofs.Bounds_Proofs

@[expose] public section HybridSISingleOddProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Odd's best responses along H-B runs (`HybridSI.SingleOdd`).
* `oddOptimal` (K1): the optimality part of `respond_spec` for Odd.
* `cycMaxSucc` (K2): `cycMax_apply`.
* `stableOddChange` (K3): the first key component is the reward `rI .zero` of the cycle maximum
  (`rI_le_of_key_le`), injective in the vertex; K1 at `k` and at `k + 1` gives both inequalities.
* `escapeMonotone` (MMON): K1 at state `k` and P2 (`runTrace_step_le`).
* `singleOddEpochs` (K4): every epoch change switches `u`; it changes the cycle maximum of some
  successor of `u` (at most `n - 1` times each, `vertexCycMaxChanges`) or none, and then also not
  that of `u` (K2, K3), so it is a local epoch change.
* `locSameTop`: K2 and K3. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-- Odd's best responses of a trace follow edges. -/
theorem runTrace_ps_edge {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) :
    ∀ k ≤ L, ∀ v, G.edge v (ps k v) := fun k hk =>
  (respond_spec G true bf _ _ (h.2.1 k hk)).2.1 (runTrace_edge G h k hk)

/-- K1, Odd optimality (headline). -/
theorem oddOptimal (bf : ℕ) : OddOptimal G bf := by
  intro L p ps h k hk u hu w hw
  simpa using (respond_spec G true bf _ _ (h.2.1 k hk)).2.2 u ((ownedBy_true_iff G u).2 hu) w hw

/-- K2, the cycle maximum of the successor (headline). -/
theorem cycMaxSucc : CycMaxSucc V := fun f v => (cycMax_apply (f := f) v).symm

/-- K3, equal cycle maxima at a cycle-maximum-stable Odd change (headline). -/
theorem stableOddChange (bf : ℕ) : StableOddChange G bf := by
  intro L p ps h k hk u hu _ ha hb
  have e := runTrace_ps_edge G h
  have h1 := rI_le_of_key_le G (oddOptimal G bf L p ps h k hk.le u hu _ (e (k + 1) (by omega) u))
  have h2 := rI_le_of_key_le G (oddOptimal G bf L p ps h (k + 1) (by omega) u hu _ (e k hk.le u))
  rw [← ha, ← hb] at h2
  exact rI_injective (le_antisymm h1 h2)

/-- MMON, the escape value is monotone (headline). -/
theorem escapeMonotone (bf : ℕ) : EscapeMonotone G bf := by
  intro L p ps h k hk u hu
  exact (oddOptimal G bf L p ps h k hk.le u hu _
    (runTrace_ps_edge G h (k + 1) (by omega) u)).trans (runTrace_step_le G h hk _)

/-- With a single Odd choice vertex `u`, every epoch change switches `u`. -/
theorem oddChange_single {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) {u : V}
    (hs : SingleOddChoice G u) {k : ℕ} (hk : k ∈ oddChangeRounds G L ps) :
    k < L ∧ ps k u ≠ ps (k + 1) u := by
  simp only [oddChangeRounds, Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hkL, u', hu', hne⟩ := hk
  refine ⟨hkL, ?_⟩
  by_cases hu : u' = u
  · exact hu ▸ hne
  · have e := runTrace_ps_edge G h
    exact absurd (hs u' hu' hu _ _ (e k hkL.le u') (e (k + 1) hkL u')) hne

/-- If no successor of the Odd vertex `u` changes its cycle maximum, neither does `u`. -/
theorem cycMax_stable_of_succ {bf L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps) {k : ℕ}
    (hk : k < L) {u : V} (hu : G.owner u = .one)
    (hw : ∀ w, G.edge u w → cycMax (ps k) w = cycMax (ps (k + 1)) w) :
    cycMax (ps k) u = cycMax (ps (k + 1)) u := by
  have e := runTrace_ps_edge G h
  have ha := hw _ (e k hk.le u)
  have hb := hw _ (e (k + 1) hk u)
  rw [← cycMax_apply (f := ps k) u, ← cycMax_apply (f := ps (k + 1)) u]
  by_cases hab : ps k u = ps (k + 1) u
  · rw [ha, hab]
  · rw [stableOddChange G bf L p ps h k hk u hu hab ha hb, hb]

/-- K4 for a single Odd choice vertex (headline). -/
theorem singleOddEpochs (bf : ℕ) : SingleOddEpochs G bf := by
  intro L p ps h u hu hs
  set C : V → Finset ℕ := fun w =>
    (Finset.range L).filter fun k => cycMax (ps k) w ≠ cycMax (ps (k + 1)) w
  set S := Finset.univ.filter (G.edge u)
  have hsub : oddChangeRounds G L ps ⊆ S.biUnion C ∪ locRounds G L ps u := by
    intro k hk
    obtain ⟨hkL, -⟩ := oddChange_single G h hs hk
    by_cases hw : ∃ w, G.edge u w ∧ cycMax (ps k) w ≠ cycMax (ps (k + 1)) w
    · obtain ⟨w, hw, hne⟩ := hw
      exact Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨w, by simpa [S] using hw, by simp [C, hkL, hne]⟩)
    · push Not at hw
      refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hk, fun v hv => ?_⟩)
      rcases hv with rfl | hv
      · exact cycMax_stable_of_succ G h hkL hu hw
      · exact hw v hv
  calc (oddChangeRounds G L ps).card ≤ (S.biUnion C ∪ locRounds G L ps u).card :=
        Finset.card_le_card hsub
    _ ≤ (S.biUnion C).card + (locRounds G L ps u).card := Finset.card_union_le _ _
    _ ≤ ∑ w ∈ S, (C w).card + (locRounds G L ps u).card := by
        gcongr; exact Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ S, (Fintype.card V - 1) + (locRounds G L ps u).card := by
        gcongr with w; exact vertexCycMaxChanges G bf L p ps h w
    _ = S.card * (Fintype.card V - 1) + (locRounds G L ps u).card := by
        rw [Finset.sum_const, smul_eq_mul]

/-- Local epoch changes switch `u` between successors with the cycle maximum of `u`
    (headline). -/
theorem locSameTop (bf : ℕ) : LocSameTop G bf := by
  intro L p ps h u hu hs k hk
  have hk' := Finset.mem_filter.1 hk
  obtain ⟨hkL, hne⟩ := oddChange_single G h hs hk'.1
  have e := runTrace_ps_edge G h
  have ha := hk'.2 _ (Or.inr (e k hkL.le u))
  have hb := hk'.2 _ (Or.inr (e (k + 1) hkL u))
  have hab := stableOddChange G bf L p ps h k hkL u hu hne ha hb
  refine ⟨hne, e k hkL.le u, e (k + 1) hkL u, cycMax_apply _, ?_⟩
  rw [← hab]
  exact cycMax_apply _

end MercLib.HybridSI

end HybridSISingleOddProofs
