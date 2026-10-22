module

public import MercLib.HybridSI.AlgorithmPoly
public import MercLib.HybridSI.Proofs.BestResponse_Proofs

@[expose] public section HybridSIAlgorithmPolyProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). Headlines:
`hbStepPoly_cost` (`HBStepCost`), `hbRunPoly_cost` (`HBRunCost`) and `hbPolyCorrect`
(`HBPolyCorrect`). Correctness follows `hbCorrect`, with `bestResponse_optimal` in place of
`respond_spec`. -/

open Function MercLib.ParityGame Cslib.Algorithms.Lean

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V] (G : Game V) [DecidableRel G.edge]

theorem keys_eq (f : V → V) : (fun v => look (keyTable G f) keyDefault v) = key G f :=
  funext (look_keyTable G f)

theorem hbStepPoly_done {p : V → V} {kt : List (V × Key)} (h : (hbStepPoly G p).ret = .done kt) :
    kt = keyTable G (bestResponse G true p) ∧
      ∀ v, improving G (key G (bestResponse G true p)) p v = [] := by
  unfold hbStepPoly keyTableT at h
  simp only [TimeM.ret_bind, TimeM.ret_pure, keys_eq] at h
  split_ifs at h with hall
  · cases h
    refine ⟨rfl, fun v => ?_⟩
    simp only [List.all_eq_true, List.isEmpty_iff] at hall
    exact hall v (mem_univList v)
  · simp at h

theorem hbStepPoly_next {p : V → V} {qt : List (V × V)} (h : (hbStepPoly G p).ret = .next qt)
    (he : ∀ v, G.edge v (p v)) : ∀ v, G.edge v (look qt v v) := by
  unfold hbStepPoly keyTableT at h
  simp only [TimeM.ret_bind, TimeM.ret_pure, keys_eq] at h
  split_ifs at h with hall
  · simp at h
  · injection h with h
    subst h
    intro v
    rw [look_tabulate]
    refine edge_of_sub G p he _ v _ fun x hx => ?_
    split_ifs at hx
    · exact filtered_sub G _ _ p v x hx
    · exact improving_sub G _ p v x hx

theorem hbRunPoly_spec : ∀ (fuel it : ℕ) (p : V → V) (it' : ℕ) (kt : List (V × Key)),
    (hbRunPoly G fuel it p).ret = some (it', kt) → (∀ v, G.edge v (p v)) →
    ∃ p', (∀ v, G.edge v (p' v)) ∧ kt = keyTable G (bestResponse G true p') ∧
      ∀ v, improving G (key G (bestResponse G true p')) p' v = []
  | 0, _, _, _, _, h, _ => by simp [hbRunPoly] at h
  | fuel + 1, it, p, it', kt, h, he => by
    unfold hbRunPoly at h
    simp only [TimeM.ret_bind] at h
    split at h
    · rename_i ks hstep
      simp only [TimeM.ret_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := hbStepPoly_done G hstep
      exact ⟨p, he, h.2 ▸ h1, h2⟩
    · rename_i qt hstep
      exact hbRunPoly_spec fuel (it + 1) _ it' kt h (hbStepPoly_next G hstep he)
    · simp at h

/-- Correctness of H-B with polynomial best responses (headline). -/
theorem hbPolyCorrect (fuel : ℕ) : HBPolyCorrect G fuel := by
  intro hrel it kt h
  obtain ⟨p', hedge', rfl, himp⟩ := hbRunPoly_spec G fuel 0 _ it kt h (initProfile_edge G)
  obtain ⟨hkeep, hedge, hodd⟩ := bestResponse_optimal G true p'
  set ps := bestResponse G true p'
  have hedgeps := hedge hedge'
  have hlook : ∀ v, look (keyTable G ps) keyDefault v = key G ps v := look_keyTable G ps
  have hEven : ∀ v, G.owner v = .zero → ∀ w, G.edge v w → key G ps w ≤ key G ps (ps v) := by
    intro v hv w hw
    have hown : ownedBy G true v = false := by simp [ownedBy, hv]
    have hi := himp v
    unfold improving at hi
    rw [ite_eq_right (by simp [hown])] at hi
    rw [hkeep v hown]
    have := List.filter_eq_nil_iff.1 hi w ((mem_succList G).2 hw)
    simpa using this
  have hOdd : ∀ v, G.owner v = .one → ∀ w, G.edge v w → key G ps (ps v) ≤ key G ps w := by
    intro v hv w hw
    have := hodd v (by simp [ownedBy, hv]) w hw
    simpa using this
  have hwin : ∀ v i, keyWinner (key G ps v) = i → G.WinsFrom Set.univ i ps v := by
    intro v i hi
    refine winsFrom_of_saddle hrel (fun v _ => hedgeps v) (fun u hu w hw => ?_) v
      (keyWinner_pos G ps v i hi)
    cases i
    · have hu1 : G.owner u = .one := by cases h : G.owner u <;> simp_all
      exact hOdd u hu1 w hw
    · have hu0 : G.owner u = .zero := by cases h : G.owner u <;> simp_all
      show negK (key G ps (ps u)) ≤ negK (key G ps w)
      rw [negK_le_negK]
      exact hEven u hu0 w hw
  intro v i
  rw [hlook]
  constructor
  · intro hi
    exact ⟨ps, hwin v i hi⟩
  · rintro ⟨σ, hσ⟩
    by_contra hne
    have hj := hwin v _ rfl
    cases i
    · have : keyWinner (key G ps v) = .one := by
        cases h : keyWinner (key G ps v) <;> simp_all
      rw [this] at hj
      exact not_winsFrom_both G hσ hj
    · have : keyWinner (key G ps v) = .zero := by
        cases h : keyWinner (key G ps v) <;> simp_all
      rw [this] at hj
      exact not_winsFrom_both G hj hσ

/-! ### Cost -/

theorem roundCost_succList : roundCost (succList G) = edgeCount G + Fintype.card V := by
  unfold roundCost edgeCount
  rw [List.sum_map_add]
  simp [univList]

/-- The cost of one iteration (headline). -/
theorem hbStepPoly_cost (p : V → V) : HBStepCost G p := by
  unfold HBStepCost hbStepBound
  have h1 := bestResponse_cost G true p
  have h2 := bestResponse_cost G false (bestResponseT G true p).ret
  unfold BestResponseCost at h1 h2
  have h3 := roundCost_succList G
  rw [show 2 * Fintype.card V * (Fintype.card V + 1) ^ 3 =
    2 * (Fintype.card V * (Fintype.card V + 1) ^ 3) by ring]
  unfold hbStepPoly keyTableT
  simp only [TimeM.time_bind, TimeM.time_tick]
  split
  · simp only [TimeM.time_pure, TimeM.ret_bind, TimeM.ret_pure] at *
    generalize Fintype.card V * (Fintype.card V + 1) ^ 3 = K at *
    omega
  · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
      TimeM.ret_pure] at *
    generalize Fintype.card V * (Fintype.card V + 1) ^ 3 = K at *
    omega

theorem hbRunPoly_cost_aux : ∀ (fuel it : ℕ) (p : V → V) (it' : ℕ) (kt : List (V × Key)),
    (hbRunPoly G fuel it p).ret = some (it', kt) →
    it ≤ it' ∧ (hbRunPoly G fuel it p).time ≤
      (it' - it + 1) * (hbStepBound (Fintype.card V) (edgeCount G) + 1)
  | 0, _, _, _, _, h => by simp [hbRunPoly] at h
  | fuel + 1, it, p, it', kt, h => by
    have hs := hbStepPoly_cost G p
    unfold HBStepCost at hs
    unfold hbRunPoly at h ⊢
    simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick] at h ⊢
    split at h
    · rename_i ks hstep
      simp only [TimeM.ret_pure, Option.some.injEq, Prod.mk.injEq] at h
      simp only [TimeM.time_pure]
      refine ⟨h.1.le, ?_⟩
      rw [h.1, Nat.sub_self]
      omega
    · rename_i qt hstep
      obtain ⟨h1, h2⟩ := hbRunPoly_cost_aux fuel (it + 1) _ it' kt h
      refine ⟨by omega, ?_⟩
      have : it' - it + 1 = (it' - (it + 1) + 1) + 1 := by omega
      rw [this, Nat.succ_mul]
      omega
    · simp at h

/-- The cost of a run: at most `it + 1` iterations' worth (headline). -/
theorem hbRunPoly_cost (fuel : ℕ) : HBRunCost G fuel := by
  intro it kt h
  have := (hbRunPoly_cost_aux G fuel 0 _ it kt h).2
  simpa using this

end MercLib.HybridSI

end HybridSIAlgorithmPolyProofs
