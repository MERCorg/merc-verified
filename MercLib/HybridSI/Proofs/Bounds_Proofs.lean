module

public import MercLib.HybridSI.Bounds
public import MercLib.HybridSI.Proofs.Potential_Proofs

@[expose] public section HybridSIBoundsProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The sandwich (`HybridSI.Bounds`). All comparisons go through the master lemma `K_le_of_dom`:
* `saddle_ge` / `saddle_le`: a saddle profile `q` is at least as good for Even as any profile
  with the same Odd moves, and at most as good as any edge-following profile with the same Even
  moves.
* `respond_odd_optimal` / `respond_even_optimal`: the same for best responses.
Mixing Even's moves of one profile with Odd's moves of another (`mix`) connects the two. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-- Even's moves of `σ`, Odd's moves of `τ`. -/
def mix (σ τ : V → V) (v : V) : V := if G.owner v = .zero then σ v else τ v

theorem mix_even {σ τ : V → V} {v : V} (h : G.owner v = .zero) : mix G σ τ v = σ v :=
  ite_eq_left h

theorem mix_odd {σ τ : V → V} {v : V} (h : G.owner v = .one) : mix G σ τ v = τ v :=
  ite_eq_right (by rw [h]; exact fun h' => Player.noConfusion h')

theorem mix_edge {σ τ : V → V} (hσ : ∀ v, G.edge v (σ v)) (hτ : ∀ v, G.edge v (τ v)) (v : V) :
    G.edge v (mix G σ τ v) := by
  unfold mix; split_ifs
  · exact hσ v
  · exact hτ v

/-- A saddle profile is at least as good for Even as any profile with the same Odd moves. -/
theorem saddle_ge {q : V → V} (hq : Saddle G q) (g : V → V) (hg : ∀ v, G.edge v (g v))
    (hgq : ∀ v, G.owner v = .one → g v = q v) (v : V) : key G g v ≤ key G q v := by
  have := K_le_of_dom (G := G) (f := q) (g := g) (i := .one) (fun u => by
    by_cases hu : G.owner u = .zero
    · simp only [K, kfor, negK_le_negK]
      exact hq.2.2 u hu (g u) (hg u)
    · rw [hgq u (owner_one_of_ne G hu)]) v
  simpa [K, kfor, negK_le_negK] using this

/-- A saddle profile is at most as good for Even as any edge-following profile with the same
    Even moves. -/
theorem saddle_le {q : V → V} (hq : Saddle G q) (g : V → V) (hg : ∀ v, G.edge v (g v))
    (hgq : ∀ v, G.owner v = .zero → g v = q v) (v : V) : key G q v ≤ key G g v := by
  have := K_le_of_dom (G := G) (f := q) (g := g) (i := .zero) (fun u => by
    by_cases hu : G.owner u = .zero
    · rw [hgq u hu]
    · exact hq.2.1 u (owner_one_of_ne G hu) (g u) (hg u)) v
  simpa [K, kfor] using this

theorem ownedBy_true_even {v : V} (h : G.owner v = .zero) : ownedBy G true v = false := by
  simp [ownedBy, h]

theorem ownedBy_false_odd {v : V} (h : G.owner v = .one) : ownedBy G false v = false := by
  simp [ownedBy, h]

/-- Uniqueness of the optimal valuation (headline). -/
theorem saddleUnique : SaddleUnique G := by
  intro q q' hq hq'
  funext v
  refine le_antisymm ?_ ?_
  · -- q ≤ mix q q' ≤ q'
    have hm := mix_edge G hq.1 hq'.1
    exact (saddle_le G hq _ hm (fun u hu => mix_even G hu) v).trans
      (saddle_ge G hq' _ hm (fun u hu => mix_odd G hu) v)
  · have hm := mix_edge G hq'.1 hq.1
    exact (saddle_le G hq' _ hm (fun u hu => mix_even G hu) v).trans
      (saddle_ge G hq _ hm (fun u hu => mix_odd G hu) v)

/-- Existence of the optimal valuation (headline): the final profile of a run with enough fuel. -/
theorem saddleExists : SaddleExists G := by
  intro hrel
  obtain ⟨⟨it, kt⟩, hrun⟩ := Option.isSome_iff_exists.1
    (hbTerminates G (hbFuel V) (hbFuel V) hrel le_rfl le_rfl)
  obtain ⟨p', ps, he, hps, -, himp⟩ := hbRun_spec G _ _ _ _ _ hrun (initProfile_edge G)
  obtain ⟨hkeep, hedge, hodd⟩ := respond_spec G true _ _ _ hps
  refine ⟨ps, hedge he, fun u hu w hw => by
    simpa using hodd u ((ownedBy_true_iff G u).2 hu) w hw, fun u hu w hw => ?_⟩
  have h := himp u
  unfold improving at h
  rw [ite_eq_right (by rw [ownedBy_true_even G hu]; exact Bool.false_ne_true)] at h
  have hw' := List.filter_eq_nil_iff.1 h w ((mem_succList G).2 hw)
  rw [hkeep u (ownedBy_true_even G hu)]
  simpa using hw'

/-- Odd's moves of a best response of Even are those of its input. -/
theorem respond_even_keep {bf : ℕ} {p q : V → V} (h : respond G false bf p = some q) {v : V}
    (hv : G.owner v = .one) : q v = p v :=
  (respond_spec G false bf p q h).1 v (ownedBy_false_odd G hv)

/-- Even's moves of a best response of Odd are those of its input. -/
theorem respond_odd_keep {bf : ℕ} {p q : V → V} (h : respond G true bf p = some q) {v : V}
    (hv : G.owner v = .zero) : q v = p v :=
  (respond_spec G true bf p q h).1 v (ownedBy_true_even G hv)

/-- `Ξ_k ≤ K*_j` (headline). -/
theorem lowerBelowUpper (bf : ℕ) : LowerBelowUpper G bf := by
  intro L p ps h k hk j hj pstar hstar v
  have hedge := runTrace_edge G h
  obtain ⟨-, hresp, -⟩ := h
  have hek := (respond_spec G true bf _ _ (hresp k hk)).2.1 (hedge k hk)
  have hej := (respond_spec G true bf _ _ (hresp j hj)).2.1 (hedge j hj)
  have hm := mix_edge G hek hej
  refine (respond_odd_optimal G (hresp k hk) _ hm (fun u hu => mix_even G hu) v).trans ?_
  exact respond_even_optimal G hstar _ hm (fun u hu => by
    rw [mix_odd G hu, respond_even_keep G hstar hu]) v

/-- The sandwich `Ξ_k ≤ v* ≤ K*_j` (headline, P2). -/
theorem sandwich (bf : ℕ) : Sandwich G bf := by
  intro L p ps h q hq
  have hedge := runTrace_edge G h
  obtain ⟨-, hresp, -⟩ := h
  refine ⟨fun k hk v => ?_, fun j hj pstar hstar v => ?_⟩
  · have hek := (respond_spec G true bf _ _ (hresp k hk)).2.1 (hedge k hk)
    have hm := mix_edge G hek hq.1
    exact (respond_odd_optimal G (hresp k hk) _ hm (fun u hu => mix_even G hu) v).trans
      (saddle_ge G hq _ hm (fun u hu => mix_odd G hu) v)
  · have hej := (respond_spec G true bf _ _ (hresp j hj)).2.1 (hedge j hj)
    have hm := mix_edge G hq.1 hej
    exact (saddle_le G hq _ hm (fun u hu => mix_even G hu) v).trans
      (respond_even_optimal G hstar _ hm (fun u hu => by
        rw [mix_odd G hu, respond_even_keep G hstar hu]) v)

/-! ### Lemma M and P4 -/

theorem weight_eq_wI (y : V) : weight G y = wI G .zero y := by
  simp only [weight, wI, good_zero_iff]

/-- Lemma M (headline). -/
theorem truncationMonotone (bf : ℕ) : TruncationMonotone G bf := by
  intro L p ps h k k' hkk hk' v hl x
  have hkey := valuationMonotone G bf L p ps h k k' hkk hk' v
  have hs := sum_le_of_key_le G hkey (by rw [hl])
  simp only [weight_eq_wI]
  exact upper_le_of_le _ (wI_signed G .zero) _ _ x hs

/-- The part of `B` at or above `x` is the part above `x` plus possibly `x`. -/
theorem sum_filter_le_split (B : Finset V) (x : V) :
    ∑ y ∈ B.filter (x ≤ ·), weight G y =
      ∑ y ∈ B.filter (x < ·), weight G y + if x ∈ B then weight G x else 0 := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_ite_eq' B x (weight G),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rw [ite_eq_left hxy.le, ite_eq_left hxy, ite_eq_right (ne_of_gt hxy), add_zero]
  · simp
  · rw [ite_eq_right (not_le.2 hxy), ite_eq_right (not_lt.2 hxy.le),
      ite_eq_right (ne_of_lt hxy), add_zero]

/-- P4 (headline). -/
theorem decisiveRounds (bf : ℕ) : DecisiveRounds G bf := by
  intro L p ps h j j' x hj' hl hup
  classical
  let R : V → Finset ℕ := fun v => (Finset.Ico j j').filter fun k =>
    ¬ (x ∈ bSet (ps k) v ↔ x ∈ bSet (ps (k + 1)) v)
  have hsub : ((Finset.Ico j j').filter fun k =>
      ∃ v, ¬ (x ∈ bSet (ps k) v ↔ x ∈ bSet (ps (k + 1)) v)) ⊆ Finset.univ.biUnion R := by
    intro k hk
    obtain ⟨hk, v, hv⟩ := Finset.mem_filter.1 hk
    exact Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, Finset.mem_filter.2 ⟨hk, hv⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hone : ∀ v, (R v).card ≤ 1 := by
    intro v
    -- cycle maximum and upper part are constant on `[j, j']`
    have hlc : ∀ k, j ≤ k → k ≤ j' → cycMax (ps j) v = cycMax (ps k) v := by
      intro k hjk hkj
      induction k, hjk using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [ih (by omega), hl k hk (by omega)]
    have huc : ∀ k, j ≤ k → k ≤ j' → ∑ y ∈ (bSet (ps j) v).filter (x < ·), weight G y =
        ∑ y ∈ (bSet (ps k) v).filter (x < ·), weight G y := by
      intro k hjk hkj
      induction k, hjk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        rw [ih (by omega)]
        congr 1
        ext y
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hy, hxy⟩; exact ⟨(hup k hk (by omega) v y hxy).1 hy, hxy⟩
        · rintro ⟨hy, hxy⟩; exact ⟨(hup k hk (by omega) v y hxy).2 hy, hxy⟩
    let ι : ℕ → ℤ := fun k => if x ∈ bSet (ps k) v then weight G x else 0
    have hmono : ∀ a b, j ≤ a → a ≤ b → b ≤ j' → ι a ≤ ι b := by
      intro a b hja hab hbj
      have hM := truncationMonotone G bf L p ps h a b hab (hbj.trans hj') v
        (by rw [← hlc a hja (hab.trans hbj), ← hlc b (hja.trans hab) hbj]) x
      rw [sum_filter_le_split, sum_filter_le_split, ← huc a hja (hab.trans hbj),
        ← huc b (hja.trans hab) hbj] at hM
      simp only [ι]
      omega
    have hw : weight G x ≠ 0 := by
      unfold weight; split_ifs <;> simp
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [R, Finset.mem_filter, Finset.mem_Ico] at ha hb
    have key : ∀ a b, j ≤ a → a < b → b < j' →
        ¬ (x ∈ bSet (ps a) v ↔ x ∈ bSet (ps (a + 1)) v) →
        ¬ (x ∈ bSet (ps b) v ↔ x ∈ bSet (ps (b + 1)) v) → False := by
      intro a b hja hab hbj hca hcb
      have m1 := hmono a (a + 1) hja (by omega) (by omega)
      have m2 := hmono (a + 1) b (by omega) (by omega) (by omega)
      have m3 := hmono b (b + 1) (by omega) (by omega) (by omega)
      simp only [ι] at m1 m2 m3
      by_cases h1 : x ∈ bSet (ps a) v <;> by_cases h2 : x ∈ bSet (ps (a + 1)) v <;>
        by_cases h3 : x ∈ bSet (ps b) v <;> by_cases h4 : x ∈ bSet (ps (b + 1)) v <;>
        simp only [h1, h2, h3, h4, ite_true, ite_false, true_iff, iff_true, not_true,
          not_false_iff] at m1 m2 m3 hca hcb <;> omega
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (key a b ha.1.1 hab hb.1.2 ha.2 hb.2).elim
    · exact hab
    · exact (key b a hb.1.1 hab ha.1.2 hb.2 ha.2).elim
  calc ∑ v, (R v).card ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => hone v
    _ = Fintype.card V := by simp

end MercLib.HybridSI

end HybridSIBoundsProofs
