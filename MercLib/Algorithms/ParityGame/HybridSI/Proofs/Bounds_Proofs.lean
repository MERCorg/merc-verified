module

public import MercLib.HybridSI.Bounds
public import MercLib.HybridSI.Proofs.Potential_Proofs
import all MercLib.HybridSI.Proofs.Correctness_Proofs
import all MercLib.HybridSI.Proofs.Epoch_Proofs
import all MercLib.HybridSI.Proofs.Filter_Proofs
import all MercLib.HybridSI.Proofs.Improvement_Proofs
import all MercLib.HybridSI.Proofs.Key_Proofs
import all MercLib.HybridSI.Proofs.Lasso_Proofs
import all MercLib.HybridSI.Proofs.Potential_Proofs
import all MercLib.HybridSI.Proofs.Termination_Proofs
import all MercLib.HybridSI.Proofs.Win_Proofs
import all MercLib.ParityGame.Proofs.Game_Proofs

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
private def mix (σ τ : V → V) (v : V) : V := if G.owner v = .zero then σ v else τ v

private theorem mix_even {σ τ : V → V} {v : V} (h : G.owner v = .zero) : mix G σ τ v = σ v :=
  ite_eq_left h

private theorem mix_odd {σ τ : V → V} {v : V} (h : G.owner v = .one) : mix G σ τ v = τ v :=
  ite_eq_right (by rw [h]; exact fun h' => Player.noConfusion h')

private theorem mix_edge {σ τ : V → V} (hσ : ∀ v, G.edge v (σ v)) (hτ : ∀ v, G.edge v (τ v)) (v : V) :
    G.edge v (mix G σ τ v) := by
  unfold mix; split_ifs
  · exact hσ v
  · exact hτ v

/-- A saddle profile is at least as good for Even as any profile with the same Odd moves. -/
private theorem saddle_ge {q : V → V} (hq : Saddle G q) (g : V → V) (hg : ∀ v, G.edge v (g v))
    (hgq : ∀ v, G.owner v = .one → g v = q v) (v : V) : key G g v ≤ key G q v := by
  have := K_le_of_dom (G := G) (f := q) (g := g) (i := .one) (fun u => by
    by_cases hu : G.owner u = .zero
    · simp only [K, kfor, negK_le_negK]
      exact hq.2.2 u hu (g u) (hg u)
    · rw [hgq u (owner_one_of_ne G hu)]) v
  simpa [K, kfor, negK_le_negK] using this

/-- A saddle profile is at most as good for Even as any edge-following profile with the same
    Even moves. -/
private theorem saddle_le {q : V → V} (hq : Saddle G q) (g : V → V) (hg : ∀ v, G.edge v (g v))
    (hgq : ∀ v, G.owner v = .zero → g v = q v) (v : V) : key G q v ≤ key G g v := by
  have := K_le_of_dom (G := G) (f := q) (g := g) (i := .zero) (fun u => by
    by_cases hu : G.owner u = .zero
    · rw [hgq u hu]
    · exact hq.2.1 u (owner_one_of_ne G hu) (g u) (hg u)) v
  simpa [K, kfor] using this

private theorem ownedBy_true_even {v : V} (h : G.owner v = .zero) : ownedBy G true v = false := by
  simp [ownedBy, h]

private theorem ownedBy_false_odd {v : V} (h : G.owner v = .one) : ownedBy G false v = false := by
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
private theorem respond_even_keep {bf : ℕ} {p q : V → V} (h : respond G false bf p = some q) {v : V}
    (hv : G.owner v = .one) : q v = p v :=
  (respond_spec G false bf p q h).1 v (ownedBy_false_odd G hv)

/-- Even's moves of a best response of Odd are those of its input. -/
private theorem respond_odd_keep {bf : ℕ} {p q : V → V} (h : respond G true bf p = some q) {v : V}
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

end MercLib.HybridSI

end HybridSIBoundsProofs
