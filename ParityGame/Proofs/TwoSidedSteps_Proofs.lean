module

public import ParityGame.TwoSidedSteps
public import ParityGame.Proofs.TwoSidedCostCorrect_Fuel_Proofs

@[expose] public section TwoSidedStepsProofs

namespace ParityGame.TwoSidedCost

open Cslib.Algorithms.Lean TimeM

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/TwoSidedSteps_Pins.lean`.

Reuses the rank argument of `TwoSidedCostCorrect_Fuel_Proofs`: the fuel invariant `FInv` (kept by
every `run`, `runLoop_fuel`, and holding for fresh lifters, `mkLifter_finv`) gives
`steps ≤ pot ≤ n · rbase n ^ (2 h)` (`pot_le`) for each lifter, whatever the fuel. A restart
adds the steps of its two lifters, and there are at most `n + 1` restarts. -/

variable {n : ℕ}

/-- The steps of a lifter satisfying the fuel invariant are bounded by the potential bound. -/
theorem finv_steps_le (c : Ctx n) (st : LState n) (h : FInv c st) :
    st.steps ≤ n * rbase n ^ (2 * c.height) :=
  h.pot.trans (pot_le c st.measure h.ok)

/-- A restart adds at most the potential bounds of its two lifters to the step counter. -/
theorem roundLoop_steps (G : PGame n) (rem fuel : ℕ) (c0 c1 : Ctx n) :
    ∀ (f : ℕ) (s : SState n) (l0 l1 : LState n), FInv c0 l0 → FInv c1 l1 →
      (roundLoop G rem fuel c0 c1 f s l0 l1).ret.state.steps ≤
        s.steps + n * rbase n ^ (2 * c0.height) + n * rbase n ^ (2 * c1.height) := by
  intro f
  induction f with
  | zero =>
    intro s l0 l1 h0 h1
    have := finv_steps_le c0 l0 h0
    have := finv_steps_le c1 l1 h1
    simp only [roundLoop, ret_pure, Outcome.state]
    omega
  | succ f ih =>
    intro s l0 l1 h0 h1
    have hF0 : FInv c0 (run c0 rem fuel l0).ret.1 := (runLoop_fuel c0 (l0.steps + rem) fuel l0 h0).1
    have hF1 : FInv c1 (run c1 rem fuel l1).ret.1 := (runLoop_fuel c1 (l1.steps + rem) fuel l1 h1).1
    have a0 := finv_steps_le c0 _ hF0
    have a1 := finv_steps_le c1 _ hF1
    have b1 := finv_steps_le c1 l1 h1
    rw [roundLoop.eq_2]
    simp only [ret_bind]
    split
    · simp only [ret_pure, Outcome.state]; omega
    · split
      · simp only [ret_bind, ret_pure, Outcome.state]; omega
      · simp only [ret_bind]
        split
        · simp only [ret_pure, Outcome.state]; omega
        · split
          · simp only [ret_bind, ret_pure, Outcome.state]; omega
          · simp only [ret_bind]
            split
            · exact ih _ _ _ hF0 hF1
            · simp only [ret_bind, ret_pure, Outcome.state]; omega

/-- The per-restart step bound `2 n · rbase n ^ (2 (d + 1))`. -/
def restartSteps (G : PGame n) : ℕ := 2 * (n * rbase n ^ (2 * (G.d + 1)))

theorem outer_steps (G : PGame n) (fuel : ℕ) :
    ∀ (k : ℕ) (s : SState n), (outer G fuel k s).ret.1.steps ≤ s.steps + k * restartSteps G := by
  have hc : ∀ (A : VSet n) (p : Bool),
      n * rbase n ^ (2 * (mkLifter G A p).ret.1.height) ≤ n * rbase n ^ (2 * (G.d + 1)) := by
    intro A p
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by unfold rbase; omega)
    have := mkLifter_height G A p
    omega
  intro k
  induction k with
  | zero => intro s; simp [outer]
  | succ k ih =>
    intro s
    rw [outer.eq_2]
    simp only [ret_bind]
    split
    · simp only [ret_pure]; omega
    · simp only [ret_bind]
      have hR := roundLoop_steps G s.alive.count fuel (mkLifter G s.alive false).ret.1
        (mkLifter G s.alive true).ret.1 fuel { s with restarts := s.restarts + 1 }
        (mkLifter G s.alive false).ret.2 (mkLifter G s.alive true).ret.2
        (mkLifter_finv G s.alive false) (mkLifter_finv G s.alive true)
      have e0 := hc s.alive false
      have e1 := hc s.alive true
      have hk : (k + 1) * restartSteps G = k * restartSteps G + restartSteps G := by ring
      rw [hk]
      unfold restartSteps at *
      generalize roundLoop G s.alive.count fuel _ _ fuel _ _ _ = o at *
      match ho : o.ret with
      | .done s' =>
        simp only [Outcome.state, ho] at hR ⊢
        simp only [ret_pure]; omega
      | .oof s' =>
        simp only [Outcome.state, ho] at hR ⊢
        simp only [ret_pure]; omega
      | .next s' =>
        simp only [Outcome.state, ho] at hR ⊢
        have := ih s'
        omega

theorem restartSteps_mul_le (G : PGame n) : (n + 1) * restartSteps G ≤ stepsBound G := by
  unfold restartSteps stepsBound
  have hb : rbase n ≤ (n + 2) ^ 2 := by unfold rbase ebound; nlinarith
  have hp : rbase n ^ (2 * (G.d + 1)) ≤ (n + 2) ^ (4 * G.d + 4) := by
    calc rbase n ^ (2 * (G.d + 1)) ≤ ((n + 2) ^ 2) ^ (2 * (G.d + 1)) := Nat.pow_le_pow_left hb _
      _ = (n + 2) ^ (4 * G.d + 4) := by rw [← pow_mul]; ring_nf
  have h3 : (n + 1) * (2 * n) ≤ (n + 2) ^ 3 := by nlinarith
  calc (n + 1) * (2 * (n * rbase n ^ (2 * (G.d + 1))))
      = ((n + 1) * (2 * n)) * rbase n ^ (2 * (G.d + 1)) := by ring
    _ ≤ (n + 2) ^ 3 * (n + 2) ^ (4 * G.d + 4) := Nat.mul_le_mul h3 hp
    _ = (n + 2) ^ (4 * G.d + 7) := by rw [← pow_add]; ring_nf

/-! ### Headlines -/

theorem stepsBoundHolds (G : PGame n) (fuel : ℕ) : StepsBound G fuel := by
  unfold StepsBound
  simp only [solve, ret_bind, ret_pure]
  have := outer_steps G fuel (n + 1) ⟨fun _ => true, fun _ => false, 0, 0, 0⟩
  have := restartSteps_mul_le G
  simp only at *
  omega

theorem solveTimeFixedPrio (G : PGame n) (fuel : ℕ) : SolveTimeFixedPrio G fuel :=
  solvePolyOfSteps G fuel (fun _ => stepsBound G) (stepsBoundHolds G fuel)

theorem solvePolyFixedPrio (D : ℕ) : SolvePolyFixedPrio D := by
  set C := 680 * (D + 1) ^ 7
  refine ⟨4 * D + 14 + C, fun n G fuel hd => ?_⟩
  set X := n + G.m + 2
  have hX : 2 ≤ X := by omega
  have h1 := solveTimeFixedPrio G fuel
  unfold SolveTimeFixedPrio stepsBound costPoly at h1
  have hB : (n + 2) ^ (4 * G.d + 7) ≤ X ^ (4 * D + 7) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn : n + 1 ≤ X ^ (4 * D + 7) :=
    (show n + 1 ≤ X by omega).trans (Nat.le_self_pow (by omega) _)
  have hS : G.size ≤ (D + 1) * X := by
    have : D * 2 ≤ D * X := Nat.mul_le_mul_left D hX
    have : (D + 1) * X = D * X + X := by ring
    unfold PGame.size; omega
  have hS7 : G.size ^ 7 ≤ (D + 1) ^ 7 * X ^ 7 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hS 7
  have hC : C ≤ X ^ C :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hX _)
  calc (solve G fuel).time
      ≤ ((n + 2) ^ (4 * G.d + 7) + n + 1) * (340 * G.size ^ 7) := h1
    _ ≤ (2 * X ^ (4 * D + 7)) * (340 * ((D + 1) ^ 7 * X ^ 7)) := by
        apply Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hS7)
    _ = C * X ^ (4 * D + 14) := by simp only [C]; ring
    _ ≤ X ^ C * X ^ (4 * D + 14) := Nat.mul_le_mul_right _ hC
    _ = X ^ (4 * D + 14 + C) := by rw [← pow_add]; ring_nf

end ParityGame.TwoSidedCost

end TwoSidedStepsProofs
