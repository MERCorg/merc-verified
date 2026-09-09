import MachineNumbers.Pos
import Mathlib.Tactic.Linarith

/-!
# Soundness theorems for the `Pos` sort

Theorems relating each `Pos` operation to the corresponding `Nat` operation via `Pos.toNat`
(`α_p`). See `MachineNumbers.Pos` for the definitions.
-/

namespace Pos

/-- Every `Pos` value denotes a strictly positive natural: there is no "zero" term. -/
theorem toNat_pos (p : Pos) : 0 < p.toNat := by
  induction p with
  | one => simp
  | dub b p ih => cases b <;> simp <;> omega

/-- `α_p` is injective: `Pos` is exactly the standard binary-numeral representation, with no
duplicate encodings. -/
theorem toNat_injective {p q : Pos} (h : p.toNat = q.toNat) : p = q := by
  induction p generalizing q with
  | one =>
    cases q with
    | one => rfl
    | dub c q => exact absurd h (by have := toNat_pos q; cases c <;> simp <;> omega)
  | dub b p ih =>
    cases q with
    | one => exact absurd h (by have := toNat_pos p; cases b <;> simp <;> omega)
    | dub c q =>
      simp only [toNat_dub] at h
      have hbc : b = c := by cases b <;> cases c <;> simp_all <;> omega
      subst hbc
      have hpq : p.toNat = q.toNat := by cases b <;> omega
      rw [ih hpq]

theorem toNat_inj {p q : Pos} : p.toNat = q.toNat ↔ p = q :=
  ⟨toNat_injective, fun h => h ▸ rfl⟩

/-! ## Successor and predecessor -/

theorem succ_toNat (p : Pos) : (succ p).toNat = p.toNat + 1 := by
  induction p with
  | one => simp [succ]
  | dub b p ih => cases b <;> simp [succ] <;> omega

theorem pospred_toNat (p : Pos) :
    (pospred p).toNat = if p.toNat = 1 then 1 else p.toNat - 1 := by
  induction p with
  | one => simp [pospred]
  | dub b p ih =>
    cases b with
    | true =>
      have := toNat_pos p
      simp [pospred, toNat_dub]
      omega
    | false =>
      cases p with
      | one => simp [pospred]
      | dub c p =>
        have hp2 := toNat_pos p
        simp [pospred, toNat_dub] at ih ⊢
        split_ifs at ih ⊢ <;> omega

/-! ## Order -/

theorem lt_le_iff (p : Pos) :
    ∀ q, (lt p q = true ↔ p.toNat < q.toNat) ∧ (le p q = true ↔ p.toNat ≤ q.toNat) := by
  induction p with
  | one =>
    intro q
    cases q with
    | one => simp [lt, le]
    | dub c q => have := toNat_pos q; simp [lt, le]; omega
  | dub b p ih =>
    intro q
    cases q with
    | one =>
      have := toNat_pos p
      cases b <;> simp [lt, le] <;> omega
    | dub c q =>
      obtain ⟨ihlt, ihle⟩ := ih q
      cases b <;> cases c <;> simp_all [lt, le] <;> omega

theorem lt_iff {p q : Pos} : lt p q = true ↔ p.toNat < q.toNat := (lt_le_iff p q).1
theorem le_iff {p q : Pos} : le p q = true ↔ p.toNat ≤ q.toNat := (lt_le_iff p q).2

/-! ## max / min -/

theorem max_toNat (p q : Pos) : (max p q).toNat = Nat.max p.toNat q.toNat := by
  unfold max
  split
  next h => exact (Nat.max_eq_right (le_iff.mp h)).symm
  next h =>
    have hnle : ¬ p.toNat ≤ q.toNat := fun hc => h (le_iff.mpr hc)
    have : q.toNat ≤ p.toNat := by omega
    exact (Nat.max_eq_left this).symm

theorem min_toNat (p q : Pos) : (min p q).toNat = Nat.min p.toNat q.toNat := by
  unfold min
  split
  next h => exact (Nat.min_eq_left (le_iff.mp h)).symm
  next h =>
    have hnle : ¬ p.toNat ≤ q.toNat := fun hc => h (le_iff.mpr hc)
    have : q.toNat ≤ p.toNat := by omega
    exact (Nat.min_eq_right this).symm

/-! ## Addition -/

theorem addc_toNat (b : Bool) (p q : Pos) :
    (addc b p q).toNat = p.toNat + q.toNat + (if b then 1 else 0) := by
  induction p generalizing b q with
  | one => cases b <;> cases q <;> simp [addc, succ_toNat] <;> omega
  | dub c p ih =>
    cases q with
    | one => cases b <;> simp [addc, succ_toNat]
    | dub c' q =>
      by_cases hcc : c = c'
      · subst hcc
        have hstep := ih c q
        simp only [addc, beq_self_eq_true, if_true, toNat_dub, hstep]
        cases b <;> cases c <;> simp <;> omega
      · have hbeq : (c == c') = false := by simp [hcc]
        have hstep := ih b q
        simp only [addc, hbeq, toNat_dub]
        cases b <;> cases c <;> cases c' <;> simp_all <;> omega

theorem add_toNat (p q : Pos) : (add p q).toNat = p.toNat + q.toNat := by
  simp [add, addc_toNat]

/-! ## Multiplication -/

theorem mul_toNat (p q : Pos) : (mul p q).toNat = p.toNat * q.toNat := by
  induction p generalizing q with
  | one => simp [mul]
  | dub b p ih =>
    cases b with
    | false =>
      have hpq := ih q
      simp [mul, toNat_dub, hpq]
      ring
    | true =>
      induction q with
      | one => simp [mul]
      | dub c q ihq =>
        cases c with
        | false =>
          simp [mul, toNat_dub, ihq]
          ring
        | true =>
          have hpq := ih q
          simp [mul, toNat_dub, addc_toNat, hpq]
          ring

/-! ## Power of two (floor log₄) -/

/-- `powerlog2(p)` is the highest power of two whose square does not exceed `p` (equivalently, the
highest power of two ≤ `√p`): with `r = powerlog2(p).toNat`, `r² ≤ p.toNat < (2r)²`. This is the
bound `sqrt` (in `nat.mcrl2`) needs from its `@powerlog2(p)` initial estimate. -/
theorem powerlog2_toNat (p : Pos) :
    (powerlog2 p).toNat * (powerlog2 p).toNat ≤ p.toNat ∧
      p.toNat < 4 * (powerlog2 p).toNat * (powerlog2 p).toNat := by
  have main : ∀ n p, p.toNat = n →
      (powerlog2 p).toNat * (powerlog2 p).toNat ≤ p.toNat ∧
      p.toNat < 4 * (powerlog2 p).toNat * (powerlog2 p).toNat := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hpn
      cases p with
      | one => simp [powerlog2]
      | dub b p =>
        cases p with
        | one => cases b <;> simp [powerlog2]
        | dub c p =>
          have hp : 0 < p.toNat := toNat_pos p
          have ihp :=
            ih p.toNat (by cases b <;> cases c <;> simp [toNat_dub] at hpn hp ⊢ <;> omega)
              p rfl
          obtain ⟨hle, hlt⟩ := ihp
          unfold powerlog2
          cases b <;> cases c <;> simp [toNat_dub] at hle hlt ⊢ <;> constructor <;> nlinarith
  exact main p.toNat p rfl

/-- `powerlog2(p)` is (the toNat of) a power of two, as its def builds a `dub false` chain. -/
theorem powerlog2_is_pow2 (p : Pos) : ∃ k, (powerlog2 p).toNat = 2 ^ k := by
  have main : ∀ n p, p.toNat = n → ∃ k, (powerlog2 p).toNat = 2 ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hpn
      cases p with
      | one => exact ⟨0, by simp [powerlog2]⟩
      | dub b p =>
        cases p with
        | one => exact ⟨0, by simp [powerlog2]⟩
        | dub c p =>
          have hp : 0 < p.toNat := toNat_pos p
          have ihp :=
            ih p.toNat (by cases b <;> cases c <;> simp [toNat_dub] at hpn hp ⊢ <;> omega)
              p rfl
          obtain ⟨k, hk⟩ := ihp
          refine ⟨k + 1, ?_⟩
          simp [powerlog2, toNat_dub, hk, pow_succ]
          ring
  exact main p.toNat p rfl

end Pos
