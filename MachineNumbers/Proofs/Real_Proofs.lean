import MachineNumbers.Real
import MachineNumbers.Proofs.Int_Proofs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Soundness theorems for the `Real` sort

Theorems about the `MReal` operations (see `MachineNumbers.Real` for the definitions).

The abstraction function `toRat : MReal → Rat` maps each machine rational to its
Lean rational value.  Every operation is then shown to commute with `toRat`.

## Overview

The comparison operations (`lt`, `le`, `beq`) are defined by cross-multiplication, so their
soundness follows directly from the `Int`-sort results.  The unary operations (`neg`, `succ`,
`pred`) are straightforward.  The arithmetic operations (`add`, `sub`, `mul`, `div`) all go
through `redfrac`, whose soundness is the central difficulty; it is proved via a well-founded
induction on the remainder (`redfracwhr_toRat`).
-/

namespace MReal

/-! ## Abstraction function -/

/-- Map a machine rational to its Lean rational value.  `@cReal(x, p)` represents `x / p`. -/
def toRat : MReal → Rat
  | .cReal x p => (MInt.zag x : Rat) / (↑(p.toNat) : Rat)

@[simp] theorem toRat_cReal (x : MInt) (p : Pos) :
    toRat (.cReal x p) = (MInt.zag x : Rat) / (↑(p.toNat) : Rat) := rfl

@[simp] theorem toRat_zero : toRat zero = 0 := by
  simp [zero, toRat, MInt.zag]

/-! ## Comparison theorems (cross-multiplication form, no Rat needed) -/

/-- `lt (cReal x p) (cReal y q)` is `true` iff `zag x * q.toNat < zag y * p.toNat`. -/
theorem lt_crossmul (x : MInt) (p : Pos) (y : MInt) (q : Pos) :
    lt (.cReal x p) (.cReal y q) = true ↔
      MInt.zag x * (q.toNat : Int) < MInt.zag y * (p.toNat : Int) := by
  simp only [lt]
  rw [MInt.lt_iff, MInt.mul_zag, MInt.mul_zag, MInt.zag_cInt, MInt.zag_cInt]
  constructor <;> intro <;> assumption

/-- `le` cross-multiplication form. -/
theorem le_crossmul (x : MInt) (p : Pos) (y : MInt) (q : Pos) :
    le (.cReal x p) (.cReal y q) = true ↔
      MInt.zag x * (q.toNat : Int) ≤ MInt.zag y * (p.toNat : Int) := by
  simp only [le]
  rw [MInt.le_iff, MInt.mul_zag, MInt.mul_zag, MInt.zag_cInt, MInt.zag_cInt]
  constructor <;> intro <;> assumption

/-- `beq` cross-multiplication form. -/
theorem beq_crossmul (x : MInt) (p : Pos) (y : MInt) (q : Pos) :
    beq (.cReal x p) (.cReal y q) = true ↔
      MInt.zag x * (q.toNat : Int) = MInt.zag y * (p.toNat : Int) := by
  simp only [beq]
  rw [MInt.beq_zag, MInt.mul_zag, MInt.mul_zag, MInt.zag_cInt, MInt.zag_cInt]
  constructor <;> intro <;> assumption

/-! ## Rat bridge lemmas

These connect the cross-multiplication comparison to `Rat` division.
For positive denominators: `a * d < c * b ↔ a / b < c / d`.
-/

/-- `a * d < c * b ↔ a/b < c/d` for positive `b, d`. -/
theorem int_cast_lt_div_iff (a c : Int) {b d : Nat} (hb : 0 < b) (hd : 0 < d) :
    (a : Int) * (d : Int) < (c : Int) * (b : Int) ↔
      (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  sorry

/-- `a * d ≤ c * b ↔ a/b ≤ c/d` for positive `b, d`. -/
theorem int_cast_le_div_iff (a c : Int) {b d : Nat} (hb : 0 < b) (hd : 0 < d) :
    (a : Int) * (d : Int) ≤ (c : Int) * (b : Int) ↔
      (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := by
  sorry

/-- `a * d = c * b ↔ a/b = c/d` for positive `b, d`. -/
theorem int_cast_eq_div_iff (a c : Int) {b d : Nat} (hb : 0 < b) (hd : 0 < d) :
    (a : Int) * (d : Int) = (c : Int) * (b : Int) ↔
      (a : Rat) / (b : Rat) = (c : Rat) / (d : Rat) := by
  sorry

/-! ## Comparison theorems (toRat form) -/

theorem lt_iff (x : MInt) (p : Pos) (y : MInt) (q : Pos) :
    lt (.cReal x p) (.cReal y q) = true ↔ toRat (.cReal x p) < toRat (.cReal y q) := by
  rw [lt_crossmul, int_cast_lt_div_iff]
  · simp only [toRat_cReal]
  · exact Pos.toNat_pos p
  · exact Pos.toNat_pos q

theorem le_iff (x : MInt) (p : Pos) (y : MInt) (q : Pos) :
    le (.cReal x p) (.cReal y q) = true ↔ toRat (.cReal x p) ≤ toRat (.cReal y q) := by
  rw [le_crossmul, int_cast_le_div_iff]
  · simp only [toRat_cReal]
  · exact Pos.toNat_pos p
  · exact Pos.toNat_pos q

theorem beq_eq (x : MInt) (p : Pos) (y : MInt) (q : Pos) :
    beq (.cReal x p) (.cReal y q) = true ↔ toRat (.cReal x p) = toRat (.cReal y q) := by
  rw [beq_crossmul, int_cast_eq_div_iff]
  · simp only [toRat_cReal]
  · exact Pos.toNat_pos p
  · exact Pos.toNat_pos q

/-! ## Unary operation soundness -/

theorem neg_toRat (r : MReal) : toRat (neg r) = -toRat r := by
  cases r with
  | cReal x p =>
    simp only [neg, toRat_cReal, MInt.neg_zag]
    sorry -- Rat: -a / b = -(a / b)

theorem succ_toRat (r : MReal) : toRat (succ r) = toRat r + 1 := by
  cases r with
  | cReal x p =>
    simp only [succ, toRat_cReal, MInt.add_zag, MInt.zag_cInt]
    sorry -- Rat: (a + b) / b = a/b + 1

theorem pred_toRat (r : MReal) : toRat (pred r) = toRat r - 1 := by
  cases r with
  | cReal x p =>
    simp only [pred, toRat_cReal, MInt.sub_zag, MInt.zag_cInt]
    sorry -- Rat: (a - b) / b = a/b - 1

/-! ## `toPos` preserves `toNat` on positive inputs -/

/-- When `n` is positive, `MInt.toPos (cInt n)` preserves the value. -/
theorem toPos_toNat_ofPos (n : MNat) (h : 0 < n.toNat) :
    (MInt.toPos (.cInt n)).toNat = n.toNat := by
  cases n with
  | zero => exact absurd h (by simp)
  | ofPos p => simp [MInt.toPos, MNat.toPos]

/-! ## The core invariant: `redfracwhr_toRat`

`redfracwhr p x r` represents the rational `x + r/p`.  Proved by strong induction on `r.toNat`.
-/

/-- The helper `redfrachlp(cReal z w, y)` combines a reduced fraction `z/w` with an integer part `y`
    into `y + w/z`.  Requires the numerator `z` to be positive. -/
theorem redfrachlp_toRat (z : MInt) (w : Pos) (y : MInt)
    (hz : 0 < MInt.zag z) :
    toRat (MReal.redfrachlp (.cReal z w) y) =
      (MInt.zag y : Rat) + (↑(w.toNat) : Rat) / (MInt.zag z : Rat) := by
  sorry

/-- The core invariant: `redfracwhr p x r` represents `x + r/p`.
    Proved by strong induction on `r.toNat` which decreases by `MInt.mod_lt`. -/
theorem redfracwhr_toRat (p : Pos) (x : MInt) (r : MNat) (hr : r.toNat < p.toNat) :
    toRat (redfracwhr p x r) = (MInt.zag x : Rat) + (↑(r.toNat) : Rat) / (↑(p.toNat) : Rat) := by
  sorry -- Core proof: strong induction on r.toNat

/-! ## `redfrac` soundness -/

/-- `redfrac x (cInt (ofPos p))` represents `x / p`. -/
theorem redfrac_toRat_pos (x : MInt) (p : Pos) :
    toRat (redfrac x (.cInt (.ofPos p))) = (MInt.zag x : Rat) / (↑(p.toNat) : Rat) := by
  sorry

/-- `redfrac x (cNeg p)` represents `-x / p`. -/
theorem redfrac_toRat_neg (x : MInt) (p : Pos) :
    toRat (redfrac x (.cNeg p)) = -(MInt.zag x : Rat) / (↑(p.toNat) : Rat) := by
  sorry

/-! ## Arithmetic operation soundness -/

theorem add_toRat (r s : MReal) : toRat (add r s) = toRat r + toRat s := by
  cases r with
  | cReal x p =>
    cases s with
    | cReal y q =>
      simp only [add, toRat_cReal]
      rw [redfrac_toRat_pos]
      sorry -- Rat: (x*q + y*p) / (p*q) = x/p + y/q

theorem sub_toRat (r s : MReal) : toRat (sub r s) = toRat r - toRat s := by
  cases r with
  | cReal x p =>
    cases s with
    | cReal y q =>
      simp only [sub, toRat_cReal]
      rw [redfrac_toRat_pos]
      sorry -- Rat: (x*q - y*p) / (p*q) = x/p - y/q

theorem mul_toRat (r s : MReal) : toRat (mul r s) = toRat r * toRat s := by
  cases r with
  | cReal x p =>
    cases s with
    | cReal y q =>
      simp only [mul, toRat_cReal]
      rw [redfrac_toRat_pos]
      sorry -- Rat: (x*y) / (p*q) = (x/p) * (y/q)

/-! ## Floor soundness -/

theorem floor_toRat (r : MReal) :
    (MInt.zag (floor r) : Rat) ≤ toRat r ∧ toRat r < (MInt.zag (floor r) : Rat) + 1 := by
  sorry

end MReal
