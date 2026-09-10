import MachineNumbers.Int
import MachineNumbers.Proofs.NatSort_Proofs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity

/-!
# Soundness theorems for the `Int` sort

Theorems about the `MInt` operations (see `MachineNumbers.Int` for the definitions).
-/

namespace MInt

/-- `mod` of a value by `@@q` (a divisor) is a natural strictly below `q`; i.e. in value
`0 ≤ x mod q < q`. This holds for both sign cases by the `Nat`-sort soundness results
(`mod_toNat`, `gtesubtb_toNat`). It is the fact `Real`'s `@redfrac` reduction needs for
termination. -/
theorem mod_lt (x : MInt) (q : Pos) : (mod x q).toNat < q.toNat := by
  cases x with
  | cInt n =>
    have hq : 0 < q.toNat := Pos.toNat_pos q
    rw [mod, MNat.mod_toNat]
    exact Nat.mod_lt n.toNat hq
  | cNeg p =>
    have htp : 0 < (MNat.succ (MNat.mod (MNat.pred p) q)).toNat := by
      rw [MNat.succ_toNat]
      omega
    cases hle : Pos.le (MNat.succ (MNat.mod (MNat.pred p) q)) q with
    | true =>
      have htq : (MNat.succ (MNat.mod (MNat.pred p) q)).toNat ≤ q.toNat :=
        Pos.le_iff.mp hle
      have hgt : (MNat.gtesubtb false q (MNat.succ (MNat.mod (MNat.pred p) q))).toNat =
          q.toNat - (MNat.succ (MNat.mod (MNat.pred p) q)).toNat :=
        MNat.gtesubtb_toNat q false (MNat.succ (MNat.mod (MNat.pred p) q)) htq
      simp [mod, subPP, hle, hgt, toNat]
      omega
    | false =>
      have hq : 0 < q.toNat := Pos.toNat_pos q
      cases hg : MNat.gtesubtb false (MNat.succ (MNat.mod (MNat.pred p) q)) q with
      | zero => simp [mod, subPP, hle, negNat, hg, toNat] <;> omega
      | ofPos pp => simp [mod, subPP, hle, negNat, hg, toNat] <;> omega

/-- `zag` maps a machine integer to its signed `Int` value.
`zag` is the "locking" function taking `MInt` to the standard integers. -/
def zag : MInt → Int
  | .cInt n => n.toNat
  | .cNeg p => -(p.toNat : Int)

theorem zag_cInt (n : MNat) : zag (.cInt n) = (n.toNat : Int) := rfl

theorem zag_cNeg (p : Pos) : zag (.cNeg p) = -((p.toNat : Int)) := rfl

theorem negNat_zag (n : MNat) : zag (negNat n) = -((n.toNat : Int)) := by
  cases n with
  | zero => simp [negNat, zag]
  | ofPos p => simp [negNat, zag]

theorem neg_zag (x : MInt) : zag (neg x) = -zag x := by
  cases x with
  | cInt n =>
      rw [neg, negNat_zag]
      rfl
  | cNeg p =>
      simp [neg, zag]

theorem subNN_zag (m n : MNat) : zag (subNN m n) = (m.toNat : Int) - (n.toNat : Int) := by
  by_cases hs : MNat.le n m
  · have hmn : n.toNat ≤ m.toNat := MNat.le_iff.mp hs
    simp [subNN, hs, zag]
    rw [MNat.monus_toNat m n hmn]
    rw [Int.ofNat_sub hmn]
  · have hnm : MNat.le n m = false := by
      by_contra h
      exact hs (Bool.eq_true_of_not_eq_false h)
    have hnle : ¬ n.toNat ≤ m.toNat := by
      intro h
      exact hs (MNat.le_iff.mpr h)
    have hlt : m.toNat < n.toNat := lt_of_not_ge hnle
    have hmn : m.toNat ≤ n.toNat := le_of_lt hlt
    simp [subNN, hnm]
    rw [negNat_zag, MNat.monus_toNat n m hmn]
    rw [Int.ofNat_sub hmn]
    omega

theorem add_zag (x y : MInt) : zag (add x y) = zag x + zag y := by
  cases y with
  | cInt n =>
      cases x with
      | cInt m =>
          simp [add, zag]
          rw [MNat.add_toNat]
          omega
      | cNeg p =>
          rw [add, subNN_zag]
          simp [zag]
          omega
  | cNeg q =>
      cases x with
      | cInt n =>
          rw [add, subNN_zag]
          simp [zag]
          omega
      | cNeg p =>
          simp [add, zag]
          rw [Pos.add_toNat]
          omega

theorem mul_zag (x y : MInt) : zag (mul x y) = zag x * zag y := by
  cases y with
  | cInt n =>
      cases x with
      | cInt m =>
          simp [mul, zag]
          rw [MNat.mul_toNat]
          exact (Int.natCast_mul m.toNat n.toNat)
      | cNeg p =>
          rw [mul, negNat_zag, MNat.mul_toNat]
          simp [zag]
  | cNeg q =>
      cases x with
      | cInt n =>
          rw [mul, negNat_zag, MNat.mul_toNat]
          simp [zag]
          ring
      | cNeg p =>
          simp [mul, zag]
          rw [Pos.mul_toNat]
          push_cast
          ring

theorem succ_zag (x : MInt) : zag (succ x) = zag x + 1 := by
  cases x with
  | cInt n =>
      simp [succ, zag]
      rw [MNat.succ_toNat]
      omega
  | cNeg p =>
      have hp : 0 < p.toNat := Pos.toNat_pos p
      rw [succ, negNat_zag]
      simp [zag]
      rw [MNat.pred_toNat]
      rw [Int.ofNat_sub (by omega : 1 ≤ p.toNat)]
      omega

theorem pred_zag (x : MInt) : zag (pred x) = zag x - 1 := by
  cases x with
  | cInt n =>
      cases n with
      | zero => simp [pred, predNat, zag]
      | ofPos p => simp [pred, predNat, zag]; rw [MNat.pred_toNat]; rw [Int.ofNat_sub (Nat.succ_le_of_lt (Pos.toNat_pos p))]; norm_num
  | cNeg p =>
      simp [pred, zag]
      rw [Pos.succ_toNat]
      omega

theorem sub_zag (x y : MInt) : zag (sub x y) = zag x - zag y := by
  simp [sub, neg_zag, add_zag]
  omega

theorem lt_iff (x y : MInt) : lt x y = true ↔ zag x < zag y := by
  cases y with
  | cInt n =>
      cases x with
      | cInt m =>
          simp [lt, zag]
          rw [MNat.lt_iff]
      | cNeg p =>
          have hp : 0 < p.toNat := Pos.toNat_pos p
          simp [lt, zag]
          omega
  | cNeg q =>
      cases x with
      | cInt m =>
          have hq : 0 < q.toNat := Pos.toNat_pos q
          simp [lt, zag]
      | cNeg p =>
          simp [lt, zag]
          constructor
          · intro h
            have hp : q.toNat < p.toNat := Pos.lt_iff.mp h
            omega
          · intro h
            apply Pos.lt_iff.mpr
            omega

theorem le_iff (x y : MInt) : le x y = true ↔ zag x ≤ zag y := by
  cases y with
  | cInt n =>
      cases x with
      | cInt m =>
          simp [le, zag]
          rw [MNat.le_iff]
      | cNeg p =>
          have hp : 0 < p.toNat := Pos.toNat_pos p
          simp [le, zag]
  | cNeg q =>
      cases x with
      | cInt m =>
          have hq : 0 < q.toNat := Pos.toNat_pos q
          simp [le, zag]
          omega
      | cNeg p =>
          simp [le, zag]
          constructor
          · intro h
            have hp : q.toNat ≤ p.toNat := Pos.le_iff.mp h
            omega
          · intro h
            apply Pos.le_iff.mpr
            omega

theorem beq_eq (x y : MInt) : beq x y = true ↔ x = y := by
  simp [beq]

theorem zag_inj {x y : MInt} (h : zag x = zag y) : x = y := by
  cases y with
  | cInt n =>
      cases x with
      | cInt m =>
          have hm : m.toNat = n.toNat := by
            simp [zag] at h
            exact_mod_cast h
          exact congrArg MInt.cInt (MNat.toNat_inj.mp hm)
      | cNeg p =>
          have hp : 0 < p.toNat := Pos.toNat_pos p
          have hn0 : (0 : Int) ≤ (n.toNat : Int) := by
            exact_mod_cast Nat.zero_le n.toNat
          exfalso
          simp [zag] at h
          omega
  | cNeg q =>
      cases x with
      | cInt m =>
          have hq : 0 < q.toNat := Pos.toNat_pos q
          have hm0 : (0 : Int) ≤ (m.toNat : Int) := by
            exact_mod_cast Nat.zero_le m.toNat
          exfalso
          simp [zag] at h
          omega
      | cNeg p =>
          simp [zag] at h
          exact congrArg MInt.cNeg (Pos.toNat_inj.mp h)

theorem beq_zag (x y : MInt) : beq x y = true ↔ zag x = zag y := by
  constructor
  · intro h
    have hxy : x = y := (beq_eq x y).mp h
    rw [hxy]
  · intro h
    exact (beq_eq x y).mpr (zag_inj h)

theorem abs_zag (x : MInt) : zag (.cInt (abs x)) = (zag x).natAbs := by
  cases x with
  | cInt n => simp [abs, zag]
  | cNeg p => simp [abs, zag]

theorem mod_toNat_cNeg (p q : Pos) :
    (mod (.cNeg p) q).toNat = q.toNat - 1 - ((MNat.pred p).toNat % q.toNat) := by
  have hq : 0 < q.toNat := Pos.toNat_pos q
  have hA : (MNat.succ (MNat.mod (MNat.pred p) q)).toNat =
      (MNat.pred p).toNat % q.toNat + 1 := by
    rw [MNat.succ_toNat, MNat.mod_toNat]
  have hlt : (MNat.pred p).toNat % q.toNat < q.toNat := Nat.mod_lt _ hq
  have hAleq : (MNat.succ (MNat.mod (MNat.pred p) q)).toNat ≤ q.toNat := by
    rw [hA]
    omega
  have hle : Pos.le (MNat.succ (MNat.mod (MNat.pred p) q)) q = true := Pos.le_iff.mpr hAleq
  have hgt : (MNat.gtesubtb false q (MNat.succ (MNat.mod (MNat.pred p) q))).toNat =
      q.toNat - (MNat.succ (MNat.mod (MNat.pred p) q)).toNat :=
    MNat.gtesubtb_toNat q false (MNat.succ (MNat.mod (MNat.pred p) q)) hAleq
  simp [mod, subPP, hle, hgt, MInt.toNat]
  rw [hA]
  rw [hA] at hAleq
  omega

lemma floor_quot_rem (t q : Nat) (hq : 0 < q) :
    -↑(t + 1) = -(↑((t / q) + 1)) * (q : Int) + ↑(q - 1 - t % q) := by
  have hr1 : t % q + 1 ≤ q := Nat.succ_le_of_lt (Nat.mod_lt t hq)
  have hs : q - 1 - t % q = q - (t % q + 1) := by omega
  have hdiv : (t : Int) = (q : Int) * ↑(t / q) + ↑(t % q) := by
    rw [← Nat.cast_mul, ← Nat.cast_add]
    congr 1
    exact (Nat.div_add_mod t q).symm
  have hrem : ↑(q - 1 - t % q) = (q : Int) - 1 - ↑(t % q) := by
    rw [hs]
    rw [Int.ofNat_sub hr1]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  conv_lhs =>
    rw [Nat.cast_add]
    rw [hdiv]
  rw [hrem]
  rw [Nat.cast_add]
  ring

theorem div_mod_eq (x : MInt) (q : Pos) :
    zag x = (zag (div x q)) * (q.toNat : Int) + ((mod x q).toNat : Int) := by
  cases x with
  | cInt n =>
      have hd : (MNat.div n q).toNat = n.toNat / q.toNat := MNat.div_toNat n q
      have hmm : (MNat.mod n q).toNat = n.toNat % q.toNat := MNat.mod_toNat n q
      simp [div, mod, zag]
      rw [hd, hmm]
      rw [← Nat.cast_mul, Nat.mul_comm, ← Nat.cast_add]
      rw [Nat.div_add_mod]
  | cNeg p =>
      have hq : 0 < q.toNat := Pos.toNat_pos q
      have hp0 : 0 < p.toNat := Pos.toNat_pos p
      have hx := mod_toNat_cNeg p q
      have hp : (MNat.pred p).toNat + 1 = p.toNat := by
        rw [MNat.pred_toNat]
        omega
      have hs : (MNat.succ (MNat.div (MNat.pred p) q)).toNat =
          (MNat.pred p).toNat / q.toNat + 1 := by
        rw [MNat.succ_toNat, MNat.div_toNat]
      rw [div, hx]
      simp [zag]
      rw [hs, ← hp]
      exact floor_quot_rem (MNat.pred p).toNat q.toNat hq

theorem exp_zag (x : MInt) (n : MNat) : zag (exp x n) = zag x ^ n.toNat := by
  cases x with
  | cInt m =>
      simp [exp, zag]
      rw [MNat.expNN_toNat]
      rw [Int.natCast_pow]
  | cNeg p =>
      cases he : MNat.even n with
      | true =>
          have hev : Even n.toNat := Nat.even_iff.mpr ((MNat.even_iff n).mp he)
          simp [exp, he, zag]
          rw [MNat.expPN_toNat]
          rw [Even.neg_pow hev]
          rw [Int.natCast_pow]
      | false =>
          have h0 : ¬ n.toNat % 2 = 0 := by
            intro hz
            have htrue : MNat.even n = true := (MNat.even_iff n).mpr hz
            simp [htrue] at he
          have hodd : Odd n.toNat := (Nat.not_even_iff_odd).mp ((Iff.not Nat.even_iff).mpr h0)
          simp [exp, he, zag]
          rw [MNat.expPN_toNat]
          rw [Odd.neg_pow hodd]
          rw [Int.natCast_pow]

end MInt