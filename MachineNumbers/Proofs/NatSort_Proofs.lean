import MachineNumbers.NatSort
import MachineNumbers.Proofs.Pos_Proofs

/-!
# Soundness theorems for the `MNat` sort

Theorems relating each `MNat` operation to the corresponding `Nat` operation via `MNat.toNat`
(`α_n`). See `MachineNumbers.NatSort` for the definitions.
-/

namespace MNat

theorem toNat_injective {m n : MNat} (h : m.toNat = n.toNat) : m = n := by
  cases m with
  | zero =>
    cases n with
    | zero => rfl
    | ofPos p => exact absurd h (by have := Pos.toNat_pos p; simp; omega)
  | ofPos p =>
    cases n with
    | zero => exact absurd h (by have := Pos.toNat_pos p; simp; omega)
    | ofPos q => simp only [toNat_ofPos] at h; rw [Pos.toNat_injective h]

theorem toNat_inj {m n : MNat} : m.toNat = n.toNat ↔ m = n :=
  ⟨toNat_injective, fun h => h ▸ rfl⟩

/-! ## `Pos2Nat` / `Nat2Pos` -/

theorem ofPosNat_toNat (p : Pos) : (ofPosNat p).toNat = p.toNat := rfl

/-! ## Order -/

theorem lt_iff {m n : MNat} : lt m n = true ↔ m.toNat < n.toNat := by
  cases m with
  | zero =>
    cases n with
    | zero => simp [lt]
    | ofPos p => have := Pos.toNat_pos p; simp [lt]; omega
  | ofPos p =>
    cases n with
    | zero => simp [lt]
    | ofPos q => simp [lt, Pos.lt_iff]

theorem le_iff {m n : MNat} : le m n = true ↔ m.toNat ≤ n.toNat := by
  cases m with
  | zero => simp [le]
  | ofPos p =>
    cases n with
    | zero => have := Pos.toNat_pos p; simp [le]; omega
    | ofPos q => simp [le, Pos.le_iff]

/-! ## max / min -/

theorem maxPN_toNat (p : Pos) (n : MNat) : (maxPN p n).toNat = Nat.max p.toNat n.toNat := by
  cases n with
  | zero => simp [maxPN]
  | ofPos q =>
    simp only [maxPN]
    split_ifs with h
    · exact (Nat.max_eq_right (Pos.le_iff.mp h)).symm
    · have hnle : ¬ p.toNat ≤ q.toNat := fun hc => h (Pos.le_iff.mpr hc)
      have hle : q.toNat ≤ p.toNat := by omega
      exact (Nat.max_eq_left hle).symm

theorem maxNP_toNat (m : MNat) (p : Pos) : (maxNP m p).toNat = Nat.max m.toNat p.toNat := by
  cases m with
  | zero => simp [maxNP]
  | ofPos q =>
    simp only [maxNP]
    split_ifs with h
    · exact (Nat.max_eq_right (Pos.le_iff.mp h)).symm
    · have hnle : ¬ q.toNat ≤ p.toNat := fun hc => h (Pos.le_iff.mpr hc)
      have hle : p.toNat ≤ q.toNat := by omega
      exact (Nat.max_eq_left hle).symm

theorem max_toNat (m n : MNat) : (max m n).toNat = Nat.max m.toNat n.toNat := by
  simp only [max]
  split_ifs with h
  · exact (Nat.max_eq_right (le_iff.mp h)).symm
  · have hnle : ¬ m.toNat ≤ n.toNat := fun hc => h (le_iff.mpr hc)
    have hle : n.toNat ≤ m.toNat := by omega
    exact (Nat.max_eq_left hle).symm

theorem min_toNat (m n : MNat) : (min m n).toNat = Nat.min m.toNat n.toNat := by
  simp only [min]
  split_ifs with h
  · exact (Nat.min_eq_left (le_iff.mp h)).symm
  · have hnle : ¬ m.toNat ≤ n.toNat := fun hc => h (le_iff.mpr hc)
    have hle : n.toNat ≤ m.toNat := by omega
    exact (Nat.min_eq_right hle).symm

/-! ## Successor, predecessor, `@dub`, `@dubsucc` -/

theorem succ_toNat (n : MNat) : (succ n).toNat = n.toNat + 1 := by
  cases n <;> simp [succ, Pos.succ_toNat]

theorem dubsucc_toNat (n : MNat) : (dubsucc n).toNat = 2 * n.toNat + 1 := by
  cases n <;> simp [dubsucc]

theorem pred_toNat (p : Pos) : (pred p).toNat = p.toNat - 1 := by
  induction p with
  | one => simp [pred]
  | dub b p ih =>
    cases b with
    | true => simp [pred]
    | false =>
      have := Pos.toNat_pos p
      simp [pred, dubsucc_toNat, ih]
      omega

/-- `pred (dubsucc n) = 2 * n` numerically, regardless of whether `n` is `zero` or `ofPos _`:
`dubsucc n` is always odd, and taking its predecessor always lands back on the even `2 * n`. Used
by `gtesubtb_toNat`. -/
theorem pred_dubsucc_toNat (n : MNat) : (pred (dubsucc n)).toNat = 2 * n.toNat := by
  cases n <;> simp [dubsucc, pred]

theorem dub_toNat (b : Bool) (n : MNat) : (dub b n).toNat = 2 * n.toNat + (if b then 1 else 0) := by
  cases b <;> cases n <;> simp [dub]

/-! ## Addition -/

theorem addPN_toNat (p : Pos) (n : MNat) : (addPN p n).toNat = p.toNat + n.toNat := by
  cases n <;> simp [addPN, Pos.addc_toNat]

theorem addNP_toNat (m : MNat) (p : Pos) : (addNP m p).toNat = m.toNat + p.toNat := by
  cases m <;> simp [addNP, Pos.addc_toNat]

theorem add_toNat (m n : MNat) : (add m n).toNat = m.toNat + n.toNat := by
  cases m <;> cases n <;> simp [add, Pos.addc_toNat]

/-! ## `@gtesubtb` and `@monus` -/

/-- **Precondition finding**: unlike `Pos`'s operations, `@gtesubtb` (and hence `@monus`) is only
correct on the domain its recursion actually maintains: `q.toNat + (borrow) ≤ p.toNat`. Outside
it, the given equations are not merely partial (as flagged above) but, on some inputs, resolve to
a well-defined value that is *not* the truncated difference: e.g. `gtesubtb true 2 2` (reachable
as an internal recursion step from a top-level call with `p < q`, never from one with `p ≥ q`)
evaluates to `1`, not `0`. So `gtesubtb_toNat`/`monus_toNat` below are stated conditionally on
`p ≥ q + borrow`, mirroring the `div_word`-style conditional theorems in
`docs/plans/machine-numbers-verification.md` §3.5 item 5. -/
theorem gtesubtb_toNat (p : Pos) : ∀ b q, q.toNat + (if b then 1 else 0) ≤ p.toNat →
    (gtesubtb b p q).toNat = p.toNat - q.toNat - (if b then 1 else 0) := by
  induction p with
  | one =>
    intro b q h
    cases q with
    | one => cases b <;> simp [gtesubtb, pred, toPos]
    | dub c q =>
      exfalso
      have := Pos.toNat_pos q
      simp only [Pos.toNat_dub, Pos.toNat_one] at h
      cases b <;> cases c <;> omega
  | dub c p ih =>
    intro b q hle
    cases q with
    | one =>
      have := Pos.toNat_pos p
      cases b <;> cases c <;>
        simp [gtesubtb, pred, toPos, pred_toNat, dubsucc_toNat, pred_dubsucc_toNat] <;> omega
    | dub c' q =>
      have hp := Pos.toNat_pos p
      have hq := Pos.toNat_pos q
      simp only [Pos.toNat_dub] at hle
      cases c with
      | false =>
        cases c' with
        | false =>
          have hpre : q.toNat + (if b then 1 else 0) ≤ p.toNat := by
            by_cases hb : b <;> simp [hb] at hle ⊢ <;> omega
          have hstep := ih b q hpre
          simp [gtesubtb, dub_toNat, hstep]
          omega
        | true =>
          have hpre : q.toNat + 1 ≤ p.toNat := by
            by_cases hb : b <;> simp [hb] at hle ⊢ <;> omega
          have hstep := ih true q hpre
          cases b <;> simp [gtesubtb, dub_toNat, hstep] <;> omega
      | true =>
        cases c' with
        | false =>
          have hpre : q.toNat ≤ p.toNat := by
            by_cases hb : b <;> simp [hb] at hle ⊢ <;> omega
          have hstep := ih false q hpre
          cases b <;> simp [gtesubtb, dub_toNat, hstep] <;> omega
        | true =>
          have hpre : q.toNat + (if b then 1 else 0) ≤ p.toNat := by
            by_cases hb : b <;> simp [hb] at hle ⊢ <;> omega
          have hstep := ih b q hpre
          simp [gtesubtb, dub_toNat, hstep]
          omega

/-- Conditional, for the reason documented at `gtesubtb_toNat`: the given equations only compute
truncated subtraction when `n ≤ m`. -/
theorem monus_toNat (m n : MNat) (h : n.toNat ≤ m.toNat) :
    (monus m n).toNat = m.toNat - n.toNat := by
  cases m with
  | zero =>
    cases n with
    | zero => simp [monus]
    | ofPos q => exact absurd h (by have := Pos.toNat_pos q; simp; omega)
  | ofPos p =>
    cases n with
    | zero => simp [monus]
    | ofPos q =>
      simp only [monus, toNat_ofPos] at h ⊢
      exact gtesubtb_toNat p false q (by simpa using h)

/-! ## Multiplication -/

theorem mul_toNat (m n : MNat) : (mul m n).toNat = m.toNat * n.toNat := by
  cases m <;> cases n <;> simp [mul, Pos.mul_toNat]

/-! ## `@even` -/

theorem even_iff (n : MNat) : even n = true ↔ n.toNat % 2 = 0 := by
  cases n with
  | zero => simp [even]
  | ofPos p =>
    cases p with
    | one => simp [even]
    | dub b p => cases b <;> simp [even] <;> omega

/-! ## Exponentiation -/

theorem expPN_toNat (p : Pos) (n : MNat) : (expPN p n).toNat = p.toNat ^ n.toNat := by
  have main : ∀ k n, n.toNat = k → ∀ p, (expPN p n).toNat = p.toNat ^ n.toNat := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hkn p
      cases n with
      | zero =>
        subst k
        simp [expPN]
      | ofPos e =>
        cases e with
        | one =>
          subst k
          simp [expPN]
        | dub b q =>
          have hqpos : 0 < q.toNat := Pos.toNat_pos q
          have hq : (ofPos q : MNat).toNat < k := by
            cases b <;> simp [Pos.toNat_dub] at hkn ⊢ <;> omega
          have ihq : (expPN (Pos.mul p p) (.ofPos q)).toNat = (Pos.mul p p).toNat ^ q.toNat :=
            ih (ofPos q).toNat hq (.ofPos q) rfl (Pos.mul p p)
          subst k
          cases b <;> simp [expPN, Pos.mul_toNat, ihq]
          · rw [← pow_two, ← pow_mul]
          · rw [← pow_two, ← pow_mul, pow_succ]
            ring
  exact main n.toNat n rfl p

theorem expNN_toNat (m n : MNat) : (expNN m n).toNat = m.toNat ^ n.toNat := by
  cases n with
  | zero => simp [expNN]
  | ofPos e =>
    cases m with
    | zero =>
      have hE : e.toNat ≠ 0 := Nat.ne_of_gt (Pos.toNat_pos e)
      simp [expNN]
      rw [zero_pow hE]
    | ofPos p => simp [expNN, expPN_toNat]

/-! ## `@swap_zero` -/

theorem swapZero_toNat (m n : MNat) :
    (swapZero m n).toNat =
      if m.toNat = n.toNat then 0 else if n.toNat = 0 then m.toNat else n.toNat := by
  cases m with
  | zero =>
    cases n with
    | zero => simp [swapZero]
    | ofPos q =>
      have hqz : q.toNat ≠ 0 := Nat.ne_of_gt (Pos.toNat_pos q)
      simp [swapZero, hqz] <;> omega
  | ofPos p =>
    cases n with
    | zero => simp [swapZero]
    | ofPos q =>
      by_cases hpq : p = q
      · subst hpq
        simp [swapZero]
      · have hpneq : p.toNat ≠ q.toNat := fun h => hpq (Pos.toNat_injective h)
        have hqz : q.toNat ≠ 0 := by have := Pos.toNat_pos q; omega
        have hpz : p.toNat ≠ 0 := by have := Pos.toNat_pos p; omega
        have hbeq : (p == q) = false := by
          rw [Bool.beq_eq_decide_eq]
          exact (decide_eq_false_iff_not.mpr hpq)
        simp [swapZero, hbeq, hpneq, hqz, hpz]

/-! ## Division and remainder -/

/-- Contract of one `@ggdivmod` step: with `g` the remainder-so-far shifted in and `n` the quotient
so far, the step's quotient and remainder satisfy `quot * q + rem = 2 * n * q + g` (`@cDub(false,n)`
and `@cDub(true,n)` double `n`, so the invariant is `quot = 2·n` or `2·n + 1`) and `rem < q`. The
precondition `g.toNat < 2 * q.toNat` states that `g` was obtained by shifting a remainder `< q`. -/
theorem ggdivmod_sound (g n : MNat) (q : Pos) (hg : g.toNat < 2 * q.toNat) :
    (MNatPair.first (ggdivmod g n q)).toNat * q.toNat +
        (MNatPair.last (ggdivmod g n q)).toNat = 2 * n.toNat * q.toNat + g.toNat ∧
      (MNatPair.last (ggdivmod g n q)).toNat < q.toNat := by
  cases g with
  | zero =>
    simp [ggdivmod, dub_toNat] at hg ⊢
    omega
  | ofPos p =>
    by_cases hlt : Pos.lt p q = true
    · have hltn : p.toNat < q.toNat := Pos.lt_iff.mp hlt
      simp [ggdivmod, hlt, dub_toNat]
      omega
    · have hnot : ¬ p.toNat < q.toNat := fun h => hlt (Pos.lt_iff.mpr h)
      have hle : q.toNat ≤ p.toNat := Nat.le_of_not_gt hnot
      have hp2 : p.toNat < 2 * q.toNat := by simpa using hg
      have hrest : (gtesubtb false p q).toNat = p.toNat - q.toNat :=
        gtesubtb_toNat p false q (by simpa using hle)
      simp [ggdivmod, hlt, dub_toNat, hrest]
      constructor
      · have hqle : p.toNat - q.toNat + q.toNat = p.toNat := by omega
        have hs : (2 * n.toNat + 1) * q.toNat = 2 * n.toNat * q.toNat + q.toNat := by ring
        nlinarith [hqle, hs]
      · omega

/-- `@divmod` is Euclidean division: `first * q + last = p` and `last < q`. -/
theorem divmod_toNat (p q : Pos) :
    (MNatPair.first (divmod p q)).toNat * q.toNat + (MNatPair.last (divmod p q)).toNat = p.toNat ∧
      (MNatPair.last (divmod p q)).toNat < q.toNat := by
  have main : ∀ k p, p.toNat = k →
      ∀ q, (MNatPair.first (divmod p q)).toNat * q.toNat + (MNatPair.last (divmod p q)).toNat = p.toNat ∧
        (MNatPair.last (divmod p q)).toNat < q.toNat := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro p hpk q
      cases p with
      | one =>
        cases q with
        | one => simp [divmod]
        | dub c q0 =>
          simp [divmod]
          have hq0 := Pos.toNat_pos q0
          cases c <;> simp <;> omega
      | dub b p0 =>
        have hp0pos : 0 < p0.toNat := Pos.toNat_pos p0
        have hp0 : p0.toNat < k := by
          cases b <;> simp [Pos.toNat_dub] at hpk ⊢ <;> omega
        have hprev := ih p0.toNat hp0 p0 rfl q
        obtain ⟨hq0, hr0⟩ := hprev
        have hg : (dub b (MNatPair.last (divmod p0 q))).toNat < 2 * q.toNat := by
          have hqpos : 0 < q.toNat := Pos.toNat_pos q
          cases b <;> simp [dub_toNat] at hr0 ⊢ <;> omega
        have hgg := ggdivmod_sound
          (dub b (MNatPair.last (divmod p0 q))) (MNatPair.first (divmod p0 q)) q hg
        have hq0' : (divmod p0 q).1.toNat * q.toNat + (divmod p0 q).2.toNat = p0.toNat := by
          simpa using hq0
        simp [divmod, gdivmod]
        constructor
        · cases b <;> simp [dub_toNat] at hgg ⊢ <;> nlinarith [hq0', hgg.1]
        · exact hgg.2
  exact main p.toNat p rfl q

/-- The quotient of `@divmod` is the natural division. -/
theorem divmod_first_toNat (p q : Pos) :
    p.toNat / q.toNat = (MNatPair.first (divmod p q)).toNat := by
  have ⟨hfull, hlast⟩ := divmod_toNat p q
  have hqpos : 0 < q.toNat := Pos.toNat_pos q
  apply le_antisymm
  · have hlt : p.toNat / q.toNat < (MNatPair.first (divmod p q)).toNat + 1 := by
      rw [Nat.div_lt_iff_lt_mul hqpos]
      nlinarith [hfull, hlast]
    omega
  · rw [Nat.le_div_iff_mul_le hqpos]
    nlinarith [hfull]

theorem div_toNat (m : MNat) (q : Pos) : (div m q).toNat = m.toNat / q.toNat := by
  cases m with
  | zero => simp [div]
  | ofPos p =>
    simpa [div] using (divmod_first_toNat p q).symm

theorem mod_toNat (m : MNat) (q : Pos) : (mod m q).toNat = m.toNat % q.toNat := by
  cases m with
  | zero => simp [mod]
  | ofPos p =>
    have ⟨hfull, hlast⟩ := divmod_toNat p q
    have hlastv : p.toNat % q.toNat = (MNatPair.last (divmod p q)).toNat := by
      have hadd := Nat.mod_add_div p.toNat q.toNat
      rw [divmod_first_toNat p q] at hadd
      nlinarith [hfull, hadd]
    simp [mod]
    exact hlastv.symm

/-! ## `sqrt` -/

/-- Soundness of one `@sqrt_nat` step. The invariant is the one a binary (digit-by-digit) search
maintains: with `R` the approximation built from the bits chosen *above* the current candidate `a`
(`m = 2R`, `n = N − R²`), and `a` a power of two satisfying `R² ≤ N < (R + 2a)²`, calling
`sqrtNat n m a` returns `t` with `(R + t)² ≤ N < (R + t + 1)²`. The bounds are exactly the ones
`Pos.powerlog2_toNat` supplies for the top-level call (`a = @powerlog2`, `R = 0`). -/
theorem sqrtNat_sound : ∀ a : Pos, ∀ (n m : MNat) (N R : Nat),
    (∃ k, a.toNat = 2 ^ k) → m.toNat = 2 * R → n.toNat = N - R * R →
      R * R ≤ N → N < (R + 2 * a.toNat) ^ 2 →
      (R + (sqrtNat n m a).toNat) ^ 2 ≤ N ∧
        N < (R + (sqrtNat n m a).toNat + 1) ^ 2 := by
  intro a
  induction a with
  | one =>
    intro n m N R hpow hm hn hlo hhi
    by_cases hle : le n m = true
    · have hnm : N - R * R ≤ 2 * R := by
        simpa [hm, hn] using (MNat.le_iff.mp hle)
      simp [sqrtNat, hle]
      constructor
      · nlinarith [hlo]
      · have hnm' : N ≤ R * R + 2 * R := by omega
        nlinarith [hnm']
    · have hgt : 2 * R + R * R < N := by
        have hnot := fun h : n.toNat ≤ m.toNat => hle (MNat.le_iff.mpr h)
        simpa [hm, hn] using hnot
      simp [sqrtNat, hle]
      constructor
      · nlinarith [hgt]
      · simpa using hhi
  | dub b p ih =>
    intro n m N R hpow hm hn hlo hhi
    cases b with
    | true =>
      exfalso
      obtain ⟨k, hk⟩ := hpow
      have hp : 0 < p.toNat := Pos.toNat_pos p
      cases k <;> simp [Pos.toNat_dub, pow_succ] at hk <;> omega
    | false =>
      have haX : (ofPos (.dub false p) : MNat).toNat = 2 * p.toNat := by simp [Pos.toNat_dub]
      have hpk' : ∃ k, p.toNat = 2 ^ k := by
        obtain ⟨k, hk⟩ := hpow
        cases k with
        | zero =>
          exfalso
          have hp : 0 < p.toNat := Pos.toNat_pos p
          simp [Pos.toNat_dub] at hk
          omega
        | succ k =>
          refine ⟨k, ?_⟩
          simp [Pos.toNat_dub, pow_succ] at hk
          omega
      let xMNat : MNat := .ofPos (.dub false p)
      let sMNat : MNat := mul (add xMNat m) xMNat
      have hsMNat : sMNat.toNat = (2 * p.toNat + m.toNat) * (2 * p.toNat) := by
        simp [sMNat, xMNat, add_toNat, mul_toNat, haX]
      by_cases hlt : lt n sMNat = true
      · have hN_lt : N - R * R < (2 * p.toNat + 2 * R) * (2 * p.toNat) := by
          rw [← hn]
          rw [← hm]
          rw [← hsMNat]
          exact MNat.lt_iff.mp hlt
        have hhi_p : N < (R + 2 * p.toNat) ^ 2 := by
          have hN : N < R * R + (2 * p.toNat + 2 * R) * (2 * p.toNat) := by omega
          nlinarith [hN]
        have ihp := ih n m N R hpk' hm hn hlo hhi_p
        simp [sqrtNat, hlt, xMNat, sMNat]
        exact ihp
      · have hnot_lt : ¬ n.toNat < sMNat.toNat := fun h => hlt (MNat.lt_iff.mpr h)
        have hs_le : sMNat.toNat ≤ n.toNat := Nat.le_of_not_gt hnot_lt
        let n' := monus n sMNat
        let m' := add m (.dub false xMNat)
        let R' := R + 2 * p.toNat
        have hn' : n'.toNat = N - R' * R' := by
          unfold n' R'
          rw [monus_toNat (m := n) (n := sMNat) hs_le, hn]
          simp [sMNat, xMNat, add_toNat, mul_toNat, haX, hm]
          rw [Nat.sub_sub]
          ring
        have hm' : m'.toNat = 2 * R' := by
          unfold m' R'
          simp [xMNat, add_toNat, dub_toNat, hm, haX]
          ring
        have hlo' : R' * R' ≤ N := by
          unfold R'
          have h1 : (2 * p.toNat + 2 * R) * (2 * p.toNat) ≤ N - R * R := by
            nlinarith [hs_le, hsMNat, hm]
          have h2 : R * R + (2 * p.toNat + 2 * R) * (2 * p.toNat) ≤ N := by omega
          nlinarith [h2]
        have hhi' : N < (R' + 2 * p.toNat) ^ 2 := by
          unfold R'
          have hvalA : (Pos.dub false p).toNat = 2 * p.toNat := by simp [Pos.toNat_dub]
          rw [hvalA] at hhi
          nlinarith [hhi]
        have ihp := ih n' m' N R' hpk' hm' hn' hlo' hhi'
        have ht : (sqrtNat n m (.dub false p)).toNat =
            xMNat.toNat + (sqrtNat n' m' p).toNat := by
          unfold n' m'
          simp [sqrtNat, hlt, add_toNat, xMNat, sMNat]
        rw [ht]
        simp [R', xMNat, haX] at ihp ⊢
        simpa [add_assoc, add_left_comm, add_comm] using ihp

/-- `@sqrt` is the integer square root: `r² ≤ n < (r + 1)²` for `r = sqrt n`. -/
theorem sqrt_toNat (n : MNat) : (sqrt n).toNat ^ 2 ≤ n.toNat ∧
    n.toNat < ((sqrt n).toNat + 1) ^ 2 := by
  cases n with
  | zero => simp [sqrt]
  | ofPos p =>
    have hs := sqrtNat_sound (Pos.powerlog2 p) (.ofPos p) .zero p.toNat 0
      (Pos.powerlog2_is_pow2 p)
      (by simp)
      (by simp)
      (by omega)
      (by
        obtain ⟨hle, hlt⟩ := Pos.powerlog2_toNat p
        nlinarith)
    simpa [sqrt] using hs

end MNat
