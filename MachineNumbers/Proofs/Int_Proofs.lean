import MachineNumbers.Int
import MachineNumbers.Proofs.NatSort_Proofs

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

end MInt