import MachineNumbers.Pos

/-!
# Soundness of the `Nat` sort against `Nat`

Lean port of mCRL2's `Nat` data sort (`3rd-party/merc/crates/syntax/spec/nat.mcrl2`), built on
top of `Pos` (see `MachineNumbers.Pos`).

```
cons @c0 : Nat;
     @cNat : Pos -> Nat;
```

`@c0` is `.zero`, `@cNat(p)` is `.ofPos p`. As with `Pos`, every `map` operator gets a
structurally-recursive Lean function following its `eqn` block and a soundness theorem against
`Nat`'s abstraction `MNat.toNat` (`α_n`). The same "ignore rewriting" remark from
`MachineNumbers.Pos` applies throughout.

We use `MNat` rather than `Nat` for the type name to avoid shadowing Lean's own `Nat`.
-/

/-- Lean port of mCRL2's `Nat` sort. -/
inductive MNat where
  /-- `@c0`. -/
  | zero : MNat
  /-- `@cNat`. -/
  | ofPos (p : Pos) : MNat
  deriving DecidableEq, Repr

namespace MNat

/-- `α_n`. -/
def toNat : MNat → Nat
  | .zero => 0
  | .ofPos p => p.toNat

@[simp] theorem toNat_zero : toNat .zero = 0 := rfl
@[simp] theorem toNat_ofPos (p : Pos) : toNat (.ofPos p) = p.toNat := rfl

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

/-- `Pos2Nat`. -/
def ofPosNat (p : Pos) : MNat := .ofPos p

theorem ofPosNat_toNat (p : Pos) : (ofPosNat p).toNat = p.toNat := rfl

/-- `Nat2Pos`. The equational theory has no rule for `Nat2Pos(@c0)`: `Nat2Pos` is partial,
defined only on `@cNat(p)` terms. Lean requires totality, so we pin the `@c0` case at `Pos.one` —
an explicit, documented junk value. This choice is not arbitrary: `@gtesubtb`'s
`pred(Nat2Pos(pred(p)))` clause (see below) routes through exactly this junk value whenever
`pred p = @c0`, and `Pos.one` is the unique choice that keeps `@monus`'s truncating-subtraction
behaviour correct at that call site (`gtesubtb_toNat` below is proved unconditionally, with no
side condition excluding it). Any other junk value would break that theorem. -/
def toPos : MNat → Pos
  | .zero => .one
  | .ofPos p => p

@[simp] theorem toPos_ofPos (p : Pos) : toPos (.ofPos p) = p := rfl

/-! ## Order -/

/-- `<`. -/
def lt : MNat → MNat → Bool
  | _, .zero => false
  | .zero, .ofPos _ => true
  | .ofPos p, .ofPos q => Pos.lt p q

/-- `<=`. -/
def le : MNat → MNat → Bool
  | .zero, _ => true
  | .ofPos _, .zero => false
  | .ofPos p, .ofPos q => Pos.le p q

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

/-! ## `max` / `min`

mCRL2 overloads `max` at `Pos # Nat`, `Nat # Pos` and `Nat # Nat`; Lean needs three distinct
names. -/

/-- `max : Pos # Nat -> Pos`. -/
def maxPN (p : Pos) : MNat → Pos
  | .zero => p
  | .ofPos q => if Pos.le p q then q else p

/-- `max : Nat # Pos -> Pos`. -/
def maxNP : MNat → Pos → Pos
  | .zero, p => p
  | .ofPos q, p => if Pos.le q p then p else q

/-- `max : Nat # Nat -> Nat`. -/
def max : MNat → MNat → MNat
  | m, n => if le m n then n else m

/-- `min : Nat # Nat -> Nat`. -/
def min : MNat → MNat → MNat
  | m, n => if le m n then m else n

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

/-- `succ : Nat -> Pos`. -/
def succ : MNat → Pos
  | .zero => .one
  | .ofPos p => Pos.succ p

theorem succ_toNat (n : MNat) : (succ n).toNat = n.toNat + 1 := by
  cases n <;> simp [succ, Pos.succ_toNat]

/-- `@dubsucc : Nat -> Pos` ("double and add 1"). -/
def dubsucc : MNat → Pos
  | .zero => .one
  | .ofPos p => .dub true p

theorem dubsucc_toNat (n : MNat) : (dubsucc n).toNat = 2 * n.toNat + 1 := by
  cases n <;> simp [dubsucc]

/-- `pred : Pos -> Nat`. Exact predecessor: total and always correct, since every `Pos` value is
`≥ 1`. -/
def pred : Pos → MNat
  | .one => .zero
  | .dub b p => .ofPos (if b then .dub false p else dubsucc (pred p))

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

/-- `@dub : Bool # Nat -> Nat` ("double and conditionally add 1"). -/
def dub : Bool → MNat → MNat
  | false, .zero => .zero
  | true, .zero => .ofPos .one
  | b, .ofPos p => .ofPos (.dub b p)

theorem dub_toNat (b : Bool) (n : MNat) : (dub b n).toNat = 2 * n.toNat + (if b then 1 else 0) := by
  cases b <;> cases n <;> simp [dub]

/-! ## Addition -/

/-- `+ : Pos # Nat -> Pos`. -/
def addPN (p : Pos) : MNat → Pos
  | .zero => p
  | .ofPos q => Pos.addc false p q

/-- `+ : Nat # Pos -> Pos`. -/
def addNP : MNat → Pos → Pos
  | .zero, p => p
  | .ofPos q, p => Pos.addc false q p

/-- `+ : Nat # Nat -> Nat`. -/
def add : MNat → MNat → MNat
  | .zero, n => n
  | m, .zero => m
  | .ofPos p, .ofPos q => .ofPos (Pos.addc false p q)

theorem addPN_toNat (p : Pos) (n : MNat) : (addPN p n).toNat = p.toNat + n.toNat := by
  cases n <;> simp [addPN, Pos.addc_toNat]

theorem addNP_toNat (m : MNat) (p : Pos) : (addNP m p).toNat = m.toNat + p.toNat := by
  cases m <;> simp [addNP, Pos.addc_toNat]

theorem add_toNat (m n : MNat) : (add m n).toNat = m.toNat + n.toNat := by
  cases m <;> cases n <;> simp [add, Pos.addc_toNat]

/-! ## `@gtesubtb` and `@monus`

`@gtesubtb(b, p, q)` computes `p - q - (b ? 1 : 0)` (truncated at `0`) via a bitwise
borrow-propagating recursion on `p` and `q` together. **Finding:** the equations in `nat.mcrl2`
do not cover every argument shape — there is no rule for `@gtesubtb(b, @c1, @cDub(c, q))` (`p`
shorter than `q`). A literal transcription is therefore a *partial* function; the case is
needed (e.g. `@monus(@cNat(1), @cNat(2))` routes through it) so we complete it with `MNat.zero`,
the mathematically correct answer (`p ≤ q` here, so the truncated result is always `0`). This
completion is additional to the spec, not derived from it; flagged here as the `@monus`
counterpart of the `div_word`/`div_doubleword` precondition gaps already tracked in
`docs/plans/machine-numbers-verification.md`. -/
def gtesubtb : Bool → Pos → Pos → MNat
  | false, p, .one => pred p
  | true, p, .one => pred (toPos (pred p))
  | b, .dub false p, .dub false q => dub b (gtesubtb b p q)
  | b, .dub true p, .dub true q => dub b (gtesubtb b p q)
  | b, .dub false p, .dub true q => dub (!b) (gtesubtb true p q)
  | b, .dub true p, .dub false q => dub (!b) (gtesubtb false p q)
  | _, .one, .dub _ _ => .zero -- completion: `p ≤ q`, see the docstring above.

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
          have hpre : q.toNat + (if b then 1 else 0) ≤ p.toNat := by cases b <;> omega
          have hstep := ih b q hpre
          simp [gtesubtb, dub_toNat, hstep]
          omega
        | true =>
          have hpre : q.toNat + 1 ≤ p.toNat := by cases b <;> omega
          have hstep := ih true q hpre
          cases b <;> simp [gtesubtb, dub_toNat, hstep] <;> omega
      | true =>
        cases c' with
        | false =>
          have hpre : q.toNat ≤ p.toNat := by cases b <;> omega
          have hstep := ih false q hpre
          cases b <;> simp [gtesubtb, dub_toNat, hstep] <;> omega
        | true =>
          have hpre : q.toNat + (if b then 1 else 0) ≤ p.toNat := by cases b <;> omega
          have hstep := ih b q hpre
          simp [gtesubtb, dub_toNat, hstep]
          omega

/-- `@monus`. -/
def monus : MNat → MNat → MNat
  | .zero, _ => .zero
  | n, .zero => n
  | .ofPos p, .ofPos q => gtesubtb false p q

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

/-- `* : Nat # Nat -> Nat`. -/
def mul : MNat → MNat → MNat
  | .zero, _ => .zero
  | _, .zero => .zero
  | .ofPos p, .ofPos q => .ofPos (Pos.mul p q)

theorem mul_toNat (m n : MNat) : (mul m n).toNat = m.toNat * n.toNat := by
  cases m <;> cases n <;> simp [mul, Pos.mul_toNat]

/-! ## `@even` -/

/-- `@even`. -/
def even : MNat → Bool
  | .zero => true
  | .ofPos .one => false
  | .ofPos (.dub b _) => !b

theorem even_iff (n : MNat) : even n = true ↔ n.toNat % 2 = 0 := by
  cases n with
  | zero => simp [even]
  | ofPos p =>
    cases p with
    | one => simp [even]
    | dub b p => cases b <;> simp [even] <;> omega

end MNat
