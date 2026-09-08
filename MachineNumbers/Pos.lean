import Mathlib.Tactic.Ring

/-!
# Soundness of the `Pos` sort against `Nat`

Lean port of mCRL2's `Pos` data sort (`3rd-party/merc/crates/syntax/spec/pos.mcrl2`): the
positive naturals represented as binary digit chains, most-significant end terminated by `@c1`.

```
cons @c1 : Pos;
     @cDub : Bool # Pos -> Pos;
```

`@cDub(b, p)` prepends the bit `b` at the *least*-significant end: unwinding a chain from the
outside in walks the bits from LSB to MSB, with the innermost `@c1` standing for the (implicit,
always-`1`) leading bit. This is exactly the standard "cons-based" binary numeral trick (the same
representation as Mathlib's `PosNum`/Coq's `positive`): every `Pos` value denotes a unique
positive natural, with no leading-zero ambiguity to worry about.

For each `map` operator in `pos.mcrl2` we give a structurally-recursive Lean function following
its `eqn` block, and a theorem relating it to the corresponding `Nat` operation via `Pos.toNat`
(`α_p` in the plan's notation). Some `eqn` rules exist only to normalise a *symbolic* subterm
(e.g. an un-reduced `succ(p)` sitting where a `@cDub`/`@c1` pattern is expected) during term
rewriting; since our `succ`/`@pospred` etc. are genuine total Lean functions rather than symbolic
rewrite targets, every term is always already in `Pos` normal form, so those rules are vacuously
respected and need no separate lemma. This is exactly the "ignore rewriting" carve-out: we model
the *value* semantics of the equational theory, not its confluent normalisation procedure.
-/

/-- Lean port of mCRL2's `Pos` sort: `@c1` is `.one`, `@cDub(b, p)` is `.dub b p`. -/
inductive Pos where
  /-- `@c1`. -/
  | one : Pos
  /-- `@cDub`. -/
  | dub (b : Bool) (p : Pos) : Pos
  deriving DecidableEq, Repr

namespace Pos

/-- `α_p`: the abstraction of a `Pos` value into the natural number it denotes. -/
def toNat : Pos → Nat
  | .one => 1
  | .dub b p => 2 * p.toNat + (if b then 1 else 0)

@[simp] theorem toNat_one : toNat .one = 1 := rfl

@[simp] theorem toNat_dub (b : Bool) (p : Pos) :
    toNat (.dub b p) = 2 * p.toNat + (if b then 1 else 0) := rfl

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

/-- `succ`. -/
def succ : Pos → Pos
  | .one => .dub false .one
  | .dub false p => .dub true p
  | .dub true p => .dub false (succ p)

theorem succ_toNat (p : Pos) : (succ p).toNat = p.toNat + 1 := by
  induction p with
  | one => simp [succ]
  | dub b p ih => cases b <;> simp [succ] <;> omega

/-- `@pospred`. As specified, `@pospred(@c1) = @c1`: there is no `Pos` value below `@c1`, so the
equational theory pins the predecessor of `1` at `1` rather than leaving it undefined. -/
def pospred : Pos → Pos
  | .one => .one
  | .dub false .one => .one
  | .dub false (.dub b p) => .dub true (pospred (.dub b p))
  | .dub true p => .dub false p

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

/-! `<` and `<=` are mutually recursive on the shared `Pos` structure; `pos.mcrl2`'s additional
rules for comparing against an unreduced `succ(_)` term are the "normalise a symbolic subterm"
rules discussed above and are dropped here (see the module docstring). -/
mutual
def lt : Pos → Pos → Bool
  | _, .one => false
  | .one, .dub _ _ => true
  | .dub b p, .dub c q => if !c || b then lt p q else le p q

def le : Pos → Pos → Bool
  | .one, _ => true
  | .dub _ _, .one => false
  | .dub b p, .dub c q => if !b || c then le p q else lt p q
end

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

/-- `max`. -/
def max (p q : Pos) : Pos := if le p q then q else p

/-- `min`. -/
def min (p q : Pos) : Pos := if le p q then p else q

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

/-- `@addc`: ripple-carry addition with an explicit incoming carry bit. -/
def addc : Bool → Pos → Pos → Pos
  | false, .one, q => succ q
  | true, .one, q => succ (succ q)
  | b, p, .one => if b then succ (succ p) else succ p
  | b, .dub c p, .dub c' q =>
    if c == c' then .dub b (addc c p q)
    else .dub (!b) (addc b p q)

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

/-- `+`. -/
def add (p q : Pos) : Pos := addc false p q

theorem add_toNat (p q : Pos) : (add p q).toNat = p.toNat + q.toNat := by
  simp [add, addc_toNat]

/-! ## Multiplication -/

/-- `*`. -/
def mul : Pos → Pos → Pos
  | .one, q => q
  | .dub false p, q => .dub false (mul p q)
  | .dub true p, .one => .dub true p
  | .dub true p, .dub false q => .dub false (mul (.dub true p) q)
  | .dub true p, .dub true q => .dub true (addc false p (addc false q (.dub false (mul p q))))

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

end Pos
