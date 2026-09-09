import MachineNumbers.Int
import MachineNumbers.Proofs.Int_Proofs

/-!
# Definitions of the `Real` sort

Lean port of mCRL2's `Real` data sort (`3rd-party/merc/crates/syntax/spec/real.mcrl2`), built on
top of `MInt`/`MNat`/`Pos` (see `MachineNumbers.Int` and `MachineNumbers.NatSort`).

```
cons @cReal : Int # Pos -> Real;
```

`@cReal(x, p)` is `.cReal x p` and denotes the rational `x / p`. As everywhere in this project,
every `map` operator gets a function following its `eqn` block; `==` is *not* the derived equality
of the inductive type here, because the equational theory equates two `@cReal`s by
cross-multiplying:

```
@cReal(x, p) == @cReal(y, q)  =  (x * @cInt(@cNat(q))) == (y * @cInt(@cNat(p)));
@cReal(x, p) <  @cReal(y, q)  =  (x * @cInt(@cNat(q))) <  (y * @cInt(@cNat(p)));
@cReal(x, p) <= @cReal(y, q)  =  (x * @cInt(@cNat(q))) <= (y * @cInt(@cNat(p)));
```

We use `MReal` rather than `Real` to avoid shadowing Lean's own `Real`.

## `@redfrac` and its termination

The core of the sort is the reduction `@redfrac : Int # Int -> Real`, which normalises a fraction
`x/d` into its (uniquely determined) simplest form using mCRL2's continued-fraction-style whole
and remainder decomposition:

```
@redfrac(x, @cNeg(p))            = @redfrac(-(x), @cInt(@cNat(p)));   -- flip both signs
@redfrac(x, @cInt(@cNat(p)))     = @redfracwhr(p, x div p, x mod p);
@redfracwhr(p, x, @c0)           = @cReal(x, @c1);
@redfracwhr(p, x, @cNat(q))      = @redfrachlp(@redfrac(@cInt(@cNat(p)), @cInt(@cNat(q))), x);
```

`@redfrachlp` combines an integer part `y` with a reduced fraction `@cReal(z, w)`:

```
@redfrachlp(@cReal(z, w), y)  =  @cReal(@cInt(@cNat(w)) + (y * z), Int2Pos(z));
```

Unfolding `@redfrac`'s positive-denominator equation inside `@redfracwhr`'s `@cNat(q)` clause, the
single recursion `@redfracwhr(p, x, @cNat(q)) = @redfrachlp(@redfracwhr(q, (p) div q, p mod q), x)`
is the Euclidean step: the new remainder `p mod q` has value strictly below `q` = the value of the
old remainder, so the recursion is well-founded with measure the *value of the remainder* — this is
`MInt.mod_lt`. (This inlining is the value-semantics analogue of the "ignore rewriting" carve-out
documented in `MachineNumbers.Pos`; `@redfrac` itself is then a non-recursive sign-normalising
dispatcher.) Since mCRL2 leaves `@redfrac(x, @cInt(@c0))` and division by zero without rules, those
cases are completed with explicit, documented junk values.

`floor` is mCRL2's truncated (floor) division `x div p`; `ceil`/`round` are defined from it exactly
as in the output equations.
-/

/-- Lean port of mCRL2's `Real` sort. -/
inductive MReal where
  /-- `@cReal`. Denotes the rational `x / p`. -/
  | cReal (x : MInt) (p : Pos) : MReal
  deriving Repr

namespace MReal

/-- The zero value `@cReal(@cInt(@c0), @c1)`, used as the documented junk completion. -/
def zero : MReal := .cReal (.cInt .zero) .one

/-- `Int2Real`. -/
def ofInt (x : MInt) : MReal := .cReal x .one

/-- `Nat2Real`. -/
def ofNat (n : MNat) : MReal := .cReal (.cInt n) .one

/-- `Pos2Real`. -/
def ofPos (p : Pos) : MReal := .cReal (.cInt (.ofPos p)) .one

/-! ## Equality and order

```
@cReal(x, p) == @cReal(y, q)  =  (x * @cInt(@cNat(q))) == (y * @cInt(@cNat(p)));
@cReal(x, p) <  @cReal(y, q)  =  (x * @cInt(@cNat(q))) <  (y * @cInt(@cNat(p)));
@cReal(x, p) <= @cReal(y, q)  =  (x * @cInt(@cNat(q))) <= (y * @cInt(@cNat(p)));
```
-/

/-- `==`, value-level equality on the represented rationals (cross-multiplication). -/
def beq : MReal → MReal → Bool
  | .cReal x p, .cReal y q =>
      MInt.beq (MInt.mul x (.cInt (.ofPos q))) (MInt.mul y (.cInt (.ofPos p)))

/-- `<`. -/
def lt : MReal → MReal → Bool
  | .cReal x p, .cReal y q =>
      MInt.lt (MInt.mul x (.cInt (.ofPos q))) (MInt.mul y (.cInt (.ofPos p)))

/-- `<=`. -/
def le : MReal → MReal → Bool
  | .cReal x p, .cReal y q =>
      MInt.le (MInt.mul x (.cInt (.ofPos q))) (MInt.mul y (.cInt (.ofPos p)))

/-! ## `@redfrac` / `@redfracwhr` / `@redfrachlp`

```
@redfrac(x, @cNeg(p))            =  @redfrac(-(x), @cInt(@cNat(p)));
@redfrac(x, @cInt(@cNat(p)))     =  @redfracwhr(p, x div p, x mod p);
@redfracwhr(p, x, @c0)           =  @cReal(x, @c1);
@redfracwhr(p, x, @cNat(q))      =  @redfrachlp(@redfrac(@cInt(@cNat(p)), @cInt(@cNat(q))), x);
@redfrachlp(@cReal(x, p), y)     =  @cReal(@cInt(@cNat(p)) + (y * x), Int2Pos(x));
```
`@redfrac(x, @cInt(@c0))` (division by zero) has no rule in the spec; it is completed with the
zero value. See the module docstring for the termination argument. -/

/-- `@redfrachlp`: combine a reduced fraction `@cReal(z, w)` with an integer part `y` into a single
`@cReal`. -/
def redfrachlp (r : MReal) (y : MInt) : MReal :=
  match r with
  | .cReal z w => .cReal (MInt.add (.cInt (.ofPos w)) (MInt.mul y z)) (MInt.toPos z)

/-- `@redfracwhr`: whole-and-remainder reduction. Recurses on the *value* of the remainder (`r`),
which strictly decreases at each Euclidean step by `MInt.mod_lt`. -/
def redfracwhr (p : Pos) (x : MInt) (r : MNat) : MReal :=
  match r with
  | .zero => .cReal x .one
  | .ofPos q =>
      (redfracwhr q (MInt.div (.cInt (.ofPos p)) q) (MInt.mod (.cInt (.ofPos p)) q)).redfrachlp x
  termination_by r.toNat
  decreasing_by
    simp [MNat.toNat_ofPos]
    exact MInt.mod_lt (.cInt (.ofPos p)) q

/-- `@redfrac`: reduce a fraction `x/d` to normal form, normalising the sign of the denominator
first and then reducing by the whole-and-remainder decomposition. Non-recursive (the recursion is
inside `redfracwhr`). -/
def redfrac (x d : MInt) : MReal :=
  match d with
  | .cNeg p => redfracwhr p (MInt.div (MInt.neg x) p) (MInt.mod (MInt.neg x) p)
  | .cInt .zero => zero -- completion: division by zero has no rule
  | .cInt (.ofPos p) => redfracwhr p (MInt.div x p) (MInt.mod x p)

/-! ## Conversions back to the other sorts

```
Real2Int(@cReal(x, @c1))  =  x;
Real2Nat(@cReal(x, @c1))  =  Int2Nat(x);
Real2Pos(@cReal(x, @c1))  =  Int2Pos(x);
```
Only the denominator-`@c1` (whole-number) cases are specified; the others are partial and are
completed with explicit junk values (only reachable if a stray non-integral denominator is fed in;
the reduction `@redfrac` always produces `@cReal(x, @c1)` for integral values). -/

/-- `Real2Int`. -/
def toInt : MReal → MInt
  | .cReal x .one => x
  | .cReal _ _ => .cInt .zero -- completion: junk

/-- `Real2Nat`. -/
def toNat : MReal → MNat
  | .cReal x .one => MInt.toNat x
  | .cReal _ _ => .zero -- completion: junk

/-- `Real2Pos`. -/
def toPos : MReal → Pos
  | .cReal x .one => MInt.toPos x
  | .cReal _ _ => .one -- completion: junk

/-! ## `min` / `max` / `abs` / unary minus / `succ` / `pred`

```
min(r, s)          = if(r < s, r, s);
max(r, s)          = if(r < s, s, r);
abs(r)             = if(r < @cReal(@cInt(@c0), @c1), -(r), r);
-(@cReal(x, p))    = @cReal(-(x), p);
succ(@cReal(x, p)) = @cReal(x + @cInt(@cNat(p)), p);
pred(@cReal(x, p)) = @cReal(x - @cInt(@cNat(p)), p);
```
-/

/-- `- : Real -> Real`. -/
def neg : MReal → MReal
  | .cReal x p => .cReal (MInt.neg x) p

/-- `min`. -/
def min (r s : MReal) : MReal := if lt r s then r else s

/-- `max`. -/
def max (r s : MReal) : MReal := if lt r s then s else r

/-- `abs`. -/
def abs (r : MReal) : MReal := if lt r zero then neg r else r

/-- `succ : Real -> Real`. -/
def succ : MReal → MReal
  | .cReal x p => .cReal (MInt.add x (.cInt (.ofPos p))) p

/-- `pred : Real -> Real`. -/
def pred : MReal → MReal
  | .cReal x p => .cReal (MInt.sub x (.cInt (.ofPos p))) p

/-! ## Arithmetic

```
@cReal(x, p) + @cReal(y, q)  =  @redfrac((x * @cInt(@cNat(q))) + (y * @cInt(@cNat(p))), @cInt(@cNat(p * q)));
@cReal(x, p) - @cReal(y, q)  =  @redfrac((x * @cInt(@cNat(q))) - (y * @cInt(@cNat(p))), @cInt(@cNat(p * q)));
@cReal(x, p) * @cReal(y, q)  =  @redfrac(x * y, @cInt(@cNat(p * q)));
```
The two zero-absorption rules `r * @cReal(@cInt(@c0), p) = @cReal(@cInt(@c0), @c1)` (and its
mirror) are consequences of the generic `*` rule because `@redfrac(0, p * q) = @cReal(0, @c1)`
(`0 mod (p * q) = 0`), so they are not ported separately. -/

/-- `+ : Real # Real -> Real`. -/
def add : MReal → MReal → MReal
  | .cReal x p, .cReal y q =>
      redfrac (MInt.add (MInt.mul x (.cInt (.ofPos q))) (MInt.mul y (.cInt (.ofPos p))))
              (.cInt (.ofPos (Pos.mul p q)))

/-- `- : Real # Real -> Real`. -/
def sub : MReal → MReal → MReal
  | .cReal x p, .cReal y q =>
      redfrac (MInt.sub (MInt.mul x (.cInt (.ofPos q))) (MInt.mul y (.cInt (.ofPos p))))
              (.cInt (.ofPos (Pos.mul p q)))

/-- `* : Real # Real -> Real`. -/
def mul : MReal → MReal → MReal
  | .cReal x p, .cReal y q =>
      redfrac (MInt.mul x y) (.cInt (.ofPos (Pos.mul p q)))

/-! ## Division

```
y != @cInt(@c0)  ->  @cReal(x, p) / @cReal(y, q)  =  @redfrac(x * @cInt(@cNat(q)), y * @cInt(@cNat(p)));
p / q            =  @redfrac(@cInt(@cNat(p)), @cInt(@cNat(q)));
n != @c0         ->  m / n  =  @redfrac(@cInt(m), @cInt(n));
y != @cInt(@c0)  ->  x / y  =  @redfrac(x, y);
```
Division by a zero *value* has no rule; we complete it with `@cReal(@cInt(@c0), @c1)` (the zero
value). Since values are in normal form, a value is zero exactly when its numerator is the term
`@cInt(@c0)`, so the guard is the representational `==` check on the numerator. -/

/-- `/ : Real # Real -> Real`. Guarded by the denominator not being the zero value. -/
def div : MReal → MReal → MReal
  | .cReal x p, .cReal y q =>
      if MInt.beq y (.cInt .zero) then zero
      else redfrac (MInt.mul x (.cInt (.ofPos q))) (MInt.mul y (.cInt (.ofPos p)))

/-- `/ : Pos # Pos -> Real`. -/
def divPP (p q : Pos) : MReal :=
  redfrac (.cInt (.ofPos p)) (.cInt (.ofPos q))

/-- `/ : Nat # Nat -> Real`. Guarded by `n != @c0`. -/
def divNN (m n : MNat) : MReal :=
  if n == .zero then zero else redfrac (.cInt m) (.cInt n)

/-- `/ : Int # Int -> Real`. Guarded by `y != @cInt(@c0)`. -/
def divII (x y : MInt) : MReal :=
  if MInt.beq y (.cInt .zero) then zero else redfrac x y

/-! ## Exponentiation

```
exp(@cReal(x, p), @cInt(n))     =  @redfrac(exp(x, n), @cInt(@cNat(exp(p, n))));
x != @cInt(@c0)  ->  exp(@cReal(x, p), @cNeg(q))  =  @redfrac(@cInt(@cNat(exp(p, @cNat(q)))), exp(x, @cNat(q)));
```
The negative-exponent rule is guarded (`x != @cInt(@c0)`, i.e. the base is not the zero value);
when the guard fails the base is `0` and we complete with the zero value. -/

/-- `exp : Real # Int -> Real`. -/
def exp (r : MReal) (e : MInt) : MReal :=
  match r, e with
  | .cReal x p, .cInt n =>
      redfrac (MInt.exp x n) (.cInt (.ofPos (MNat.expPN p n)))
  | .cReal x p, .cNeg q =>
      if MInt.beq x (.cInt .zero) then zero
      else redfrac (.cInt (.ofPos (MNat.expPN p (.ofPos q)))) (MInt.exp x (.ofPos q))

/-! ## `floor` / `ceil` / `round`

```
floor(@cReal(x, p))  =  x div p;
ceil(r)              =  -(floor(-(r)));
round(r)             =  floor(r + @cReal(@cInt(@cNat(@c1)), @cDub(false, @c1)));
```
The added constant in `round` is the half `@cReal(1, 2)`; `x div p` is mCRL2's truncated (floor)
division on the represented numerator. -/

/-- `floor : Real -> Int` (mCRL2 truncated division, i.e. the floor of the represented value). -/
def floor : MReal → MInt
  | .cReal x p => MInt.div x p

/-- `ceil : Real -> Int`. `ceil(r) = -(floor(-(r)))`. -/
def ceil (r : MReal) : MInt := MInt.neg (floor (neg r))

/-- `round : Real -> Int`. `round(r) = floor(r + 1/2)`. -/
def round (r : MReal) : MInt := floor (add r (.cReal (.cInt (.ofPos .one)) (.dub false .one)))

/-! ## Convenience lemmas for the operations -/

@[simp] theorem toInt_cReal_one (x : MInt) : toInt (.cReal x .one) = x := rfl

@[simp] theorem neg_cReal (x : MInt) (p : Pos) : neg (.cReal x p) = .cReal (MInt.neg x) p := rfl

@[simp] theorem succ_cReal (x : MInt) (p : Pos) :
    succ (.cReal x p) = .cReal (MInt.add x (.cInt (.ofPos p))) p := rfl

@[simp] theorem pred_cReal (x : MInt) (p : Pos) :
    pred (.cReal x p) = .cReal (MInt.sub x (.cInt (.ofPos p))) p := rfl

@[simp] theorem floor_cReal (x : MInt) (p : Pos) : floor (.cReal x p) = MInt.div x p := rfl

end MReal