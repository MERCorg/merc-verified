import MachineNumbers.NatSort

/-!
# Definitions of the `Int` sort

Lean port of mCRL2's `Int` data sort (`3rd-party/merc/crates/syntax/spec/int.mcrl2`), built on
top of `MNat` and `Pos` (see `MachineNumbers.NatSort` and `MachineNumbers.Pos`).

```
cons @cInt : Nat -> Int;
     @cNeg : Pos -> Int;
```

`@cInt(n)` is `.cInt n` (a natural), `@cNeg(p)` is `.cNeg p` (a negative with magnitude `p`).
As everywhere in this project, every `map` operator gets a structurally-recursive Lean function
following its `eqn` block, and the "ignore rewriting" remark from `MachineNumbers.Pos` applies
(equations whose only point is to normalise a symbolic `succ(p)`/`pred(_)` subterm are dropped).

We use `MInt` rather than `Int` to avoid shadowing Lean's own `Int`.

Where the equational theory is *partial*, the missed cases are completed with an explicit,
documented junk value (marked `-- completion:` in the code), exactly as done for `MNat.toPos`
and `MNat.gtesubtb` in `MachineNumbers.NatSort`.

The two genuinely non-trivial totals of the sort are the conversion `Int2Nat`/`Int2Pos` (which the
theory only defines on `@cInt(n)`) and `MInt.mod_lt`, a small soundness fact used by `Real`'s
`@redfrac` reduction; it lives here because the termination of that reduction is a property of
`Int`'s `div`/`mod`.
-/

/-- Lean port of mCRL2's `Int` sort. -/
inductive MInt where
  /-- `@cInt`. -/
  | cInt (n : MNat) : MInt
  /-- `@cNeg`. -/
  | cNeg (p : Pos) : MInt
  deriving DecidableEq, Repr

namespace MInt

/-- The `==` equations
```
@cInt(m) == @cInt(n) = m == n;
@cInt(n) == @cNeg(p) = false;
@cNeg(p) == @cInt(n) = false;
@cNeg(p) == @cNeg(q) = p == q;
```
are exactly the derived equality of the inductive type (constructor-disjoint with per-field
equality), exactly as for `Pos`/`Nat`.

`Nat2Int`. -/
def ofNat : MNat → MInt := .cInt

/-- `Pos2Int` (`@cInt(@cNat(p))`). -/
def ofPos (p : Pos) : MInt := .cInt (.ofPos p)

/-- `Int2Nat`. The theory only has `Int2Nat(@cInt(n)) = n`; there is no rule for `@cNeg(p)`.
Lean requires totality, so a negative magnitude is pinned at `MNat.zero` — an explicit, documented
junk value (it is never reached in value: `mod`, its only caller, always returns a natural). -/
def toNat : MInt → MNat
  | .cInt n => n
  | .cNeg _ => .zero -- completion: junk

/-- `Int2Pos`. The theory only has `Int2Pos(@cInt(n)) = Nat2Pos(n)` (see `MNat.toPos`, itself
partial); `@cNeg(p)` is completed with `Pos.one` (only ever reached through `Real`'s helper
`@redfrachlp`, whose arguments are positive in value). -/
def toPos : MInt → Pos
  | .cInt n => MNat.toPos n
  | .cNeg _ => .one -- completion: junk

@[simp] theorem toNat_cInt (n : MNat) : toNat (.cInt n) = n := rfl
@[simp] theorem toNat_cNeg (p : Pos) : toNat (.cNeg p) = .zero := rfl

@[simp] theorem toPos_cInt (n : MNat) : toPos (.cInt n) = MNat.toPos n := rfl
@[simp] theorem toPos_cNeg (p : Pos) : toPos (.cNeg p) = .one := rfl

/-- `==` as a `Bool`, definitionally the derived equality. -/
def beq (x y : MInt) : Bool := x == y

/-! ## Order

```
@cInt(m) < @cInt(n)     = m < n;
@cInt(n) < @cNeg(p)     = false;
@cNeg(p) < @cInt(n)     = true;
@cNeg(p) < @cNeg(q)     = q < p;
@cInt(m) <= @cInt(n)    = m <= n;
@cInt(n) <= @cNeg(p)    = false;
@cNeg(p) <= @cInt(n)    = true;
@cNeg(p) <= @cNeg(q)    = q <= p;
```
-/

/-- `<`. The `succ`-normalisation `<` rules are the usual dropped rewriting rules. -/
def lt : MInt → MInt → Bool
  | .cInt m, .cInt n => MNat.lt m n
  | .cInt _, .cNeg _ => false
  | .cNeg _, .cInt _ => true
  | .cNeg p, .cNeg q => Pos.lt q p

/-- `<=`. -/
def le : MInt → MInt → Bool
  | .cInt m, .cInt n => MNat.le m n
  | .cInt _, .cNeg _ => false
  | .cNeg _, .cInt _ => true
  | .cNeg p, .cNeg q => Pos.le q p

/-! ## `max` / `min`

mCRL2 overloads `max` at `Pos # Int`, `Int # Pos`, `Nat # Int`, `Int # Nat` and `Int # Int`.
```
max(p, @cInt(n))     = max(p, n);
max(p, @cNeg(q))     = p;
max(@cInt(n), p)     = max(n, p);
max(@cNeg(q), p)     = p;
max(m, @cInt(n))     = if(m <= n, n, m);
max(n, @cNeg(p))     = n;
max(@cInt(m), n)     = if(m <= n, n, m);
max(@cNeg(p), n)     = n;
max(x, y)            = if(x <= y, y, x);
min(x, y)            = if(x <= y, x, y);
```
The right-hand `max(p, n)`/`max(n, p)`/`max(m, n)` uses are the `Nat`-sort overloads from
`MachineNumbers.NatSort`. -/

/-- `max : Pos # Int -> Pos`. -/
def maxPI (p : Pos) : MInt → Pos
  | .cInt n => MNat.maxPN p n
  | .cNeg _ => p

/-- `max : Int # Pos -> Pos`. -/
def maxIP : MInt → Pos → Pos
  | .cInt n, p => MNat.maxNP n p
  | .cNeg _, p => p

/-- `max : Nat # Int -> Nat`. -/
def maxNI (m : MNat) : MInt → MNat
  | .cInt n => MNat.max m n
  | .cNeg _ => m

/-- `max : Int # Nat -> Nat`. -/
def maxIN : MInt → MNat → MNat
  | .cInt m, n => MNat.max m n
  | .cNeg _, n => n

/-- `max : Int # Int -> Int`. -/
def max (x y : MInt) : MInt := if le x y then y else x

/-- `min : Int # Int -> Int`. -/
def min (x y : MInt) : MInt := if le x y then x else y

/-- `abs : Int -> Nat`.
```
abs(@cInt(n))  = n;
abs(@cNeg(p))  = @cNat(p);
```
-/
def abs : MInt → MNat
  | .cInt n => n
  | .cNeg p => .ofPos p

/-! ## Unary minus

```
-p          = @cNeg(p);          -- : Pos -> Int
-@c0        = @cInt(@c0);        -- : Nat -> Int
-@cNat(p)   = @cNeg(p);
-@cInt(n)   = -n;                -- : Int -> Int, RHS is the Nat overload
-@cNeg(p)   = @cInt(@cNat(p));
```
-/

/-- `- : Pos -> Int`. -/
def negPos (p : Pos) : MInt := .cNeg p

/-- `- : Nat -> Int`. -/
def negNat : MNat → MInt
  | .zero => .cInt .zero
  | .ofPos p => .cNeg p

/-- `- : Int -> Int`. -/
def neg : MInt → MInt
  | .cInt n => negNat n
  | .cNeg p => .cInt (.ofPos p)

/-! ## Successor / predecessor

```
succ(@cInt(n))     = @cInt(@cNat(succ(n)));     -- RHS succ : Nat -> Pos
succ(@cNeg(p))     = -(pred(p));                 -- RHS pred : Pos -> Nat, - : Nat -> Int
pred(@c0)          = @cNeg(@c1);                 -- pred : Nat -> Int
pred(@cNat(p))     = @cInt(pred(p));             -- RHS pred : Pos -> Nat
pred(@cInt(n))     = pred(n);                    -- RHS pred : Nat -> Int
pred(@cNeg(p))     = @cNeg(succ(p));             -- RHS succ : Pos -> Pos
```
-/

/-- `succ : Int -> Int`. -/
def succ : MInt → MInt
  | .cInt n => .cInt (.ofPos (MNat.succ n))
  | .cNeg p => negNat (MNat.pred p)

/-- `pred : Nat -> Int`. -/
def predNat : MNat → MInt
  | .zero => .cNeg .one
  | .ofPos p => .cInt (MNat.pred p)

/-- `pred : Int -> Int`. -/
def pred : MInt → MInt
  | .cInt n => predNat n
  | .cNeg p => .cNeg (Pos.succ p)

/-! ## Addition

```
@cInt(m) + @cInt(n)    = @cInt(m + n);
@cInt(n) + @cNeg(p)    = n - @cNat(p);           -- - : Nat # Nat -> Int
@cNeg(p) + @cInt(n)    = n - @cNat(p);
@cNeg(p) + @cNeg(q)    = @cNeg(@addc(false, p, q));
```
-/

/-- `- : Nat # Nat -> Int`.
```
n <= m  ->  m - n = @cInt(@monus(m, n));
m < n   ->  m - n = -(@monus(n, m));
```
-/
def subNN (m n : MNat) : MInt :=
  if MNat.le n m then .cInt (MNat.monus m n) else negNat (MNat.monus n m)

/-- `- : Pos # Pos -> Int`.
```
q <= p  ->  p - q = @cInt(@gtesubtb(false, p, q));
p < q   ->  p - q = -(@gtesubtb(false, q, p));
```
-/
def subPP (p q : Pos) : MInt :=
  if Pos.le q p then .cInt (MNat.gtesubtb false p q) else negNat (MNat.gtesubtb false q p)

/-- `+ : Int # Int -> Int`. -/
def add : MInt → MInt → MInt
  | .cInt m, .cInt n => .cInt (MNat.add m n)
  | .cInt n, .cNeg p => subNN n (.ofPos p)
  | .cNeg p, .cInt n => subNN n (.ofPos p)
  | .cNeg p, .cNeg q => .cNeg (Pos.add p q)

/-- `- : Int # Int -> Int`, by `x - y = x + (-y)`. -/
def sub (x y : MInt) : MInt := add x (neg y)

/-! ## Multiplication

```
@cInt(m) * @cInt(n)       = @cInt(m * n);
@cInt(n) * @cNeg(p)       = -(@cNat(p) * n);
@cNeg(p) * @cInt(n)       = -(@cNat(p) * n);
@cNeg(p) * @cNeg(q)       = @cInt(@cNat(p * q));
```
-/

/-- `* : Int # Int -> Int`. -/
def mul : MInt → MInt → MInt
  | .cInt m, .cInt n => .cInt (MNat.mul m n)
  | .cInt n, .cNeg p => negNat (MNat.mul (.ofPos p) n)
  | .cNeg p, .cInt n => negNat (MNat.mul (.ofPos p) n)
  | .cNeg p, .cNeg q => .cInt (.ofPos (Pos.mul p q))

/-! ## Division and remainder

```
@cInt(n) div p                  = @cInt(n div p);              -- : Int # Pos -> Int
@cNeg(p) div q                  = @cNeg(succ(pred(p) div q));
@cInt(n) mod p                  = n mod p;                     -- : Int # Pos -> Nat
@cNeg(p) mod q                  = Int2Nat(q - succ(pred(p) mod q));
```
Division is mCRL2's truncated (floor) division; the negative case maps the non-negative
`succ(pred(p) div q)` magnitude into a `@cNeg`, and the negative remainder is expressed as
`q - (1 + ((p - 1) mod q))` (which is always non-negative in value, so `Int2Nat`'s junk case is
never reached).
-/

/-- `div : Int # Pos -> Int`. -/
def div : MInt → Pos → MInt
  | .cInt n, q => .cInt (MNat.div n q)
  | .cNeg p, q => .cNeg (MNat.succ (MNat.div (MNat.pred p) q))

/-- `mod : Int # Pos -> Nat`. -/
def mod : MInt → Pos → MNat
  | .cInt n, q => MNat.mod n q
  | .cNeg p, q => toNat (subPP q (MNat.succ (MNat.mod (MNat.pred p) q)))

/-! ## Exponentiation

```
exp(@cInt(m), n)            = @cInt(exp(m, n));
@even(n)  ->  exp(@cNeg(p), n) = @cInt(@cNat(exp(p, n)));
!@even(n) ->  exp(@cNeg(p), n) = @cNeg(exp(p, n));
```
-/

/-- `exp : Int # Nat -> Int`. -/
def exp : MInt → MNat → MInt
  | .cInt m, n => .cInt (MNat.expNN m n)
  | .cNeg p, n => if MNat.even n then .cInt (.ofPos (MNat.expPN p n)) else .cNeg (MNat.expPN p n)

end MInt