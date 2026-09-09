import Mathlib.Tactic.Ring

/-!
# Definitions of the `Pos` sort

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
its `eqn` block. Some `eqn` rules exist only to normalise a *symbolic* subterm (e.g. an
un-reduced `succ(p)` sitting where a `@cDub`/`@c1` pattern is expected) during term rewriting;
since our `succ`/`@pospred` etc. are genuine total Lean functions rather than symbolic rewrite
targets, every term is always already in `Pos` normal form, so those rules are vacuously respected
and need no separate lemma. This is exactly the "ignore rewriting" carve-out: we model the *value*
semantics of the equational theory, not its confluent normalisation procedure.

Soundness theorems relating each operation to `Nat` via `Pos.toNat` (`α_p` in the plan's
notation) are in `MachineNumbers.Proofs.PosProofs`.
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

/-! ## Successor and predecessor -/

/-- `succ`.
```
succ(@c1)             = @cDub(false, @c1);
succ(@cDub(false, p)) = @cDub(true, p);
succ(@cDub(true, p))  = @cDub(false, succ(p));
```
-/
def succ : Pos → Pos
  | .one => .dub false .one
  | .dub false p => .dub true p
  | .dub true p => .dub false (succ p)

/-- `@pospred`. As specified, `@pospred(@c1) = @c1`: there is no `Pos` value below `@c1`, so the
equational theory pins the predecessor of `1` at `1` rather than leaving it undefined.
```
@pospred(@c1)                          = @c1;
@pospred(@cDub(false, @c1))            = @c1;
@pospred(@cDub(false, @cDub(b, p)))    = @cDub(true, @pospred(@cDub(b, p)));
@pospred(@cDub(true, p))               = @cDub(false, p);
```
-/
def pospred : Pos → Pos
  | .one => .one
  | .dub false .one => .one
  | .dub false (.dub b p) => .dub true (pospred (.dub b p))
  | .dub true p => .dub false p

/-! ## Order -/

/-! `<` and `<=` are mutually recursive on the shared `Pos` structure; `pos.mcrl2`'s additional
rules for comparing against an unreduced `succ(_)` term are the "normalise a symbolic subterm"
rules discussed above and are dropped here (see the module docstring).
```
p < @c1                         = false;
@c1 < @cDub(b, p)               = true;
@cDub(b, p) < @cDub(c, q)       = if(c => b, p < q, p <= q);
@c1 <= p                        = true;
@cDub(b, p) <= @c1              = false;
@cDub(b, p) <= @cDub(c, q)      = if(b => c, p <= q, p < q);
```
-/
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

/-! The `==` equations of `pos.mcrl2` pin down genericity and the unique binary representation:
```
@c1 == @cDub(b, p)          = false;
@cDub(b, p) == @c1          = false;
@cDub(b, p) == @cDub(b, q)  = p == q;
@cDub(false, p) == @cDub(true, q) = false;
@cDub(true, p) == @cDub(false, q) = false;
```
(`b` is non-linear on the left: the rule fires only when both bits agree.) Together these are
exactly "`@cDub(b,p) == @cDub(c,q) = b == c ∧ p == q`", which Lean's derived `DecidableEq` on the
inductive type satisfies trivially (every value has a canonical normal form).

## max / min

```
max(p, q) = if(p <= q, q, p);
min(p, q) = if(p <= q, p, q);
```
-/

/-- `max`. -/
def max (p q : Pos) : Pos := if le p q then q else p

/-- `min`. -/
def min (p q : Pos) : Pos := if le p q then p else q

/-! ## Addition -/

/-- `@addc`: ripple-carry addition with an explicit incoming carry bit.
```
p + q                          = @addc(false, p, q);
@addc(false, @c1, p)          = succ(p);
@addc(true, @c1, p)           = succ(succ(p));
@addc(b, p, @c1)              = if b then succ(succ(p)) else succ(p);
@addc(b, @cDub(c, p),
        @cDub(c, q))          = @cDub(b, @addc(c, p, q));
@addc(b, @cDub(false, p),
        @cDub(true, q))       = @cDub(!(b), @addc(b, p, q));
@addc(b, @cDub(true, p),
        @cDub(false, q))      = @cDub(!(b), @addc(b, p, q));
```
The three `@addc(b, p, @c1)` equations are folded into one Lean clause on `p` via `if b`. -/
def addc : Bool → Pos → Pos → Pos
  | false, .one, q => succ q
  | true, .one, q => succ (succ q)
  | b, p, .one => if b then succ (succ p) else succ p
  | b, .dub c p, .dub c' q =>
    if c == c' then .dub b (addc c p q)
    else .dub (!b) (addc b p q)

/-- `+`. Defined by `p + q = @addc(false, p, q)`. -/
def add (p q : Pos) : Pos := addc false p q

/-! ## Power of two (floor log₄) -/

/-- `@powerlog2`: the highest power of two whose square does not exceed `p` (equivalently, the
highest power of two ≤ `√p`; it peels off two bits at a time, halving the number of doublings).
```
@powerlog2(@c1)                    = @c1;
@powerlog2(@cDub(b, @c1))         = @c1;
@powerlog2(@cDub(b, @cDub(c, p))) = @cDub(false, @powerlog2(p));
```
-/
def powerlog2 : Pos → Pos
  | .one => .one
  | .dub _ .one => .one
  | .dub _ (.dub _ p) => .dub false (powerlog2 p)

/-! ## Multiplication -/

/-- `*`.
```
@c1 * p                            = p;
p * @c1                            = p;
@cDub(false, p) * q               = @cDub(false, p * q);
p * @cDub(false, q)               = @cDub(false, p * q);
@cDub(true, p) * @cDub(true, q)   =
    @cDub(true, @addc(false, p, @addc(false, q, @cDub(false, p * q))));
```
The `p * @c1` and `p * @cDub(false, q)` equations give the symmetric clauses on `q` below. -/
def mul : Pos → Pos → Pos
  | .one, q => q
  | .dub false p, q => .dub false (mul p q)
  | .dub true p, .one => .dub true p
  | .dub true p, .dub false q => .dub false (mul (.dub true p) q)
  | .dub true p, .dub true q => .dub true (addc false p (addc false q (.dub false (mul p q))))

end Pos
