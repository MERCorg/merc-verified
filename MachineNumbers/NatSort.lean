import MachineNumbers.Pos

/-!
# Definitions of the `Nat` sort

Lean port of mCRL2's `Nat` data sort (`3rd-party/merc/crates/syntax/spec/nat.mcrl2`), built on
top of `Pos` (see `MachineNumbers.Pos`).

```
cons @c0 : Nat;
     @cNat : Pos -> Nat;
```

`@c0` is `.zero`, `@cNat(p)` is `.ofPos p`. As with `Pos`, every `map` operator gets a
structurally-recursive Lean function following its `eqn` block. The same "ignore rewriting" remark
from `MachineNumbers.Pos` applies throughout.

We use `MNat` rather than `Nat` for the type name to avoid shadowing Lean's own `Nat`.

Soundness theorems relating each operation to `Nat` via `MNat.toNat` (`α_n`) are in
`MachineNumbers.Proofs.NatSortProofs`.
-/

/-- Lean port of mCRL2's `Nat` sort. -/
inductive MNat where
  /-- `@c0`. -/
  | zero : MNat
  /-- `@cNat`. -/
  | ofPos (p : Pos) : MNat
  deriving DecidableEq, Repr

/-- Lean port of mCRL2's auxilliary `@NatPair` sort (`nat.mcrl2`): a pair of `Nat`s.
```
cons @cPair : Nat # Nat -> @NatPair;
```
`@cPair(m, n)` is `.pair m n`.
```
@cPair(m, n) == @cPair(u, v) = (m == u) && (n == v);
@cPair(m, n) < @cPair(u, v)  = (m < u) || ((m == u) && (n < v));
@cPair(m, n) <= @cPair(u, v) = (m < u) || ((m == u) && (n <= v));
```
As for `Nat`, `==` is the derived equality of the inductive type. The `<`/`<=` pair-order rules
are quoted here for completeness but no translated operation needs them, so they are not ported. -/
inductive MNatPair where
  /-- `@cPair`. -/
  | pair (m n : MNat) : MNatPair
  deriving DecidableEq, Repr

namespace MNatPair

/-- `@first`.
```
@first(@cPair(m, n)) = m;
```
-/
@[simp] def first : MNatPair → MNat
  | .pair m _ => m

/-- `@last`.
```
@last(@cPair(m, n)) = n;
```
-/
@[simp] def last : MNatPair → MNat
  | .pair _ n => n

/-- The `first` projection agrees with the `.1` projector generated for `pair`. -/
@[simp] theorem first_eq_proj (m : MNatPair) : first m = m.1 := by
  cases m <;> rfl

/-- The `last` projection agrees with the `.2` projector generated for `pair`. -/
@[simp] theorem last_eq_proj (m : MNatPair) : last m = m.2 := by
  cases m <;> rfl

end MNatPair

namespace MNat

/-- `α_n`. -/
def toNat : MNat → Nat
  | .zero => 0
  | .ofPos p => p.toNat

@[simp] theorem toNat_zero : toNat .zero = 0 := rfl
@[simp] theorem toNat_ofPos (p : Pos) : toNat (.ofPos p) = p.toNat := rfl

/-! ## `Pos2Nat` / `Nat2Pos`

```
Pos2Nat(p)        = @cNat(p);
Nat2Pos(@cNat(p)) = p;
```
-/

/-- `Pos2Nat`. -/
def ofPosNat (p : Pos) : MNat := .ofPos p

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

/-! ## Order

```
@c0 < @cNat(p)         = true;
n < @c0                = false;
@cNat(p) < @cNat(q)    = p < q;

@c0 <= n               = true;
@cNat(p) <= @c0        = false;
@cNat(p) <= @cNat(q)   = p <= q;
```
-/

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

/-! ## `max` / `min`

mCRL2 overloads `max` at `Pos # Nat`, `Nat # Pos` and `Nat # Nat`; Lean needs three distinct
names.
```
max(p, @c0)                  = p;
max(p, @cNat(q))             = if(p <= q, q, p);
max(@c0, p)                  = p;
max(@cNat(p), q)             = if(p <= q, q, p);
max(m, n)                    = if(m <= n, n, m);
min(m, n)                    = if(m <= n, m, n);
```
Also `n == m` on `Nat` is the derived equality of the inductive type (`@c0 == @cNat(p) = false`,
`@cNat(p) == @cNat(q) = p == q`), same as for `Pos`. -/

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

/-! ## Successor, predecessor, `@dub`, `@dubsucc`

```
succ(@c0)              = @c1;
succ(@cNat(p))         = succ(p);
@dubsucc(@c0)          = @c1;
@dubsucc(@cNat(p))     = @cDub(true, p);
pred(@c1)              = @c0;
pred(@cDub(b, p))      = @cNat(if(b, @cDub(false, p), @dubsucc(pred(p))));
@dub(false, @c0)       = @c0;
@dub(true, @c0)        = @cNat(@c1);
@dub(b, @cNat(p))      = @cNat(@cDub(b, p));
```
-/

/-- `succ : Nat -> Pos`. -/
def succ : MNat → Pos
  | .zero => .one
  | .ofPos p => Pos.succ p

/-- `@dubsucc : Nat -> Pos` ("double and add 1"). -/
def dubsucc : MNat → Pos
  | .zero => .one
  | .ofPos p => .dub true p

/-- `pred : Pos -> Nat`. Exact predecessor: total and always correct, since every `Pos` value is
`≥ 1`. -/
def pred : Pos → MNat
  | .one => .zero
  | .dub b p => .ofPos (if b then .dub false p else dubsucc (pred p))

/-- `@dub : Bool # Nat -> Nat` ("double and conditionally add 1"). -/
def dub : Bool → MNat → MNat
  | false, .zero => .zero
  | true, .zero => .ofPos .one
  | b, .ofPos p => .ofPos (.dub b p)

/-! ## Addition

```
p + @c0                    = p;
p + @cNat(q)               = @addc(false, p, q);
@c0 + p                    = p;
@cNat(p) + q               = @addc(false, p, q);
@c0 + n                    = n;
n + @c0                    = n;
@cNat(p) + @cNat(q)        = @cNat(@addc(false, p, q));
```
-/

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

/-! ## `@gtesubtb` and `@monus`

`@gtesubtb(b, p, q)` computes `p - q - (b ? 1 : 0)` (truncated at `0`) via a bitwise
borrow-propagating recursion on `p` and `q` together. **Finding:** the equations in `nat.mcrl2`
do not cover every argument shape — there is no rule for `@gtesubtb(b, @c1, @cDub(c, q))` (`p`
shorter than `q`). A literal transcription is therefore a *partial* function; the case is
needed (e.g. `@monus(@cNat(1), @cNat(2))` routes through it) so we complete it with `MNat.zero`,
the mathematically correct answer (`p ≤ q` here, so the truncated result is always `0`). This
completion is additional to the spec, not derived from it; flagged here as the `@monus`
counterpart of the `div_word`/`div_doubleword` precondition gaps already tracked in
`docs/plans/machine-numbers-verification.md`.
```
@gtesubtb(false, p, @c1)                = pred(p);
@gtesubtb(true, p, @c1)                 = pred(Nat2Pos(pred(p)));
@gtesubtb(b, @cDub(c, p), @cDub(c, q))  = @dub(b, @gtesubtb(b, p, q));
@gtesubtb(b, @cDub(false, p), @cDub(true, q)) = @dub(!(b), @gtesubtb(true, p, q));
@gtesubtb(b, @cDub(true, p), @cDub(false, q)) = @dub(!(b), @gtesubtb(false, p, q));
```
(The missing `b, @c1, @cDub(c, q)` clause lives at the end below.) -/
def gtesubtb : Bool → Pos → Pos → MNat
  | false, p, .one => pred p
  | true, p, .one => pred (toPos (pred p))
  | b, .dub false p, .dub false q => dub b (gtesubtb b p q)
  | b, .dub true p, .dub true q => dub b (gtesubtb b p q)
  | b, .dub false p, .dub true q => dub (!b) (gtesubtb true p q)
  | b, .dub true p, .dub false q => dub (!b) (gtesubtb false p q)
  | _, .one, .dub _ _ => .zero -- completion: `p ≤ q`, see the docstring above.

/-- `@monus`.
```
@monus(@c0, n)               = @c0;
@monus(n, @c0)               = n;
@monus(@cNat(p), @cNat(q))   = @gtesubtb(false, p, q);
```
-/
def monus : MNat → MNat → MNat
  | .zero, _ => .zero
  | n, .zero => n
  | .ofPos p, .ofPos q => gtesubtb false p q

/-! ## Multiplication -/

/-- `* : Nat # Nat -> Nat`.
```
@c0 * n                    = @c0;
n * @c0                    = @c0;
@cNat(p) * @cNat(q)        = @cNat(p * q);
```
-/
def mul : MNat → MNat → MNat
  | .zero, _ => .zero
  | _, .zero => .zero
  | .ofPos p, .ofPos q => .ofPos (Pos.mul p q)

/-! ## `@even` -/

/-- `@even`.
```
@even(@c0)             = true;
@even(@cNat(@c1))      = false;
@even(@cNat(@cDub(b, p))) = !(b);
```
-/
def even : MNat → Bool
  | .zero => true
  | .ofPos .one => false
  | .ofPos (.dub b _) => !b

/-! ## Exponentiation -/

/-- `exp : Pos # Nat -> Pos` (exponentiation by repeated squaring, reading the exponent from the
LSB up).
```
exp(p, @c0)                    = @c1;
exp(p, @cNat(@c1))             = p;
exp(p, @cNat(@cDub(false, q))) = exp(p * p, @cNat(q));
exp(p, @cNat(@cDub(true, q)))  = p * exp(p * p, @cNat(q));
```
-/
def expPN : Pos → MNat → Pos
  | _, .zero => .one
  | p, .ofPos .one => p
  | p, .ofPos (.dub false q) => expPN (Pos.mul p p) (.ofPos q)
  | p, .ofPos (.dub true q) => Pos.mul p (expPN (Pos.mul p p) (.ofPos q))

/-- `exp : Nat # Nat -> Nat`.
```
exp(n, @c0)       = @cNat(@c1);
exp(@c0, @cNat(p)) = @c0;
exp(@cNat(p), n)  = @cNat(exp(p, n));
```
-/
def expNN : MNat → MNat → MNat
  | _, .zero => .ofPos .one
  | .zero, _ => .zero
  | .ofPos p, n => .ofPos (expPN p n)

/-! ## `div` / `mod`

`@div`, `@mod` and the `@NatPair` machinery below implement long division of `Pos`es: `@divmod`
is the quotient/remainder pair, `@gdivmod` shifts in one bit at a time, and `@ggdivmod` does the
single long-division step (subtracting one copy of the divisor when it fits).
```
@c0 div p      = @c0;
@cNat(p) div q = @first(@divmod(p, q));
@c0 mod p      = @c0;
@cNat(p) mod q = @last(@divmod(p, q));

@divmod(@c1, @c1)      = @cPair(@cNat(@c1), @c0);
@divmod(@c1, @cDub(b, p)) = @cPair(@c0, @cNat(@c1));
@divmod(@cDub(b, p), q)   = @gdivmod(@divmod(p, q), b, q);

@gdivmod(@cPair(m, n), b, p) = @ggdivmod(@dub(b, n), m, p);

@ggdivmod(@c0, n, p)                              = @cPair(@dub(false, n), @c0);
p < q  ->  @ggdivmod(@cNat(p), n, q)              = @cPair(@dub(false, n), @cNat(p));
q <= p ->  @ggdivmod(@cNat(p), n, q)              = @cPair(@dub(true, n), @gtesubtb(false, p, q));
```
The two conditional `@ggdivmod` rules are exhaustive and mutually exclusive, so we fold them into
an `if Pos.lt p q`. The definitions are given bottom-up (`@ggdivmod`, `@gdivmod`, `@divmod`) to
respect dependency order. -/

/-- `@ggdivmod`: one long-division step. `g` is the current high part (`@dub(b,n)` after a shift),
`n` the quotient built so far, and `q` the divisor. -/
def ggdivmod : MNat → MNat → Pos → MNatPair
  | .zero, n, _ => .pair (dub false n) .zero
  | .ofPos p, n, q =>
    if Pos.lt p q then .pair (dub false n) (.ofPos p)
    else .pair (dub true n) (gtesubtb false p q)

/-- `@gdivmod`: shift bit `b` into the remainder and continue the division. -/
def gdivmod : MNatPair → Bool → Pos → MNatPair
  | .pair m n, b, p => ggdivmod (dub b n) m p

/-- `@divmod`: quotient/remainder of two `Pos`es (left-to-right long division, reading the
divisor-position bits from the MSB). -/
def divmod : Pos → Pos → MNatPair
  | .one, .one => .pair (.ofPos .one) .zero
  | .one, .dub _ _ => .pair .zero (.ofPos .one)
  | .dub b p, q => gdivmod (divmod p q) b q

/-- `div : Nat # Pos -> Nat`.
```
@c0 div p      = @c0;
@cNat(p) div q = @first(@divmod(p, q));
```
-/
def div : MNat → Pos → MNat
  | .zero, _ => .zero
  | .ofPos p, q => MNatPair.first (divmod p q)

/-- `mod : Nat # Pos -> Nat`.
```
@c0 mod p      = @c0;
@cNat(p) mod q = @last(@divmod(p, q));
```
-/
def mod : MNat → Pos → MNat
  | .zero, _ => .zero
  | .ofPos p, q => MNatPair.last (divmod p q)

/-! ## `@swap_zero` and friends

`@swap_zero` is an auxiliary used by merc's newsort/extensional-recovery computations. Its
overlapping equations define: `swapZero(m, n) = if m = n then 0 else (if n = 0 then m else n)`.
```
@swap_zero(m, @c0)               = m;
@swap_zero(@c0, n)               = n;
@swap_zero(@cNat(p), @cNat(p))   = @c0;
p != q ->

@swap_zero(@cNat(p), @cNat(q))   = @cNat(q);
```
The `@swap_zero_add`/`_min`/`_monus` families distribute `+`/`min`/`@monus` over the swap, giving
a sort of "sum if unequal, else zero" arithmetic used by the enumeration machinery. -/

/-- `@swap_zero`. -/
def swapZero : MNat → MNat → MNat
  | m, .zero => m
  | .zero, n => n
  | .ofPos p, .ofPos q => if p == q then .zero else .ofPos q

/-- `@swap_zero_add`.
```
@swap_zero_add(@c0, @c0, m, n)              = m + n;
@swap_zero_add(@cNat(p), @c0, m, @c0)       = m;
@swap_zero_add(@cNat(p), @c0, m, @cNat(q))  = @swap_zero(@cNat(p), @swap_zero(@cNat(p), m) + @cNat(q));
@swap_zero_add(@c0, @cNat(p), @c0, n)       = n;
@swap_zero_add(@c0, @cNat(p), @cNat(q), n)  = @swap_zero(@cNat(p), @cNat(q) + @swap_zero(@cNat(p), n));
@swap_zero_add(@cNat(p), @cNat(q), m, n)    = @swap_zero(@cNat(p) + @cNat(q), @swap_zero(@cNat(p), m) + @swap_zero(@cNat(q), n));
```
-/
def swapZeroAdd : MNat → MNat → MNat → MNat → MNat
  | .zero, .zero, m, n => add m n
  | .ofPos _, .zero, m, .zero => m
  | .ofPos p, .zero, m, .ofPos q => swapZero (.ofPos p) (add (swapZero (.ofPos p) m) (.ofPos q))
  | .zero, .ofPos _, .zero, n => n
  | .zero, .ofPos p, .ofPos q, n => swapZero (.ofPos p) (add (.ofPos q) (swapZero (.ofPos p) n))
  | .ofPos p, .ofPos q, m, n =>
    swapZero (add (.ofPos p) (.ofPos q)) (add (swapZero (.ofPos p) m) (swapZero (.ofPos q) n))

/-- `@swap_zero_min`.
```
@swap_zero_min(@c0, @c0, m, n)              = min(m, n);
@swap_zero_min(@cNat(p), @c0, m, @c0)       = @c0;
@swap_zero_min(@cNat(p), @c0, m, @cNat(q))  = min(@swap_zero(@cNat(p), m), @cNat(q));
@swap_zero_min(@c0, @cNat(p), @c0, n)       = @c0;
@swap_zero_min(@c0, @cNat(p), @cNat(q), n)  = min(@cNat(q), @swap_zero(@cNat(p), n));
@swap_zero_min(@cNat(p), @cNat(q), m, n)    = @swap_zero(min(@cNat(p), @cNat(q)), min(@swap_zero(@cNat(p), m), @swap_zero(@cNat(q), n)));
```
-/
def swapZeroMin : MNat → MNat → MNat → MNat → MNat
  | .zero, .zero, m, n => min m n
  | .ofPos _, .zero, _, .zero => .zero
  | .ofPos p, .zero, m, .ofPos q => min (swapZero (.ofPos p) m) (.ofPos q)
  | .zero, .ofPos _, .zero, _ => .zero
  | .zero, .ofPos p, .ofPos q, n => min (.ofPos q) (swapZero (.ofPos p) n)
  | .ofPos p, .ofPos q, m, n =>
    swapZero (min (.ofPos p) (.ofPos q)) (min (swapZero (.ofPos p) m) (swapZero (.ofPos q) n))

/-- `@swap_zero_monus`.
```
@swap_zero_monus(@c0, @c0, m, n)            = @monus(m, n);
@swap_zero_monus(@cNat(p), @c0, m, @c0)     = m;
@swap_zero_monus(@cNat(p), @c0, m, @cNat(q))= @swap_zero(@cNat(p), @monus(@swap_zero(@cNat(p), m), @cNat(q)));
@swap_zero_monus(@c0, @cNat(p), @c0, n)     = @c0;
@swap_zero_monus(@c0, @cNat(p), @cNat(q), n)= @monus(@cNat(q), @swap_zero(@cNat(p), n));
@swap_zero_monus(@cNat(p), @cNat(q), m, n)  = @swap_zero(@monus(@cNat(p), @cNat(q)), @monus(@swap_zero(@cNat(p), m), @swap_zero(@cNat(q), n)));
```
-/
def swapZeroMonus : MNat → MNat → MNat → MNat → MNat
  | .zero, .zero, m, n => monus m n
  | .ofPos _, .zero, m, .zero => m
  | .ofPos p, .zero, m, .ofPos q => swapZero (.ofPos p) (monus (swapZero (.ofPos p) m) (.ofPos q))
  | .zero, .ofPos _, .zero, _ => .zero
  | .zero, .ofPos p, .ofPos q, n => monus (.ofPos q) (swapZero (.ofPos p) n)
  | .ofPos p, .ofPos q, m, n =>
    swapZero (monus (.ofPos p) (.ofPos q)) (monus (swapZero (.ofPos p) m) (swapZero (.ofPos q) n))

/-! ## `sqrt` -/

/-- `@sqrt_nat`: binary (digit-by-digit) square root. `n` is the remaining radicand, `m` twice the
approximation formed by the bits chosen *above* the current level, and `p` the current candidate
bit. The identity `(x + m) · x = x² + m·x` is what a binary search on `sqrt` needs: when the
candidate `x = @cNat(@cDub(b, p))` fits (`(x + m)·x ≤ n`) it is kept and `n` and `m` are updated
so that `n ≡ N − (result)²` and `m = 2·result` remain true; otherwise the bit is dropped.
```
@sqrt_nat(n, m, @c1) = if(n <= m, @c0, @cNat(@c1));
@sqrt_nat(n, m, @cDub(b, p)) =
    if((@cNat(@cDub(b, p)) + m) * @cNat(@cDub(b, p)) > n,
       @sqrt_nat(n, m, p),
       @cNat(@cDub(b, p)) + @sqrt_nat(@monus(n, (@cNat(@cDub(b, p)) + m) * @cNat(@cDub(b, p))),
                                      m + @cNat(@cDub(false, @cDub(b, p))), p));
```
-/
def sqrtNat : MNat → MNat → Pos → MNat
  | n, m, .one => if le n m then .zero else .ofPos .one
  | n, m, .dub b p =>
    let x : MNat := .ofPos (.dub b p)
    let s : MNat := mul (add x m) x
    if lt n s then sqrtNat n m p
    else add x (sqrtNat (monus n s) (add m (dub false x)) p)

/-- `sqrt`.
```
sqrt(@c0)      = @c0;
sqrt(@cNat(p)) = @sqrt_nat(@cNat(p), @c0, @powerlog2(p));
```
The third argument `@powerlog2(p)` is the largest power of two whose square does not exceed `p`
(see `Pos.powerlog2` / `Pos.powerlog2_toNat`), giving the estimate the binary search refines. -/
def sqrt : MNat → MNat
  | .zero => .zero
  | .ofPos p => sqrtNat (.ofPos p) .zero (Pos.powerlog2 p)

end MNat
