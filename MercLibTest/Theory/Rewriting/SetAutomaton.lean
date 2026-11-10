import MercLib.Theory.Rewriting.SetAutomaton
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Tests for `MercLib.Theory.Rewriting.SetAutomaton`

Runs the set automaton on the examples of Erkens and Groote (ICTAC 2021): the associativity patterns
of Section 3 and the pattern and term of Figures 2 and 3. The announced matches are compared with an
independent check of `Pat.Matches`, and every position must be inspected exactly once.
-/

namespace MercLibTest.SetAutomaton

open MercLib.SetAutomaton

/-- The function symbols of the examples. -/
inductive Sym | f | g | a
  deriving DecidableEq

/-- The arities. -/
def ar : Sym → ℕ
  | .f => 2
  | .g => 1
  | .a => 0

abbrev ω : Pat Sym := .omega
abbrev f (x y : Pat Sym) : Pat Sym := .app .f [x, y]
abbrev g (x : Pat Sym) : Pat Sym := .app .g [x]
abbrev a : Pat Sym := .app .a []

/-- A state labelling: the least position of the obligations of the root goals. -/
def L (s : State Sym) : Position :=
  ((s.filter fun g => g.2.2 = []).biUnion fun g => pos g.1).sort (· ≤ ·) |>.headD []

/-- Evaluate from `(s, p)`: the matches announced and the positions inspected. -/
def run (Ls : Finset (Pat Sym)) (t : Pat Sym) : ℕ → State Sym → Position →
    Multiset (At Sym) × Multiset Position
  | 0, _, _ => (0, 0)
  | fuel + 1, s, p =>
    match headAt t (p ++ L s) with
    | none => (0, 0)
    | some h =>
      let here := ((eta ar s (L s) h).val.map fun b => (b.1, p ++ b.2), {p ++ L s})
      here + (delta ar Ls s (L s) h).sum fun n => run Ls t fuel n.1 (p ++ n.2)

/-- `Pat.Matches`, computed directly. -/
def matches? (l t : Pat Sym) (p : Position) : Bool :=
  l.domList.all fun p' => match l.at p' with
    | some l' => l' == .omega || (t.at (p ++ p')).bind Pat.hd == l'.hd
    | none => true

/-- The expected matches: all pairs of a pattern and a position of `t` that match. -/
def expected (Ls : Finset (Pat Sym)) (t : Pat Sym) : Finset (At Sym) :=
  Ls.biUnion fun l => (t.dom.filter fun p => matches? l t p).image fun p => (l, p)

/-- The announced matches are exactly the expected ones, and every position is inspected once. -/
def check (Ls : Finset (Pat Sym)) (t : Pat Sym) : Bool :=
  let r := run Ls t 64 (initial Ls) []
  r.1 == (expected Ls t).val && r.2 == t.dom.val

def l₁ : Pat Sym := f (f ω ω) ω
def l₂ : Pat Sym := f ω (f ω ω)
def assoc : Finset (Pat Sym) := {l₁, l₂}

/-- The example of Section 3. -/
def t₁ : Pat Sym := f (f a (f a a)) a

#guard check assoc t₁
#guard (run assoc t₁ 64 (initial assoc) []).1 == ({(l₁, []), (l₂, [1])} : Finset (At Sym)).val

/-- The pattern of Example 1 and the term of Figure 3. -/
def l₃ : Pat Sym := f (f ω (g ω)) (g ω)
def t₂ : Pat Sym := f (g a) (f (f a (g a)) (g a))

#guard check {l₃} t₂
#guard (run {l₃} t₂ 64 (initial {l₃}) []).1 == ({(l₃, [2])} : Finset (At Sym)).val

-- No match at all, and overlapping matches at nested positions.
#guard check {l₃} a
#guard check assoc (f (f (f a a) (f a a)) (f (f a a) a))
#guard check {g ω, f ω ω} (f (g a) (g (f a a)))

end MercLibTest.SetAutomaton
