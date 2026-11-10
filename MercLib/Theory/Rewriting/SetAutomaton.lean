module

public import MercLib.Theory.Rewriting.Position
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Set.Function

@[expose] public section

/-!
# The set automaton

The set automaton of [R. Erkens and J. F. Groote, *A Set Automaton to Locate All Pattern Matches in
a Term*][Erkens2021], ICTAC 2021. Given a finite set of linear patterns, the automaton finds every
match of every pattern in a term, inspecting each function symbol of the term exactly once.

The setting is that of the paper: a ranked alphabet and terms over a single variable `ω`. The state
labelling `L` is a parameter, since any position of a root goal may be chosen (Section 4.6).

## Main definitions

- `Pat`: terms over the alphabet `F` and the variable `ω`; `Pat.dom`, `Pat.at`, `Pat.hd`.
- `Pat.Matches`: `ℓ` matches `t` at position `p`.
- `Goal`, `State`: match goals and states.
- `reduce`, `deriv`, `classes`, `lift`: the steps of the construction.
- `delta`, `eta`: the transition and output functions.
- `Reachable`, `Node`: the reachable states and the nodes of the evaluation tree.
- `output`: the matches announced along the evaluation tree of a term.
-/

namespace MercLib.SetAutomaton

/-- Terms over the function symbols `F` and the variable `ω`. -/
inductive Pat (F : Type) where
  | omega : Pat F
  | app (f : F) (args : List (Pat F)) : Pat F

variable {F : Type} [DecidableEq F]

mutual

/-- Decidable equality of patterns. -/
def Pat.decEq : (a b : Pat F) → Decidable (a = b)
  | .omega, .omega => isTrue rfl
  | .omega, .app _ _ => isFalse (by intro c; cases c)
  | .app _ _, .omega => isFalse (by intro c; cases c)
  | .app f as, .app g bs =>
    if h : f = g then
      match Pat.decEqArgs as bs with
      | isTrue e => isTrue (by rw [h, e])
      | isFalse e => isFalse fun c => e (Pat.app.inj c).2
    else isFalse fun c => h (Pat.app.inj c).1

/-- Decidable equality of argument lists. -/
def Pat.decEqArgs : (as bs : List (Pat F)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro c; cases c)
  | _ :: _, [] => isFalse (by intro c; cases c)
  | a :: as, b :: bs =>
    match Pat.decEq a b, Pat.decEqArgs as bs with
    | isTrue h, isTrue e => isTrue (by rw [h, e])
    | isFalse h, _ => isFalse fun c => h (List.cons.inj c).1
    | _, isFalse e => isFalse fun c => e (List.cons.inj c).2

end

instance : DecidableEq (Pat F) := Pat.decEq

namespace Pat

/-- The head symbol; the variable `ω` has none. -/
def hd : Pat F → Option F
  | .omega => none
  | .app f _ => some f

mutual

/-- `t[p]`: the subterm of `t` at position `p`, if `p ∈ D(t)`. -/
def «at» : Pat F → Position → Option (Pat F)
  | t, [] => some t
  | .omega, _ :: _ => none
  | .app _ args, i :: p => atArgs args i p

/-- The subterm at position `i.p` of an argument list (arguments are numbered from `1`). -/
def atArgs : List (Pat F) → ℕ → Position → Option (Pat F)
  | [], _, _ => none
  | _ :: _, 0, _ => none
  | t :: _, 1, p => «at» t p
  | _ :: ts, i + 2, p => atArgs ts (i + 1) p

end

mutual

/-- The term domain `D(t)` as a list. -/
def domList : Pat F → List Position
  | .omega => [[]]
  | .app _ args => [] :: domArgs args 1

/-- The positions of an argument list, the first argument having number `i`. -/
def domArgs : List (Pat F) → ℕ → List Position
  | [], _ => []
  | t :: ts, i => (domList t).map (i :: ·) ++ domArgs ts (i + 1)

end

/-- The term domain `D(t)`. -/
def dom (t : Pat F) : Finset Position := (domList t).toFinset

/-- `ℓ` matches `t` at position `p`: for all `p' ∈ D(ℓ)` with `ℓ[p'] ≠ ω`, the head symbols of
`t[p.p']` and `ℓ[p']` agree. -/
def Matches (l t : Pat F) (p : Position) : Prop :=
  ∀ p' ∈ l.dom, ∀ l', l.at p' = some l' → l' ≠ .omega →
    (t.at (p ++ p')).bind hd = l'.hd

mutual

/-- `t` is closed: it does not contain `ω`. -/
def Closed : Pat F → Prop
  | .omega => False
  | .app _ args => ClosedArgs args

/-- All terms of an argument list are closed. -/
def ClosedArgs : List (Pat F) → Prop
  | [] => True
  | t :: ts => Closed t ∧ ClosedArgs ts

end

mutual

/-- `t` respects the arities `ar`. -/
def WF (ar : F → ℕ) : Pat F → Prop
  | .omega => True
  | .app f args => args.length = ar f ∧ WFArgs ar args

/-- All terms of an argument list respect the arities. -/
def WFArgs (ar : F → ℕ) : List (Pat F) → Prop
  | [] => True
  | t :: ts => WF ar t ∧ WFArgs ar ts

end

end Pat

/-- `ℓ@p`: a (sub)pattern at a position. -/
abbrev At (F : Type) := Pat F × Position

/-- A match goal `mo → ma`: in order to announce the match `ma`, the obligations `mo` have to be
observed. -/
abbrev Goal (F : Type) := Finset (At F) × At F

/-- A state: a set of match goals. -/
abbrev State (F : Type) := Finset (Goal F)

instance : DecidableEq (At F) := instDecidableEqProd
instance : DecidableEq (Goal F) := instDecidableEqProd
instance : DecidableEq (State F) := Finset.decidableEq

/-- `pos(mo)`: the positions of a match obligation. -/
def pos (mo : Finset (At F)) : Finset Position := mo.image Prod.snd

/-- The arguments of a pattern, for `1 ≤ i ≤ #f`. -/
def argAt (l : Pat F) (i : ℕ) : Option (Pat F) := l.at [i]

/-- `reduce(mo, f, p)` of Section 4.2: remove the obligations at `p` and add the arguments of the
removed patterns that are not `ω`. -/
def reduce (ar : F → ℕ) (mo : Finset (At F)) (f : F) (p : Position) : Finset (At F) :=
  mo.filter (fun a => a.2 ≠ p) ∪
    (mo.filter (fun a => a.2 = p)).biUnion fun a =>
      ((Finset.range (ar f)).image (· + 1)).biUnion fun i =>
        match argAt a.1 i with
        | some l' => if l' = .omega then ∅ else {(l', p ++ [i])}
        | none => ∅

/-- `deriv(s, f)` of Section 4.2, for the state label `l = L(s)`: the unchanged, reduced and fresh
goals. -/
def deriv (ar : F → ℕ) (Ls : Finset (Pat F)) (s : State F) (l : Position) (f : F) : State F :=
  s.filter (fun g => l ∉ pos g.1) ∪
    ((s.filter fun g => ∃ a ∈ g.1, a.2 = l ∧ a.1.hd = some f).image
        (fun g => (reduce ar g.1 f l, g.2))).filter (fun g => g.1 ≠ ∅) ∪
    Ls.biUnion fun p => ((Finset.range (ar f)).image (· + 1)).image fun i =>
      ({(p, l ++ [i])}, (p, l ++ [i]))

/-- Direct dependency of match goals (Section 4.3): their obligations share a position. -/
def Depends (g h : Goal F) : Prop := (pos g.1 ∩ pos h.1).Nonempty

instance : DecidableRel (Depends (F := F)) := fun g h =>
  inferInstanceAs (Decidable (pos g.1 ∩ pos h.1).Nonempty)

/-- The goals of `X` dependent on `g`: the `∼_X`-class of `g`, by `|X|` rounds of closure. -/
def classOf (X : State F) (g : Goal F) : State F :=
  (List.range X.card).foldl (fun K _ => K ∪ X.filter fun h => ∃ k ∈ K, Depends k h) {g}

/-- `[X]_∼`: the partition of `X` into dependency classes (Section 4.3). -/
def classes (X : State F) : Finset (State F) := X.image (classOf X)

/-- The positions of the match announcements of a class. -/
def posMA (K : State F) : Finset Position := K.image fun g => g.2.2

/-- `gcp(K)`: the greatest common prefix of the announcements of a class (Section 4.4). -/
def gcpOf (K : State F) : Position := Position.gcp (posMA K)

/-- Remove the prefix `c` from a position. -/
def shorten (c q : Position) : Position := q.drop c.length

/-- `lift(K)` of Section 4.4: shorten every position of a class by its `gcp`. -/
def lift (K : State F) : State F :=
  K.image fun g =>
    (g.1.image fun a => (a.1, shorten (gcpOf K) a.2), (g.2.1, shorten (gcpOf K) g.2.2))

/-- The initial state `s₀`: all fresh root goals. -/
def initial (Ls : Finset (Pat F)) : State F := Ls.image fun p => ({(p, [])}, (p, []))

/-- The transition function `δ(s, f)` of Section 4.7 for the state label `l = L(s)`. -/
def delta (ar : F → ℕ) (Ls : Finset (Pat F)) (s : State F) (l : Position) (f : F) :
    Finset (State F × Position) :=
  (classes (deriv ar Ls s l f)).image fun K => (lift K, gcpOf K)

/-- `f(ω, …, ω)`: the pattern consisting of the symbol `f` only. -/
def shallow (ar : F → ℕ) (f : F) : Pat F := .app f (List.replicate (ar f) .omega)

/-- The output function `η(s, f)` of Section 4.5 for the state label `l = L(s)`. -/
def eta (ar : F → ℕ) (s : State F) (l : Position) (f : F) : Finset (At F) :=
  (s.filter fun g => g.1 = {(shallow ar f, l)}).image Prod.snd

variable (ar : F → ℕ) (Ls : Finset (Pat F))

/-- A state labelling is admissible (Section 4.6): on every state with a root goal, it chooses a
position of the obligations of a root goal. -/
def Admissible (L : State F → Position) : Prop :=
  ∀ s, (∃ g ∈ s, g.2.2 = []) → ∃ g ∈ s, g.2.2 = [] ∧ L s ∈ pos g.1

/-- The reachable states of the automaton with state labelling `L`. -/
inductive Reachable (L : State F → Position) : State F → Prop
  | init : Reachable L (initial Ls)
  | step {s s' : State F} {f : F} {p' : Position} :
      Reachable L s → (s', p') ∈ delta ar Ls s (L s) f → Reachable L s'

/-- The head symbol of `t` at position `p`. -/
def headAt (t : Pat F) (p : Position) : Option F := (t.at p).bind Pat.hd

/-- The nodes `(s, p)` of the evaluation tree of `t` (Definition 2). -/
inductive Node (L : State F → Position) (t : Pat F) : State F × Position → Prop
  | root : Node L t (initial Ls, [])
  | step {s s' : State F} {p p' : Position} {f : F} :
      Node L t (s, p) → headAt t (p ++ L s) = some f → (s', p') ∈ delta ar Ls s (L s) f →
      Node L t (s', p ++ p')

/-- The pattern matches announced along the evaluation tree of `t`: Equation (1) of the paper. -/
def output (L : State F → Position) (t : Pat F) : Set (At F) :=
  {a | ∃ s p f q, Node ar Ls L t (s, p) ∧ headAt t (p ++ L s) = some f ∧
      (a.1, q) ∈ eta ar s (L s) f ∧ a.2 = p ++ q}

/-- **Correctness (Theorem 1).** For a non-empty set of well-formed, linear patterns other than `ω` and
a closed well-formed term `t`, the matches announced are exactly the matches of the patterns in `t`.
Linearity is built into `Pat`, which has the single anonymous variable `ω`. -/
def Correct (L : State F → Position) : Prop :=
  Admissible L → Ls.Nonempty → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) →
    ∀ t : Pat F, t.Closed → t.WF ar →
      output ar Ls L t = {a | a.1 ∈ Ls ∧ a.2 ∈ t.dom ∧ a.1.Matches t a.2}

/-- **Every position is inspected once (Corollary 4).** `φ(s, p) = p.L(s)` is a bijection from the
nodes of the evaluation tree of `t` onto `D(t)`. -/
def InspectsOnce (L : State F → Position) : Prop :=
  Admissible L → Ls.Nonempty → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) →
    ∀ t : Pat F, t.Closed → t.WF ar →
      Set.BijOn (fun n : State F × Position => n.2 ++ L n.1)
        {n | Node ar Ls L t n} {p | p ∈ t.dom}

/-- **Finiteness (Corollary 2).** Over a finite alphabet, the automaton has finitely many reachable
states. -/
def FinitelyManyStates [Finite F] (L : State F → Position) : Prop :=
  Admissible L → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) → Set.Finite {s | Reachable ar Ls L s}

end MercLib.SetAutomaton
