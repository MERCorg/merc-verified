module

public import MercLib.Theory.Rewriting.SetAutomaton
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.BooleanAlgebra

@[expose] public section

/-!
# The set automaton: construction and matching

The two algorithms on top of `MercLib.Theory.Rewriting.SetAutomaton`, after [Erkens2021]:
`construct` builds the tables of the automaton from the reachable states, and `findMatches` runs the
automaton on a term, with an explicit work set of configurations.

The configurations of `findMatches` are independent, so they may be processed in any order or in
parallel. The parameter `pick` takes that choice: it selects the non-empty batch of configurations
to process next, and the claim holds for every such choice. `construct` proceeds in rounds, since
the order cannot influence its result.

## Main definitions

- `Automaton`: the tables `δ` and `η`.
- `construct`: a worklist over the states.
- `findMatches`: the matches announced and the positions inspected, as a multiset.

## Main claims

- `ConstructCorrect`: `construct` terminates with exactly the reachable part of the automaton.
- `FindMatchesCorrect`: `findMatches` terminates with exactly the matches of the patterns, and
  inspects every position of the term exactly once.
-/

namespace MercLib.SetAutomaton

variable {F : Type} [DecidableEq F]

/-- The tables of a set automaton: `(s, f, s', p') ∈ delta` and `(s, f, a) ∈ eta` stand for
`(s', p') ∈ δ(s, f)` and `a ∈ η(s, f)`. -/
structure Automaton (F : Type) where
  init : State F
  states : Finset (State F)
  delta : Finset (State F × F × State F × Position)
  eta : Finset (State F × F × At F)

/-- A configuration `(s, p)`: state `s` is to be evaluated at position `p` of the term. -/
abbrev Config (F : Type) := State F × Position

section Construct

variable [Fintype F] (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position)

/-- The entries of the table `δ` for the state `s`. -/
def edges (s : State F) : Finset (State F × F × State F × Position) :=
  Finset.univ.biUnion fun f => (delta ar Ls s (L s) f).image fun n => (s, f, n.1, n.2)

/-- The entries of the table `η` for the state `s`. -/
def outputs (s : State F) : Finset (State F × F × At F) :=
  Finset.univ.biUnion fun f => (eta ar s (L s) f).image fun a => (s, f, a)

/-- Construct the automaton: `Q` holds the states whose table entries are not computed yet. -/
def construct : Automaton F := Id.run do
  let mut S : Finset (State F) := {initial Ls}
  let mut Q : Finset (State F) := {initial Ls}
  let mut δ : Finset (State F × F × State F × Position) := ∅
  let mut η : Finset (State F × F × At F) := ∅
  while Q ≠ ∅ do
    let E := Q.biUnion (edges ar Ls L)
    δ := δ ∪ E
    η := η ∪ Q.biUnion (outputs ar L)
    let T := E.image fun e => e.2.2.1                  -- the target states
    Q := T \ S
    S := S ∪ T
  return ⟨initial Ls, S, δ, η⟩

end Construct

section FindMatches

variable (M : Automaton F) (L : State F → Position)

/-- The matches announced in configuration `c` of the evaluation of `t`. -/
def Automaton.announced (t : Pat F) (c : Config F) : Finset (At F) :=
  match headAt t (c.2 ++ L c.1) with
  | some f => (M.eta.filter fun o => o.1 = c.1 ∧ o.2.1 = f).image fun o =>
      (o.2.2.1, c.2 ++ o.2.2.2)
  | none => ∅

/-- The configurations that configuration `c` of the evaluation of `t` leads to. -/
def Automaton.successors (t : Pat F) (c : Config F) : Finset (Config F) :=
  match headAt t (c.2 ++ L c.1) with
  | some f => (M.delta.filter fun e => e.1 = c.1 ∧ e.2.1 = f).image fun e =>
      (e.2.2.1, c.2 ++ e.2.2.2)
  | none => ∅

/-- Evaluate the automaton `M` on `t`: the matches, and the positions inspected with multiplicity.
`pick` chooses the configurations to process next. -/
def findMatches (pick : Finset (Config F) → Finset (Config F)) (t : Pat F) :
    Finset (At F) × Multiset Position := Id.run do
  let mut W : Finset (Config F) := {(M.init, [])}
  let mut A : Finset (At F) := ∅
  let mut inspected : Multiset Position := 0
  while W ≠ ∅ do
    let B := pick W
    A := A ∪ B.biUnion (M.announced L t)
    inspected := inspected + B.val.map fun c => c.2 ++ L c.1
    W := (W \ B) ∪ B.biUnion (M.successors L t)
  return (A, inspected)

end FindMatches

variable [Fintype F] (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position)

/-- **Correctness of the construction**: the tables of `construct` are exactly `δ` and `η` on the
reachable states. -/
def ConstructCorrect : Prop :=
  Admissible L → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) →
    let M := construct ar Ls L
    M.init = initial Ls ∧ (∀ s, s ∈ M.states ↔ Reachable ar Ls L s) ∧
      (∀ s f s' p', (s, f, s', p') ∈ M.delta ↔
        Reachable ar Ls L s ∧ (s', p') ∈ delta ar Ls s (L s) f) ∧
      (∀ s f a, (s, f, a) ∈ M.eta ↔ Reachable ar Ls L s ∧ a ∈ eta ar s (L s) f)

/-- **Correctness of matching**: for every way of choosing the batches, `findMatches` on the
constructed automaton returns exactly the matches of the patterns in `t` and inspects every position
of `t` exactly once. -/
def FindMatchesCorrect (pick : Finset (Config F) → Finset (Config F)) : Prop :=
  Admissible L → Ls.Nonempty → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) →
    (∀ W, W.Nonempty → (pick W).Nonempty ∧ pick W ⊆ W) →
    ∀ t : Pat F, t.Closed → t.WF ar →
      let r := findMatches (construct ar Ls L) L pick t
      (r.1 : Set (At F)) = {a | a.1 ∈ Ls ∧ a.2 ∈ t.dom ∧ a.1.Matches t a.2} ∧ r.2 = t.dom.val

end MercLib.SetAutomaton
