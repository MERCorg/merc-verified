module

public import MercLib.Theory.Rewriting.SetAutomaton

@[expose] public section

/-!
# The set automaton with another partition

The construction of `MercLib.Theory.Rewriting.SetAutomaton` partitions a derivative into the classes
of dependency (Section 4.3 of [Erkens2021]). merc partitions more coarsely: goals that are not fresh
are also grouped when their announcement positions are comparable. This module generalises the
construction to the classes of any relation `R` on the goals of a derivative, and states the three
theorems of the paper for every relation that is *admissible*: symmetric, containing dependency, and
relating only goals that depend or announce at comparable positions.

## Main definitions

- `classOfBy`, `deltaBy`: the class of a goal, and the transition function, for a relation `R`.
- `ReachableBy`, `NodeBy`, `outputBy`: the reachable states, evaluation tree and matches.
- `PartitionAdmissible`: the conditions on `R`.
- `freshGoals`, `MercDepends`: the fresh goals of a derivative, and merc's relation.

## Main claims

- `CorrectBy`, `InspectsOnceBy`, `FinitelyManyStatesBy`: Theorem 1, Corollary 4 and Corollary 2 of
  the paper for the relation `R`.
- `PartitionTheorems`: the three hold for every admissible relation.
- `MercPartitionAdmissible`: merc's relation is admissible, so the three hold for merc's partition.
-/

namespace MercLib.SetAutomaton

variable {F : Type} [DecidableEq F]

/-- The goals of `X` related to `g` by the reflexive-transitive closure of `R` in `X`, by `|X|`
rounds of closure. `classOf` is the instance `R = Depends`. -/
def classOfBy (R : Goal F → Goal F → Prop) [DecidableRel R] (X : State F) (g : Goal F) : State F :=
  (List.range X.card).foldl (fun K _ => K ∪ X.filter fun h => ∃ k ∈ K, R k h) {g}

/-- The partition of `X` into the classes of `R`. -/
def classesBy (R : Goal F → Goal F → Prop) [DecidableRel R] (X : State F) : Finset (State F) :=
  X.image (classOfBy R X)

/-- Two positions are comparable if one is a prefix of the other. -/
def Comparable (p q : Position) : Prop := p <+: q ∨ q <+: p

instance : DecidableRel Comparable := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

variable (R : Position → F → Goal F → Goal F → Prop) [∀ l f, DecidableRel (R l f)]
  (ar : F → ℕ) (Ls : Finset (Pat F))

/-- The transition function for the relation `R`: `R l f` partitions the derivative of a state
with label `l` with respect to `f`. -/
def deltaBy (s : State F) (l : Position) (f : F) : Finset (State F × Position) :=
  (classesBy (R l f) (deriv ar Ls s l f)).image fun K => (lift K, gcpOf K)

/-- The reachable states for the relation `R`. -/
inductive ReachableBy (L : State F → Position) : State F → Prop
  | init : ReachableBy L (initial Ls)
  | step {s s' : State F} {f : F} {p' : Position} :
      ReachableBy L s → (s', p') ∈ deltaBy R ar Ls s (L s) f → ReachableBy L s'

/-- The nodes of the evaluation tree of `t` for the relation `R`. -/
inductive NodeBy (L : State F → Position) (t : Pat F) : State F × Position → Prop
  | root : NodeBy L t (initial Ls, [])
  | step {s s' : State F} {p p' : Position} {f : F} :
      NodeBy L t (s, p) → headAt t (p ++ L s) = some f → (s', p') ∈ deltaBy R ar Ls s (L s) f →
      NodeBy L t (s', p ++ p')

/-- The matches announced along the evaluation tree of `t` for the relation `R`. -/
def outputBy (L : State F → Position) (t : Pat F) : Set (At F) :=
  {a | ∃ s p f q, NodeBy R ar Ls L t (s, p) ∧ headAt t (p ++ L s) = some f ∧
      (a.1, q) ∈ eta ar s (L s) f ∧ a.2 = p ++ q}

/-- `R` is admissible: each `R l f` is symmetric, contains dependency (so its classes are unions of
dependency classes), and relates only goals that depend or announce at comparable positions. -/
def PartitionAdmissible : Prop :=
  ∀ l f g h, (R l f g h → R l f h g) ∧ (Depends g h → R l f g h) ∧
    (R l f g h → Depends g h ∨ Comparable g.2.2 h.2.2)

/-- **Correctness (Theorem 1)** for the relation `R`; see `Correct`. -/
def CorrectBy (L : State F → Position) : Prop :=
  Admissible L → Ls.Nonempty → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) →
    ∀ t : Pat F, t.Closed → t.WF ar →
      outputBy R ar Ls L t = {a | a.1 ∈ Ls ∧ a.2 ∈ t.dom ∧ a.1.Matches t a.2}

/-- **Every position is inspected once (Corollary 4)** for the relation `R`; see `InspectsOnce`. -/
def InspectsOnceBy (L : State F → Position) : Prop :=
  Admissible L → Ls.Nonempty → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) →
    ∀ t : Pat F, t.Closed → t.WF ar →
      Set.BijOn (fun n : State F × Position => n.2 ++ L n.1)
        {n | NodeBy R ar Ls L t n} {p | p ∈ t.dom}

/-- **Finiteness (Corollary 2)** for the relation `R`; see `FinitelyManyStates`. -/
def FinitelyManyStatesBy [Finite F] (L : State F → Position) : Prop :=
  Admissible L → (∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) → Set.Finite {s | ReachableBy R ar Ls L s}

/-- **The theorems hold for every admissible partition.** -/
def PartitionTheorems : Prop :=
  PartitionAdmissible R →
    ∀ L : State F → Position, CorrectBy R ar Ls L ∧ InspectsOnceBy R ar Ls L ∧
      ∀ [Finite F], FinitelyManyStatesBy R ar Ls L

/-- The fresh goals `ℓ@l.i → ℓ@l.i` of the `f`-derivative of a state with label `l`. -/
def freshGoals (l : Position) (f : F) : State F :=
  Ls.biUnion fun p => ((Finset.range (ar f)).image (· + 1)).image fun i =>
    ({(p, l ++ [i])}, (p, l ++ [i]))

/-- **merc's partition (Definition 9 of the website).** Goals depend as in Definition 7, and goals
that are not fresh are also related when their announcement positions are comparable. A fresh goal
at `l.i` thus joins the class of the goals with an obligation at `l.i`, as in merc. -/
def MercDepends (l : Position) (f : F) (g h : Goal F) : Prop :=
  Depends g h ∨
    (g ∉ freshGoals ar Ls l f ∧ h ∉ freshGoals ar Ls l f ∧ Comparable g.2.2 h.2.2)

instance (l : Position) (f : F) : DecidableRel (MercDepends ar Ls l f) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- **merc's partition is admissible** (Conjecture 1 of the website, for the partition). -/
def MercPartitionAdmissible : Prop := PartitionAdmissible (MercDepends ar Ls)

end MercLib.SetAutomaton
