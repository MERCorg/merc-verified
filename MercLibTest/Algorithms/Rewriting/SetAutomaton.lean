import MercLib.Algorithms.Rewriting.SetAutomaton
import MercLibTest.Theory.Rewriting.SetAutomaton

/-!
# Tests for `MercLib.Algorithms.Rewriting.SetAutomaton`

Runs `construct` and `findMatches` on the examples of Erkens and Groote (ICTAC 2021), with several
ways of choosing the configurations to process. The matches are compared with an independent check
of `Pat.Matches`, and the inspected positions must be exactly the positions of the term.
-/

namespace MercLibTest.SetAutomaton

open MercLib.SetAutomaton

instance : Fintype Sym := ⟨{.f, .g, .a}, by intro x; cases x <;> simp⟩

/-- Process the whole work set at once. -/
def pickAll (W : Finset (Config Sym)) : Finset (Config Sym) := W

/-- Process only the configurations at the deepest position. -/
def pickDeepest (W : Finset (Config Sym)) : Finset (Config Sym) :=
  W.filter fun c => ∀ d ∈ W, d.2.length ≤ c.2.length

/-- Process only the configurations at the shallowest position. -/
def pickShallowest (W : Finset (Config Sym)) : Finset (Config Sym) :=
  W.filter fun c => ∀ d ∈ W, c.2.length ≤ d.2.length

/-- The matches are the expected ones and every position is inspected exactly once. -/
def checkRun (pick : Finset (Config Sym) → Finset (Config Sym)) (Ls : Finset (Pat Sym))
    (t : Pat Sym) : Bool :=
  let r := findMatches (construct ar Ls L) L pick t
  r.1.val == (expected Ls t).val && r.2 == t.dom.val

/-- The tables contain every state that was found, and the initial state. -/
def checkTables (Ls : Finset (Pat Sym)) : Bool :=
  let M := construct ar Ls L
  decide (M.init ∈ M.states) && decide (∀ e ∈ M.delta, e.1 ∈ M.states ∧ e.2.2.1 ∈ M.states)

def pat : Finset (Pat Sym) := {l₃}
def mixed : Finset (Pat Sym) := {g ω, f ω ω}
def big : Pat Sym := f (f (f a a) (f a a)) (f (f a a) a)
def nest : Pat Sym := f (g a) (g (f a a))

#guard checkTables assoc
#guard checkTables pat
#guard checkTables mixed

#guard checkRun pickAll assoc t₁
#guard checkRun pickDeepest assoc t₁
#guard checkRun pickShallowest assoc t₁
#guard checkRun pickAll pat t₂
#guard checkRun pickDeepest pat t₂
#guard checkRun pickShallowest pat t₂
#guard checkRun pickAll pat a
#guard checkRun pickAll assoc big
#guard checkRun pickDeepest assoc big
#guard checkRun pickAll mixed nest
#guard checkRun pickShallowest mixed nest

end MercLibTest.SetAutomaton
