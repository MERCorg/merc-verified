import MercLib.Theory.Rewriting.Basic
import MercLibTest.Theory.Rewriting.Rewrite

/-!
# Tests for matching and critical pairs

The rules `f(a) → b` and `a → b` overlap at the argument of `f`, with the critical pair
`⟨b, f(b)⟩`. The test builds that overlap and checks the two terms of the pair.
-/

namespace MercLibTest.Rewriting

open MercLib.Rewriting

/-- The rules `f(a) → b` and `a → b`. -/
def R₂ : TRS Sg X (Fin 2)
  | 0 => { srt := (), lhs := F A, rhs := B }
  | 1 => { srt := (), lhs := A, rhs := B }

/-- The overlap of the second rule on the argument of the first. -/
def overlap : Overlap R₂ where
  i := 0
  j := 1
  C := .op Op.f (.head .hole .nil)
  u := A
  μ := fun _ x => .var x
  fill_eq := rfl
  nonvar := fun _ h => by cases h
  mgu := ⟨rfl, fun _ τ _ => ⟨τ, fun _ _ => rfl⟩⟩

example : overlap.left = (B : T (Both X)) := rfl
example : overlap.right = (F B : T (Both X)) := rfl

/-- `toPat` forgets the variable name. -/
example : (F x : T X).toPat = .app ⟨[()], (), Op.f⟩ [.omega] := rfl

/-- `x` is linear, and `f(x)` matches `f(a)`. -/
example : (F x : T X).Linear := by simp [Term.Linear, Term.vars, Args.vars]
example : (F x : T X).Matches (F A : T (Ground Sg)) := ⟨fun _ _ => A, rfl⟩

end MercLibTest.Rewriting
