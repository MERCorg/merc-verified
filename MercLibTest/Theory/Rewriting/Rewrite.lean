import MercLib.Theory.Rewriting.Basic

/-!
# Tests for `MercLib.Theory.Rewriting`

A small one-sorted conditional rewrite system: `f(x) → x`, `a → b` and `g(x) → b if x →* b`.
-/

namespace MercLibTest.Rewriting

open MercLib.Rewriting

/-- The operators: constants `a`, `b` and unary `f`, `g`. -/
inductive Op : List Unit → Unit → Type
  | a : Op [] ()
  | b : Op [] ()
  | f : Op [()] ()
  | g : Op [()] ()

abbrev Sg : Signature := ⟨Unit, Op⟩

/-- One rule variable `x`. -/
abbrev X : VarSet Sg := fun _ => Unit

abbrev T (V : VarSet Sg) := Term Sg V ()

abbrev A {V} : T V := .op Op.a .nil
abbrev B {V} : T V := .op Op.b .nil
abbrev F {V} (t : T V) : T V := .op Op.f (.cons t .nil)
abbrev G {V} (t : T V) : T V := .op Op.g (.cons t .nil)
abbrev x : T X := .var ()

/-- The rules. -/
def R : TRS Sg X (Fin 3)
  | 0 => { srt := (), lhs := F x, rhs := x }
  | 1 => { srt := (), lhs := A, rhs := B }
  | 2 => { srt := (), lhs := G x, rhs := B, conds := [{ srt := (), lhs := x, rhs := B }] }

/-- The ground substitution `x ↦ t`. -/
abbrev sub (t : T (Ground Sg)) : Term.Subst Sg X (Ground Sg) := fun _ _ => t

/-- A root step. -/
example : Step R () (F A : T (Ground Sg)) A :=
  ⟨1, StepWith.rule (R := R) 0 (sub A) (by simp [R])⟩

/-- A step inside a context. -/
example : Step R () (F A : T (Ground Sg)) (F B) :=
  ⟨1, show StepWith R _ () (F A) (F B) from .op Op.f (.head
    (show StepWith R _ () A B from StepWith.rule (R := R) 1 (sub A) (by simp [R])))⟩

/-- The condition of `g(b)` holds with no steps, so it fires at depth 1. -/
example : stepAt R 1 () (G B : T (Ground Sg)) B :=
  StepWith.rule (R := R) 2 (sub B) (by
    intro c hc
    simp only [R, List.mem_singleton] at hc
    subst hc
    exact Relation.ReflTransGen.refl)

/-- The condition of `g(a)` needs the step `a → b`, so it fires at depth 2. -/
example : stepAt R 2 () (G A : T (Ground Sg)) B :=
  StepWith.rule (R := R) 2 (sub A) (by
    intro c hc
    simp only [R, List.mem_singleton] at hc
    subst hc
    exact Relation.ReflTransGen.single (StepWith.rule (R := R) 1 (sub A) (by simp [R])))

/-- Depth 0 has no steps. -/
example : ¬ stepAt R 0 () (F A : T (Ground Sg)) A := by simp [stepAt]

/-- A monotone interpretation in the natural numbers. -/
def M : MonotoneInterpretation Sg where
  carrier _ := ℕ
  interp
    | Op.a, _ => 1
    | Op.b, _ => 0
    | Op.f, (n, _) => n + 1
    | Op.g, (n, _) => n + 1
  lt _ a b := a < b
  wf _ := Nat.lt_wfRel.wf
  mono op as bs h := by
    cases op with
    | a => exact h.elim
    | b => exact h.elim
    | f =>
      rcases as with ⟨a, _⟩; rcases bs with ⟨b, _⟩
      rcases h with ⟨h, _⟩ | ⟨_, h⟩
      · exact Nat.succ_lt_succ h
      · exact h.elim
    | g =>
      rcases as with ⟨a, _⟩; rcases bs with ⟨b, _⟩
      rcases h with ⟨h, _⟩ | ⟨_, h⟩
      · exact Nat.succ_lt_succ h
      · exact h.elim

/-- Every rule decreases, so the system terminates on ground terms. -/
example : Terminating R (Ground Sg) := by
  refine terminating_of_interpretation (M := M) ?_ (fun _ e => e.elim)
  intro i ν
  match i with
  | 0 => exact Nat.lt_succ_self _
  | 1 => exact Nat.zero_lt_one
  | 2 => exact Nat.succ_pos _

end MercLibTest.Rewriting
