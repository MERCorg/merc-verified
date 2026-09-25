import Rewriting.Signature
import Cslib.Foundations.Relation.Confluence

/-!
# Conditional rewrite systems

An mCRL2 `eqn` block is a list of (conditional) rewrite rules: `c -> l = r` rewrites an instance
`lσ` to `rσ` provided the condition instance `cσ` rewrites to `true`. Here a rule carries a list of
*oriented* conditions `u → v`; an mCRL2 condition `c` is the single condition `c → true`.

Such a system is an oriented CTRS, whose rewrite relation is defined by the usual stratification by
condition depth: `stepAt R 0` is empty, and `stepAt R (n+1)` fires a rule whose conditions are
already joinable by `stepAt R n`. `Step R` is the union over all levels; it is the least relation
closed under the rule and congruence clauses, which is what makes induction over a rewrite step
possible (`Step.rec_on` style proofs go by induction on the level).

The relation is defined for terms over an arbitrary variable family `W`, so it covers both ground
rewriting (`W = Ground S`) and rewriting of open terms.
-/

namespace Rewriting

variable {S : Signature}

/-- An oriented condition `lhs → rhs` of a conditional rewrite rule. -/
structure Cond (S : Signature) (V : VarSet S) where
  /-- The sort at which the condition is stated. -/
  srt : S.Srt
  /-- The left-hand side. -/
  lhs : Term S V srt
  /-- The right-hand side; for an mCRL2 condition this is `true`. -/
  rhs : Term S V srt

/-- A conditional rewrite rule `conds -> lhs = rhs` with variables drawn from `V`. -/
structure Rule (S : Signature) (V : VarSet S) where
  /-- The sort of both sides of the rule. -/
  srt : S.Srt
  /-- The left-hand side. -/
  lhs : Term S V srt
  /-- The right-hand side. -/
  rhs : Term S V srt
  /-- The conditions that must hold for the rule to fire. -/
  conds : List (Cond S V) := []

/-- A rewrite system: a family of rules indexed by `ι` (an enumeration of rule names). -/
abbrev TRS (S : Signature) (V : VarSet S) (ι : Type) := ι → Rule S V

mutual

/-- One rewrite step, with the conditions checked against an arbitrary relation `C`. Taking `C` to
be the reachability relation of the previous level yields the rewrite relation of a CTRS. -/
inductive StepWith {V W : VarSet S} {ι : Type} (R : TRS S V ι)
    (C : ∀ s, Term S W s → Term S W s → Prop) : ∀ s, Term S W s → Term S W s → Prop where
  /-- Contract a rule instance at the root. -/
  | rule (i : ι) (σ : Term.Subst S V W)
      (hc : ∀ c ∈ (R i).conds, C c.srt (Term.subst σ c.lhs) (Term.subst σ c.rhs)) :
      StepWith R C (R i).srt (Term.subst σ (R i).lhs) (Term.subst σ (R i).rhs)
  /-- Rewrite inside an argument (closure under contexts). -/
  | op {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) {as bs : Args S W ss}
      (h : ArgsStepWith R C ss as bs) : StepWith R C s (.op f as) (.op f bs)

/-- One rewrite step inside an argument list. -/
inductive ArgsStepWith {V W : VarSet S} {ι : Type} (R : TRS S V ι)
    (C : ∀ s, Term S W s → Term S W s → Prop) : ∀ ss, Args S W ss → Args S W ss → Prop where
  /-- Rewrite the first argument. -/
  | head {s : S.Srt} {ss : List S.Srt} {t t' : Term S W s} {ts : Args S W ss}
      (h : StepWith R C s t t') : ArgsStepWith R C (s :: ss) (.cons t ts) (.cons t' ts)
  /-- Rewrite one of the remaining arguments. -/
  | tail {s : S.Srt} {ss : List S.Srt} {t : Term S W s} {ts ts' : Args S W ss}
      (h : ArgsStepWith R C ss ts ts') : ArgsStepWith R C (s :: ss) (.cons t ts) (.cons t ts')

end

variable {V W : VarSet S} {ι : Type}

/-- The rewrite relation at condition depth `n`: rules whose conditions are reachable at depth
`n - 1`. -/
def stepAt (R : TRS S V ι) : Nat → ∀ s, Term S W s → Term S W s → Prop
  | 0 => fun _ _ _ => False
  | n + 1 => StepWith R fun s => Relation.ReflTransGen (stepAt R n s)

/-- The same, for argument lists. -/
def argsStepAt (R : TRS S V ι) : Nat → ∀ ss, Args S W ss → Args S W ss → Prop
  | 0 => fun _ _ _ => False
  | n + 1 => ArgsStepWith R fun s => Relation.ReflTransGen (stepAt R n s)

/-- One rewrite step of the conditional rewrite system `R`. -/
def Step (R : TRS S V ι) (s : S.Srt) (a b : Term S W s) : Prop := ∃ n, stepAt R n s a b

/-- One rewrite step inside an argument list. -/
def ArgsStep (R : TRS S V ι) (ss : List S.Srt) (as bs : Args S W ss) : Prop :=
  ∃ n, argsStepAt R n ss as bs

/-- Zero or more rewrite steps. -/
abbrev Steps (R : TRS S V ι) (s : S.Srt) : Term S W s → Term S W s → Prop :=
  Relation.ReflTransGen (Step (W := W) R s)

/-- The rewrite relation of `R` on terms of sort `s` over the variables `W`, as a plain relation:
this is what the abstract-rewriting vocabulary of `Cslib.Foundations.Relation` applies to. -/
abbrev rel (R : TRS S V ι) (W : VarSet S) (s : S.Srt) : Term S W s → Term S W s → Prop :=
  fun a b => Step R s a b

/-- A term is reducible if some rewrite step applies to it (`Relation.Reducible`). -/
abbrev Reducible (R : TRS S V ι) {s : S.Srt} (t : Term S W s) : Prop :=
  Relation.Reducible (rel R W s) t

/-- A term is a normal form if no rewrite step applies to it (`Relation.Normal`). -/
abbrev Normal (R : TRS S V ι) {s : S.Srt} (t : Term S W s) : Prop :=
  Relation.Normal (rel R W s) t

/-- `R` is terminating on terms over `W`: no sort admits an infinite rewrite sequence. -/
def Terminating (R : TRS S V ι) (W : VarSet S) : Prop := ∀ s, Relation.Terminating (rel R W s)

/-! ## Basic closure properties -/

/-- An unconditional rule fires at the root, at depth 1. -/
theorem Step.rule (R : TRS S V ι) (i : ι) (hc : (R i).conds = []) (σ : Term.Subst S V W) :
    Step R (R i).srt (Term.subst σ (R i).lhs) (Term.subst σ (R i).rhs) :=
  ⟨1, StepWith.rule i σ (by simp [hc])⟩

/-- Rewriting is closed under contexts. -/
theorem Step.op (R : TRS S V ι) {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s)
    {as bs : Args S W ss} (h : ArgsStep R ss as bs) : Step R s (.op f as) (.op f bs) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact absurd hn (by simp [argsStepAt])
  | succ n => exact ⟨n + 1, StepWith.op f hn⟩

/-- Rewriting the first argument. -/
theorem ArgsStep.head (R : TRS S V ι) {s : S.Srt} {ss : List S.Srt} {t t' : Term S W s}
    {ts : Args S W ss} (h : Step R s t t') : ArgsStep R (s :: ss) (.cons t ts) (.cons t' ts) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact absurd hn (by simp [stepAt])
  | succ n => exact ⟨n + 1, ArgsStepWith.head hn⟩

/-- Rewriting one of the remaining arguments. -/
theorem ArgsStep.tail (R : TRS S V ι) {s : S.Srt} {ss : List S.Srt} {t : Term S W s}
    {ts ts' : Args S W ss} (h : ArgsStep R ss ts ts') :
    ArgsStep R (s :: ss) (.cons t ts) (.cons t ts') := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact absurd hn (by simp [argsStepAt])
  | succ n => exact ⟨n + 1, ArgsStepWith.tail hn⟩

/-- A term whose first argument is reducible is itself reducible. -/
theorem Reducible.head (R : TRS S V ι) {ss : List S.Srt} {s' : S.Srt} (f : S.Op (s' :: ss) s)
    {t : Term S W s'} {ts : Args S W ss} (h : Reducible R t) :
    Reducible R (Term.op f (.cons t ts)) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨_, Step.op R f (ArgsStep.head R hu)⟩

end Rewriting
