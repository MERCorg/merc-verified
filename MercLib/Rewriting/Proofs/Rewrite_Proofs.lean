module

public import MercLib.Rewriting.Rewrite
public import MercLib.Rewriting.Proofs.Signature_Proofs

@[expose] public section

/-!
# Proofs: Rewrite

Basic closure properties of the rewrite relation: rules fire at the root, and rewriting is closed
under contexts.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The definitions live in
`Rewriting/Rewrite.lean` (human-vetted).
-/

namespace MercLib.Rewriting

variable {S : Signature}

variable {V W : VarSet S} {ι : Type}

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

end MercLib.Rewriting
