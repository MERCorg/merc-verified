module

public import MercLib.Theory.Rewriting.Semantics
public import MercLib.Theory.Rewriting.Proofs.Signature_Proofs
import all MercLib.Theory.Rewriting.Proofs.Signature_Proofs

@[expose] public section

/-!
# Proofs: Semantics

`stepsSound` (rewriting preserves the value of a term in every model) and `distinctOfStepsFalse`
(`a == b` rewriting to `false` separates `a` and `b` in every model in which `==` is equality).

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/Rewriting.lean` (human-vetted); the definitions live in
`MercLib/Theory/Rewriting/Semantics.lean`.
-/

namespace MercLib.Rewriting

variable {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι}

namespace Term

@[simp] private theorem denote_op {V : VarSet S} (A : Algebra S) (ν : Assignment A V)
    {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) (args : Args S V ss) :
    denote A ν (.op f args) = A.interp f (Args.denote A ν args) := rfl

@[simp] private theorem _root_.MercLib.Rewriting.Args.denote_cons {V : VarSet S} (A : Algebra S)
    (ν : Assignment A V) {s : S.Srt} {ss : List S.Srt} (t : Term S V s) (ts : Args S V ss) :
    Args.denote A ν (.cons t ts) = (Term.denote A ν t, Args.denote A ν ts) := rfl

mutual

/-- The value of a substituted term is the value of the term under the induced assignment. -/
private theorem denote_subst {V W : VarSet S} (A : Algebra S) (ν : Assignment A W)
    (σ : Subst S V W) :
    ∀ {s : S.Srt} (t : Term S V s),
      denote A ν (subst σ t) = denote A (fun s x => denote A ν (σ s x)) t
  | _, .var _ => rfl
  | _, .op _ args => by rw [subst_op, denote_op, denote_op, Args.denote_subst A ν σ args]

/-- `denote_subst` for argument lists. -/
private theorem _root_.MercLib.Rewriting.Args.denote_subst {V W : VarSet S} (A : Algebra S)
    (ν : Assignment A W) (σ : Subst S V W) :
    ∀ {ss : List S.Srt} (as : Args S V ss),
      Args.denote A ν (Args.subst σ as) = Args.denote A (fun s x => denote A ν (σ s x)) as
  | _, .nil => rfl
  | _, .cons t ts => by
    rw [Args.subst_cons, Args.denote_cons, Args.denote_cons, Term.denote_subst A ν σ t,
      Args.denote_subst A ν σ ts]

end

end Term

mutual

/-- A step whose conditions are checked by a relation that preserves values preserves values. -/
private theorem denote_stepWith {A : Algebra S} (hA : Models A R) (ν : Assignment A W)
    {C : ∀ s, Term S W s → Term S W s → Prop}
    (hC : ∀ s a b, C s a b → Term.denote A ν a = Term.denote A ν b) :
    ∀ {s : S.Srt} {a b : Term S W s}, StepWith R C s a b →
      Term.denote A ν a = Term.denote A ν b
  | _, _, _, .rule i σ hc => by
    rw [Term.denote_subst, Term.denote_subst]
    refine hA i _ fun c hc' => ?_
    have h := hC _ _ _ (hc c hc')
    rwa [Term.denote_subst, Term.denote_subst] at h
  | _, _, _, .op f h => by
    rw [Term.denote_op, Term.denote_op, denote_argsStepWith hA ν hC h]

/-- `denote_stepWith` for argument lists. -/
private theorem denote_argsStepWith {A : Algebra S} (hA : Models A R) (ν : Assignment A W)
    {C : ∀ s, Term S W s → Term S W s → Prop}
    (hC : ∀ s a b, C s a b → Term.denote A ν a = Term.denote A ν b) :
    ∀ {ss : List S.Srt} {as bs : Args S W ss}, ArgsStepWith R C ss as bs →
      Args.denote A ν as = Args.denote A ν bs
  | _, _, _, .head h => by
    rw [Args.denote_cons, Args.denote_cons, denote_stepWith hA ν hC h]
  | _, _, _, .tail h => by
    rw [Args.denote_cons, Args.denote_cons, denote_argsStepWith hA ν hC h]

end

/-- A step at every condition depth preserves values. -/
private theorem denote_stepAt {A : Algebra S} (hA : Models A R) (ν : Assignment A W) :
    ∀ (n : Nat) {s : S.Srt} {a b : Term S W s}, stepAt R n s a b →
      Term.denote A ν a = Term.denote A ν b
  | 0, _, _, _, h => h.elim
  | n + 1, _, _, _, h => by
    refine denote_stepWith hA ν (fun s a b hab => ?_) h
    induction hab with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans (denote_stepAt hA ν n hstep)

/-- **Rewriting is sound.** -/
public theorem stepsSound (R : TRS S V ι) (W : VarSet S) : StepsSound R W := by
  intro A hA ν s a b h
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := hstep
    exact ih.trans (denote_stepAt hA ν n hn)

/-- **Distinct by rewriting.** -/
public theorem distinctOfStepsFalse (E : Equality S) (R : TRS S V ι) (W : VarSet S) :
    DistinctOfStepsFalse E R W := by
  intro A hA hE ν s a b h heq
  have hv := stepsSound R W A hA ν h
  have htrue : A.interp (E.eqOp s) (Term.denote A ν a, Term.denote A ν b, PUnit.unit) =
      A.interp E.trueOp PUnit.unit := (hE.2 s _ _).2 heq
  exact hE.1 (htrue.symm.trans hv)

end MercLib.Rewriting
