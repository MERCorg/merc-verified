module

public import MercLib.Theory.Rewriting.Context
public import MercLib.Theory.Rewriting.Matching
public import MercLib.Theory.Rewriting.Proofs.Signature_Proofs
import all MercLib.Theory.Rewriting.Proofs.Signature_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Facts about substitution, variables and contexts, shared by the proofs of matching, unification and
the critical pair lemma. Every lemma is private; the users `import all` this module. -/

namespace MercLib.Rewriting

variable {S : Signature} {V W Y : VarSet S} {h : S.Srt}

open Term

@[simp] private theorem Ctx.fill_hole (u : Term S V h) : Ctx.fill (Ctx.hole : Ctx S V h h) u = u := rfl
@[simp] private theorem Ctx.fill_op {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s)
    (c : ArgsCtx S V h ss) (u : Term S V h) : Ctx.fill (.op f c) u = .op f (ArgsCtx.fill c u) := rfl
@[simp] private theorem ArgsCtx.fill_head {s : S.Srt} {ss : List S.Srt} (c : Ctx S V h s)
    (ts : Args S V ss) (u : Term S V h) :
    ArgsCtx.fill (.head c ts) u = .cons (Ctx.fill c u) ts := rfl
@[simp] private theorem ArgsCtx.fill_tail {s : S.Srt} {ss : List S.Srt} (t : Term S V s)
    (c : ArgsCtx S V h ss) (u : Term S V h) :
    ArgsCtx.fill (.tail t c) u = .cons t (ArgsCtx.fill c u) := rfl

@[simp] private theorem Ctx.subst_hole (σ : Subst S V W) :
    Ctx.subst σ (Ctx.hole : Ctx S V h h) = .hole := rfl
@[simp] private theorem Ctx.subst_op (σ : Subst S V W) {ss : List S.Srt} {s : S.Srt}
    (f : S.Op ss s) (c : ArgsCtx S V h ss) : Ctx.subst σ (.op f c) = .op f (ArgsCtx.subst σ c) := rfl
@[simp] private theorem ArgsCtx.subst_head (σ : Subst S V W) {s : S.Srt} {ss : List S.Srt}
    (c : Ctx S V h s) (ts : Args S V ss) :
    ArgsCtx.subst σ (.head c ts) = .head (Ctx.subst σ c) (Args.subst σ ts) := rfl
@[simp] private theorem ArgsCtx.subst_tail (σ : Subst S V W) {s : S.Srt} {ss : List S.Srt}
    (t : Term S V s) (c : ArgsCtx S V h ss) :
    ArgsCtx.subst σ (.tail t c) = .tail (Term.subst σ t) (ArgsCtx.subst σ c) := rfl

@[simp] private theorem Term.vars_var {s : S.Srt} (x : V s) : Term.vars (.var x) = [⟨s, x⟩] := rfl
@[simp] private theorem Term.vars_op {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s)
    (args : Args S V ss) : Term.vars (.op f args) = Args.vars args := rfl
@[simp] private theorem Args.vars_nil : Args.vars (.nil : Args S V []) = [] := rfl
@[simp] private theorem Args.vars_cons {s : S.Srt} {ss : List S.Srt} (t : Term S V s)
    (ts : Args S V ss) : Args.vars (.cons t ts) = Term.vars t ++ Args.vars ts := rfl

/-- The composition of two substitutions. -/
private abbrev comp (ρ : Subst S W Y) (μ : Subst S V W) : Subst S V Y := fun s x => subst ρ (μ s x)

mutual

private theorem subst_subst (ρ : Subst S W Y) (μ : Subst S V W) :
    ∀ {s : S.Srt} (t : Term S V s), subst ρ (subst μ t) = subst (comp ρ μ) t
  | _, .var _ => rfl
  | _, .op f args => by simp [args_subst_subst ρ μ args]

private theorem args_subst_subst (ρ : Subst S W Y) (μ : Subst S V W) :
    ∀ {ss : List S.Srt} (as : Args S V ss), Args.subst ρ (Args.subst μ as) = Args.subst (comp ρ μ) as
  | _, .nil => rfl
  | _, .cons t ts => by simp [subst_subst ρ μ t, args_subst_subst ρ μ ts]

end

mutual

private theorem subst_id : ∀ {s : S.Srt} (t : Term S V s), subst (fun _ x => .var x) t = t
  | _, .var _ => rfl
  | _, .op f args => by simp [args_subst_id args]

private theorem args_subst_id : ∀ {ss : List S.Srt} (as : Args S V ss),
    Args.subst (fun _ x => .var x) as = as
  | _, .nil => rfl
  | _, .cons t ts => by simp [subst_id t, args_subst_id ts]

end

mutual

private theorem subst_congr {σ τ : Subst S V W} :
    ∀ {s : S.Srt} (t : Term S V s), (∀ y ∈ Term.vars t, σ y.1 y.2 = τ y.1 y.2) → subst σ t = subst τ t
  | _, .var x, e => by simpa using e ⟨_, x⟩ (by simp)
  | _, .op f args, e => by simp [args_subst_congr args (by simpa using e)]

private theorem args_subst_congr {σ τ : Subst S V W} :
    ∀ {ss : List S.Srt} (as : Args S V ss), (∀ y ∈ Args.vars as, σ y.1 y.2 = τ y.1 y.2) →
      Args.subst σ as = Args.subst τ as
  | _, .nil, _ => rfl
  | _, .cons t ts, e => by
    simp only [Args.subst_cons]
    rw [subst_congr t fun y hy => e y (by simp [hy]),
      args_subst_congr ts fun y hy => e y (by simp [hy])]

end

mutual

private theorem vars_subst (σ : Subst S V W) : ∀ {s : S.Srt} (t : Term S V s) (y : Σ s, W s),
    y ∈ Term.vars (subst σ t) → ∃ z ∈ Term.vars t, y ∈ Term.vars (σ z.1 z.2)
  | _, .var x, y, hy => ⟨⟨_, x⟩, by simp, hy⟩
  | _, .op f args, y, hy => by simpa using args_vars_subst σ args y (by simpa using hy)

private theorem args_vars_subst (σ : Subst S V W) : ∀ {ss : List S.Srt} (as : Args S V ss)
    (y : Σ s, W s), y ∈ Args.vars (Args.subst σ as) →
      ∃ z ∈ Args.vars as, y ∈ Term.vars (σ z.1 z.2)
  | _, .nil, y, hy => by simp at hy
  | _, .cons t ts, y, hy => by
    simp only [Args.subst_cons, Args.vars_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨z, hz, h'⟩ := vars_subst σ t y hy
      exact ⟨z, by simp [hz], h'⟩
    · obtain ⟨z, hz, h'⟩ := args_vars_subst σ ts y hy
      exact ⟨z, by simp [hz], h'⟩

end

mutual

private theorem subst_fill (σ : Subst S V W) (u : Term S V h) : ∀ {s : S.Srt} (C : Ctx S V h s),
    subst σ (Ctx.fill C u) = Ctx.fill (Ctx.subst σ C) (subst σ u)
  | _, .hole => rfl
  | _, .op f c => by simp [args_subst_fill σ u c]

private theorem args_subst_fill (σ : Subst S V W) (u : Term S V h) :
    ∀ {ss : List S.Srt} (C : ArgsCtx S V h ss),
      Args.subst σ (ArgsCtx.fill C u) = ArgsCtx.fill (ArgsCtx.subst σ C) (subst σ u)
  | _, .head c ts => by simp [subst_fill σ u c]
  | _, .tail t c => by simp [args_subst_fill σ u c]

end

mutual

private theorem ctx_subst_subst (ρ : Subst S W Y) (μ : Subst S V W) :
    ∀ {s : S.Srt} (C : Ctx S V h s), Ctx.subst ρ (Ctx.subst μ C) = Ctx.subst (comp ρ μ) C
  | _, .hole => rfl
  | _, .op f c => by simp [argsctx_subst_subst ρ μ c]

private theorem argsctx_subst_subst (ρ : Subst S W Y) (μ : Subst S V W) :
    ∀ {ss : List S.Srt} (C : ArgsCtx S V h ss),
      ArgsCtx.subst ρ (ArgsCtx.subst μ C) = ArgsCtx.subst (comp ρ μ) C
  | _, .head c ts => by simp [ctx_subst_subst ρ μ c, args_subst_subst ρ μ ts]
  | _, .tail t c => by simp [subst_subst ρ μ t, argsctx_subst_subst ρ μ c]

end

open Classical in
/-- `σ` with the variable `x` sent to `c`. -/
private noncomputable def sUpdate (σ : Subst S V W) {k : S.Srt} (x : V k) (c : Term S W k) :
    Subst S V W :=
  fun s y => if e : (⟨s, y⟩ : Σ s, V s) = ⟨k, x⟩ then by cases e; exact c else σ s y

@[simp] private theorem sUpdate_same (σ : Subst S V W) {k : S.Srt} (x : V k) (c : Term S W k) :
    sUpdate σ x c k x = c := by
  simp [sUpdate]

private theorem sUpdate_ne (σ : Subst S V W) {k : S.Srt} (x : V k) (c : Term S W k) {s : S.Srt}
    {y : V s} (e : (⟨s, y⟩ : Σ s, V s) ≠ ⟨k, x⟩) : sUpdate σ x c s y = σ s y := by
  simp [sUpdate, e]

end MercLib.Rewriting
