module

public import MercLib.Theory.Rewriting.Matching
public import MercLib.Theory.Rewriting.Proofs.Signature_Proofs
public import MercLib.Theory.Rewriting.Proofs.Term_Proofs
import all MercLib.Theory.Rewriting.Proofs.Signature_Proofs
import all MercLib.Theory.Rewriting.Proofs.Term_Proofs
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonBase_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Matching a linear pattern is a condition on the head symbols. -/

namespace MercLib.Rewriting

open SetAutomaton

variable {S : Signature} {V W : VarSet S}

@[simp] private theorem toPat_var {s : S.Srt} (x : V s) : Term.toPat (.var x) = Pat.omega := rfl
@[simp] private theorem toPat_op {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) (a : Args S V ss) :
    Term.toPat (.op f a) = Pat.app ⟨ss, s, f⟩ (Args.toPats a) := rfl
@[simp] private theorem toPats_nil : Args.toPats (.nil : Args S V []) = [] := rfl
@[simp] private theorem toPats_cons {s : S.Srt} {ss : List S.Srt} (t : Term S V s)
    (ts : Args S V ss) : Args.toPats (.cons t ts) = Term.toPat t :: Args.toPats ts := rfl

/-- The head-symbol condition at all positions, without the domain. -/
private def Mat (l t : Pat (Sym S)) : Prop :=
  ∀ p' l', l.at p' = some l' → l' ≠ .omega → (t.at p').bind Pat.hd = l'.hd

/-- The same for argument lists. -/
private def MatArgs (ls ts : List (Pat (Sym S))) : Prop :=
  ∀ i p' l', Pat.atArgs ls i p' = some l' → l' ≠ .omega → (Pat.atArgs ts i p').bind Pat.hd = l'.hd

mutual

private theorem mat_subst (σ : Term.Subst S V W) : ∀ {s : S.Srt} (l : Term S V s),
    Mat l.toPat (Term.subst σ l).toPat
  | _, .var _ => by
    intro p' l' hl hne
    cases p' with
    | nil => simp [Pat.at] at hl; exact absurd hl.symm hne
    | cons i r => simp [Pat.at] at hl
  | _, .op f a => by
    intro p' l' hl hne
    cases p' with
    | nil =>
      simp only [toPat_op, Pat.at, Option.some.injEq] at hl
      subst hl
      simp [Pat.at, Pat.hd]
    | cons i r =>
      simp only [toPat_op, Pat.at] at hl
      simpa [Pat.at] using args_mat_subst σ a i r l' hl hne

private theorem args_mat_subst (σ : Term.Subst S V W) : ∀ {ss : List S.Srt} (a : Args S V ss),
    MatArgs (Args.toPats a) (Args.toPats (Args.subst σ a))
  | _, .nil => by intro i r l' hl; simp [Pat.atArgs] at hl
  | _, .cons t ts => by
    intro i r l' hl hne
    match i with
    | 0 => simp [Pat.atArgs] at hl
    | 1 => simpa [Pat.atArgs] using mat_subst σ t r l' (by simpa [Pat.atArgs] using hl) hne
    | i + 2 =>
      simpa [Pat.atArgs] using
        args_mat_subst σ ts (i + 1) r l' (by simpa [Pat.atArgs] using hl) hne

end

mutual

private theorem exists_of_mat (hV : ∀ s, V s → Nonempty (Term S W s)) :
    ∀ {s : S.Srt} (l : Term S V s) (t : Term S W s), (Term.vars l).Nodup → Mat l.toPat t.toPat →
      ∃ σ : Term.Subst S V W, Term.subst σ l = t
  | s, .var x, t, _, _ => by
    classical
    have hσ : Nonempty (Term.Subst S V W) := ⟨fun s y => (hV s y).some⟩
    exact ⟨sUpdate hσ.some x t, by simp⟩
  | s, @Term.op _ _ ss _ f a, t, hl, hm => by
    have hr := hm [] _ rfl (by simp)
    cases t with
    | var y => simp [Pat.at, Pat.hd] at hr
    | @op ss' _ g b =>
      simp only [toPat_op, Pat.at, Option.bind_some, Pat.hd, Option.some.injEq] at hr
      obtain ⟨rfl, hg⟩ := Sigma.mk.inj_iff.1 hr
      have hfg : g = f := by simpa using hg
      subst hfg
      obtain ⟨σ, hσ⟩ := args_exists_of_mat hV a b (by simpa using hl)
        (fun i r l' h' hne => by simpa [Pat.at] using hm (i :: r) l' (by simpa [Pat.at] using h') hne)
      exact ⟨σ, by simp [hσ]⟩

private theorem args_exists_of_mat (hV : ∀ s, V s → Nonempty (Term S W s)) :
    ∀ {ss : List S.Srt} (a : Args S V ss) (b : Args S W ss), (Args.vars a).Nodup →
      MatArgs (Args.toPats a) (Args.toPats b) → ∃ σ : Term.Subst S V W, Args.subst σ a = b
  | _, .nil, .nil, _, _ => by
    classical
    exact ⟨fun s y => (hV s y).some, rfl⟩
  | _, .cons t ts, .cons u us, hl, hm => by
    classical
    simp only [Args.vars_cons, List.nodup_append] at hl
    obtain ⟨h₁, h₂, hd⟩ := hl
    obtain ⟨σ₁, e₁⟩ := exists_of_mat hV t u h₁ (fun r l' h' hne => by
      simpa [Pat.atArgs] using hm 1 r l' (by simpa [Pat.atArgs] using h') hne)
    obtain ⟨σ₂, e₂⟩ := args_exists_of_mat hV ts us h₂ (fun i r l' h' hne => by
      match i with
      | 0 => cases e : Args.toPats ts <;> simp [e, Pat.atArgs] at h'
      | j + 1 =>
        simpa [Pat.atArgs] using hm (j + 2) r l' (by simpa [Pat.atArgs] using h') hne)
    refine ⟨fun s y => if (⟨s, y⟩ : Σ s, V s) ∈ Term.vars t then σ₁ s y else σ₂ s y, ?_⟩
    simp only [Args.subst_cons]
    rw [subst_congr (τ := σ₁) t (fun y hy => by simp [hy]),
      args_subst_congr (τ := σ₂) ts (fun y hy => ?_), e₁, e₂]
    have : y ∉ Term.vars t := fun h' => hd y h' y hy rfl
    simp [this]

end

private theorem mat_iff {l t : Pat (Sym S)} : Pat.Matches l t [] ↔ Mat l t := by
  constructor
  · intro h p' l' hl hne
    classical
    have hd : p' ∈ l.dom := (Pat.mem_dom_iff l p').2 (by simp [hl])
    simpa using h p' hd l' hl hne
  · intro h p' _ l' hl hne
    simpa using h p' l' hl hne

/-- **Matching a linear pattern is a condition on head symbols.** -/
public theorem linearMatchIffHeads (S : Signature) (V W : VarSet S) : LinearMatchIffHeads S V W := by
  intro hV s l t hl
  rw [mat_iff]
  constructor
  · rintro ⟨σ, rfl⟩
    exact mat_subst σ l
  · exact exists_of_mat hV l t hl

end MercLib.Rewriting
