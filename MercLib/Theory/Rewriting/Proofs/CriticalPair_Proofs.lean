module

public import MercLib.Theory.Rewriting.Confluence
public import MercLib.Theory.Rewriting.Proofs.Term_Proofs
public import MercLib.Theory.Rewriting.Proofs.Unification_Proofs
import all MercLib.Theory.Rewriting.Proofs.Signature_Proofs
import all MercLib.Theory.Rewriting.Proofs.Term_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The critical pair lemma. For an unconditional system the rewrite relation is `U` below, an inductive
relation without condition levels. A peak is analysed by descending into the left-hand side of the
rule contracted at the root: the other step lies either below a variable of the left-hand side, which
is joinable by rewriting the instances of that variable, or at a non-variable subterm, which is an
instance of a critical pair. -/

namespace MercLib.Rewriting

open Term Relation

variable {S : Signature} {V W Y : VarSet S} {ι : Type} {R : TRS S V ι} {h : S.Srt}

/-- One step of an unconditional system. -/
private abbrev U (R : TRS S V ι) (W : VarSet S) : ∀ s, Term S W s → Term S W s → Prop :=
  StepWith R fun _ _ _ => False

/-- One step inside an argument list. -/
private abbrev UA (R : TRS S V ι) (W : VarSet S) : ∀ ss, Args S W ss → Args S W ss → Prop :=
  ArgsStepWith R fun _ _ _ => False

private abbrev UU (R : TRS S V ι) (W : VarSet S) (s : S.Srt) := ReflTransGen (U R W s)
private abbrev AA (R : TRS S V ι) (W : VarSet S) (ss : List S.Srt) := ReflTransGen (UA R W ss)

section Mono

variable {C C' : ∀ s, Term S W s → Term S W s → Prop}

mutual

private theorem sw_mono (hu : Unconditional R) :
    ∀ {s : S.Srt} {a b : Term S W s}, StepWith R C s a b → StepWith R C' s a b
  | _, _, _, .rule i σ _ => .rule i σ (by simp [hu i])
  | _, _, _, .op f h => .op f (asw_mono hu h)

private theorem asw_mono (hu : Unconditional R) :
    ∀ {ss : List S.Srt} {a b : Args S W ss}, ArgsStepWith R C ss a b → ArgsStepWith R C' ss a b
  | _, _, _, .head h => .head (sw_mono hu h)
  | _, _, _, .tail h => .tail (asw_mono hu h)

end

end Mono

private theorem step_eq (hu : Unconditional R) (s : S.Srt) :
    (Step (W := W) R s) = U R W s := by
  funext a b
  refine propext ⟨?_, fun h => ⟨1, sw_mono hu h⟩⟩
  rintro ⟨n, hn⟩
  cases n with
  | zero => exact absurd hn (by simp [stepAt])
  | succ n => exact sw_mono hu hn

private theorem steps_eq (hu : Unconditional R) (s : S.Srt) :
    (Steps (W := W) R s) = UU R W s := by
  simp only [Steps, UU, step_eq hu s]

private theorem lift_op {ss : List S.Srt} {s : S.Srt} (f : S.Op ss s) {a b : Args S W ss}
    (h : AA R W ss a b) : UU R W s (.op f a) (.op f b) :=
  ReflTransGen.lift (Term.op f) (fun _ _ h => StepWith.op f h) _ _ h

private theorem lift_head {s : S.Srt} {ss : List S.Srt} {t t' : Term S W s} (ts : Args S W ss)
    (h : UU R W s t t') : AA R W (s :: ss) (.cons t ts) (.cons t' ts) :=
  ReflTransGen.lift (fun x => Args.cons x ts) (fun _ _ h => ArgsStepWith.head h) _ _ h

private theorem lift_tail {s : S.Srt} {ss : List S.Srt} (t : Term S W s) {ts ts' : Args S W ss}
    (h : AA R W ss ts ts') : AA R W (s :: ss) (.cons t ts) (.cons t ts') :=
  ReflTransGen.lift (fun x => Args.cons t x) (fun _ _ h => ArgsStepWith.tail h) _ _ h

mutual

private theorem u_subst (hu : Unconditional R) (τ : Subst S W Y) :
    ∀ {s : S.Srt} {a b : Term S W s}, U R W s a b → U R Y s (subst τ a) (subst τ b)
  | _, _, _, .rule i σ _ => by
    rw [subst_subst, subst_subst]
    exact .rule i _ (by simp [hu i])
  | _, _, _, .op f h => .op f (ua_subst hu τ h)

private theorem ua_subst (hu : Unconditional R) (τ : Subst S W Y) :
    ∀ {ss : List S.Srt} {a b : Args S W ss}, UA R W ss a b →
      UA R Y ss (Args.subst τ a) (Args.subst τ b)
  | _, _, _, .head h => .head (u_subst hu τ h)
  | _, _, _, .tail h => .tail (ua_subst hu τ h)

end

private theorem uu_subst (hu : Unconditional R) (τ : Subst S W Y) {s : S.Srt} {a b : Term S W s}
    (h : UU R W s a b) : UU R Y s (subst τ a) (subst τ b) :=
  ReflTransGen.lift (subst τ) (fun _ _ h => u_subst hu τ h) _ _ h

mutual

private theorem u_fill {a b : Term S W h} (hab : U R W h a b) :
    ∀ {s : S.Srt} (C : Ctx S W h s), U R W s (Ctx.fill C a) (Ctx.fill C b)
  | _, .hole => hab
  | _, .op f c => .op f (ua_fill hab c)

private theorem ua_fill {a b : Term S W h} (hab : U R W h a b) :
    ∀ {ss : List S.Srt} (C : ArgsCtx S W h ss), UA R W ss (ArgsCtx.fill C a) (ArgsCtx.fill C b)
  | _, .head c _ => .head (u_fill hab c)
  | _, .tail _ c => .tail (ua_fill hab c)

end

section Monotone

variable {σ σ' : Subst S V W} (hm : ∀ s y, UU R W s (σ s y) (σ' s y))
include hm

set_option linter.unusedSectionVars false in
mutual

private theorem subst_mono : ∀ {s : S.Srt} (t : Term S V s), UU R W s (subst σ t) (subst σ' t)
  | _, .var x => hm _ x
  | _, .op f a => lift_op f (args_subst_mono a)

private theorem args_subst_mono :
    ∀ {ss : List S.Srt} (a : Args S V ss), AA R W ss (Args.subst σ a) (Args.subst σ' a)
  | _, .nil => .refl
  | _, .cons t ts => (lift_head _ (subst_mono t)).trans (lift_tail _ (args_subst_mono ts))

end

set_option linter.unusedSectionVars false in
mutual

private theorem ctx_mono (c : Term S W h) : ∀ {s : S.Srt} (C : Ctx S V h s),
    UU R W s (Ctx.fill (Ctx.subst σ C) c) (Ctx.fill (Ctx.subst σ' C) c)
  | _, .hole => .refl
  | _, .op f a => lift_op f (argsctx_mono c a)

private theorem argsctx_mono (c : Term S W h) : ∀ {ss : List S.Srt} (C : ArgsCtx S V h ss),
    AA R W ss (ArgsCtx.fill (ArgsCtx.subst σ C) c) (ArgsCtx.fill (ArgsCtx.subst σ' C) c)
  | _, .head d ts => (lift_head _ (ctx_mono c d)).trans (lift_tail _ (args_subst_mono hm ts))
  | _, .tail t d => (lift_head _ (subst_mono hm t)).trans (lift_tail _ (argsctx_mono c d))

end

end Monotone

mutual

/-- Plug a context into the hole of another. -/
private def Ctx.comp {k : S.Srt} (D : Ctx S V h k) : {s : S.Srt} → Ctx S V k s → Ctx S V h s
  | _, .hole => D
  | _, .op f c => .op f (ArgsCtx.comp D c)

/-- The same for an argument context. -/
private def ArgsCtx.comp {k : S.Srt} (D : Ctx S V h k) :
    {ss : List S.Srt} → ArgsCtx S V k ss → ArgsCtx S V h ss
  | _, .head c ts => .head (Ctx.comp D c) ts
  | _, .tail t c => .tail t (ArgsCtx.comp D c)

end

mutual

private theorem fill_comp {k : S.Srt} (D : Ctx S V h k) (w : Term S V h) :
    ∀ {s : S.Srt} (C : Ctx S V k s), Ctx.fill (Ctx.comp D C) w = Ctx.fill C (Ctx.fill D w)
  | _, .hole => rfl
  | _, .op f c => by simp [Ctx.comp, argsfill_comp D w c]

private theorem argsfill_comp {k : S.Srt} (D : Ctx S V h k) (w : Term S V h) :
    ∀ {ss : List S.Srt} (C : ArgsCtx S V k ss),
      ArgsCtx.fill (ArgsCtx.comp D C) w = ArgsCtx.fill C (Ctx.fill D w)
  | _, .head c ts => by simp [ArgsCtx.comp, fill_comp D w c]
  | _, .tail t c => by simp [ArgsCtx.comp, argsfill_comp D w c]

end

mutual

private theorem subst_comp (σ : Subst S V W) {k : S.Srt} (D : Ctx S V h k) :
    ∀ {s : S.Srt} (C : Ctx S V k s),
      Ctx.subst σ (Ctx.comp D C) = Ctx.comp (Ctx.subst σ D) (Ctx.subst σ C)
  | _, .hole => rfl
  | _, .op f c => by simp [Ctx.comp, argssubst_comp σ D c]

private theorem argssubst_comp (σ : Subst S V W) {k : S.Srt} (D : Ctx S V h k) :
    ∀ {ss : List S.Srt} (C : ArgsCtx S V k ss),
      ArgsCtx.subst σ (ArgsCtx.comp D C) = ArgsCtx.comp (Ctx.subst σ D) (ArgsCtx.subst σ C)
  | _, .head c ts => by simp [ArgsCtx.comp, subst_comp σ D c]
  | _, .tail t c => by simp [ArgsCtx.comp, argssubst_comp σ D c]

end

/-- Joinability in an unconditional system. -/
private abbrev J (R : TRS S V ι) (W : VarSet S) (s : S.Srt) := Join (UU R W s)

private theorem J.symm {s : S.Srt} {a b : Term S W s} (h : J R W s a b) : J R W s b a := by
  obtain ⟨d, h₁, h₂⟩ := h
  exact ⟨d, h₂, h₁⟩

/-- A step below a variable of the left-hand side. -/
private theorem var_overlap (hu : Unconditional R) (i : ι) (σ : Subst S V W) {k : S.Srt} (x : V k)
    (C : Ctx S V k (R i).srt) {c : Term S W k} (hfill : Ctx.fill C (.var x) = (R i).lhs)
    (hstep : U R W k (σ k x) c) :
    J R W (R i).srt (subst σ (R i).rhs) (Ctx.fill (Ctx.subst σ C) c) := by
  classical
  let σ' : Subst S V W := sUpdate σ x c
  have hm : ∀ s y, UU R W s (σ s y) (σ' s y) := by
    intro s y
    by_cases e : (⟨s, y⟩ : Σ s, V s) = ⟨k, x⟩
    · cases e
      rw [show σ' k x = c from sUpdate_same _ _ _]
      exact .single hstep
    · rw [show σ' s y = σ s y from sUpdate_ne _ _ _ e]
  have hr : U R W (R i).srt (subst σ' (R i).lhs) (subst σ' (R i).rhs) :=
    .rule i σ' (by simp [hu i])
  have he : Ctx.fill (Ctx.subst σ' C) c = subst σ' (R i).lhs := by
    rw [← hfill, subst_fill]
    congr 1
    exact (sUpdate_same _ _ _).symm
  refine ⟨subst σ' (R i).rhs, subst_mono hm _, (ctx_mono hm c C).trans ?_⟩
  rw [he]
  exact .single hr

/-- A step at a non-variable subterm of the left-hand side: an instance of a critical pair. -/
private theorem critical_overlap (hu : Unconditional R) (hc : CriticalPairsJoinable R) (i j : ι)
    (σ : Subst S V W) (τ : Subst S V W) (C : Ctx S V (R j).srt (R i).srt) (u : Term S V (R j).srt)
    (hfill : Ctx.fill C u = (R i).lhs) (hnv : ∀ x, u ≠ .var x)
    (he : subst σ u = subst τ (R j).lhs) :
    J R W (R i).srt (subst σ (R i).rhs) (Ctx.fill (Ctx.subst σ C) (subst τ (R j).rhs)) := by
  let pair : Subst S (Both V) W := fun s x => Sum.elim (σ s) (τ s) x
  have hpl : comp pair renameL = σ := rfl
  have hpr : comp pair renameR = τ := rfl
  have uni : Unifies pair (subst renameL u) (subst renameR (R j).lhs) := by
    unfold Unifies
    rw [subst_subst, subst_subst, hpl, hpr, he]
  obtain ⟨μ, hμ⟩ := unificationTheorem S _ _ _ _ _ pair uni
  obtain ⟨ρ, hρ⟩ := hμ.2 W pair uni
  have hcomp : comp ρ μ = pair := by
    funext s x
    exact hρ s x
  let O : Overlap R := ⟨i, j, C, u, μ, hfill, hnv, hμ⟩
  obtain ⟨d, h₁, h₂⟩ := hc O
  rw [steps_eq hu] at h₁ h₂
  refine ⟨subst ρ d, ?_, ?_⟩
  · have := uu_subst hu ρ h₁
    have e : subst ρ O.left = subst σ (R i).rhs := by
      change subst ρ (subst μ (subst renameL (R i).rhs)) = _
      rw [subst_subst, hcomp, subst_subst, hpl]
    rwa [e] at this
  · have := uu_subst hu ρ h₂
    have e : subst ρ O.right = Ctx.fill (Ctx.subst σ C) (subst τ (R j).rhs) := by
      change subst ρ (subst μ (Ctx.fill (Ctx.subst renameL C) (subst renameR (R j).rhs))) = _
      rw [subst_subst, hcomp, subst_fill, ctx_subst_subst, hpl, subst_subst, hpr]
    rwa [e] at this

section Descend

variable (hu : Unconditional R) (hc : CriticalPairsJoinable R) (i : ι) (σ : Subst S V W)
include hu hc

set_option linter.unusedSectionVars false in
mutual

/-- A step in an instance of a subterm `u` of the left-hand side of the rule `i`. -/
private theorem descend : ∀ {k : S.Srt} (u : Term S V k) (C : Ctx S V k (R i).srt)
    {a c : Term S W k}, Ctx.fill C u = (R i).lhs → subst σ u = a → U R W k a c →
    J R W (R i).srt (subst σ (R i).rhs) (Ctx.fill (Ctx.subst σ C) c)
  | _, .var x, C, _, _, hfill, he, hstep => by
    subst he
    exact var_overlap hu i σ x C hfill hstep
  | _, .op f as, C, _, _, hfill, he, hstep => by
    cases hstep with
    | rule j τ _ => exact critical_overlap hu hc i j σ τ C _ hfill (fun x h => by cases h) he
    | op g hA =>
      cases he
      refine descendArgs as (fun _ A => Ctx.comp (Ctx.op f A) C)
        (fun bs => Ctx.fill (Ctx.subst σ C) (.op f bs)) ?_ ?_ rfl hA
      · intro k' A w e
        rw [fill_comp, Ctx.fill_op, e, hfill]
      · intro k' A c
        rw [subst_comp, fill_comp, Ctx.subst_op, Ctx.fill_op]

/-- A step in an instance of an argument list of a subterm of the left-hand side. -/
private theorem descendArgs : ∀ {ss : List S.Srt} (as : Args S V ss)
    (E : ∀ k, ArgsCtx S V k ss → Ctx S V k (R i).srt) (Gs : Args S W ss → Term S W (R i).srt),
    (∀ k (A : ArgsCtx S V k ss) (w : Term S V k), ArgsCtx.fill A w = as →
      Ctx.fill (E k A) w = (R i).lhs) →
    (∀ k (A : ArgsCtx S V k ss) (c : Term S W k),
      Ctx.fill (Ctx.subst σ (E k A)) c = Gs (ArgsCtx.fill (ArgsCtx.subst σ A) c)) →
    ∀ {a bs : Args S W ss}, Args.subst σ as = a → UA R W ss a bs →
      J R W (R i).srt (subst σ (R i).rhs) (Gs bs)
  | _, .nil, _, _, _, _, _, _, he, hstep => by
    cases he
    cases hstep
  | _, .cons t ts, E, Gs, hfill, hs, _, _, he, hstep => by
    cases he
    cases hstep with
    | head h' =>
      have := descend t (E _ (.head .hole ts)) (hfill _ _ t rfl) rfl h'
      rw [hs] at this
      exact this
    | tail h' =>
      exact descendArgs ts (fun k A => E k (.tail t A)) (fun bs => Gs (.cons (subst σ t) bs))
        (fun k A w e => hfill k _ w (by rw [ArgsCtx.fill_tail, e]))
        (fun k A c => hs k _ c) rfl h'

end

end Descend

mutual

private theorem peak (hu : Unconditional R) (hc : CriticalPairsJoinable R) :
    ∀ {s : S.Srt} {a b : Term S W s}, U R W s a b → ∀ {c : Term S W s}, U R W s a c → J R W s b c
  | _, _, _, .rule i σ _ => fun h₂ => by
    simpa using descend hu hc i σ (R i).lhs .hole rfl rfl h₂
  | _, _, _, .op f (as := as) (bs := bs) hA => fun h₂ => by
    generalize e : Term.op f as = a at h₂
    cases h₂ with
    | rule j τ _ =>
      have := descend hu hc j τ (R j).lhs .hole rfl e.symm (.op f hA)
      exact J.symm (by simpa using this)
    | op g hB =>
      cases e
      obtain ⟨d, h₁, h₂⟩ := argsPeak hu hc hA hB
      exact ⟨.op f d, lift_op f h₁, lift_op f h₂⟩

private theorem argsPeak (hu : Unconditional R) (hc : CriticalPairsJoinable R) :
    ∀ {ss : List S.Srt} {a b : Args S W ss}, UA R W ss a b → ∀ {c : Args S W ss}, UA R W ss a c →
      Join (AA R W ss) b c
  | _, _, _, .head h₁ => fun h₂ => by
    cases h₂ with
    | head h₂ =>
      obtain ⟨d, e₁, e₂⟩ := peak hu hc h₁ h₂
      exact ⟨_, lift_head _ e₁, lift_head _ e₂⟩
    | tail h₂ => exact ⟨_, .single (.tail h₂), .single (.head h₁)⟩
  | _, _, _, .tail h₁ => fun h₂ => by
    cases h₂ with
    | head h₂ => exact ⟨_, .single (.head h₂), .single (.tail h₁)⟩
    | tail h₂ =>
      obtain ⟨d, e₁, e₂⟩ := argsPeak hu hc h₁ h₂
      exact ⟨_, lift_tail _ e₁, lift_tail _ e₂⟩

end

private theorem joinable_of_lc (hu : Unconditional R) (hl : LocallyConfluent R (Both V)) :
    CriticalPairsJoinable R := by
  intro O
  have hu₁ : U R (Both V) (R O.i).srt (subst O.μ (subst renameL (R O.i).lhs)) O.left := by
    unfold Overlap.left
    rw [subst_subst, subst_subst]
    exact .rule O.i _ (by simp [hu O.i])
  have hu₂ : U R (Both V) (R O.i).srt (subst O.μ (subst renameL (R O.i).lhs)) O.right := by
    unfold Overlap.right
    rw [← O.fill_eq, subst_fill, subst_fill, subst_fill, O.mgu.1, subst_subst, subst_subst
      (ρ := O.μ) (μ := renameR) (R O.j).rhs]
    exact u_fill (.rule O.j _ (by simp [hu O.j])) _
  have h := hl _ (a := subst O.μ (subst renameL (R O.i).lhs)) (by
    rw [show rel R (Both V) (R O.i).srt = U R (Both V) (R O.i).srt from step_eq hu _]; exact hu₁)
    (by rw [show rel R (Both V) (R O.i).srt = U R (Both V) (R O.i).srt from step_eq hu _]; exact hu₂)
  exact h

/-- **The critical pair lemma.** -/
public theorem criticalPairLemma (R : TRS S V ι) : CriticalPairLemma R := by
  intro hu
  refine ⟨fun hc W s a b c h₁ h₂ => ?_, joinable_of_lc hu⟩
  have e : rel R W s = U R W s := step_eq hu s
  rw [e] at h₁ h₂ ⊢
  exact peak hu hc h₁ h₂

end MercLib.Rewriting
