module

public import MercLib.Theory.Rewriting.Unification
public import MercLib.Theory.Rewriting.Proofs.Term_Proofs
import all MercLib.Theory.Rewriting.Proofs.Signature_Proofs
import all MercLib.Theory.Rewriting.Proofs.Term_Proofs
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.FinRange

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The unification theorem. A list of equations with a unifier has a most general unifier, by induction
on the number of variables and then on the size of the equations: decomposing an equation, or
deleting a trivial one, reduces the size; eliminating a variable reduces the number of variables. -/

namespace MercLib.Rewriting

open Term

variable {S : Signature} {X Y Z : VarSet S}

mutual

private def Term.size : {s : S.Srt} → Term S X s → ℕ
  | _, .var _ => 1
  | _, .op _ a => 1 + Args.size a

private def Args.size : {ss : List S.Srt} → Args S X ss → ℕ
  | _, .nil => 1
  | _, .cons t ts => 1 + Term.size t + Args.size ts

end

mutual

private theorem size_le (τ : Subst S X Y) {y : Σ s, X s} : ∀ {s : S.Srt} (t : Term S X s),
    y ∈ Term.vars t → Term.size (τ y.1 y.2) ≤ Term.size (subst τ t)
  | _, .var x, h => by
    simp only [Term.vars_var, List.mem_singleton] at h
    subst h
    exact le_rfl
  | _, .op f a, h => by
    have := args_size_le τ a (by simpa using h)
    simp only [subst_op, Term.size]
    omega

private theorem args_size_le (τ : Subst S X Y) {y : Σ s, X s} : ∀ {ss : List S.Srt} (a : Args S X ss),
    y ∈ Args.vars a → Term.size (τ y.1 y.2) ≤ Args.size (Args.subst τ a)
  | _, .nil, h => by simp at h
  | _, .cons t ts, h => by
    simp only [Args.vars_cons, List.mem_append] at h
    simp only [Args.subst_cons, Args.size]
    rcases h with h | h
    · have := size_le τ t h
      omega
    · have := args_size_le τ ts h
      omega

end

/-- An equation between two terms or two argument lists. -/
private inductive Eqn (X : VarSet S) where
  | t {s : S.Srt} (u v : Term S X s)
  | a {ss : List S.Srt} (as bs : Args S X ss)

namespace Eqn

private def holds (τ : Subst S X Y) : Eqn X → Prop
  | .t u v => subst τ u = subst τ v
  | .a as bs => Args.subst τ as = Args.subst τ bs

private def vars : Eqn X → List (Σ s, X s)
  | .t u v => Term.vars u ++ Term.vars v
  | .a as bs => Args.vars as ++ Args.vars bs

private def size : Eqn X → ℕ
  | .t u v => Term.size u + Term.size v
  | .a as bs => Args.size as + Args.size bs

private def subst (θ : Subst S X X) : Eqn X → Eqn X
  | .t u v => .t (Term.subst θ u) (Term.subst θ v)
  | .a as bs => .a (Args.subst θ as) (Args.subst θ bs)

private theorem holds_subst (τ : Subst S X Y) (θ : Subst S X X) (e : Eqn X) :
    (e.subst θ).holds τ ↔ e.holds (comp τ θ) := by
  cases e <;> simp [subst, holds, subst_subst, args_subst_subst]

private theorem mem_vars_subst (θ : Subst S X X) (e : Eqn X) {y : Σ s, X s}
    (h : y ∈ (e.subst θ).vars) : ∃ z ∈ e.vars, y ∈ Term.vars (θ z.1 z.2) := by
  cases e with
  | t u v =>
    simp only [subst, vars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, h'⟩ := vars_subst θ u y h
      exact ⟨z, Or.inl hz, h'⟩
    · obtain ⟨z, hz, h'⟩ := vars_subst θ v y h
      exact ⟨z, Or.inr hz, h'⟩
  | a as bs =>
    simp only [subst, vars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨z, hz, h'⟩ := args_vars_subst θ as y h
      exact ⟨z, Or.inl hz, h'⟩
    · obtain ⟨z, hz, h'⟩ := args_vars_subst θ bs y h
      exact ⟨z, Or.inr hz, h'⟩

end Eqn

/-- `τ` solves all the equations. -/
private def Holds (τ : Subst S X Y) (E : List (Eqn X)) : Prop := ∀ e ∈ E, e.holds τ

/-- `μ` is a most general unifier of the equations. -/
private def IsMgu (μ : Subst S X X) (E : List (Eqn X)) : Prop :=
  Holds μ E ∧ ∀ (Y : VarSet S) (τ : Subst S X Y), Holds τ E →
    ∃ ρ : Subst S X Y, ∀ s x, subst ρ (μ s x) = τ s x

private abbrev allVars (E : List (Eqn X)) : List (Σ s, X s) := E.flatMap Eqn.vars

open Classical in
private noncomputable abbrev card (E : List (Eqn X)) : ℕ := (allVars E).toFinset.card

private abbrev total (E : List (Eqn X)) : ℕ := (E.map Eqn.size).sum

private abbrev Solvable (E : List (Eqn X)) : Prop := ∃ (Y : VarSet S) (τ : Subst S X Y), Holds τ E

private theorem card_le {E E' : List (Eqn X)} (h : ∀ y ∈ allVars E', y ∈ allVars E) :
    card E' ≤ card E := by
  classical
  exact Finset.card_le_card fun y hy => List.mem_toFinset.2 (h y (List.mem_toFinset.1 hy))

private theorem mgu_of_iff {μ : Subst S X X} {E E' : List (Eqn X)}
    (h : ∀ (Y : VarSet S) (τ : Subst S X Y), Holds τ E' ↔ Holds τ E) (m : IsMgu μ E') : IsMgu μ E :=
  ⟨(h _ μ).1 m.1, fun Y τ hτ => m.2 Y τ ((h Y τ).2 hτ)⟩

private theorem solvable_of_iff {E E' : List (Eqn X)}
    (h : ∀ (Y : VarSet S) (τ : Subst S X Y), Holds τ E' ↔ Holds τ E) (s : Solvable E) :
    Solvable E' := by
  obtain ⟨Y, τ, hτ⟩ := s
  exact ⟨Y, τ, (h Y τ).2 hτ⟩

private theorem holds_cons {τ : Subst S X Y} {e : Eqn X} {E : List (Eqn X)} :
    Holds τ (e :: E) ↔ e.holds τ ∧ Holds τ E := by
  simp [Holds]

/-- Eliminate the variable `x`. -/
private theorem elim_case {s : S.Srt} (x : X s) (v : Term S X s) (E : List (Eqn X))
    (hx : (⟨s, x⟩ : Σ s, X s) ∉ Term.vars v)
    (IH : ∀ E' : List (Eqn X), card E' < card (.t (.var x) v :: E) → Solvable E' → ∃ μ, IsMgu μ E')
    (hu : Solvable (.t (.var x) v :: E)) : ∃ μ, IsMgu μ (.t (.var x) v :: E) := by
  classical
  let θ : Subst S X X := sUpdate (fun _ z => .var z) x v
  have key : ∀ {Y : VarSet S} (τ : Subst S X Y), τ s x = subst τ v → comp τ θ = τ := by
    intro Y τ h
    funext s' y
    by_cases e : (⟨s', y⟩ : Σ s, X s) = ⟨s, x⟩
    · cases e
      change subst τ (θ s x) = τ s x
      rw [show θ s x = v from sUpdate_same _ _ _]
      exact h.symm
    · change subst τ (θ s' y) = τ s' y
      rw [show θ s' y = .var y from sUpdate_ne _ _ _ e]
      rfl
  have hθv : subst θ v = v := by
    refine (subst_congr v fun z hz => ?_).trans (subst_id v)
    have hne : (⟨z.1, z.2⟩ : Σ s, X s) ≠ ⟨s, x⟩ := fun e => hx (e ▸ hz)
    exact sUpdate_ne _ _ _ hne
  have hhead : ∀ {Y : VarSet S} (τ : Subst S X Y), (Eqn.t (.var x) v).holds τ → τ s x = subst τ v :=
    fun _ h => h
  have hE' : ∀ {Y : VarSet S} (τ : Subst S X Y), Holds τ (.t (.var x) v :: E) →
      Holds τ (E.map (Eqn.subst θ)) := by
    intro Y τ h e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    rw [Eqn.holds_subst, key τ (hhead τ (holds_cons.1 h).1)]
    exact (holds_cons.1 h).2 e' he'
  have hcard : card (E.map (Eqn.subst θ)) < card (.t (.var x) v :: E) := by
    refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
    · simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map] at hy ⊢
      obtain ⟨_, ⟨e', he', rfl⟩, hy⟩ := hy
      obtain ⟨z, hz, h'⟩ := Eqn.mem_vars_subst θ e' hy
      by_cases e : (⟨z.1, z.2⟩ : Σ s, X s) = ⟨s, x⟩
      · have hzx : z = ⟨s, x⟩ := e
        subst hzx
        have : y ∈ Term.vars v := by simpa [θ] using h'
        exact ⟨_, List.mem_cons_self, by simp [Eqn.vars, this]⟩
      · have : θ z.1 z.2 = .var z.2 := sUpdate_ne _ _ _ e
        rw [this] at h'
        simp only [Term.vars_var, List.mem_singleton] at h'
        exact ⟨e', List.mem_cons_of_mem _ he', h' ▸ hz⟩
    · have hm : (⟨s, x⟩ : Σ s, X s) ∈ (allVars (E.map (Eqn.subst θ))).toFinset :=
        hsub (List.mem_toFinset.2 (List.mem_flatMap.2 ⟨_, List.mem_cons_self, by simp [Eqn.vars]⟩))
      simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map] at hm
      obtain ⟨_, ⟨e', _, rfl⟩, hy⟩ := hm
      obtain ⟨z, _, h'⟩ := Eqn.mem_vars_subst θ e' hy
      by_cases e : (⟨z.1, z.2⟩ : Σ s, X s) = ⟨s, x⟩
      · have hzx : z = ⟨s, x⟩ := e
        subst hzx
        exact hx (by simpa [θ] using h')
      · have : θ z.1 z.2 = .var z.2 := sUpdate_ne _ _ _ e
        rw [this] at h'
        simp only [Term.vars_var, List.mem_singleton] at h'
        exact e h'.symm
  obtain ⟨Y₀, τ₀, hτ₀⟩ := hu
  obtain ⟨μ', hμ'⟩ := IH _ hcard ⟨Y₀, τ₀, hE' τ₀ hτ₀⟩
  refine ⟨comp μ' θ, holds_cons.2 ⟨?_, fun e he => ?_⟩, fun Y τ hτ => ?_⟩
  · change subst μ' (θ s x) = subst (comp μ' θ) v
    rw [← subst_subst, hθv]
    simp [θ]
  · exact (Eqn.holds_subst μ' θ e).1 (hμ'.1 _ (List.mem_map.2 ⟨e, he, rfl⟩))
  · obtain ⟨ρ, hρ⟩ := hμ'.2 Y τ (hE' τ hτ)
    have hc : comp ρ μ' = τ := by
      funext s' y
      exact hρ s' y
    refine ⟨ρ, fun s' y => ?_⟩
    have hk := congrFun (congrFun (key τ (hhead τ (holds_cons.1 hτ).1)) s') y
    change subst ρ (subst μ' (θ s' y)) = τ s' y
    rw [subst_subst, hc]
    exact hk

/-- A variable against anything else: eliminate it, or the occurs check fails. -/
private theorem var_case {s : S.Srt} (x : X s) (v : Term S X s) (E : List (Eqn X))
    (hne : v ≠ .var x)
    (IH : ∀ E' : List (Eqn X), card E' < card (.t (.var x) v :: E) → Solvable E' → ∃ μ, IsMgu μ E')
    (hu : Solvable (.t (.var x) v :: E)) : ∃ μ, IsMgu μ (.t (.var x) v :: E) := by
  by_cases hx : (⟨s, x⟩ : Σ s, X s) ∈ Term.vars v
  · exfalso
    obtain ⟨Y, τ, hτ⟩ := hu
    have h : τ s x = subst τ v := (holds_cons.1 hτ).1
    cases v with
    | var y =>
      simp only [Term.vars_var, List.mem_singleton] at hx
      have := eq_of_heq (Sigma.mk.inj hx).2
      exact hne (by rw [this])
    | op f a =>
      have hle := args_size_le τ a (y := ⟨s, x⟩) (by simpa using hx)
      have hs := congrArg Term.size h
      simp only [subst_op, Term.size] at hs
      simp only at hle
      omega
  · exact elim_case x v E hx IH hu

private theorem holds_flip {s : S.Srt} (u v : Term S X s) (E : List (Eqn X)) {Y : VarSet S}
    (τ : Subst S X Y) : Holds τ (.t u v :: E) ↔ Holds τ (.t v u :: E) := by
  simp only [holds_cons, Eqn.holds, eq_comm]

private theorem exists_mgu_aux : ∀ (n k : ℕ) (E : List (Eqn X)), card E = n → total E = k →
    Solvable E → ∃ μ, IsMgu μ E := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IHk =>
  intro E hn hk hu
  have IHv : ∀ E', card E' < n → Solvable E' → ∃ μ, IsMgu μ E' := fun E' h s =>
    IHn _ h _ E' rfl rfl s
  have IHs : ∀ E' : List (Eqn X), card E' ≤ n → total E' < k → Solvable E' → ∃ μ, IsMgu μ E' := by
    intro E' hc ht s
    rcases Nat.lt_or_eq_of_le hc with h | h
    · exact IHv E' h s
    · exact IHk _ ht E' h rfl s
  /- A reduction to an equivalent system of smaller size. -/
  have reduce : ∀ E' : List (Eqn X), (∀ y ∈ allVars E', y ∈ allVars E) → total E' < k →
      (∀ (Y : VarSet S) (τ : Subst S X Y), Holds τ E' ↔ Holds τ E) → ∃ μ, IsMgu μ E := by
    intro E' hv ht hiff
    obtain ⟨μ, hμ⟩ := IHs E' (hn ▸ card_le hv) ht (solvable_of_iff hiff hu)
    exact ⟨μ, mgu_of_iff hiff hμ⟩
  subst hn
  match E, hk, hu, reduce, IHv with
  | [], _, _, _, _ =>
    exact ⟨fun _ x => .var x, by simp [Holds], fun Y τ _ => ⟨τ, fun _ _ => rfl⟩⟩
  | .a .nil .nil :: E, hk, _, reduce, _ =>
    refine reduce E (fun y hy => ?_) (by simp [total, Eqn.size, Args.size] at hk ⊢; omega) (fun Y τ => ?_)
    · simp only [List.flatMap_cons, List.mem_append]
      exact Or.inr hy
    · simp [holds_cons, Eqn.holds]
  | .a (.cons t ts) (.cons t' ts') :: E, hk, _, reduce, _ =>
    refine reduce (.t t t' :: .a ts ts' :: E) (fun y hy => ?_)
      (by simp [total, Eqn.size, Args.size] at hk ⊢; omega) (fun Y τ => ?_)
    · simp only [List.flatMap_cons, List.mem_append, Eqn.vars, Args.vars_cons] at hy ⊢
      tauto
    · simp only [holds_cons, Eqn.holds, Args.subst_cons, Args.cons.injEq]
      tauto
  | .t (.var x) (.var y) :: E, hk, hu, reduce, IHv =>
    by_cases e : y = x
    · subst e
      refine reduce E (fun z hz => ?_) (by simp [total, Eqn.size, Term.size] at hk ⊢; omega) (fun Y τ => ?_)
      · simp only [List.flatMap_cons, List.mem_append]
        exact Or.inr hz
      · simp [holds_cons, Eqn.holds]
    · exact var_case x _ E (fun h => e (Term.var.inj h)) IHv hu
  | .t (.var x) (.op f a) :: E, _, hu, _, IHv =>
    exact var_case x _ E (fun h => by cases h) IHv hu
  | .t (.op f a) (.var x) :: E, _, hu, _, IHv =>
    have hiff := fun (Y : VarSet S) (τ : Subst S X Y) => holds_flip (Term.op f a) (.var x) E τ
    obtain ⟨μ, hμ⟩ := var_case x (.op f a) E (fun h => by cases h)
      (fun E' hc s => IHv E' (lt_of_lt_of_le hc (card_le fun y hy => by
        simp only [List.flatMap_cons, List.mem_append, Eqn.vars] at hy ⊢
        tauto)) s)
      (solvable_of_iff (E := .t (.op f a) (.var x) :: E) (fun Y τ => (hiff Y τ).symm) hu)
    exact ⟨μ, mgu_of_iff (fun Y τ => (hiff Y τ).symm) hμ⟩
  | @List.cons _ (@Eqn.t _ _ s (@Term.op _ _ ss _ f a) (@Term.op _ _ ss' _ g b)) E, hk, hu, reduce, _ =>
    obtain ⟨Y₀, τ₀, hτ₀⟩ := hu
    have h₀ : Term.op f (Args.subst τ₀ a) = Term.op g (Args.subst τ₀ b) := (holds_cons.1 hτ₀).1
    obtain ⟨rfl, hfg, -⟩ := Term.op.inj h₀
    obtain rfl := eq_of_heq hfg
    refine reduce (.a a b :: E) (fun y hy => ?_) (by simp [total, Eqn.size, Term.size] at hk ⊢; omega)
      (fun Y τ => ?_)
    · simp only [List.flatMap_cons, List.mem_append, Eqn.vars, Term.vars_op] at hy ⊢
      tauto
    · simp only [holds_cons, Eqn.holds, subst_op, Term.op.injEq, heq_eq_eq, true_and]

/-- **The unification theorem.** -/
public theorem unificationTheorem (S : Signature) : UnificationTheorem S := by
  intro X Y s u v τ h
  obtain ⟨μ, h₁, h₂⟩ := exists_mgu_aux _ _ [.t u v] rfl rfl ⟨Y, τ, by simpa [Holds, Eqn.holds, Unifies] using h⟩
  exact ⟨μ, by simpa [Holds, Eqn.holds, Unifies] using h₁, fun Y τ hτ =>
    h₂ Y τ (by simpa [Holds, Eqn.holds, Unifies] using hτ)⟩

end MercLib.Rewriting
