module

public import MercLib.Theory.ControlFlow.ControlFlow

@[expose] public section

/-!
# Proofs: Control flow graphs

`pruningSound` and `syntacticPruningSound`, from a congruence lemma for `Formula.replace` under a
variable that the formula does not bind, and the two counterexamples `syntacticPruningUnsound` and
`shadowedPruningUnsound`, over a data language with a single variable.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/ControlFlow.lean` (human-vetted); the definitions live in
`MercLib/Theory/ControlFlow/ControlFlow.lean`.
-/

namespace MercLib.ControlFlow

variable {L : DataLanguage} {P : Type}

/-- Replacing a PVI by either of two formulae that agree wherever `d` has the value `a` gives
equivalent formulae, when `d` has the value `a` and no quantifier binds `d`. -/
private theorem replace_congr (η : P → List L.Val → Prop) (d : L.Var) (a : L.Val)
    (ψ₁ ψ₂ : Formula L P) (h : ∀ δ : L.Var → L.Val, δ d = a → (ψ₁.eval η δ ↔ ψ₂.eval η δ)) :
    ∀ (φ : Formula L P) (i : ℕ) (δ : L.Var → L.Val), ¬ φ.Binds d → δ d = a →
      ((φ.replace i ψ₁).eval η δ ↔ (φ.replace i ψ₂).eval η δ) := by
  intro φ
  induction φ with
  | data b => intro i δ _ _; exact Iff.rfl
  | pvi X e =>
    intro i δ _ hd
    by_cases hi : i = 0
    · simp only [Formula.replace, hi, ↓reduceIte]; exact h δ hd
    · simp only [Formula.replace, hi, ↓reduceIte]
  | and φ₁ φ₂ ih₁ ih₂ =>
    intro i δ hb hd
    simp only [Formula.Binds, not_or] at hb
    by_cases hi : i < φ₁.npred
    · simp only [Formula.replace, hi, ↓reduceIte, Formula.eval, ih₁ i δ hb.1 hd]
    · simp only [Formula.replace, hi, ↓reduceIte, Formula.eval, ih₂ _ δ hb.2 hd]
  | or φ₁ φ₂ ih₁ ih₂ =>
    intro i δ hb hd
    simp only [Formula.Binds, not_or] at hb
    by_cases hi : i < φ₁.npred
    · simp only [Formula.replace, hi, ↓reduceIte, Formula.eval, ih₁ i δ hb.1 hd]
    · simp only [Formula.replace, hi, ↓reduceIte, Formula.eval, ih₂ _ δ hb.2 hd]
  | all x φ ih =>
    intro i δ hb hd
    simp only [Formula.Binds, not_or] at hb
    simp only [Formula.replace, Formula.eval]
    refine forall_congr' fun v => ih i _ hb.2 ?_
    rw [Function.update_of_ne (fun h => hb.1 h.symm)]; exact hd
  | ex x φ ih =>
    intro i δ hb hd
    simp only [Formula.Binds, not_or] at hb
    simp only [Formula.replace, Formula.eval]
    refine exists_congr fun v => ih i _ hb.2 ?_
    rw [Function.update_of_ne (fun h => hb.1 h.symm)]; exact hd

/-- **Pruning is sound.** -/
public theorem pruningSound {m : ℕ} (φ : Formula L P) (i : ℕ) (c : Fin m → L.Var)
    (s : Fin m → Option L.Term) : PruningSound φ i c s := by
  intro hs hb η δ hne
  simp only [SemanticEdge, not_forall] at hne
  obtain ⟨k, e, hk, hv⟩ := hne
  obtain ⟨hg, χ, -, hsrc⟩ := hs k e hk
  rw [hsrc η δ]
  refine replace_congr η (c k) (δ (c k)) _ _ (fun δ' hd' => ?_) φ i δ (hb k) rfl
  simp only [Formula.eval, L.holds_eq, L.eval_var, hd']
  refine ⟨fun h => absurd (h.1.trans (L.eval_ground e hg δ' δ)) hv, fun h => absurd h (L.holds_ff δ')⟩

/-- **Pruning with syntactic edges is sound for distinct values.** -/
public theorem syntacticPruningSound {m : ℕ} (φ : Formula L P) (i : ℕ) (c : Fin m → L.Var)
    (s : Fin m → Option L.Term) (v : Fin m → L.Term) : SyntacticPruningSound φ i c s v := by
  intro hs hb η δ hv hinj hne
  refine pruningSound φ i c s hs hb η δ fun hedge => hne fun k e hk => ?_
  exact hinj k e hk ((hedge k e hk).symm.trans (hv k))

/-- Terms of the data language of the counterexamples: the single variable, the literals, equality
and `false`. -/
private inductive T where
  | var
  | lit (b : Bool)
  | eq (x y : T)
  | ff

/-- The variable occurs in the term. -/
private def T.HasVar : T → Prop
  | .var => True
  | .lit _ => False
  | .eq x y => x.HasVar ∨ y.HasVar
  | .ff => False

/-- The value of a term, where the literals have the values `lit` and the boolean terms an arbitrary
one. -/
private def T.eval {V : Type} (lit : Bool → V) (δ : Unit → V) : T → V
  | .var => δ ()
  | .lit b => lit b
  | .eq _ _ => lit false
  | .ff => lit false

/-- The data language of the counterexamples, with a single variable and values in `V`. -/
private def lang (V : Type) (lit : Bool → V) : DataLanguage where
  Var := Unit
  Term := T
  Val := V
  decEqVar := inferInstance
  eval δ t := t.eval lit δ
  Holds δ t := match t with
    | .eq x y => x.eval lit δ = y.eval lit δ
    | _ => False
  var _ := .var
  eq := .eq
  ff := .ff
  Occurs _ t := t.HasVar
  Ground t := ¬ t.HasVar
  eval_var _ _ := rfl
  holds_eq _ _ _ := Iff.rfl
  holds_ff _ h := h
  eval_ground t ht δ δ' := by
    cases t with
    | var => exact absurd trivial ht
    | lit b => rfl
    | eq x y => rfl
    | ff => rfl

/-- **Pruning with syntactic edges is unsound for equal values.** -/
public theorem syntacticPruningUnsound : SyntacticPruningUnsound := by
  refine ⟨lang Unit (fun _ => ()), Unit, .pvi () [], 0, (), T.lit true, T.lit false,
    fun _ _ => True, fun _ => (), ⟨?_, .pvi () [], rfl, fun η δ => ?_⟩, ?_, ?_, rfl, ?_, ?_⟩
  · exact id
  · simp only [Formula.replace, ↓reduceIte, Formula.eval]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  · exact id
  · exact id
  · intro h; cases h
  · simp only [Formula.replace, ↓reduceIte, Formula.eval]
    exact fun h => h.1 trivial

/-- **Pruning is unsound when a quantifier binds a control flow parameter.** -/
public theorem shadowedPruningUnsound : ShadowedPruningUnsound := by
  refine ⟨lang Bool id, Unit, .ex () (.pvi () []), 0, (), T.lit true, fun _ _ => True,
    fun _ => false, ⟨id, .pvi () [], rfl, fun η δ => ?_⟩, ?_, ?_, ?_⟩
  · simp only [Formula.replace, ↓reduceIte, Formula.eval]
    refine ⟨fun ⟨_, h⟩ => ⟨true, ?_, h⟩, fun ⟨v, _, h⟩ => ⟨v, h⟩⟩
    exact Function.update_self (f := δ) (a := ()) true
  · intro d _ hfree
    exact hfree.1 rfl
  · intro h; cases h
  · simp only [Formula.replace, ↓reduceIte, Formula.eval]
    exact fun h => (h.1 ⟨false, trivial⟩).elim fun _ h => h

end MercLib.ControlFlow
