module

public import Init.Internal.Order.While

@[expose] public section

namespace MercLib.Util

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Reasoning about `while` loops in `Id.run do` blocks. A `while` loop elaborates to
`forIn Lean.Loop.mk init f` for a loop body `f : Unit → σ → Id (ForInStep σ)`. `whileInduction`
proves a property of the final state from an invariant that every non-final step preserves and a
well-founded relation that every non-final step decreases. It rests on the one-step unfolding
lemma `Lean.Loop.forIn_eq_of_monadTail` of `Init.Internal.Order.While`. `forInList_induction` is
the analogue for `for x in l do` loops over a list, which always terminate. -/

/-- One-step unfolding of a loop in `Id`. -/
private theorem loop_unfold {σ : Type u} (f : Unit → σ → Id (ForInStep σ)) (s : σ) :
    forIn Lean.Loop.mk s f = (match f () s with
      | .done s' => pure s'
      | .yield s' => forIn Lean.Loop.mk s' f : Id σ) := by
  change Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

/-- **Loop induction.** If every step from an `Inv`-state either finishes in a `P`-state or
    continues in an `Inv`-state that is `r`-smaller, then the loop ends in a `P`-state. -/
private theorem whileInduction {σ : Type u} (f : Unit → σ → Id (ForInStep σ)) {r : σ → σ → Prop}
    (hwf : WellFounded r) (Inv P : σ → Prop)
    (hstep : ∀ s, Inv s → match (f () s).run with
      | .done s' => P s'
      | .yield s' => Inv s' ∧ r s' s) :
    ∀ s, Inv s → P (forIn Lean.Loop.mk s f).run := by
  intro s
  induction s using hwf.induction with
  | _ s ih =>
    intro hs
    rw [loop_unfold]
    have h := hstep s hs
    revert h
    cases f () s with
    | done s' => exact id
    | yield s' => exact fun ⟨hi, hr⟩ => ih s' hr hi

/-- **List loop induction.** If every step preserves `Inv`, whether it continues or breaks, then a
    `for` loop over a list ends in an `Inv`-state. -/
private theorem forInList_induction {α : Type v} {σ : Type u} (f : α → σ → Id (ForInStep σ))
    (Inv : σ → Prop) (hstep : ∀ a s, Inv s → Inv (f a s).run.value) :
    ∀ (l : List α) (s : σ), Inv s → Inv (forIn l s f).run
  | [], _, hs => hs
  | a :: l, s, hs => by
    rw [List.forIn_cons]
    have h := hstep a s hs
    revert h
    cases f a s with
    | done s' => exact id
    | yield s' => exact fun h => forInList_induction f Inv hstep l s' h

/-- **Per-element loop induction.** For a `for x in l do` loop whose body never breaks: if every
    step preserves `Inv` and is related to its input by `Ext`, the step for `a` establishes `Q a`,
    and `Q a` is preserved along `Ext`, then the final state satisfies `Q a` for every `a ∈ l`. -/
private theorem forInList_mem_induction {α : Type v} {σ : Type u} (f : α → σ → Id (ForInStep σ))
    (Inv : σ → Prop) (Ext : σ → σ → Prop) (Q : α → σ → Prop)
    (hy : ∀ a s, (f a s).run = .yield (f a s).run.value)
    (hstep : ∀ a s, Inv s → Inv (f a s).run.value ∧ Ext s (f a s).run.value)
    (hQ : ∀ a s, Inv s → Q a (f a s).run.value)
    (hpres : ∀ a s s', Q a s → Ext s s' → Q a s') :
    ∀ (l : List α) (s : σ), Inv s → (∀ a, Q a s → Q a (forIn l s f).run) ∧
      ∀ a ∈ l, Q a (forIn l s f).run
  | [], _, _ => ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | b :: l, s, hs => by
    rw [List.forIn_cons]
    have hyb := hy b s
    revert hyb
    generalize hfb : f b s = st
    intro hyb
    have hinv : Inv st.run.value := hfb ▸ (hstep b s hs).1
    have hQb : Q b st.run.value := hfb ▸ hQ b s hs
    have hpb : ∀ a, Q a s → Q a st.run.value := fun a h => hpres a s _ h (hfb ▸ (hstep b s hs).2)
    change ForInStep σ at st
    change st = _ at hyb
    rw [hyb]
    obtain ⟨ih1, ih2⟩ := forInList_mem_induction f Inv Ext Q hy hstep hQ hpres l _ hinv
    refine ⟨fun a h => ih1 a (hpb a h), fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ih1 a hQb
    · exact ih2 a ha

end MercLib.Util
