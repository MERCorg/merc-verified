module

public import MercLib.Theory.ControlFlow.LinearProcess

@[expose] public section

/-!
# Proofs: Control flow graphs of linear processes

`proposition1`, `decidedLocationsAreValues` and `locationPruningSound`.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/ControlFlow.lean` (human-vetted); the definitions live in
`MercLib/Theory/ControlFlow/LinearProcess.lean`.
-/

namespace MercLib.ControlFlow.Lpe

variable {J I E Val : Type}

/-- **Proposition 1 of [vandePol2009].** -/
public theorem proposition1 (L : LinearProcess J I E Val) (source destination : I → J → Option Val) :
    Proposition1 L source destination := by
  intro hs hd i j v e hr hen
  obtain ⟨hsrc, hdst⟩ := hr
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.mp hsrc
  obtain ⟨t, ht'⟩ := Option.isSome_iff_exists.mp hdst
  refine ⟨?_, ?_⟩
  · rw [hs', hs i j s hs' v e hen]
  · rw [ht', hd i j t ht' v e hen]

/-- **Decided locations are values.** -/
public theorem decidedLocationsAreValues {Term : Type} (eval : Term → Val)
    (decide : Term → Term → Option Bool) (locations : Set Term) :
    DecidedLocationsAreValues eval decide locations := by
  intro hsound hdec a ha b hb
  refine ⟨(hsound a b).1, fun heq => ?_⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hdec a ha b hb)
  cases r with
  | true => exact hr
  | false => exact absurd heq ((hsound a b).2 hr)

/-- **Pruning by locations is sound.** -/
public theorem locationPruningSound {Term : Type} (L : LinearProcess J I E Val) (eval : Term → Val)
    (decide : Term → Term → Option Bool) (locations : Set Term) (source : I → J → Option Term) :
    LocationPruningSound L eval decide locations source := by
  intro hs hsound hdec i j v e l s hl hsl hv hsrc hne hen
  have hsv : v j = eval s := hs i j (eval s) (by simp [hsrc]) v e hen
  exact hne ((decidedLocationsAreValues eval decide locations hsound hdec l hl s hsl).2
    (hv.symm.trans hsv))

end MercLib.ControlFlow.Lpe
