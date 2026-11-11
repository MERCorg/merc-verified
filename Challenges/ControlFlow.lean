import MercLib.Theory.ControlFlow.ControlFlow
import MercLib.Theory.ControlFlow.LinearProcess

/-!
# Comparator challenge: control flow graphs (human-vetted)

The headline theorems of `MercLib/Theory/ControlFlow/`, stated with `sorry` against the human-vetted
spec files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.ControlFlow

/-! ## Pruning with control flow graphs -/

/-- **Pruning is sound (Lemma 2 of [Keiren2014], with its assumptions made explicit).** Let `s k` be
the source of the PVI at position `i` of `φ` for the control flow parameter `c k` where defined, so
that `φ` is equivalent to `φ` with that PVI guarded by `c k = s k`, and let no quantifier of `φ` bind a
control flow parameter. In every data environment in which some control flow parameter does not have
the value of its source, `φ` is equivalent to `φ` with the PVI replaced by `false`. See
`PruningSound` (`Theory/ControlFlow/ControlFlow.lean`). -/
theorem pruningSound {L : DataLanguage} {P : Type} {m : ℕ} (φ : Formula L P) (i : ℕ)
    (c : Fin m → L.Var) (s : Fin m → Option L.Term) : PruningSound φ i c s := sorry

/-- **Pruning with syntactic edges is sound for distinct values.** Under the assumptions of
`pruningSound`, if the data environment gives every control flow parameter `c k` the value of the
term `v k`, and every source with the value of `v k` is the term `v k`, then a PVI whose source differs
from `v` as a term can be replaced by `false`. See `SyntacticPruningSound`
(`Theory/ControlFlow/ControlFlow.lean`). -/
theorem syntacticPruningSound {L : DataLanguage} {P : Type} {m : ℕ} (φ : Formula L P) (i : ℕ)
    (c : Fin m → L.Var) (s : Fin m → Option L.Term) (v : Fin m → L.Term) :
    SyntacticPruningSound φ i c s v := sorry

/-- **Pruning with syntactic edges is unsound for equal values.** There is a formula with a PVI
whose source for a parameter `d` that no quantifier binds is `e`, and a ground term `v` other than `e`
with the same value, such that in an environment in which `d` has the value of `v`, replacing the PVI
by `false` changes the truth of the formula. See `SyntacticPruningUnsound`
(`Theory/ControlFlow/ControlFlow.lean`). -/
theorem syntacticPruningUnsound : SyntacticPruningUnsound := sorry

/-- **Pruning is unsound when a quantifier binds a control flow parameter.** There is a formula in
which no bound variable also occurs free, with a PVI whose source for `d` is `e`, such that in an
environment in which `d` does not have the value of `e`, replacing the PVI by `false` changes the
truth of the formula. See `ShadowedPruningUnsound` (`Theory/ControlFlow/ControlFlow.lean`). -/
theorem shadowedPruningUnsound : ShadowedPruningUnsound := sorry

end MercLib.ControlFlow

namespace MercLib.ControlFlow.Lpe

/-! ## Control flow graphs of linear processes -/

/-- **Proposition 1 of [vandePol2009].** If `source` and `destination` are a source and a
destination function, parameter `j` rules summand `i`, and `i` is enabled in state `v` for the local
variables `e`, then the control flow graph of `j` has the edge `(v j, i, t)` with `t` the value of
`j` in the next state. See `Proposition1` (`Theory/ControlFlow/LinearProcess.lean`). -/
theorem proposition1 {J I E Val : Type} (L : LinearProcess J I E Val)
    (source destination : I → J → Option Val) : Proposition1 L source destination := sorry

/-- **Decided locations are values.** If `decide` is a sound procedure for the equality of terms and
decides every two terms of `locations`, then on `locations` it decides two terms equal exactly when
they have the same value. See `DecidedLocationsAreValues` (`Theory/ControlFlow/LinearProcess.lean`). -/
theorem decidedLocationsAreValues {Val Term : Type} (eval : Term → Val)
    (decide : Term → Term → Option Bool) (locations : Set Term) :
    DecidedLocationsAreValues eval decide locations := sorry

/-- **Pruning by locations is sound.** Let the values of the terms `source` be a source function,
and let `decide` be a sound procedure for the equality of terms that decides every two terms of
`locations`. If parameter `j` has the value of the location term `l` in state `v`, and the source
term `s` of summand `i` for `j` is a location term that `decide` does not decide equal to `l`, then
`i` is not enabled in `v`. See `LocationPruningSound` (`Theory/ControlFlow/LinearProcess.lean`). -/
theorem locationPruningSound {J I E Val Term : Type} (L : LinearProcess J I E Val)
    (eval : Term → Val) (decide : Term → Term → Option Bool) (locations : Set Term)
    (source : I → J → Option Term) : LocationPruningSound L eval decide locations source := sorry

end MercLib.ControlFlow.Lpe
