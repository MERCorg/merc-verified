import MercLib.Theory.Pbes.SymmetryDetection

/-!
# Comparator challenge: symmetry detection for PBESs (human-vetted)

The headline theorems of `MercLib/Theory/Pbes/`, stated with `sorry` against the human-vetted
spec file only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`).

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Symmetry

variable {F P : Type} {n : ℕ}

/-! ## The directed SDG -/

/-- **Automorphisms restrict to parameter permutations.** For every automorphism `h` of the
directed SDG of `E` there is a permutation `π` of the parameters with `h(d_k) = d_{π(k)}` for
every `k`. See `RestrictionExists` (`Theory/Pbes/SymmetryDetection.lean`). -/
theorem restrictionExists (comm : F → Prop) (E : Pbes F P n) : RestrictionExists comm E := sorry

/-- **Automorphisms fix right-hand sides (Lemma 1).** If `E` is well-formed (one equation per
predicate variable, and one argument per parameter in every PVI), then every automorphism of the
directed SDG of `E` maps the vertex of every right-hand side `φ_X` to itself. See `RhsFixed`
(`Theory/Pbes/SymmetryDetection.lean`). -/
theorem rhsFixed (comm : F → Prop) (E : Pbes F P n) : RhsFixed comm E := sorry

/-- **Automorphisms preserve size (Lemma 2).** If `E` is well-formed, then every automorphism of
the directed SDG of `E` maps every subformula and parameter `φ` to a formula `ψ` with
`|ψ| = |φ|`. See `SizePreserved` (`Theory/Pbes/SymmetryDetection.lean`). -/
theorem sizePreserved (comm : F → Prop) (E : Pbes F P n) : SizePreserved comm E := sorry

section Semantics

variable {D : Type} [Inhabited D] (I : F → List D → D) (T : D → Prop)

/-- **Automorphisms act as their restriction (Lemma 3).** If every symbol in `comm` is
interpreted by a commutative binary function, `E` is well-formed, `h` is an automorphism of the
directed SDG of `E` and `π = h|pars(E)`, then `h` maps every subformula and parameter `φ` to a
formula `ψ` that has the same value as `π(φ)` and holds in the same environments. See
`AgreesWithAct` (`Theory/Pbes/SymmetryDetection.lean`). -/
theorem agreesWithAct (comm : F → Prop) (E : Pbes F P n) : AgreesWithAct I T comm E := sorry

/-- **SDG automorphisms give symmetries (Theorem 2).** If every symbol in `comm` is interpreted
by a commutative binary function, `E` is well-formed, `h` is an automorphism of the directed SDG
of `E` with role-coloured update arcs, and `π = h|pars(E)`, then `π` is a symmetry of `E`:
`π(φ_X) ≡ φ_X` for every equation. See `SymmetryFromAutomorphism`
(`Theory/Pbes/SymmetryDetection.lean`). -/
theorem symmetryFromAutomorphism (comm : F → Prop) (E : Pbes F P n) :
    SymmetryFromAutomorphism I T comm E := sorry

end Semantics

/-! ## The paper's SDG -/

/-- **The undirected SDG is unsound.** There is a well-formed PBES with three Boolean parameters
and an automorphism of its undirected SDG whose restriction to the parameters is not a symmetry.
See `UndirectedUnsound` (`Theory/Pbes/SymmetryDetection.lean`). -/
theorem undirectedUnsound : UndirectedUnsound := sorry

/-- **Uncoloured update arcs are unsound.** There is a well-formed PBES with three Boolean
parameters and an automorphism of its directed SDG, with the paper's uncoloured update arcs,
whose restriction to the parameters is not a symmetry. See `UncolouredUpdatesUnsound`
(`Theory/Pbes/SymmetryDetection.lean`). -/
theorem uncolouredUpdatesUnsound : UncolouredUpdatesUnsound := sorry

end MercLib.Symmetry
