import MercLib.Algorithms.Rewriting.SetAutomaton
import MercLib.Theory.Rewriting.Confluence
import MercLib.Theory.Rewriting.Matching
import MercLib.Theory.Rewriting.Unification
import MercLib.Theory.Rewriting.Rewrite
import MercLib.Theory.Rewriting.SetAutomaton
import MercLib.Theory.Rewriting.SetAutomatonPartition
import MercLib.Theory.Rewriting.Signature
import MercLib.Theory.Rewriting.Termination

/-!
# Comparator challenge: conditional term rewriting (human-vetted)

The headline theorems of `MercLib/Theory/Rewriting/`, stated with `sorry` against the human-vetted spec
files only; `lake comparator` checks them against the solution module `MercLib` (see
`Challenges.Refinement`). Intermediate lemmas are not challenged.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

namespace MercLib.Rewriting

/-! ## Termination -/

/-- **Termination by a measure.** If a measure `μ` on terms into a well-founded order `lt`
strictly decreases with every rewrite step of `R`, then `R` is terminating on terms over the
variables `W`. -/
theorem terminating_of_measure {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {γ : Type*} (lt : γ → γ → Prop) (hwf : WellFounded lt)
    (μ : (s : S.Srt) → Term S W s → γ)
    (hdec : ∀ {s : S.Srt} {a b : Term S W s}, Step R s a b → lt (μ s b) (μ s a)) :
    Terminating R W := sorry

/-- **Termination by a monotone interpretation.** If every rule of `R` strictly decreases under
every valuation in a monotone interpretation `M` (`Decreasing`; conditions are ignored), and `W`
has a valuation `ν` in `M`, then `R` is terminating on terms over `W`. -/
theorem terminating_of_interpretation {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} {M : MonotoneInterpretation S} (hD : Decreasing R M) (ν : Valuation M W) :
    Terminating R W := sorry

/-! ## Confluence -/

/-- **Newman's lemma.** A rewrite system that is terminating and locally confluent on the terms
over `W` is confluent on those terms. -/
theorem confluent_of_locallyConfluent {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} (ht : Terminating R W) (hl : LocallyConfluent R W) : Confluent R W := sorry

/-- **Unique normal forms.** In a rewrite system that is terminating and confluent on the terms over
`W`, every term `t` has exactly one normal form `u` with `t →* u`. -/
theorem existsUnique_normalForm {S : Signature} {V W : VarSet S} {ι : Type}
    {R : TRS S V ι} (ht : Terminating R W) (hc : Confluent R W) {s : S.Srt} (t : Term S W s) :
    ∃! u, Steps R s t u ∧ Normal R u := sorry

/-! ## Matching, unification and critical pairs -/

/-- **Matching a linear pattern is a condition on head symbols.** For a linear pattern `l` and a term
`t` of the same sort, `l` matches `t` exactly when `t` has the head symbols of `l` at the
non-variable positions of `l`, provided every sort with a variable in `V` has a term over `W`. See
`LinearMatchIffHeads` (`Theory/Rewriting/Matching.lean`). -/
theorem linearMatchIffHeads (S : Signature) (V W : VarSet S) : LinearMatchIffHeads S V W := sorry

/-- **The unification theorem.** Two terms with a unifier have a most general unifier. See
`UnificationTheorem` (`Theory/Rewriting/Unification.lean`). -/
theorem unificationTheorem (S : Signature) : UnificationTheorem S := sorry

/-- **The critical pair lemma.** An unconditional rewrite system whose critical pairs are joinable
is locally confluent on the terms over every variable family, and a system that is locally confluent
on the terms over `Both V` has joinable critical pairs. See `CriticalPairLemma`
(`Theory/Rewriting/Confluence.lean`). -/
theorem criticalPairLemma {S : Signature} {V : VarSet S} {ι : Type} (R : TRS S V ι) :
    CriticalPairLemma R := sorry

end MercLib.Rewriting

namespace MercLib.SetAutomaton

/-! ## The set automaton -/

/-- **Correctness of the set automaton (Theorem 1 of [Erkens2021]).** Let `Ls` be a non-empty set of
patterns other than `ω` that respect the arities `ar`, and `L` an admissible state labelling
(`Admissible`). For every closed term `t` respecting the arities, the matches announced along the
evaluation tree of `t` are exactly the pairs `ℓ@p` with `ℓ ∈ Ls` and `p ∈ D(t)` such that `ℓ` matches
`t` at `p`. See `Correct` (`Theory/Rewriting/SetAutomaton.lean`). -/
theorem setAutomatonCorrect {F : Type} [DecidableEq F] (ar : F → ℕ) (Ls : Finset (Pat F))
    (L : State F → Position) : Correct ar Ls L := sorry

/-- **Every position is inspected exactly once (Corollary 4 of [Erkens2021]).** Under the
assumptions of `setAutomatonCorrect`, the map sending a node `(s, p)` of the evaluation tree of `t`
to the inspected position `p.L(s)` is a bijection from the nodes onto `D(t)`. See `InspectsOnce`
(`Theory/Rewriting/SetAutomaton.lean`). -/
theorem setAutomatonInspectsOnce {F : Type} [DecidableEq F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position) : InspectsOnce ar Ls L := sorry

/-- **Finitely many states (Corollary 2 of [Erkens2021]).** Over a finite alphabet, for patterns
other than `ω` that respect the arities and an admissible state labelling, the automaton has finitely
many reachable states. See `FinitelyManyStates` (`Theory/Rewriting/SetAutomaton.lean`). -/
theorem setAutomatonFinite {F : Type} [DecidableEq F] [Finite F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position) : FinitelyManyStates ar Ls L := sorry

/-- **The three theorems hold for every admissible partition.** If `R` partitions each derivative
into classes that are unions of dependency classes, by a symmetric relation that relates only goals
which depend or announce at comparable positions, then Theorem 1, Corollary 4 and Corollary 2 hold
for the automaton built with the classes of `R`, for every admissible state labelling. See
`PartitionTheorems` (`Theory/Rewriting/SetAutomatonPartition.lean`). -/
theorem partitionTheorems {F : Type} [DecidableEq F]
    (R : Position → F → Goal F → Goal F → Prop) [∀ l f, DecidableRel (R l f)] (ar : F → ℕ)
    (Ls : Finset (Pat F)) : PartitionTheorems R ar Ls := sorry

/-- **merc's partition is admissible.** Grouping the goals that are not fresh also by comparable
announcement positions satisfies the conditions of `PartitionTheorems`, so the set automaton with
merc's partition is correct, inspects every position once and has finitely many states. See
`MercPartitionAdmissible` (`Theory/Rewriting/SetAutomatonPartition.lean`). -/
theorem mercPartitionAdmissible {F : Type} [DecidableEq F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) : MercPartitionAdmissible ar Ls := sorry

/-- **The construction is correct.** Over a finite alphabet, for patterns other than `ω` that respect
the arities and an admissible state labelling, `construct` terminates, its states are exactly the
reachable states, and its tables are exactly `δ` and `η` on them. See `ConstructCorrect`
(`Algorithms/Rewriting/SetAutomaton.lean`). -/
theorem constructCorrect {F : Type} [DecidableEq F] [Fintype F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position) : ConstructCorrect ar Ls L := sorry

/-- **Matching is correct and inspects every position once.** Under the assumptions of
`setAutomatonCorrect` and for every `pick` that selects a non-empty subset of a non-empty work set,
`findMatches` on the constructed automaton terminates, returns exactly the matches of the patterns
in `t`, and the multiset of positions it inspects is `D(t)`. See `FindMatchesCorrect`
(`Algorithms/Rewriting/SetAutomaton.lean`). -/
theorem findMatchesCorrect {F : Type} [DecidableEq F] [Fintype F] (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position)
    (pick : Finset (Config F) → Finset (Config F)) : FindMatchesCorrect ar Ls L pick := sorry

end MercLib.SetAutomaton
