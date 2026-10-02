module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Cslib.Foundations.Semantics.LTS.Divergence

open Cslib (LTS HasTau)

@[expose] public section Semantics

/-!
# Weak traces, refusals, failures and divergences

Section 2 of M. Laveaux, J. F. Groote, T. A. C. Willemse, *Correct and Efficient Antichain
Algorithms for Refinement Checking*, LMCS 17(1:8), 2021.

`Label` plays the role of the paper's `Actτ = Act ∪ {τ}`: visible actions are exactly the
`μ : Label` with `μ ≠ HasTau.τ`. Weak transitions and weak traces are built on top of
`Cslib.LTS.saturate`/`STr` (the saturated/weak single-label step) rather than redefined, and
divergence reuses `Cslib.LTS.Divergent` (an infinite τ-sequence from a state).
-/

/-- A label is visible (ranges over `Act`) iff it is not the internal action `τ` (Section 2.1). -/
def IsVisible [HasTau Label] (μ : Label) : Prop := μ ≠ HasTau.τ

/-- The weak transition `s =ρ=> t` for a (possibly empty) sequence `ρ` of *visible* actions
    (Section 2.1), defined as the smallest relation satisfying the paper's four generating rules
    directly: reflexivity, a single `τ`-step (absorbed, contributing nothing to `ρ`), a single
    visible step (contributing that one label to `ρ`), and sequential composition. Composability
    (`WeakTr.comp`, the paper's fourth rule) is then built in rather than something to reprove. -/
inductive WeakTr [HasTau Label] (lts : LTS State Label) : State → List Label → State → Prop where
  | refl (s : State) : WeakTr lts s [] s
  | tau {s t : State} : lts.Tr s HasTau.τ t → WeakTr lts s [] t
  | vis {s t : State} {a : Label} : IsVisible a → lts.Tr s a t → WeakTr lts s [a] t
  | comp {s u t : State} {ρ σ : List Label} :
      WeakTr lts s ρ u → WeakTr lts u σ t → WeakTr lts s (ρ ++ σ) t

/-- Every label occurring in a weak trace is visible, i.e. `ρ ∈ Act*` as the paper requires. -/
theorem WeakTr.visible [HasTau Label] {lts : LTS State Label} {s t : State} {ρ : List Label}
    (h : WeakTr lts s ρ t) : ∀ μ ∈ ρ, IsVisible μ := by
  induction h with
  | refl _ => simp
  | tau _ => simp
  | vis hv _ => simpa using hv
  | comp _ _ ih1 ih2 =>
    intro μ hμ
    rcases List.mem_append.mp hμ with h | h
    · exact ih1 μ h
    · exact ih2 μ h

/-- The weak traces of a state `s` (Definition 2.2): the visible-action sequences reachable from
    `s` via `WeakTr`. -/
def weaktraces [HasTau Label] (lts : LTS State Label) (s : State) : Set (List Label) :=
  { ρ | ∃ t, WeakTr lts s ρ t }

/-- A state is stable (used throughout Section 2, e.g. Definition 2.5) iff it has no outgoing
    `τ`-transition. -/
def Stable [HasTau Label] (lts : LTS State Label) (s : State) : Prop :=
  ¬ lts.HasOutLabel s HasTau.τ

/-- The refusals of a single state `s` (Definition 2.5): the subsets of `Act` that `s` does not
    enable, i.e. `P(Act \ enabled(s))`. Only meaningful when `Stable lts s` holds; that guard is
    made explicit at every use site (`refusals`, `failures`). -/
def refusalsOf [HasTau Label] (lts : LTS State Label) (s : State) : Set (Set Label) :=
  { X | X ⊆ { μ | IsVisible μ } \ lts.outgoingLabels s }

/-- The refusals of a set of states `U` (Definition 2.5): refusals observable at some stable
    member of `U`. -/
def refusals [HasTau Label] (lts : LTS State Label) (U : Set State) : Set (Set Label) :=
  { X | ∃ s ∈ U, Stable lts s ∧ X ∈ refusalsOf lts s }

/-- The divergences of a state `s` (Definition 2.6): weak traces that have a prefix reaching a
    divergent state (`Cslib.LTS.Divergent`: a state from which an infinite τ-sequence exists). -/
def divergences [HasTau Label] (lts : LTS State Label) (s : State) : Set (List Label) :=
  { ν | (∀ μ ∈ ν, IsVisible μ) ∧ ∃ ρ σ, ν = ρ ++ σ ∧ ∃ t, WeakTr lts s ρ t ∧ lts.Divergent t }

/-- The stable failures of a state `s` (Definition 2.7). -/
def failures [HasTau Label] (lts : LTS State Label) (s : State) :
    Set (List Label × Set Label) :=
  { p | ∃ t, WeakTr lts s p.1 t ∧ Stable lts t ∧ p.2 ∈ refusalsOf lts t }

/-- The stable failures of `s` with post-divergence details obscured (Definition 2.7). -/
def failuresBot [HasTau Label] (lts : LTS State Label) (s : State) :
    Set (List Label × Set Label) :=
  failures lts s ∪ { p | p.1 ∈ divergences lts s }

/-! ## Refinement relations (Definition 2.9)

`lts1`/`s1` plays the role of the specification, `lts2`/`s2` the implementation; both are LTSs
over the same label type `Label`, so `Act` and `τ` coincide between them. -/

/-- Trace refinement, `L1 ⊑tr L2`: every weak trace of the implementation is a weak trace of the
    specification. -/
def TraceRefines [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) : Prop :=
  weaktraces lts2 s2 ⊆ weaktraces lts1 s1

/-- Stable failures refinement, `L1 ⊑sfr L2`. -/
def StableFailuresRefines [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) : Prop :=
  failures lts2 s2 ⊆ failures lts1 s1 ∧ weaktraces lts2 s2 ⊆ weaktraces lts1 s1

/-- Failures-divergences refinement, `L1 ⊑fdr L2`. -/
def FailuresDivergencesRefines [HasTau Label]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) : Prop :=
  failuresBot lts2 s2 ⊆ failuresBot lts1 s1 ∧ divergences lts2 s2 ⊆ divergences lts1 s1

/-- Notation for trace refinement, mirroring the paper's `L1 ⊑tr L2`. As with Cslib's `~tr[...]`
    (`Cslib.Foundations.Semantics.LTS.TraceEq`), the two LTSs are named explicitly since `s1`/`s2`
    alone don't determine them. -/
notation s1:max " ⊑tr[" lts1 "," lts2 "] " s2:max => TraceRefines lts1 s1 lts2 s2

/-- Notation for stable failures refinement, `L1 ⊑sfr L2`. -/
notation s1:max " ⊑sfr[" lts1 "," lts2 "] " s2:max => StableFailuresRefines lts1 s1 lts2 s2

/-- Notation for failures-divergences refinement, `L1 ⊑fdr L2`. -/
notation s1:max " ⊑fdr[" lts1 "," lts2 "] " s2:max => FailuresDivergencesRefines lts1 s1 lts2 s2

end Semantics
