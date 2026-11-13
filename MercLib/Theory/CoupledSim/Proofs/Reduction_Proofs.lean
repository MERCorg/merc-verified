module

public import MercLib.Theory.CoupledSim.CoupledSimilarity

open Cslib (LTS HasTau)

@[expose] public section ReductionProofs

namespace MercLib.CoupledSim

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The "headline"
theorems below are stated in `Challenges/CoupledSim.lean` (human-vetted). -/

/-! ## Helper lemmas about `extendSink` -/

/-- A strong step out of the sink must stay in the sink, and its label must be `τ`. -/
private theorem ext_tr_none [HasTau Label] {lts : LTS State Label} {μ : Label} {c : Option State}
    (h : (extendSink lts).Tr none μ c) : c = none ∧ μ = HasTau.τ := by
  cases c with
  | none => exact ⟨rfl, h⟩
  | some s => exact (h : False).elim

/-- A strong step out of a `some` state either goes to the sink (with label `τ`) or is a strong
step of the original LTS. -/
private theorem ext_tr_some_cases [HasTau Label] {lts : LTS State Label} {s : State} {μ : Label}
    {c : Option State} (h : (extendSink lts).Tr (some s) μ c) :
    (c = none ∧ μ = HasTau.τ) ∨ ∃ y, c = some y ∧ lts.Tr s μ y := by
  cases c with
  | none => exact Or.inl ⟨rfl, h⟩
  | some y => exact Or.inr ⟨y, rfl, h⟩

/-- Every state of the sink-extended LTS can reach the sink by a `τ`-step. -/
private theorem τSTr_ext_sink [HasTau Label] {lts : LTS State Label} (b : Option State) :
    (extendSink lts).τSTr b none :=
  Relation.ReflTransGen.single (show (extendSink lts).Tr b HasTau.τ none from by
    cases b <;> rfl)

/-- The sink step is a saturated step. -/
private theorem stτr_sink [HasTau Label] {lts : LTS State Label} (b : Option State) :
    (extendSink lts).STr b HasTau.τ none :=
  (LTS.sTr_τSTr_iff (extendSink lts)).mpr (τSTr_ext_sink b)

/-- `τ`-reachability in the sink-extended LTS from a `some` state: the endpoint is either the
sink or `τ`-reachable in the original LTS. -/
private theorem τSTr_ext_some_cases [HasTau Label] {lts : LTS State Label} {x : State}
    {z : Option State} (h : (extendSink lts).τSTr (some x) z) :
    z = none ∨ ∃ y, z = some y ∧ lts.τSTr x y := by
  induction h with
  | refl => exact Or.inr ⟨x, rfl, LTS.τSTr.refl⟩
  | tail _ hLast ih =>
    rcases ih with rfl | ⟨y, rfl, hyτ⟩
    · obtain ⟨hc, -⟩ := ext_tr_none hLast
      subst hc
      exact Or.inl rfl
    · rcases ext_tr_some_cases hLast with ⟨hc, -⟩ | ⟨y0, hc, htr⟩
      · subst hc
        exact Or.inl rfl
      · subst hc
        exact Or.inr ⟨y0, rfl, Relation.ReflTransGen.tail hyτ htr⟩

/-- `τ`-reachability in the original LTS lifts to the sink-extended LTS. -/
private theorem τSTr_ext_some_mono [HasTau Label] {lts : LTS State Label} {x y : State}
    (h : lts.τSTr x y) : (extendSink lts).τSTr (some x) (some y) := by
  induction h with
  | refl => exact LTS.τSTr.refl
  | tail _ hLast ih => exact Relation.ReflTransGen.tail ih hLast

/-- Strong steps of the original LTS lift to the sink-extended LTS. -/
private theorem STr_ext_lift [HasTau Label] {lts : LTS State Label} {y v : State} {μ : Label}
    (h : lts.STr y μ v) : (extendSink lts).STr (some y) μ (some v) := by
  cases h with
  | refl => exact (LTS.sTr_τSTr_iff (extendSink lts)).mpr LTS.τSTr.refl
  | tr hτ1 htr hτ2 =>
    refine LTS.STr.tr (τSTr_ext_some_mono hτ1) ?_ (τSTr_ext_some_mono hτ2)
    exact htr

/-- A saturated step of the sink-extended LTS either moves inside the original LTS (with
`τ`-padding before and after) or is a `τ`-step that does not change the state. -/
private theorem STr_ext_split [HasTau Label] {lts : LTS State Label} {a b : Option State}
    {μ : Label} (h : (extendSink lts).STr a μ b) :
    (∃ t s', (extendSink lts).τSTr a t ∧ (extendSink lts).Tr t μ s' ∧ (extendSink lts).τSTr s' b) ∨
      (μ = HasTau.τ ∧ a = b) := by
  cases h with
  | refl => exact Or.inr ⟨rfl, rfl⟩
  | tr hτ1 htr' hτ2 => exact Or.inl ⟨_, _, hτ1, htr', hτ2⟩

/-! ## The reduction of weak similarity to coupled similarity (Theorem 1) -/

/-- Relations on the sink-extended LTS become coupled simulation relations by adding all pairs
out of the sink: the coupling constraint is discharged by the `τ`-reachable sink. -/
private def sinkRel (r : Option State → Option State → Prop) (a b : Option State) : Prop :=
  r a b ∨ a = none

/-- Weak simulation relations on the original LTS lift to the sink-extended LTS. -/
private def sinkLiftRel (r : State → State → Prop) (a b : Option State) : Prop :=
  a = none ∨ ∃ s t, a = some s ∧ b = some t ∧ r s t

/-- Relations on the sink-extended LTS pull back to the original LTS along the `some`-embedding,
closing the right state under `τ`-steps towards related states. -/
private def preimageRel [HasTau Label] (lts : LTS State Label)
    (r : Option State → Option State → Prop) (x y : State) : Prop :=
  ∃ m, r (some x) m ∧ (extendSink lts).τSTr (some y) m

private theorem sinkRel_isWeakSimulation [HasTau Label] {lts : LTS State Label}
    {r : Option State → Option State → Prop} (hr : IsWeakSimulation (extendSink lts) r) :
    IsWeakSimulation (extendSink lts) (sinkRel r) := by
  rintro a b (hb | rfl) μ a' htr
  · obtain ⟨b', hb', hsTr⟩ := hr hb μ a' htr
    refine ⟨b', ?_, hsTr⟩
    exact Or.inl hb'
  · cases a' with
    | none =>
      have hμ : μ = HasTau.τ := htr
      subst hμ
      refine ⟨none, ?_, stτr_sink b⟩
      exact Or.inr rfl
    | some s => exact (htr : False).elim

private theorem sinkRel_coupling [HasTau Label] {lts : LTS State Label}
    {r : Option State → Option State → Prop} : Coupling (extendSink lts) (sinkRel r) := by
  rintro a b (_ | rfl)
  · refine ⟨none, τSTr_ext_sink b, ?_⟩
    exact Or.inr rfl
  · refine ⟨none, τSTr_ext_sink b, ?_⟩
    exact Or.inr rfl

/-- **Theorem 1 of [Bisping2019]** (first part): on the sink-extended LTS, the weak simulation
preorder and the coupled simulation preorder coincide. -/
theorem extendSink_ws_iff_cs [HasTau Label] (lts : LTS State Label) (p q : Option State) :
    p ≼ws[extendSink lts] q ↔ p ≼cs[extendSink lts] q := by
  constructor
  · rintro ⟨r, hr, hmem⟩
    refine ⟨sinkRel r, ⟨sinkRel_isWeakSimulation hr, sinkRel_coupling⟩, ?_⟩
    exact Or.inl hmem
  · rintro ⟨r, hr, hmem⟩
    exact ⟨r, hr.1, hmem⟩

private theorem sinkLiftRel_isWeakSimulation [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : IsWeakSimulation lts r) :
    IsWeakSimulation (extendSink lts) (sinkLiftRel r) := by
  rintro a b hmem μ a' htr
  rcases hmem with rfl | ⟨s, t, rfl, rfl, hrs⟩
  · cases a' with
    | none =>
      have hμ : μ = HasTau.τ := htr
      subst hμ
      refine ⟨none, ?_, stτr_sink b⟩
      exact Or.inl rfl
    | some u => exact (htr : False).elim
  · cases a' with
    | none =>
      have hμ : μ = HasTau.τ := htr
      subst hμ
      refine ⟨none, ?_, stτr_sink (some t)⟩
      exact Or.inl rfl
    | some u =>
      obtain ⟨v, hv, hsTr⟩ := hr hrs μ u htr
      refine ⟨some v, ?_, STr_ext_lift hsTr⟩
      exact Or.inr ⟨u, v, rfl, rfl, hv⟩

private theorem preimageRel_isWeakSimulation [HasTau Label] {lts : LTS State Label}
    {r : Option State → Option State → Prop} (hr : IsWeakSimulation (extendSink lts) r) :
    IsWeakSimulation lts (preimageRel lts r) := by
  rintro x y ⟨m, hRm, hyτm⟩ μ u htr
  obtain ⟨c, hRc, hsTr⟩ := hr hRm μ (some u)
    (show (extendSink lts).Tr (some x) μ (some u) from htr)
  rcases STr_ext_split hsTr with ⟨t, s', hτ1, htr', hτ2⟩ | ⟨hμτ, hmc⟩
  · cases s' with
    | none =>
      have hμ : μ = HasTau.τ := by cases t <;> exact htr'
      subst hμ
      refine ⟨y, ⟨c, hRc, Relation.ReflTransGen.trans hyτm
        (Relation.ReflTransGen.trans (τSTr_ext_sink m) hτ2)⟩, ?_⟩
      exact LTS.STr.refl
    | some w =>
      cases t with
      | none => exact (htr' : False).elim
      | some m2 =>
        have hyτ2 : (extendSink lts).τSTr (some y) (some m2) :=
          Relation.ReflTransGen.trans hyτm hτ1
        rcases τSTr_ext_some_cases hyτ2 with hz | ⟨y0, hz, hyτ⟩
        · simp at hz
        · have hz' : m2 = y0 := Option.some.inj hz
          subst hz'
          refine ⟨w, ⟨c, hRc, hτ2⟩, LTS.STr.tr hyτ ?_ LTS.τSTr.refl⟩
          exact htr'
  · subst hμτ
    subst hmc
    refine ⟨y, ⟨m, hRc, hyτm⟩, ?_⟩
    exact LTS.STr.refl

/-- **Theorem 1 of [Bisping2019]** (second part): weak similarity in the original LTS agrees
with weak similarity between the corresponding `some`-states of the sink-extended LTS. -/
theorem extendSink_ws_some_iff [HasTau Label] (lts : LTS State Label) (s t : State) :
    s ≼ws[lts] t ↔ (some s) ≼ws[extendSink lts] (some t) := by
  constructor
  · rintro ⟨r, hr, hmem⟩
    exact ⟨sinkLiftRel r, sinkLiftRel_isWeakSimulation hr, Or.inr ⟨s, t, rfl, rfl, hmem⟩⟩
  · rintro ⟨r, hr, hmem⟩
    exact ⟨preimageRel lts r, preimageRel_isWeakSimulation hr, ⟨some t, hmem, LTS.τSTr.refl⟩⟩

end MercLib.CoupledSim
