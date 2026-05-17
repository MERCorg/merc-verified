module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau

open Cslib (LTS HasTau)

@[expose] public section BranchingBisimulation

/-! ## Branching bisimulation and branching bisimilarity -/

/-- A branching bisimulation is similar to a `WeakBisimulation` in that it allows for a saturation
of internal transitions, but it is a stronger equivalence in that it is able to distinguish
when internal work constitutes a choice. There are several (equivalent) definitions used in
literature. The original one can be found in [R.J. van Glabbeek and W.P. Weijland,
"Branching Time and Abstraction in Bisimulation Semantics", 1990]. But we follow the slightly
more popular definition of [de Nicola and Vaandrager, 1995, https://doi.org/10.1145/201019.201032].
-/
def LTS.IsBranchingBisimulation [HasTau Label] (lts : LTS State Label)
  (r : State → State → Prop) :=
  ∀ ⦃s1 s2⦄, r s1 s2 → ∀ μ,
    /- In case of a transition on the left -/
    (∀ s1', lts.Tr s1 μ s1' →
       /- A single tau transition can be mimicked by doing nothing. -/
       (μ = HasTau.τ ∧ r s1' s2) ∨
       /- Any transition can be mimicked by first performing a number of
       τ transitions while relating to the original state, and then mimicking
       the intended transition. -/
       ∃ s2' s2'', lts.STr s2 HasTau.τ s2' ∧ lts.Tr s2' μ s2'' ∧ r s1 s2' ∧ r s1' s2'')
    ∧
    /- The symmetric case of a transition on the right -/
    (∀ s2', lts.Tr s2 μ s2' →
       (μ = HasTau.τ ∧ r s1 s2') ∨
       ∃ s1' s1'', lts.STr s1 HasTau.τ s1' ∧ lts.Tr s1' μ s1'' ∧ r s1' s2 ∧ r s1'' s2')

/-- Two states are branching bisimilar if they are related by some branching bisimulation. -/
def BranchingBisimilarity [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 =>
    ∃ r : State → State → Prop, r s1 s2 ∧ LTS.IsBranchingBisimulation lts r

-- Homogeneous branching bisimulation: the single-LTS variant of LTS.IsBranchingBisimulation
abbrev IsHomBranchingBisimulation [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    (r : State → State → Prop) : Prop :=
  LTS.IsBranchingBisimulation lts r

/-- Notation for branching bisimilarity. -/
notation s:max " ≈br[" lts "] " s':max => BranchingBisimilarity lts s s'

/-- Stuttering lemma: under a branching bisimulation `r`, every τ*-path on the left can be
mimicked by a τ*-path on the right that ends in a related state. -/
theorem LTS.IsBranchingBisimulation.stutter [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : LTS.IsBranchingBisimulation lts r)
    {s s' t : State} (hst : r s t) (hτ : lts.τSTr s s') :
    ∃ t', lts.τSTr t t' ∧ r s' t' := by
  induction hτ with
  | refl => exact ⟨t, Relation.ReflTransGen.refl, hst⟩
  | tail _ hLast ih =>
    obtain ⟨tPrev, hPath, hrPrev⟩ := ih
    rcases (hr hrPrev HasTau.τ).1 _ hLast with hCase | hCase
    · exact ⟨tPrev, hPath, hCase.2⟩
    · obtain ⟨v, v', hsv, hsv', _, hrv⟩ := hCase
      have hPath' : lts.τSTr t v := hPath.trans ((LTS.sTr_τSTr lts).mp hsv)
      exact ⟨v', hPath'.tail hsv', hrv⟩

/-- An iterated form of the stuttering lemma: a two-stage τ*-path can be mimicked while preserving
the relation at the intermediate stage. -/
theorem LTS.IsBranchingBisimulation.stutter₂ [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : LTS.IsBranchingBisimulation lts r)
    {s sMid s' t : State} (hst : r s t) (h1 : lts.τSTr s sMid) (h2 : lts.τSTr sMid s') :
    ∃ tMid t', lts.τSTr t tMid ∧ lts.τSTr tMid t' ∧ r sMid tMid ∧ r s' t' := by
  obtain ⟨tMid, hPath1, hrMid⟩ := LTS.IsBranchingBisimulation.stutter hr hst h1
  obtain ⟨t', hPath2, hrEnd⟩ := LTS.IsBranchingBisimulation.stutter hr hrMid h2
  exact ⟨tMid, t', hPath1, hPath2, hrMid, hrEnd⟩

/-- Branching bisimilarity is reflexive: `Eq` is a branching bisimulation. -/
theorem BranchingBisimilarity.refl [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈br[lts] s := by
  refine ⟨Eq, rfl, ?_⟩
  intro a b hEq μ
  subst hEq
  refine ⟨?_, ?_⟩
  · intro s' hTr
    exact Or.inr ⟨a, s', (LTS.sTr_τSTr lts).mpr Relation.ReflTransGen.refl, hTr, rfl, rfl⟩
  · intro s' hTr
    exact Or.inr ⟨a, s', (LTS.sTr_τSTr lts).mpr Relation.ReflTransGen.refl, hTr, rfl, rfl⟩

/-- The inverse of a branching bisimulation is a branching bisimulation. -/
theorem LTS.IsBranchingBisimulation.flip [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : LTS.IsBranchingBisimulation lts r) :
    LTS.IsBranchingBisimulation lts (fun s s' => r s' s) := by
  intro s1 s2 hr12 μ
  refine ⟨?_, ?_⟩
  · intro s1' hTr
    rcases (hr hr12 μ).2 _ hTr with hCase | hCase
    · exact Or.inl hCase
    · exact Or.inr hCase
  · intro s2' hTr
    rcases (hr hr12 μ).1 _ hTr with hCase | hCase
    · exact Or.inl hCase
    · exact Or.inr hCase

/-- Branching bisimilarity is symmetric. -/
theorem BranchingBisimilarity.symm [HasTau Label] {lts : LTS State Label}
    {s s' : State} (h : s ≈br[lts] s') : s' ≈br[lts] s := by
  obtain ⟨r, hr12, hr⟩ := h
  exact ⟨fun a b => r b a, hr12, LTS.IsBranchingBisimulation.flip hr⟩

/-! ## Semi-branching bisimulation

A semi-branching bisimulation uses the unified condition `t →τ*→ t' (→μ→ t'' | t' = t'')`,
merging the two disjuncts of branching bisimulation. This formulation is closed under relational
composition, making transitivity tractable. (van Glabbeek–Weijland 1996.) -/

/-- A semi-branching bisimulation: every transition is matched by an optional τ*-prefix followed
by an optional matching transition (or no step, when the label is τ). -/
def LTS.IsSemiBranchingBisimulation [HasTau Label] (lts : LTS State Label)
    (r : State → State → Prop) :=
  ∀ ⦃s1 s2⦄, r s1 s2 → ∀ μ,
    (∀ s1', lts.Tr s1 μ s1' → ∃ s2' s2'',
       lts.τSTr s2 s2' ∧
       ((μ = HasTau.τ ∧ s2' = s2'') ∨ lts.Tr s2' μ s2'') ∧
       r s1 s2' ∧ r s1' s2'')
    ∧
    (∀ s2', lts.Tr s2 μ s2' → ∃ s1' s1'',
       lts.τSTr s1 s1' ∧
       ((μ = HasTau.τ ∧ s1' = s1'') ∨ lts.Tr s1' μ s1'') ∧
       r s1' s2 ∧ r s1'' s2')

/-- Two states are semi-branching bisimilar if related by some semi-branching bisimulation. -/
def SemiBranchingBisimilarity [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 => ∃ r, r s1 s2 ∧ LTS.IsSemiBranchingBisimulation lts r

/-- Every branching bisimulation is also a semi-branching bisimulation: just absorb `Or.inl`
into the unified condition with an empty τ-prefix and no final step. -/
theorem LTS.IsBranchingBisimulation.toSemi [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : LTS.IsBranchingBisimulation lts r) :
    LTS.IsSemiBranchingBisimulation lts r := by
  intro s1 s2 hr12 μ
  refine ⟨?_, ?_⟩
  · intro s1' hTr
    rcases (hr hr12 μ).1 _ hTr with ⟨hμτ, hr12'⟩ | ⟨s2', s2'', hSTr, hTr', hr1, hr2⟩
    · exact ⟨s2, s2, Relation.ReflTransGen.refl, Or.inl ⟨hμτ, rfl⟩, hr12, hr12'⟩
    · exact ⟨s2', s2'', (LTS.sTr_τSTr lts).mp hSTr, Or.inr hTr', hr1, hr2⟩
  · intro s2' hTr
    rcases (hr hr12 μ).2 _ hTr with ⟨hμτ, hr12'⟩ | ⟨s1', s1'', hSTr, hTr', hr1, hr2⟩
    · exact ⟨s1, s1, Relation.ReflTransGen.refl, Or.inl ⟨hμτ, rfl⟩, hr12, hr12'⟩
    · exact ⟨s1', s1'', (LTS.sTr_τSTr lts).mp hSTr, Or.inr hTr', hr1, hr2⟩

/-- Stuttering lemma for semi-branching bisimulations. Same statement as the branching version. -/
theorem LTS.IsSemiBranchingBisimulation.stutter [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : LTS.IsSemiBranchingBisimulation lts r)
    {s s' t : State} (hst : r s t) (hτ : lts.τSTr s s') :
    ∃ t', lts.τSTr t t' ∧ r s' t' := by
  induction hτ with
  | refl => exact ⟨t, Relation.ReflTransGen.refl, hst⟩
  | tail _ hLast ih =>
    obtain ⟨tPrev, hPath, hrPrev⟩ := ih
    obtain ⟨t_a, t_b, hPath', hFinal, _, hr'⟩ := (hr hrPrev HasTau.τ).1 _ hLast
    rcases hFinal with ⟨_, htEq⟩ | hStep
    · exact ⟨t_b, hPath.trans (htEq ▸ hPath'), hr'⟩
    · exact ⟨t_b, (hPath.trans hPath').tail hStep, hr'⟩

/-- The inverse of a semi-branching bisimulation is a semi-branching bisimulation. -/
theorem LTS.IsSemiBranchingBisimulation.flip [HasTau Label] {lts : LTS State Label}
    {r : State → State → Prop} (hr : LTS.IsSemiBranchingBisimulation lts r) :
    LTS.IsSemiBranchingBisimulation lts (fun s s' => r s' s) := by
  intro s1 s2 hr12 μ
  refine ⟨?_, ?_⟩
  · intro s1' hTr
    obtain ⟨a, b, h1, h2, h3, h4⟩ := (hr hr12 μ).2 _ hTr
    exact ⟨a, b, h1, h2, h3, h4⟩
  · intro s2' hTr
    obtain ⟨a, b, h1, h2, h3, h4⟩ := (hr hr12 μ).1 _ hTr
    exact ⟨a, b, h1, h2, h3, h4⟩

/-- **Composition of semi-branching bisimulations is a semi-branching bisimulation.**
The unified condition makes composition transparent: stutter on the right factor through the
left factor's τ*-prefix, then apply the right factor's SBB condition to the final step. -/
theorem LTS.IsSemiBranchingBisimulation.comp [HasTau Label] {lts : LTS State Label}
    {r1 r2 : State → State → Prop}
    (hr1 : LTS.IsSemiBranchingBisimulation lts r1)
    (hr2 : LTS.IsSemiBranchingBisimulation lts r2) :
    LTS.IsSemiBranchingBisimulation lts (fun s t => ∃ u, r1 s u ∧ r2 u t) := by
  intro s t hst μ
  obtain ⟨u, hr1su, hr2ut⟩ := hst
  refine ⟨?_, ?_⟩
  · intro s' hTr
    -- r1 SBB on (s, u) with s →μ→ s': ∃ u', u'', u →τ*→ u' ∧ (μ-step or no step) ∧ ...
    obtain ⟨u', u'', hτuu', hFinal1, hr1su', hr1s'u''⟩ := (hr1 hr1su μ).1 _ hTr
    -- Stutter r2 across the τ*-prefix u →τ*→ u'.
    obtain ⟨tA, hPathA, hr2u'tA⟩ :=
      LTS.IsSemiBranchingBisimulation.stutter hr2 hr2ut hτuu'
    rcases hFinal1 with ⟨hμτ, hu'Eq⟩ | hStep1
    · -- r1 absorbed by "no step": u' = u''. Then r2 u' tA = r2 u'' tA.
      subst hu'Eq
      exact ⟨tA, tA, hPathA, Or.inl ⟨hμτ, rfl⟩, ⟨u', hr1su', hr2u'tA⟩, ⟨u', hr1s'u'', hr2u'tA⟩⟩
    · -- r1 produced an actual u' →μ→ u''. Apply r2 SBB on (u', tA).
      obtain ⟨tB, tC, hPathB, hFinal2, hr2u'tB, hr2u''tC⟩ :=
        (hr2 hr2u'tA μ).1 _ hStep1
      exact ⟨tB, tC, hPathA.trans hPathB, hFinal2,
        ⟨u', hr1su', hr2u'tB⟩, ⟨u'', hr1s'u'', hr2u''tC⟩⟩
  · intro t' hTr
    -- Symmetric direction: r2's t-side, then r1's s-side stutter.
    obtain ⟨u', u'', hτuu', hFinal2, hr2u't, hr2u''t'⟩ := (hr2 hr2ut μ).2 _ hTr
    -- Stutter r1's flipped form for u →τ*→ u'.
    obtain ⟨sA, hPathA, hr1u'sA⟩ :=
      LTS.IsSemiBranchingBisimulation.stutter (LTS.IsSemiBranchingBisimulation.flip hr1)
        hr1su hτuu'
    rcases hFinal2 with ⟨hμτ, hu'Eq⟩ | hStep2
    · subst hu'Eq
      exact ⟨sA, sA, hPathA, Or.inl ⟨hμτ, rfl⟩,
        ⟨u', hr1u'sA, hr2u't⟩, ⟨u', hr1u'sA, hr2u''t'⟩⟩
    · obtain ⟨sB, sC, hPathB, hFinal1, hr1u'sB, hr1u''sC⟩ :=
        (LTS.IsSemiBranchingBisimulation.flip hr1 hr1u'sA μ).1 _ hStep2
      exact ⟨sB, sC, hPathA.trans hPathB, hFinal1,
        ⟨u', hr1u'sB, hr2u't⟩, ⟨u'', hr1u''sC, hr2u''t'⟩⟩

/-! ## Equivalence properties of semi-branching bisimilarity -/

/-- Notation for semi-branching bisimilarity. -/
notation s:max " ≈sbr[" lts "] " s':max => SemiBranchingBisimilarity lts s s'

/-- Semi-branching bisimilarity is reflexive: `Eq` is a semi-branching bisimulation. -/
theorem SemiBranchingBisimilarity.refl [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈sbr[lts] s := by
  refine ⟨Eq, rfl, ?_⟩
  intro a b hEq μ
  subst hEq
  refine ⟨?_, ?_⟩
  · intro s' hTr
    exact ⟨a, s', Relation.ReflTransGen.refl, Or.inr hTr, rfl, rfl⟩
  · intro s' hTr
    exact ⟨a, s', Relation.ReflTransGen.refl, Or.inr hTr, rfl, rfl⟩

/-- Semi-branching bisimilarity is symmetric. -/
theorem SemiBranchingBisimilarity.symm [HasTau Label] {lts : LTS State Label}
    {s s' : State} (h : s ≈sbr[lts] s') : s' ≈sbr[lts] s := by
  obtain ⟨r, hr12, hr⟩ := h
  exact ⟨fun a b => r b a, hr12, LTS.IsSemiBranchingBisimulation.flip hr⟩

/-- **Semi-branching bisimilarity is transitive.** Direct consequence of SBB closure under
relational composition. -/
theorem SemiBranchingBisimilarity.trans [HasTau Label] {lts : LTS State Label}
    {s1 s2 s3 : State} (h12 : s1 ≈sbr[lts] s2) (h23 : s2 ≈sbr[lts] s3) :
    s1 ≈sbr[lts] s3 := by
  obtain ⟨r1, h1, hbr1⟩ := h12
  obtain ⟨r2, h2, hbr2⟩ := h23
  exact ⟨fun s t => ∃ u, r1 s u ∧ r2 u t, ⟨s2, h1, h2⟩,
    LTS.IsSemiBranchingBisimulation.comp hbr1 hbr2⟩

/-- Branching bisimilarity is contained in semi-branching bisimilarity. -/
theorem BranchingBisimilarity.toSemi [HasTau Label] {lts : LTS State Label}
    {s s' : State} (h : s ≈br[lts] s') : s ≈sbr[lts] s' := by
  obtain ⟨r, hr12, hr⟩ := h
  exact ⟨r, hr12, LTS.IsBranchingBisimulation.toSemi hr⟩

/-! ## Basten's approach to transitivity

Following T. Basten, "Branching bisimilarity is an equivalence indeed!" (1996), transitivity
factors through semi-branching bisimilarity, which is closed under composition (proved above
as `LTS.IsSemiBranchingBisimulation.comp`). The remaining ingredient is the inclusion
`≈sbr ⊆ ≈br`. Once proved, transitivity of `≈br` follows immediately:

```
s ≈br u ≈br t  →  s ≈sbr u ≈sbr t  →  s ≈sbr t  →  s ≈br t
       (toSemi)              (trans)         (toBranching)
```

The inclusion `≈sbr ⊆ ≈br` reduces to showing that `≈sbr` itself satisfies the dN-V BB conditions.
The technically delicate step is the **semi-branching stuttering lemma**: intermediate states on
a τ-path between two states `≈sbr`-related to the same `q` are themselves `≈sbr`-related to `q`.
This holds for `≈sbr` (and `≈br`) by maximality but is non-trivial to formalize: it requires
either Basten's saturation argument or a strong-stuttering lemma tracking intermediate matches
along the path. -/

/-- `≈br` is itself a branching bisimulation. The union of BBs is a BB: the witness BB for any
≈br-pair provides matching transitions, and the matched derivatives are themselves ≈br-related. -/
theorem BranchingBisimilarity.isBranchingBisimulation [HasTau Label] {lts : LTS State Label} :
    LTS.IsBranchingBisimulation lts (BranchingBisimilarity lts) := by
  intro s t hst μ
  obtain ⟨r, hrst, hr⟩ := hst
  refine ⟨?_, ?_⟩
  · intro s' hTr
    rcases (hr hrst μ).1 _ hTr with ⟨hμτ, hr'⟩ | ⟨t', t'', hSTr, hTr', hr1, hr2⟩
    · exact Or.inl ⟨hμτ, r, hr', hr⟩
    · exact Or.inr ⟨t', t'', hSTr, hTr', ⟨r, hr1, hr⟩, ⟨r, hr2, hr⟩⟩
  · intro t' hTr
    rcases (hr hrst μ).2 _ hTr with ⟨hμτ, hr'⟩ | ⟨s', s'', hSTr, hTr', hr1, hr2⟩
    · exact Or.inl ⟨hμτ, r, hr', hr⟩
    · exact Or.inr ⟨s', s'', hSTr, hTr', ⟨r, hr1, hr⟩, ⟨r, hr2, hr⟩⟩

/-- `≈sbr` is itself a semi-branching bisimulation. The union of SBBs is an SBB. -/
theorem SemiBranchingBisimilarity.isSemiBranchingBisimulation
    [HasTau Label] {lts : LTS State Label} :
    LTS.IsSemiBranchingBisimulation lts (SemiBranchingBisimilarity lts) := by
  intro s t hst μ
  obtain ⟨r, hrst, hr⟩ := hst
  refine ⟨?_, ?_⟩
  · intro s' hTr
    obtain ⟨t', t'', hPath, hFinal, hr1, hr2⟩ := (hr hrst μ).1 _ hTr
    exact ⟨t', t'', hPath, hFinal, ⟨r, hr1, hr⟩, ⟨r, hr2, hr⟩⟩
  · intro t' hTr
    obtain ⟨s', s'', hPath, hFinal, hr1, hr2⟩ := (hr hrst μ).2 _ hTr
    exact ⟨s', s'', hPath, hFinal, ⟨r, hr1, hr⟩, ⟨r, hr2, hr⟩⟩

/-- **`≈sbr` is itself a branching bisimulation.**

This is the technical heart of `≈sbr ⊆ ≈br`. The proof verifies the dN-V conditions on the SBB
result. The delicate case (μ=τ, no final step, non-empty τ*-prefix) is closed by using `≈sbr`'s
transitivity: from `s ≈sbr t`, `s ≈sbr t'` (intermediate), and `s' ≈sbr t'` (final) — all
endpoints related to the same equivalence class — transitivity directly gives `s' ≈sbr t`, which
satisfies the dN-V `Or.inl`. -/
theorem SemiBranchingBisimilarity.isBranchingBisimulation
    [HasTau Label] {lts : LTS State Label} :
    LTS.IsBranchingBisimulation lts (SemiBranchingBisimilarity lts) := by
  have hsbrSBB : LTS.IsSemiBranchingBisimulation lts (SemiBranchingBisimilarity lts) :=
    SemiBranchingBisimilarity.isSemiBranchingBisimulation
  intro s t hst μ
  refine ⟨?_, ?_⟩
  · intro s' hTr
    obtain ⟨t', t'', hPath, hFinal, hsbr_st', hsbr_s't''⟩ := (hsbrSBB hst μ).1 _ hTr
    rcases hFinal with ⟨hμτ, ht'Eq⟩ | hStep
    · -- No final step: t' = t''. Use transitivity: s ≈sbr t and s ≈sbr t' put t and t' in the
      -- same class, so s' ≈sbr t' bridges to s' ≈sbr t.
      subst ht'Eq
      refine Or.inl ⟨hμτ, ?_⟩
      have h_t_t' : t ≈sbr[lts] t' :=
        SemiBranchingBisimilarity.trans (SemiBranchingBisimilarity.symm hst) hsbr_st'
      exact SemiBranchingBisimilarity.trans hsbr_s't''
        (SemiBranchingBisimilarity.symm h_t_t')
    · -- Real μ-step: direct BB Or.inr.
      exact Or.inr ⟨t', t'', (LTS.sTr_τSTr lts).mpr hPath, hStep, hsbr_st', hsbr_s't''⟩
  · intro t' hTr
    obtain ⟨s', s'', hPath, hFinal, hsbr_s't, hsbr_s''t'⟩ := (hsbrSBB hst μ).2 _ hTr
    rcases hFinal with ⟨hμτ, hs'Eq⟩ | hStep
    · -- Symmetric closure via transitivity.
      subst hs'Eq
      refine Or.inl ⟨hμτ, ?_⟩
      have h_s_s' : s ≈sbr[lts] s' :=
        SemiBranchingBisimilarity.trans hst (SemiBranchingBisimilarity.symm hsbr_s't)
      exact SemiBranchingBisimilarity.trans h_s_s' hsbr_s''t'
    · exact Or.inr ⟨s', s'', (LTS.sTr_τSTr lts).mpr hPath, hStep, hsbr_s't, hsbr_s''t'⟩

/-- **`≈sbr` is contained in `≈br`.** Since `≈sbr` is itself a BB and `≈br` is the largest BB,
`≈sbr` witnesses any of its pairs as `≈br`-related. -/
theorem SemiBranchingBisimilarity.toBranching [HasTau Label] {lts : LTS State Label}
    {s s' : State} (h : s ≈sbr[lts] s') : s ≈br[lts] s' :=
  ⟨SemiBranchingBisimilarity lts, h, SemiBranchingBisimilarity.isBranchingBisimulation⟩

/-- **Branching bisimilarity is transitive** (Basten 1996).

Routed through semi-branching bisimilarity: the SBB framework gives clean composition closure
(`SemiBranchingBisimilarity.trans`), and `BranchingBisimilarity.toSemi` / `toBranching` bridge the
two notions. -/
theorem BranchingBisimilarity.trans [HasTau Label] {lts : LTS State Label}
    {s1 s2 s3 : State} (h12 : s1 ≈br[lts] s2) (h23 : s2 ≈br[lts] s3) :
    s1 ≈br[lts] s3 :=
  SemiBranchingBisimilarity.toBranching
    (SemiBranchingBisimilarity.trans
      (BranchingBisimilarity.toSemi h12)
      (BranchingBisimilarity.toSemi h23))

end BranchingBisimulation
