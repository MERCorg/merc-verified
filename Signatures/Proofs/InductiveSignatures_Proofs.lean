module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Signatures.BranchingBisimilarity
public import Signatures.Signature
public import Signatures.InductiveSignatures
public import Signatures.Proofs.BranchingBisimilarity_Transitivity

@[expose] public section InductiveSignaturesProofs

/-! ## Inductive signatures and branching bisimilarity for τ-loop-free LTSs

The `Sig` operator is a one-step recurrence. Its full fixed point exists when the
inert τ-relation is well-founded (no infinite τ-chains, hence no τ-loops). For such LTSs,
a partition stable under the fixed point induces a branching bisimulation.
-/

/-- Witness extraction for a fixed point of `Sig` under τ-loop-freedom.

If `sigFn` is a fixed point of `Sig` and the LTS is τ-loop-free, then every non-inert element
`(μ, Sum.inl α) ∈ sigFn s` is *realized* by an actual transition: there is an inert τ*-path
`s →τ*→ s'` (staying in `partition s`'s block) followed by a transition `s' →μ→ t` with
`partition t = α`.

Proof: well-founded induction on `s` via the τ-relation. If `Sig` delegates at `s` (to some
inert τ-successor `s_chosen`), the element lies in `sigFn s_chosen`; apply the IH and prepend
the τ-step. Otherwise `sigFn s = PreSig s`, and the first PreSig branch supplies the witness
directly (the inert-τ branch is excluded because it is tagged `Sum.inr`). -/
theorem Sig.exists_witness_of_inl [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) (partition : State → Block)
    {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s) :
    ∀ s μ α, (μ, Sum.inl α) ∈ sigFn s →
      ∃ s' t, lts.τSTr s s' ∧ partition s' = partition s ∧
              lts.Tr s' μ t ∧ partition t = α := by
  intro s
  induction s using WellFounded.induction hWF with
  | _ s ih =>
    intro μ α hmem
    by_cases hDeleg : ∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ partition s = partition s' ∧
                PreSig lts partition sigHash s ⊆
                  sigFn s' ∪ {(Cslib.HasTau.τ, Sum.inr (sigHash s'))}
    · -- Delegation case: sigFn s = sigFn hDeleg.choose
      have hEq : sigFn s = sigFn hDeleg.choose := by
        rw [hFix s, Sig, dif_pos hDeleg]
      rw [hEq] at hmem
      obtain ⟨hτ, hπ, _⟩ := hDeleg.choose_spec
      obtain ⟨s', t, hτPath, hπs', hStep, hπt⟩ := ih hDeleg.choose hτ μ α hmem
      exact ⟨s', t, Relation.ReflTransGen.head hτ hτPath, hπs'.trans hπ.symm, hStep, hπt⟩
    · -- No-delegation case: sigFn s = PreSig s
      have hEq : sigFn s = PreSig lts partition sigHash s := by
        rw [hFix s, Sig, dif_neg hDeleg]
      rw [hEq] at hmem
      rcases hmem with ⟨a, s', hStep, _, hPair⟩ | ⟨s', _, _, hPair⟩
      · -- Visible/non-inert PreSig branch — direct witness.
        obtain ⟨rfl, hSum⟩ := Prod.mk.inj hPair
        cases Sum.inl.inj hSum
        exact ⟨s, s', Relation.ReflTransGen.refl, rfl, hStep, rfl⟩
      · -- Inert-τ PreSig branch is tagged Sum.inr, contradicting Sum.inl.
        exact nomatch (Prod.mk.inj hPair).2

/-- A non-inert transition `s →μ→ t` witnesses `(μ, Sum.inl (partition t)) ∈ sigFn s` for
any fixed point of `Sig`. In the delegation case `Sum.inl`-tagged elements pass through the
subset condition (the singleton only contains `Sum.inr`); in the non-delegation case
`sigFn s = PreSig s` and membership is direct. -/
private theorem sigFn_mem_of_nonInert_tr [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    {s t : State} {μ : Label}
    (hTr : lts.Tr s μ t) (hSide : μ ≠ Cslib.HasTau.τ ∨ partition s ≠ partition t) :
    (μ, Sum.inl (partition t)) ∈ sigFn s := by
  have hMem : (μ, Sum.inl (partition t)) ∈ PreSig lts partition sigHash s :=
    Or.inl ⟨μ, t, hTr, hSide, rfl⟩
  by_cases hDeleg : ∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ partition s = partition s' ∧
              PreSig lts partition sigHash s ⊆
                sigFn s' ∪ {(Cslib.HasTau.τ, Sum.inr (sigHash s'))}
  · have hEq : sigFn s = sigFn hDeleg.choose := by rw [hFix s, Sig, dif_pos hDeleg]
    rw [hEq]
    obtain ⟨_, _, hSub⟩ := hDeleg.choose_spec
    rcases hSub hMem with h | h
    · exact h
    · exact nomatch (Prod.mk.inj (Set.mem_singleton_iff.mp h)).2
  · rw [hFix s, Sig, dif_neg hDeleg]; exact hMem

/-- If a partition is stable w.r.t. a fixed point `sigFn` of the inductive `Sig` operator
(in a τ-loop-free LTS), then same-block states form a branching bisimulation.

The argument: for inert τ-moves the matching state does nothing (Or.inl). For non-inert moves
on the left, the witness `(μ, Sum.inl (partition t)) ∈ sigFn s₁` lifts via stability to
`sigFn s₂`; the previous lemma realizes it as an inert τ*-path on the right followed by a
matching transition, giving Or.inr. The symmetric direction is identical. -/
theorem IsStable.isHomBranchingBisimulation_inductive [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    (hStable : IsStable sigFn partition) :
    IsHomBranchingBisimulation lts (fun s s' => partition s = partition s') := by
  intro s₁ s₂ hRel μ
  refine ⟨?_, ?_⟩
  · intro t₁ hTr₁
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₁ = partition s₁
    · exact Or.inl ⟨hInert.1, hInert.2.trans hRel⟩
    · have hSide : μ ≠ Cslib.HasTau.τ ∨ partition s₁ ≠ partition t₁ := by
        rcases Classical.em (μ = Cslib.HasTau.τ) with hμ | hμ
        · exact Or.inr fun h => hInert ⟨hμ, h.symm⟩
        · exact Or.inl hμ
      have hMem1 : (μ, Sum.inl (partition t₁)) ∈ sigFn s₁ :=
        sigFn_mem_of_nonInert_tr partition sigHash sigFn hFix hTr₁ hSide
      have hMem2 : (μ, Sum.inl (partition t₁)) ∈ sigFn s₂ := by
        rw [← hStable s₁ s₂ hRel]; exact hMem1
      obtain ⟨s₂', t₂, hτPath, hπs₂', hStep, hπt₂⟩ :=
        Sig.exists_witness_of_inl hWF partition sigHash sigFn hFix s₂ μ (partition t₁) hMem2
      refine Or.inr ⟨s₂', t₂, (Cslib.LTS.sTr_τSTr lts).mpr hτPath, hStep, ?_, hπt₂.symm⟩
      exact hRel.trans hπs₂'.symm
  · intro t₂ hTr₂
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₂ = partition s₂
    · exact Or.inl ⟨hInert.1, hRel.trans hInert.2.symm⟩
    · have hSide : μ ≠ Cslib.HasTau.τ ∨ partition s₂ ≠ partition t₂ := by
        rcases Classical.em (μ = Cslib.HasTau.τ) with hμ | hμ
        · exact Or.inr fun h => hInert ⟨hμ, h.symm⟩
        · exact Or.inl hμ
      have hMem2 : (μ, Sum.inl (partition t₂)) ∈ sigFn s₂ :=
        sigFn_mem_of_nonInert_tr partition sigHash sigFn hFix hTr₂ hSide
      have hMem1 : (μ, Sum.inl (partition t₂)) ∈ sigFn s₁ := by
        rw [hStable s₁ s₂ hRel]; exact hMem2
      obtain ⟨s₁', t₁, hτPath, hπs₁', hStep, hπt₁⟩ :=
        Sig.exists_witness_of_inl hWF partition sigHash sigFn hFix s₁ μ (partition t₂) hMem1
      refine Or.inr ⟨s₁', t₁, (Cslib.LTS.sTr_τSTr lts).mpr hτPath, hStep, hπs₁'.trans hRel, hπt₁⟩

/-- Same-block states under a Sig-fixed-point stable partition (in a τ-loop-free LTS) are
branching bisimilar. -/
theorem IsStable.branchingBisimilarity_inductive [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    (partition : State → Block) {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag)))
    (hFix : ∀ s, sigFn s = Sig lts partition sigHash sigFn s)
    (hStable : IsStable sigFn partition)
    {s₁ s₂ : State} (hRel : partition s₁ = partition s₂) :
    BranchingBisimilarity lts s₁ s₂ :=
  ⟨fun a b => partition a = partition b, hRel,
    IsStable.isHomBranchingBisimulation_inductive hWF partition sigHash sigFn hFix hStable⟩

/-! ## Converse direction: branching bisimilarity yields a Sig fixed point

The companion to `IsStable.branchingBisimilarity_inductive`: every pair of branching bisimilar
states in a τ-loop-free LTS is witnessed by some `Sig`-stable, fixed-point partition. The
construction uses the branching-bisimilarity quotient as both the partition and (via `Tag = Block`)
the inert-τ hash, and defines `sigFn` by well-founded recursion on the τ-relation.

Mirrors `BranchingBisimilarity.branchingFixPoint` from `Signature_Proofs.lean`. -/

namespace BranchingBisimilarity

/-- Setoid on `State` given by branching bisimilarity (uses `refl`, `symm`, `trans` from
`BranchingBisimilarity_Transitivity`). -/
private def brSetoid [Cslib.HasTau Label] (lts : Cslib.LTS State Label) : Setoid State :=
  ⟨fun a b => BranchingBisimilarity lts a b,
   ⟨BranchingBisimilarity.refl,
    fun {_ _} => BranchingBisimilarity.symm,
    fun {_ _ _} => BranchingBisimilarity.trans⟩⟩

/-- One step of the `Sig` recurrence, expressed parametrically in `sigFn`. Compared with `Sig`,
the existential is rephrased as `∃ p : Subtype …` so that the recursive call to `sigFn` (with
its required `lts.Tr` proof) is well-typed inside the predicate. The two existentials are
propositionally equivalent — see `buildSig_eq_Sig` below. -/
private def sigStep [Cslib.HasTau Label] (lts : Cslib.LTS State Label)
    {Block : Type _} (partition : State → Block)
    (s : State) (ih : ∀ s', lts.Tr s Cslib.HasTau.τ s' → Set (Label × (Block ⊕ Block))) :
    Set (Label × (Block ⊕ Block)) :=
  open Classical in
  if h : ∃ p : Subtype (fun s' => lts.Tr s Cslib.HasTau.τ s'),
              partition s = partition p.val ∧
              PreSig lts partition partition s ⊆
                ih p.val p.property ∪ {(Cslib.HasTau.τ, Sum.inr (partition p.val))} then
    ih h.choose.val h.choose.property
  else
    PreSig lts partition partition s

/-- The `sigFn` witness used in the converse: well-founded recursion on the τ-relation with the
one-step operator `sigStep`. The well-foundedness from `TauLoopFree` ensures termination. -/
private noncomputable def buildSig [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) {Block : Type _} (partition : State → Block) :
    State → Set (Label × (Block ⊕ Block)) :=
  hWF.fix (fun s ih => sigStep lts partition s ih)

private theorem buildSig_unfold [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) {Block : Type _} (partition : State → Block) (s : State) :
    buildSig hWF partition s =
      sigStep lts partition s (fun s' _ => buildSig hWF partition s') := by
  unfold buildSig
  exact WellFounded.fix_eq hWF _ s

/-- **`buildSig` satisfies the `Sig` fixed-point equation.** Both sides use a (propositionally
equivalent) existential for the delegation check. With `buildSig` bisim-stable, the choices made
by the two `.choose` operations yield the same `buildSig` value (both witnesses are inert
τ-successors of `s`, hence in the same bisim class). -/
private theorem buildSig_eq_Sig [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts)
    (hStable : ∀ a b : State,
      Quotient.mk (brSetoid lts) a = Quotient.mk (brSetoid lts) b →
      buildSig hWF (Quotient.mk (brSetoid lts)) a =
        buildSig hWF (Quotient.mk (brSetoid lts)) b)
    (s : State) :
    buildSig hWF (Quotient.mk (brSetoid lts)) s =
      Sig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts))
        (buildSig hWF (Quotient.mk (brSetoid lts))) s := by
  set π : State → Quotient (brSetoid lts) := Quotient.mk (brSetoid lts)
  set sigFn := buildSig hWF π
  rw [show sigFn s = sigStep lts π s (fun s' _ => sigFn s') from buildSig_unfold hWF π s]
  unfold sigStep Sig
  -- Both `if` conditions are propositionally equivalent existentials.
  by_cases hQ : ∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ π s = π s' ∧
                PreSig lts π π s ⊆ sigFn s' ∪ {(Cslib.HasTau.τ, Sum.inr (π s'))}
  · -- Both delegate.
    have hP : ∃ p : Subtype (fun s' => lts.Tr s Cslib.HasTau.τ s'),
                π s = π p.val ∧
                PreSig lts π π s ⊆ sigFn p.val ∪ {(Cslib.HasTau.τ, Sum.inr (π p.val))} := by
      obtain ⟨s', hTr, hπ, hSub⟩ := hQ
      exact ⟨⟨s', hTr⟩, hπ, hSub⟩
    rw [dif_pos hP, dif_pos hQ]
    -- Both `.choose` witnesses are inert τ-successors of s; by stability their buildSigs agree.
    apply hStable
    exact hP.choose_spec.1.symm.trans hQ.choose_spec.2.1
  · -- Neither delegates.
    have hP : ¬ ∃ p : Subtype (fun s' => lts.Tr s Cslib.HasTau.τ s'),
                π s = π p.val ∧
                PreSig lts π π s ⊆ sigFn p.val ∪ {(Cslib.HasTau.τ, Sum.inr (π p.val))} := by
      intro ⟨⟨s', hTr⟩, hπ, hSub⟩
      exact hQ ⟨s', hTr, hπ, hSub⟩
    rw [dif_neg hP, dif_neg hQ]

end BranchingBisimilarity

namespace BranchingBisimilarity

/-- **Path inertness (helper lemma).** In a τ-loop-free LTS with the branching-bisimilarity
quotient as the partition, any τ*-path between same-block states stays within that block
(every intermediate state has the same block as the endpoints).

Proof strategy: double well-founded induction on `(y, x)` in τ-WF, then split the head step
with `ReflTransGen.cases_head` and extract a concrete BB via `Quotient.exact`. The forward
BB match has two shapes:
* `Or.inl` (inert): `r x_first y` directly. Closed below — partition equality gives `⟦x_first⟧
  = ⟦x⟧`, recurse on the tail with `ih_x`, prepend the head step.
* `Or.inr` (matched-with-τ-prefix): `y →τ*→ t →τ→ t'` with `t ≈br x`, `t' ≈br x_first`.
  Still open; requires further nested case analysis on the matching path (see plan below).

The argument is the formal version of the classical "stuttering" property of branching
bisimulation under τ-loop-freeness (van Glabbeek–Weijland 1996). -/
private theorem path_inertness [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) :
    ∀ {x y : State}, lts.τSTr x y →
      Quotient.mk (brSetoid lts) x = Quotient.mk (brSetoid lts) y →
      Relation.ReflTransGen
        (fun u v => lts.Tr u Cslib.HasTau.τ v ∧
          Quotient.mk (brSetoid lts) u = Quotient.mk (brSetoid lts) x ∧
          Quotient.mk (brSetoid lts) v = Quotient.mk (brSetoid lts) x)
        x y := by
  -- Double WF induction: outer on `y` (path endpoint), inner on `x` (path start).
  intro x y
  revert x
  apply WellFounded.induction hWF y
  intro y' ih_y x
  apply WellFounded.induction hWF x
  intro x' ih_x hPath hπ
  -- Split the path into empty | head step `x' →τ→ x₁ →τ*→ y'`.
  rcases Relation.ReflTransGen.cases_head hPath with hEq | ⟨x₁, hFirst, hTail⟩
  · subst hEq; exact Relation.ReflTransGen.refl
  -- Extract a concrete bisimulation `r` witnessing `x' ≈br y'`, then forward-match the
  -- head step `x' →τ→ x₁` along it.
  obtain ⟨r, hrxy, hBis⟩ := Quotient.exact hπ
  rcases (hBis hrxy Cslib.HasTau.τ).1 x₁ hFirst with
    ⟨-, hrx₁y'⟩ | ⟨t, t', hSTr, hTrt, hrxt, hrx₁t'⟩
  · -- CASE A (Or.inl, `r x₁ y'`): head step is inert. Closed.
    have hπx₁y' := Quotient.sound (s := brSetoid lts) ⟨r, hrx₁y', hBis⟩
    have hπx₁ : ⟦x₁⟧ = ⟦x'⟧ := hπx₁y'.trans hπ.symm
    have htail := ih_x x₁ hFirst hTail hπx₁y'
    exact Relation.ReflTransGen.head ⟨hFirst, rfl, hπx₁⟩
      (htail.mono (fun u v ⟨htr, hu, hv⟩ => ⟨htr, hu.trans hπx₁, hv.trans hπx₁⟩))
  -- CASE B (Or.inr): matched path `y' →τ*→ t →τ→ t'` with `r x' t`, `r x₁ t'`.
  --
  -- Difficulties hit during the previous attempt:
  --   (D1) Case explosion. Splitting hSTr with cases_head, then doing backward BB on the
  --        emerging step, then splitting *that* match's τ-prefix, yields 5 leaves
  --        (B.1.inl, B.1.inr.{trivial-x, non-trivial-x}, B.2.inl, B.2.inr). Each is
  --        ultimately closed by an ih_x or ih_y call, but the bookkeeping is heavy.
  --   (D2) Partition retargeting. The goal's ReflTransGen embeds `⟦u⟧ = ⟦x'⟧`, but each
  --        IH instantiates the relation at a fresh start (ih_y at the new x, ih_x at
  --        the new path start). Every recursive result must be transported with
  --        `.mono` and a chained `.trans hπ?` on both partition components.
  --   (D3) WF descent shape. ih_x and ih_y descend on a single `lts.Tr · τ ·` step, not
  --        the τ-transitive closure. B.1.inr's witness `x' →τ*→ x_p →τ→ x_p''` only
  --        gives `x_p'' < x'` when the x-side prefix is empty; otherwise we must peel
  --        a head with `cases_head` and feed only that head to `ih_x`, dispatching
  --        the rest via ih_x's own inner WF.
  --   (D4) No reduction to `LTS.IsBranchingBisimulation.stutter`. Stutter mimics a
  --        τ-path on the *opposite* side; it does not assert partition agreement at
  --        intermediate states, so it cannot replace the WF argument here.
  --
  -- Refined plan for Case B (each leaf is independent; tackle in this order):
  --   Pre-work — extract two helpers to compress the leaf bodies:
  --     (H1) `inert_step (hrst : r s t) (hrs't : r s' t) : ⟦s⟧ = ⟦s'⟧`
  --          — two `Quotient.sound` calls glued by `.trans .symm`.
  --     (H2) `mono_partition (h : ⟦α⟧ = ⟦β⟧)`
  --          — wraps the standard `.mono` cast through both partition components
  --          so each leaf's final move becomes a single `apply`.
  --
  --   Leaf order (easiest first):
  --     1. B.1.inl  — trivial y-prefix (t = y'), backward BB at y' →τ→ t' gives r x' t';
  --                   then H1 with hrx₁t' yields ⟦x'⟧ = ⟦x₁⟧ → step inert → ih_x.
  --     2. B.2.inl  — non-trivial y-prefix splits y' →τ→ y₁ →τ*→ t; backward BB at
  --                   y' →τ→ y₁ Or.inl gives r x' y₁; ih_y at y₁ closes the tail.
  --     3. B.1.inr.non-trivial-x — x' →τ→ x₁_first →τ*→ x_p; ih_x on x₁_first reaches x_p.
  --     4. B.1.inr.trivial-x    — x' →τ→ x_p''; recurse via ih_x on the produced step
  --                                (most delicate — last).
  --     5. B.2.inr  — backward BB at y' →τ→ y₁; reassembled from leaves above.
  --
  -- If H1+H2 don't tame the casework, fall back to reformulating the induction as a
  -- single `WellFounded.induction` over `Prod.lex hWF hWF` on `(y, x)`; this unifies
  -- ih_x/ih_y into one IH that admits descent in either coordinate uniformly.
  --
  -- Helper: two `r`-relations to the same state give partition equality.
  have bisEq : ∀ {s u s' : State}, r s u → r s' u →
      (Quotient.mk (brSetoid lts) s : Quotient (brSetoid lts)) = Quotient.mk (brSetoid lts) s' :=
    fun h1 h2 =>
      (Quotient.sound (s := brSetoid lts) ⟨r, h1, hBis⟩).trans
        (Quotient.sound (s := brSetoid lts) ⟨r, h2, hBis⟩).symm
  -- Strategy: reduce to `⟦x'⟧ = ⟦x₁⟧` (i.e., the original step `x' →τ→ x₁` is inert).
  -- WARNING: this reduction is too strong in general — the original step may be non-inert
  -- (the BB matching's Or.inr branch handles non-inert steps via the y-side path), in which
  -- case `⟦x'⟧ ≠ ⟦x₁⟧` and a DIFFERENT inert first step from x' must be constructed.
  -- The inner lemma below is therefore only correct in a restricted context, and the deep
  -- recursion case still contains a `sorry`. A complete proof needs to drop this reduction
  -- and instead construct the inert path's first step directly from the BB matching data.
  suffices hπx₁ : (Quotient.mk (brSetoid lts) x' : Quotient (brSetoid lts)) =
      Quotient.mk (brSetoid lts) x₁ by
    have hπx₁y' :
        (Quotient.mk (brSetoid lts) x₁ : Quotient (brSetoid lts)) = Quotient.mk (brSetoid lts) y' :=
      hπx₁.symm.trans hπ
    have htail := ih_x x₁ hFirst hTail hπx₁y'
    exact Relation.ReflTransGen.head ⟨hFirst, rfl, hπx₁.symm⟩
      (htail.mono (fun u v ⟨htr, hu, hv⟩ => ⟨htr, hu.trans hπx₁.symm, hv.trans hπx₁.symm⟩))
  -- Inner WF induction on `t` via the transitive closure of τ-step:
  -- in `r a tInner` paired with a forward step `tInner →τ→ tNext` to `r b tNext`, the partition
  -- equality `⟦a⟧ = ⟦b⟧` follows by nested BB matching. Using TransGen WF lets us apply IH at
  -- any τ-descendant of tInner (multi-step), not just direct successors.
  -- We instantiate it with `(t, x', t', x₁)` to obtain `⟦x'⟧ = ⟦x₁⟧`.
  have inner : ∀ (tInner : State),
      ∀ (a b tNext : State), r a tInner → lts.Tr tInner Cslib.HasTau.τ tNext → r b tNext →
        (Quotient.mk (brSetoid lts) a : Quotient (brSetoid lts)) = Quotient.mk (brSetoid lts) b := by
    intro tInner
    induction tInner using WellFounded.induction (WellFounded.transGen hWF) with
    | _ tInner IH_t =>
      intro a b tNext hra hStep hrb
      -- Backward BB at `tInner →τ→ tNext` via `r a tInner`.
      rcases (hBis hra Cslib.HasTau.τ).2 tNext hStep with ⟨_, hrat'⟩ | ⟨xp, xp', hPathXp, hStepXp, hrXpt, hrXp't'⟩
      · -- Or.inl: r a tNext. ⟦a⟧ = ⟦tNext⟧ = ⟦b⟧.
        exact bisEq hrat' hrb
      · -- Or.inr: a →τ*→ xp →τ→ xp', r xp tInner, r xp' tNext.
        -- Forward BB on `r xp tInner` at step `xp →τ→ xp'`.
        rcases (hBis hrXpt Cslib.HasTau.τ).1 xp' hStepXp with ⟨_, hrxp't⟩ | ⟨tq, tq', hPathTq, hStepTq, hrXptq, hrXp'tq'⟩
        · -- Or.inl: r xp' tInner. ⟦xp'⟧ = ⟦tInner⟧ = ⟦a⟧, and ⟦xp'⟧ = ⟦tNext⟧ = ⟦b⟧.
          exact (bisEq hra hrxp't).trans (bisEq hrXp't' hrb)
        · -- Or.inr: tInner →τ*→ tq →τ→ tq'. r xp tq. r xp' tq'.
          -- Convert hPathTq from STr to τSTr (ReflTransGen).
          have hPathTq' : Relation.ReflTransGen (Cslib.LTS.Tr.toRelation lts Cslib.HasTau.τ) tInner tq :=
            (Cslib.LTS.sTr_τSTr lts).mp hPathTq
          -- Case split on whether tInner = tq.
          rcases Relation.ReflTransGen.cases_head hPathTq' with hEq | ⟨tMid, hHead, hRest⟩
          · -- Trivial t-path: tInner = tq. New step tInner →τ→ tq'.
            subst hEq
            -- Recurse: apply backward BB on tInner →τ→ tq' via r xp tInner, then forward etc.
            -- We can use the IH only when the new step's source is strictly smaller in WF.
            -- Here the source is still tInner, so we can't use IH_t directly.
            -- Instead: apply backward BB on tInner →τ→ tq' via r a tInner (re-using hra).
            rcases (hBis hra Cslib.HasTau.τ).2 tq' hStepTq with ⟨_, hratq'⟩ | ⟨xr, xr', hPathXr, hStepXr, hrXrt, hrXr'tq'⟩
            · -- Or.inl: r a tq'. ⟦a⟧ = ⟦tq'⟧ = ⟦xp'⟧ = ⟦tNext⟧ = ⟦b⟧.
              exact (bisEq hratq' hrXp'tq').trans (bisEq hrXp't' hrb)
            · -- Or.inr: a →τ*→ xr →τ→ xr'. r xr tInner. r xr' tq'.
              -- Forward BB on r xr tInner at step xr →τ→ xr'.
              rcases (hBis hrXrt Cslib.HasTau.τ).1 xr' hStepXr with ⟨_, hrxr't⟩ | ⟨ts, ts', hPathTs, hStepTs, hrXrts, hrXr'ts'⟩
              · -- Or.inl: r xr' tInner. ⟦xr'⟧ = ⟦tInner⟧ = ⟦a⟧.
                -- ⟦xr'⟧ = ⟦tq'⟧ = ⟦xp'⟧ = ⟦tNext⟧ = ⟦b⟧.
                exact (bisEq hra hrxr't).trans
                  ((bisEq hrXr'tq' hrXp'tq').trans (bisEq hrXp't' hrb))
              · -- Or.inr deep: tInner →τ*→ ts →τ→ ts'. r xr ts. r xr' ts'.
                -- Case split on whether ts = tInner (trivial path) or not.
                have hPathTs' : Relation.ReflTransGen
                    (Cslib.LTS.Tr.toRelation lts Cslib.HasTau.τ) tInner ts :=
                  (Cslib.LTS.sTr_τSTr lts).mp hPathTs
                rcases Relation.ReflTransGen.cases_head hPathTs' with hEqTs | ⟨tMid2, hHead2, hRest2⟩
                · -- Trivial ts-path: ts = tInner. New step tInner →τ→ ts'.
                  -- ============================================================================
                  -- PLAN FOR CLOSING THIS CASE
                  -- ============================================================================
                  -- Context arriving here (all paths trivial on the t-side so far):
                  --   r a tInner, r xp tInner, r xr tInner, r xr' ts' with
                  --   tInner →τ→ tNext (original step matched as Or.inr → tInner →τ→ tq'
                  --   matched again as Or.inr → tInner →τ→ ts' matched as Or.inr → ...).
                  --
                  -- The cascade can continue indefinitely: each nested Or.inr generates
                  --   (i) a fresh τ-successor of tInner (ts', then t_u', t_v', …), and
                  --   (ii) a fresh BB-related x-state (xr, then xq, …),
                  -- none of which is forced to be strictly smaller in any single argument's
                  -- WF: tInner is fixed, and the new x-states can equal `a` in the trivial
                  -- x-path sub-cases.
                  --
                  -- FUNDAMENTAL OBSTACLE: the local `inner` lemma in its current form is
                  -- *too strong* — it claims `r a tInner → tInner →τ→ tNext → r b tNext →
                  -- ⟦a⟧ = ⟦b⟧`, which is false whenever the step `tInner →τ→ tNext` is
                  -- non-inert. (In path_inertness's Case B, the matched step is non-inert
                  -- precisely when the original `x' →τ→ x₁` is non-inert; Case A would
                  -- otherwise apply.) The `suffices ⟦x'⟧ = ⟦x₁⟧` reduction above is
                  -- therefore unsound in general, and any proof of `inner` that closes
                  -- this case would actually prove `False` in the non-inert scenario.
                  --
                  -- RECOMMENDED FIX: abandon the `suffices ⟦x'⟧ = ⟦x₁⟧` reduction and
                  -- instead build the target `ReflTransGen` directly:
                  --   (a) If `x' = y'`: done by `ReflTransGen.refl`.
                  --   (b) Otherwise, locate *some* inert τ-successor `x_inert` of `x'`
                  --       (i.e., a state with `x' →τ→ x_inert` and `⟦x_inert⟧ = ⟦x'⟧`).
                  --       Such a state is yielded by repeated BB matching in the
                  --       Or.inr Or.inl branches (forward BB on the matched x-side path
                  --       gives `r x_p' t` whenever the matching closes there).
                  --   (c) Establish an inert path `x_inert →τ*→ y'`. The construction is
                  --       NOT a sub-path of the original `hPath`; it must be assembled
                  --       from BB-matching data on both sides. The classical approach
                  --       (van Glabbeek–Weijland 1996; Basten 1996) is the "computation
                  --       lemma": given BB `r s t` and `s →τ*→ s'`, produce a parallel
                  --       chain on the t-side whose intermediate states are all bisim
                  --       to corresponding states on the s-side. Then transfer back.
                  --   (d) Recurse on `x_inert →τ*→ y'` via `ih_x` (now legitimately
                  --       applicable because `⟦x_inert⟧ = ⟦y'⟧` by construction).
                  --
                  -- ALTERNATIVE: restructure the WF induction. The current nested
                  -- `WellFounded.induction hWF` (outer on y', inner on x') admits descent
                  -- in only one coordinate at a time. A `Prod.lex hWF hWF` induction on
                  -- `(y', x')` (or even on `(rank y', rank x', rank t)` with appropriate
                  -- lex ordering) plus a stronger generalized statement may absorb the
                  -- cascade. See the original comment block at lines 286–324 for the
                  -- previously contemplated leaf order.
                  --
                  -- For now this case is left unproven; the rest of the proof builds.
                  sorry
                · -- Non-trivial ts-path: tInner →τ→ tMid2 →τ*→ ts. ts < tInner in TransGen WF.
                  have hTsLt :
                      Relation.TransGen (fun s' s => lts.Tr s Cslib.HasTau.τ s') ts tInner := by
                    have aux : ∀ {z}, Relation.ReflTransGen
                        (Cslib.LTS.Tr.toRelation lts Cslib.HasTau.τ) tMid2 z →
                        Relation.TransGen (fun s' s => lts.Tr s Cslib.HasTau.τ s') z tInner := by
                      intro z h
                      induction h with
                      | refl => exact Relation.TransGen.single hHead2
                      | tail _ hLast ih => exact Relation.TransGen.head hLast ih
                    exact aux hRest2
                  have hπxrxr' := IH_t ts hTsLt xr xr' ts' hrXrts hStepTs hrXr'ts'
                  -- ⟦a⟧ = ⟦xr⟧ (bisEq via tInner) = ⟦xr'⟧ (IH) = ⟦tq'⟧ (bisEq) = ⟦xp'⟧ (bisEq)
                  --      = ⟦tNext⟧ (bisEq) = ⟦b⟧.
                  exact (bisEq hra hrXrt).trans
                    (hπxrxr'.trans ((bisEq hrXr'tq' hrXp'tq').trans (bisEq hrXp't' hrb)))
          · -- Non-trivial t-path: tInner →τ→ tMid →τ*→ tq.
            -- tq is a strict τ-descendant of tInner via TransGen, so IH_t applies at tq.
            -- IH_t at tq gives: ∀ a' b' tNext', r a' tq → tq →τ→ tNext' → r b' tNext' → ⟦a'⟧ = ⟦b'⟧.
            -- Apply with (xp, xp', tq'): ⟦xp⟧ = ⟦xp'⟧.
            -- Then ⟦a⟧ = ⟦xp⟧ (bisEq via tInner) = ⟦xp'⟧ (IH) = ⟦tNext⟧ = ⟦b⟧.
            have hTqLt : Relation.TransGen (fun s' s => lts.Tr s Cslib.HasTau.τ s') tq tInner := by
              -- Build TransGen from tInner →τ→ tMid →τ*→ tq via an isolated auxiliary lemma.
              have aux : ∀ {z}, Relation.ReflTransGen
                  (Cslib.LTS.Tr.toRelation lts Cslib.HasTau.τ) tMid z →
                  Relation.TransGen (fun s' s => lts.Tr s Cslib.HasTau.τ s') z tInner := by
                intro z h
                induction h with
                | refl => exact Relation.TransGen.single hHead
                | tail _ hLast ih => exact Relation.TransGen.head hLast ih
              exact aux hRest
            have hπxpxp' := IH_t tq hTqLt xp xp' tq' hrXptq hStepTq hrXp'tq'
            exact (bisEq hra hrXpt).trans
              (hπxpxp'.trans (bisEq hrXp't' hrb))
  -- Apply the inner lemma to (t, x', x₁, t').
  exact inner t x' x₁ t' hrxt hTrt hrx₁t'

/-- **Corollary.** If a state has no inert τ-successor and a τ*-path returns to the same block,
the path must be trivial (length 0). Direct consequence of `path_inertness`. -/
private theorem noInertSucc_path_trivial [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) {x y : State} (hPath : lts.τSTr x y)
    (hπ : Quotient.mk (brSetoid lts) x = Quotient.mk (brSetoid lts) y)
    (hNoInert : ∀ x', lts.Tr x Cslib.HasTau.τ x' →
       Quotient.mk (brSetoid lts) x ≠ Quotient.mk (brSetoid lts) x') :
    x = y := by
  have hInert := path_inertness hWF hPath hπ
  rcases hInert.cases_head with hEq | ⟨xFirst, ⟨hTr, _, hπFirst⟩, _⟩
  · exact hEq
  · exact absurd hπFirst.symm (hNoInert xFirst hTr)

/-- **BB direct match (helper for stability).** If `a ≈br b` (in bisim quotient) and `b` has no
inert τ-successor, then any non-inert direct transition out of `a` is matched directly (without
τ-prefix) by `b`.

This is the key lemma that lets us reason about `PreSig a = PreSig b` without going through the
full path-inertness machinery at every use site: the BB matching's τ-prefix on `b`'s side is
forced to be trivial by `noInertSucc_path_trivial`. -/
private theorem direct_match_via_no_inert [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) {a b : State}
    (hab : Quotient.mk (brSetoid lts) a = Quotient.mk (brSetoid lts) b)
    (hb_no_inert : ∀ b' (_ : lts.Tr b Cslib.HasTau.τ b'),
      Quotient.mk (brSetoid lts) b ≠ Quotient.mk (brSetoid lts) b')
    {μ : Label} {t : State}
    (hStep : lts.Tr a μ t)
    (hSide : μ ≠ Cslib.HasTau.τ ∨
      Quotient.mk (brSetoid lts) a ≠ Quotient.mk (brSetoid lts) t) :
    ∃ t', lts.Tr b μ t' ∧
      Quotient.mk (brSetoid lts) t = Quotient.mk (brSetoid lts) t' := by
  obtain ⟨r, hrab, hrBis⟩ := Quotient.exact hab
  rcases (hrBis hrab μ).1 _ hStep with
    ⟨hμτ, hrTB⟩ | ⟨bPre, bPre', hSTr, hStep', hrAbpre, hrTBpre⟩
  · -- Or.inl: contradicts `hSide`.
    exfalso
    have hπtb : Quotient.mk (brSetoid lts) t = Quotient.mk (brSetoid lts) b :=
      Quotient.sound (s := brSetoid lts) ⟨r, hrTB, hrBis⟩
    rcases hSide with hMu | hPi
    · exact hMu hμτ
    · exact hPi (hπtb.trans hab.symm).symm
  · -- Or.inr: τ-prefix on `b`'s side is forced to be trivial.
    have hPath := (Cslib.LTS.sTr_τSTr lts).mp hSTr
    have hπBBpre : Quotient.mk (brSetoid lts) b = Quotient.mk (brSetoid lts) bPre :=
      hab.symm.trans (Quotient.sound (s := brSetoid lts) ⟨r, hrAbpre, hrBis⟩)
    have hBEq : b = bPre := noInertSucc_path_trivial hWF hPath hπBBpre hb_no_inert
    subst hBEq
    exact ⟨bPre', hStep',
      Quotient.sound (s := brSetoid lts) ⟨r, hrTBpre, hrBis⟩⟩

/-- If `⟦a⟧ = ⟦b⟧` and `a` has no inert τ-successor, then `PreSig b ⊆ PreSig a ∪ {inert-tag}`.
This absorption condition is used in `buildSig_stable` to derive a contradiction when `b` has
an inert τ-successor in the "neither delegates" case. -/
private theorem preSig_subset_via_bisim [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) {a b b' : State}
    (hab : Quotient.mk (brSetoid lts) a = Quotient.mk (brSetoid lts) b)
    (hπbb' : Quotient.mk (brSetoid lts) b = Quotient.mk (brSetoid lts) b')
    (ha_no_inert : ∀ a' (_ : lts.Tr a Cslib.HasTau.τ a'),
        Quotient.mk (brSetoid lts) a ≠ Quotient.mk (brSetoid lts) a') :
    PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) b ⊆
      PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) a ∪
        {(Cslib.HasTau.τ, Sum.inr (Quotient.mk (brSetoid lts) b'))} := by
  rintro x (⟨μ, t, hTrBt, hSide, hPair⟩ | ⟨t, hTrBt, hπbt, hPair⟩)
  · obtain ⟨t', hTrAt', hπtt'⟩ := direct_match_via_no_inert hWF hab.symm ha_no_inert hTrBt hSide
    exact Or.inl (Or.inl ⟨μ, t', hTrAt',
        hSide.imp_right (fun hPi heq => hPi (hab.symm.trans (heq.trans hπtt'.symm))),
        by cases hPair; simp [hπtt']⟩)
  · exact Or.inr (Set.mem_singleton_iff.mpr (by cases hPair; simp [hπbt.symm.trans hπbb']))

/-- If `⟦a⟧ = ⟦b⟧` and neither `a` nor `b` has an inert τ-successor, then `PreSig a = PreSig b`.
Bidirectional subset via `direct_match_via_no_inert`; inert-τ elements from each side are
excluded by the respective no-inert hypothesis. -/
private theorem preSig_eq_of_bisim_noInert [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) {a b : State}
    (hab : Quotient.mk (brSetoid lts) a = Quotient.mk (brSetoid lts) b)
    (ha_no_inert : ∀ a' (_ : lts.Tr a Cslib.HasTau.τ a'),
        Quotient.mk (brSetoid lts) a ≠ Quotient.mk (brSetoid lts) a')
    (hb_no_inert : ∀ b' (_ : lts.Tr b Cslib.HasTau.τ b'),
        Quotient.mk (brSetoid lts) b ≠ Quotient.mk (brSetoid lts) b') :
    PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) a =
    PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) b := by
  ext ⟨μ, x⟩
  constructor
  · rintro (⟨μ', t, hTrAt, hSide, hPair⟩ | ⟨t, hTrAt, hπat, _⟩)
    · obtain ⟨t', hTrBt', hπtt'⟩ := direct_match_via_no_inert hWF hab hb_no_inert hTrAt hSide
      exact Or.inl ⟨μ', t', hTrBt',
          hSide.imp_right (fun hPi heq => hPi (hab.trans (heq.trans hπtt'.symm))),
          by cases hPair; simp [hπtt']⟩
    · exact absurd hπat (ha_no_inert t hTrAt)
  · rintro (⟨μ', t, hTrBt, hSide, hPair⟩ | ⟨t, hTrBt, hπbt, _⟩)
    · obtain ⟨t', hTrAt', hπtt'⟩ := direct_match_via_no_inert hWF hab.symm ha_no_inert hTrBt hSide
      exact Or.inl ⟨μ', t', hTrAt',
          hSide.imp_right (fun hPi heq => hPi (hab.symm.trans (heq.trans hπtt'.symm))),
          by cases hPair; simp [hπtt']⟩
    · exact absurd hπbt (hb_no_inert t hTrBt)

/-- **Bisim stability of `buildSig`.** With the branching-bisimilarity quotient as the partition,
states in the same block have equal `buildSig` value.

Proof: nested well-founded induction on the τ-relation (outer on `a`, inner on `b`). The
load-bearing observation in the "neither delegates" case is: if `a` were to have an inert
τ-successor `a'`, the outer IH would give `buildSig a' = buildSig a = PreSig a` and absorption
at `a'` would trivially hold (`PreSig a ⊆ PreSig a ∪ {…}`), forcing `a` to delegate —
contradicting the case. The symmetric argument rules out inert τ-successors of `b` via the
inner IH. With no inert τ-successors on either side, branching bisimulation matches direct
transitions with trivial τ-prefix (by `noInertSucc_path_trivial`), so `PreSig a = PreSig b`. -/
private theorem buildSig_stable [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) :
    ∀ a b : State, Quotient.mk (brSetoid lts) a = Quotient.mk (brSetoid lts) b →
      buildSig hWF (Quotient.mk (brSetoid lts)) a =
        buildSig hWF (Quotient.mk (brSetoid lts)) b := by
  intro a
  induction a using WellFounded.induction hWF with
  | _ a IH_a =>
    intro b
    induction b using WellFounded.induction hWF with
    | _ b IH_b =>
      intro hab
      have ha_unfold :
          buildSig hWF (Quotient.mk (brSetoid lts)) a =
            sigStep lts (Quotient.mk (brSetoid lts)) a
              (fun s' _ => buildSig hWF (Quotient.mk (brSetoid lts)) s') :=
        buildSig_unfold hWF _ a
      have hb_unfold :
          buildSig hWF (Quotient.mk (brSetoid lts)) b =
            sigStep lts (Quotient.mk (brSetoid lts)) b
              (fun s' _ => buildSig hWF (Quotient.mk (brSetoid lts)) s') :=
        buildSig_unfold hWF _ b
      -- Case analysis on whether a delegates.
      by_cases hAbsA :
          ∃ p : Subtype (fun s' => lts.Tr a Cslib.HasTau.τ s'),
            Quotient.mk (brSetoid lts) a = Quotient.mk (brSetoid lts) p.val ∧
            PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) a ⊆
              buildSig hWF (Quotient.mk (brSetoid lts)) p.val ∪
                {(Cslib.HasTau.τ, Sum.inr (Quotient.mk (brSetoid lts) p.val))}
      · -- Case 1: a delegates to a' = hAbsA.choose.val. Use outer IH on (a', b).
        have ha_eq :
            buildSig hWF (Quotient.mk (brSetoid lts)) a =
              buildSig hWF (Quotient.mk (brSetoid lts)) hAbsA.choose.val := by
          rw [ha_unfold]; unfold sigStep; exact dif_pos hAbsA
        have ha'_tr : lts.Tr a Cslib.HasTau.τ hAbsA.choose.val := hAbsA.choose.property
        have hπa'b : Quotient.mk (brSetoid lts) hAbsA.choose.val =
                     Quotient.mk (brSetoid lts) b :=
          hAbsA.choose_spec.1.symm.trans hab
        rw [ha_eq]
        exact IH_a _ ha'_tr _ hπa'b
      · -- Case 2: a does not delegate, so sigFn a = PreSig a.
        have ha_eq :
            buildSig hWF (Quotient.mk (brSetoid lts)) a =
              PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) a := by
          rw [ha_unfold]; unfold sigStep; exact dif_neg hAbsA
        by_cases hAbsB :
            ∃ p : Subtype (fun s' => lts.Tr b Cslib.HasTau.τ s'),
              Quotient.mk (brSetoid lts) b = Quotient.mk (brSetoid lts) p.val ∧
              PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) b ⊆
                buildSig hWF (Quotient.mk (brSetoid lts)) p.val ∪
                  {(Cslib.HasTau.τ, Sum.inr (Quotient.mk (brSetoid lts) p.val))}
        · -- Sub-case 2a: b delegates. Use inner IH on (a, b').
          have hb_eq :
              buildSig hWF (Quotient.mk (brSetoid lts)) b =
                buildSig hWF (Quotient.mk (brSetoid lts)) hAbsB.choose.val := by
            rw [hb_unfold]; unfold sigStep; exact dif_pos hAbsB
          have hb'_tr : lts.Tr b Cslib.HasTau.τ hAbsB.choose.val := hAbsB.choose.property
          have hπab' : Quotient.mk (brSetoid lts) a =
                       Quotient.mk (brSetoid lts) hAbsB.choose.val :=
            hab.trans hAbsB.choose_spec.1
          rw [hb_eq]
          exact IH_b _ hb'_tr hπab'
        · -- Sub-case 2b: neither delegates. Both sides reduce to PreSig.
          rw [ha_eq]
          have hb_eq :
              buildSig hWF (Quotient.mk (brSetoid lts)) b =
                PreSig lts (Quotient.mk (brSetoid lts)) (Quotient.mk (brSetoid lts)) b := by
            rw [hb_unfold]; unfold sigStep; exact dif_neg hAbsB
          rw [hb_eq]
          -- Step 1: a has no inert τ-successor.
          -- If a had inert τ-successor a', IH_a would give sigFn a' = sigFn a = PreSig a, so
          -- absorption PreSig a ⊆ PreSig a ∪ {tag} would hold and a would delegate.
          have ha_no_inert :
              ∀ a' (_ : lts.Tr a Cslib.HasTau.τ a'),
                Quotient.mk (brSetoid lts) a ≠ Quotient.mk (brSetoid lts) a' := by
            intro a' hTra' hπaa'
            apply hAbsA
            refine ⟨⟨a', hTra'⟩, hπaa', ?_⟩
            intro x hx
            left
            rw [IH_a a' hTra' a hπaa'.symm, ha_eq]
            exact hx
          -- Step 2: b has no inert τ-successor (uses preSig_subset_via_bisim).
          have hb_no_inert :
              ∀ b' (_ : lts.Tr b Cslib.HasTau.τ b'),
                Quotient.mk (brSetoid lts) b ≠ Quotient.mk (brSetoid lts) b' := by
            intro b' hTrb' hπbb'
            apply hAbsB
            refine ⟨⟨b', hTrb'⟩, hπbb', ?_⟩
            rw [← IH_b b' hTrb' (hab.trans hπbb'), ha_eq]
            exact preSig_subset_via_bisim hWF hab hπbb' ha_no_inert
          -- Step 3: BB matches direct transitions directly; PreSig a = PreSig b.
          exact preSig_eq_of_bisim_noInert hWF hab ha_no_inert hb_no_inert

end BranchingBisimilarity

/-! ### Equivalence of `InductiveBranchingFixPoint` and `BranchingBisimilarity` -/

/-- **Forward direction.** Any pair of states in a Sig-stable, fixed-point partition (over a
τ-loop-free LTS) is branching bisimilar. -/
theorem InductiveBranchingFixPoint.branchingBisimilarity [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s s' : State} (h : InductiveBranchingFixPoint lts s s') :
    BranchingBisimilarity lts s s' := by
  obtain ⟨_, partition, _, sigHash, sigFn, hFix, hStable, hEq⟩ := h
  exact IsStable.branchingBisimilarity_inductive hWF partition sigHash sigFn hFix hStable hEq

/-- **Reverse direction.** Every pair of branching bisimilar states in a τ-loop-free LTS lies in
some `Sig`-stable fixed-point partition.

The witnesses: `Block = Tag` is the branching-bisimilarity quotient `Quotient brSetoid`,
`partition = sigHash = Quotient.mk brSetoid`, and `sigFn = buildSig` (well-founded recursion
on the τ-relation, see `BranchingBisimilarity.buildSig`). -/
theorem BranchingBisimilarity.inductiveBranchingFixPoint.{u, v}
    {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s₁ s₂ : State} (h : BranchingBisimilarity lts s₁ s₂) :
    InductiveBranchingFixPoint lts s₁ s₂ := by
  let π : State → Quotient (BranchingBisimilarity.brSetoid lts) :=
    Quotient.mk (BranchingBisimilarity.brSetoid lts)
  have hπEq : π s₁ = π s₂ := Quotient.sound (s := BranchingBisimilarity.brSetoid lts) h
  refine ⟨Quotient (BranchingBisimilarity.brSetoid lts), π,
          Quotient (BranchingBisimilarity.brSetoid lts), π,
          BranchingBisimilarity.buildSig hWF π,
          ?_, ?_, hπEq⟩
  · -- Fixed-point equation
    intro s
    exact BranchingBisimilarity.buildSig_eq_Sig hWF
      (BranchingBisimilarity.buildSig_stable hWF) s
  · -- Stability
    intro a b hab
    exact BranchingBisimilarity.buildSig_stable hWF a b hab

end InductiveSignaturesProofs
