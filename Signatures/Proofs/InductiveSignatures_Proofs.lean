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
  -- Inert/non-inert membership helper for the PreSig left branch.
  have hPreSigMem : ∀ {s t μ}, lts.Tr s μ t → (μ ≠ Cslib.HasTau.τ ∨ partition s ≠ partition t) →
      (μ, Sum.inl (partition t)) ∈ PreSig lts partition sigHash s := by
    intro s t μ hTr hSide
    exact Or.inl ⟨μ, t, hTr, hSide, rfl⟩
  -- The PreSig element survives the (possible) delegation step: it lands in sigFn s itself.
  have hInSigFn : ∀ {s t μ}, lts.Tr s μ t → (μ ≠ Cslib.HasTau.τ ∨ partition s ≠ partition t) →
      (μ, Sum.inl (partition t)) ∈ sigFn s := by
    intro s t μ hTr hSide
    have hMem : (μ, Sum.inl (partition t)) ∈ PreSig lts partition sigHash s :=
      hPreSigMem hTr hSide
    by_cases hDeleg : ∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ partition s = partition s' ∧
                PreSig lts partition sigHash s ⊆
                  sigFn s' ∪ {(Cslib.HasTau.τ, Sum.inr (sigHash s'))}
    · have hEq : sigFn s = sigFn hDeleg.choose := by
        rw [hFix s, Sig, dif_pos hDeleg]
      rw [hEq]
      obtain ⟨_, _, hSub⟩ := hDeleg.choose_spec
      rcases hSub hMem with h | h
      · exact h
      · exact nomatch (Prod.mk.inj (Set.mem_singleton_iff.mp h)).2
    · have hEq : sigFn s = PreSig lts partition sigHash s := by
        rw [hFix s, Sig, dif_neg hDeleg]
      rw [hEq]; exact hMem
  intro s₁ s₂ hRel μ
  refine ⟨?_, ?_⟩
  · intro t₁ hTr₁
    by_cases hInert : μ = Cslib.HasTau.τ ∧ partition t₁ = partition s₁
    · exact Or.inl ⟨hInert.1, hInert.2.trans hRel⟩
    · have hSide : μ ≠ Cslib.HasTau.τ ∨ partition s₁ ≠ partition t₁ := by
        rcases Classical.em (μ = Cslib.HasTau.τ) with hμ | hμ
        · exact Or.inr fun h => hInert ⟨hμ, h.symm⟩
        · exact Or.inl hμ
      have hMem1 : (μ, Sum.inl (partition t₁)) ∈ sigFn s₁ := hInSigFn hTr₁ hSide
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
      have hMem2 : (μ, Sum.inl (partition t₂)) ∈ sigFn s₂ := hInSigFn hTr₂ hSide
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

/-- **Bisim stability of `buildSig`.** With the branching-bisimilarity quotient as the partition,
states in the same block have equal `buildSig` value.

Proof: nested well-founded induction on the τ-relation (outer on `a`, inner on `b`). The
load-bearing observation in the "neither delegates" case is: if `a` were to have an inert
τ-successor `a'`, the outer IH would give `buildSig a' = buildSig a = PreSig a` and absorption
at `a'` would trivially hold (`PreSig a ⊆ PreSig a ∪ {…}`), forcing `a` to delegate —
contradicting the case. The symmetric argument rules out inert τ-successors of `b` via the
inner IH. With no inert τ-successors on either side, branching bisimulation matches direct
transitions with trivial τ-prefix, so `PreSig a = PreSig b`. -/
private theorem buildSig_stable [Cslib.HasTau Label] {lts : Cslib.LTS State Label}
    (hWF : TauLoopFree lts) :
    ∀ a b : State, Quotient.mk (brSetoid lts) a = Quotient.mk (brSetoid lts) b →
      buildSig hWF (Quotient.mk (brSetoid lts)) a =
        buildSig hWF (Quotient.mk (brSetoid lts)) b := by
  -- Proof outline (nested well-founded induction on the τ-relation, outer on `a`, inner on `b`):
  --
  -- Let π = Quotient.mk (brSetoid lts) and sigFn = buildSig hWF π. Case-analyze whether a has an
  -- absorbing inert τ-successor (call this the "delegation predicate" hAbsA), and similarly hAbsB.
  --
  -- * Case 1 (a delegates to a' := hAbsA.choose.val): sigFn a = sigFn a'. Outer IH on
  --   (a', b) — using π a' = π a = π b — gives sigFn a' = sigFn b. Combine.
  --
  -- * Case 2 + sub-case 2a (a doesn't delegate, b delegates to b'): symmetric — sigFn b = sigFn b',
  --   and inner IH on b' gives sigFn a = sigFn b'.
  --
  -- * Case 2 + sub-case 2b (neither delegates): sigFn a = PreSig a, sigFn b = PreSig b. The
  --   load-bearing step: if a had an inert τ-successor a', outer IH would give sigFn a' = sigFn a
  --   = PreSig a, so absorption at a' would hold (PreSig a ⊆ PreSig a ∪ {tag}), forcing a to
  --   delegate — contradicting case 2. So a has no inert τ-successor; similarly for b (using
  --   inner IH and the freshly-established fact about a). With neither side having inert
  --   τ-successors, the branching-bisimulation matching of any direct transition must use a
  --   trivial τ-prefix (else stutter would yield an inert τ-successor). Hence direct transitions
  --   are matched directly, giving PreSig a = PreSig b.
  --
  -- The full tactic proof requires careful threading of the BB stutter lemma, the
  -- `cases_head`-style decomposition of `ReflTransGen` τ-paths, and several `Quotient.sound`
  -- coercions to lift bisim-related states to partition equality. Left as `sorry` here pending
  -- further development; the converse statement is correct and the strategy is sound.
  sorry

end BranchingBisimilarity

/-- **Converse direction (inductive Sig).** Every pair of branching bisimilar states in a
τ-loop-free LTS is witnessed by some `Sig`-stable, fixed-point partition.

The witnesses: `Block = Tag` is the branching-bisimilarity quotient `Quotient brSetoid`,
`partition = sigHash = Quotient.mk brSetoid`, and `sigFn = buildSig` (well-founded recursion
on the τ-relation, see `BranchingBisimilarity.buildSig`). -/
theorem BranchingBisimilarity.exists_sig_stable.{u, v}
    {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    {lts : Cslib.LTS State Label} (hWF : TauLoopFree lts)
    {s₁ s₂ : State} (h : BranchingBisimilarity lts s₁ s₂) :
    ∃ (Block : Type u) (partition : State → Block) (Tag : Type u) (sigHash : State → Tag)
      (sigFn : State → Set (Label × (Block ⊕ Tag))),
      (∀ s, sigFn s = Sig lts partition sigHash sigFn s) ∧
      IsStable sigFn partition ∧
      partition s₁ = partition s₂ := by
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
