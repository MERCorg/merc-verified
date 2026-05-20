module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Signatures.Signature
import Signatures.BranchingBisimilarity

@[expose] public section InductiveSignatures

-- PreSig: refined signature combining visible/non-inert transitions (tagged by block) with
-- inert τ-transitions (tagged with a hash of the destination's Sig). The `sigHash` parameter is
-- abstract — for the recursive definition in the paper, `sigHash s' = h (Sig π sigHash s')`,
-- the hash of the destination's signature.
--
-- Reference: signature-based partition refinement for branching bisimilarity.
def PreSig [Cslib.HasTau Label] (lts : Cslib.LTS State Label) (partition : State → Block)
    {Tag : Type _} (sigHash : State → Tag) (s : State) : Set (Label × (Block ⊕ Tag)) :=
  { e | (∃ a s', lts.Tr s a s' ∧ (a ≠ Cslib.HasTau.τ ∨ partition s ≠ partition s') ∧
                e = (a, Sum.inl (partition s'))) ∨
        (∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ partition s = partition s' ∧
                e = (Cslib.HasTau.τ, Sum.inr (sigHash s'))) }

-- Sig (one-step operator): given an oracle `sigFn` for `Sig`, computes one step of the recurrence.
-- If `s` has an inert τ-successor `s'` (within the same block) whose `sigFn s'` absorbs `PreSig s`
-- (plus the inert step itself), then `Sig s` collapses to `sigFn s'`; otherwise `Sig s = PreSig s`.
--
-- The full recursive `Sig π` of the paper is the fixed point of this operator under the
-- coherence condition `sigHash s' = h (sigFn s')`. We expose it as a parameterized one-step
-- operator so it can be instantiated by future fixed-point developments.
open Classical in
noncomputable def Sig [Cslib.HasTau Label] (lts : Cslib.LTS State Label) (partition : State → Block)
    {Tag : Type _} (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag))) (s : State) :
    Set (Label × (Block ⊕ Tag)) :=
  if h : ∃ s', lts.Tr s Cslib.HasTau.τ s' ∧ partition s = partition s' ∧
              PreSig lts partition sigHash s ⊆
                sigFn s' ∪ {(Cslib.HasTau.τ, Sum.inr (sigHash s'))} then
    sigFn h.choose
  else
    PreSig lts partition sigHash s

/-- An LTS is τ-loop-free if its τ-transition relation is well-founded: there are no infinite
sequences of τ-transitions (equivalently, on a finite state space, no τ-cycles). -/
def TauLoopFree [Cslib.HasTau Label] (lts : Cslib.LTS State Label) : Prop :=
  WellFounded (fun s' s => lts.Tr s Cslib.HasTau.τ s')

/-- **Fixed-point relation for the inductive branching signature.** Two states are related iff
some partition (over which we exhibit a `sigHash` and a `sigFn` fixed point of `Sig`) is stable
and places both states in the same block.

This is the inductive analogue of `BranchingFixPoint` from `Signature.lean`; the additional
witnesses (`Tag`, `sigHash`, `sigFn`) account for the inert-τ tag and the locally recursive
shape of `Sig`. Equivalence with `BranchingBisimilarity` in a τ-loop-free LTS is proved in
`Signatures.Proofs.InductiveSignatures_Proofs`. -/
def InductiveBranchingFixPoint.{u, v} {State : Type u} {Label : Type v} [Cslib.HasTau Label]
    (lts : Cslib.LTS State Label) : State → State → Prop :=
  fun s s' => ∃ (Block : Type u) (partition : State → Block) (Tag : Type u) (sigHash : State → Tag)
    (sigFn : State → Set (Label × (Block ⊕ Tag))),
    (∀ x, sigFn x = Sig lts partition sigHash sigFn x) ∧
    IsStable sigFn partition ∧
    partition s = partition s'

end InductiveSignatures
