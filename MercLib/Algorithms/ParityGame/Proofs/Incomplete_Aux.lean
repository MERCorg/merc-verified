module

public import MercLib.Algorithms.ParityGame.Incomplete
import Std.Tactic.Do

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The iteration `Incomplete.lfp f` stops at a stage `F^[k] ∅` of the corresponding set operator,
which is then the union of all stages. The computations of `Incomplete` return the sets of
`IncompleteGame`. `Incomplete_Proofs` imports this module privately, so that the lemmas
`mvcgen` and `simp` generate are not exported. -/

namespace MercLib.ParityGame

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The least fixed point iteration -/

private theorem eval_iff.{u} {σ : Type u} (f : σ → ℕ) (s : σ) (m : ℕ) :
    (Std.Do.WhileVariant.eval (ps := Std.Do.PostShape.pure)
        (fun s : σ => (⟨f s⟩ : ULift.{u} ℕ)) s m).down ↔ f s = m := by
  simp [Std.Do.WhileVariant.eval, Std.Do.SVal.evalsTo, eq_comm]

omit [Fintype V] [DecidableEq V] in
/-- A stage that equals the next one is the union of all stages. -/
private theorem iUnion_of_stable {F : Set V → Set V} (hF : Monotone F) {k : ℕ}
    (h : F (F^[k] ∅) = F^[k] ∅) : {v | ∃ n, v ∈ F^[n] ∅} = F^[k] ∅ := by
  have hall : ∀ j, F^[k + j] ∅ = F^[k] ∅ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, h]
  have hmono := hF.monotone_iterate_of_le_map (Set.empty_subset (F ∅))
  ext v
  constructor
  · rintro ⟨n, hn⟩
    rcases le_total n k with hnk | hkn
    · exact hmono hnk hn
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
      rwa [hall j] at hn
  · intro hv
    exact ⟨k, hv⟩

open Std.Do in
set_option linter.deprecated.syntax false in
private theorem lfp_spec (f : Finset V → Finset V) (F : Set V → Set V) (hF : Monotone F)
    (hc : ∀ Z, (f Z : Set V) = F Z) :
    ∃ k, (Incomplete.lfp f : Set V) = F^[k] ∅ ∧ F (F^[k] ∅) = F^[k] ∅ := by
  have hmono := hF.monotone_iterate_of_le_map (Set.empty_subset (F ∅))
  generalize h : Incomplete.lfp f = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => fun Z => ⟨Fintype.card V - Z.card⟩
  | inv2 => ⇓ x => match x with
      | .inl Z => ⌜∃ k, (Z : Set V) = F^[k] ∅⌝
      | .inr Z => ⌜(∃ k, (Z : Set V) = F^[k] ∅) ∧ f Z = Z⌝
  case vc1.step.isTrue =>
    rename_i Z mb hne hi
    obtain ⟨hev, k, hk⟩ := hi
    have hfZ : (f Z : Set V) = F^[k + 1] ∅ := by
      rw [hc, hk, Function.iterate_succ_apply']
    have hsub : Z ⊆ f Z := by
      rw [← Finset.coe_subset, hk, hfZ]
      exact hmono (Nat.le_succ k)
    have hc' := Finset.card_lt_card (hsub.ssubset_of_ne (Ne.symm hne))
    have hle := Finset.card_le_univ (f Z)
    refine ⟨_, (eval_iff _ _ _).2 rfl, ?_, ⟨k + 1, hfZ⟩⟩
    rw [← (eval_iff _ Z mb).1 hev]
    omega
  case vc2.step.isFalse hne hi => exact ⟨hi.2, not_not.1 hne⟩
  case vc3.pre => exact ⟨0, by simp⟩
  case vc4.post.success r hi =>
    obtain ⟨⟨k, hk⟩, hfix⟩ := hi
    refine ⟨k, hk, ?_⟩
    rw [← hk, ← hc, hfix]

/-- `Incomplete.lfp f` is the union of the stages `F^[k] ∅` of a monotone set operator `F`
that `f` computes. -/
private theorem lfp_eq (f : Finset V → Finset V) (F : Set V → Set V) (hF : Monotone F)
    (hc : ∀ Z, (f Z : Set V) = F Z) : (Incomplete.lfp f : Set V) = {v | ∃ k, v ∈ F^[k] ∅} := by
  obtain ⟨k, hk, hs⟩ := lfp_spec f F hF hc
  rw [hk, iUnion_of_stable hF hs]

/-! ### The set operations -/

namespace IncompleteGame

section Sets

variable {V : Type*} (a : IncompleteGame V)

private theorem pre_mono {U U' : Set V} (h : U ⊆ U') : a.pre U ⊆ a.pre U' :=
  fun _ ⟨hv, w, hw, he⟩ => ⟨hv, w, h hw, he⟩

private theorem pre_compl_anti {U U' : Set V} (h : U ⊆ U') :
    a.pre (a.vs \ U') ⊆ a.pre (a.vs \ U) :=
  a.pre_mono (Set.sdiff_subset_sdiff_right h)

private theorem cpre_mono (α : Player) (U : Set V) : Monotone fun Z => U ∪ a.cpre α Z := by
  intro Z Z' h v hv
  rcases hv with hv | (⟨ho, hp⟩ | ⟨ho, hn⟩)
  · exact Or.inl hv
  · exact Or.inr (Or.inl ⟨ho, a.pre_mono h hp⟩)
  · refine Or.inr (Or.inr ⟨ho, fun hm => hn ?_⟩)
    rcases hm with hm | hm
    · exact Or.inl (a.pre_compl_anti h hm)
    · exact Or.inr hm

private theorem spre_mono (α : Player) (U : Set V) : Monotone fun Z => U ∪ a.spre α Z := by
  intro Z Z' h v hv
  rcases hv with hv | (⟨ho, hp⟩ | ⟨ho, hn⟩)
  · exact Or.inl hv
  · exact Or.inr (Or.inl ⟨ho, a.pre_mono h hp⟩)
  · refine Or.inr (Or.inr ⟨ho, fun hm => hn ?_⟩)
    rcases hm with (hm | hm) | hm
    · exact Or.inl (Or.inl (a.pre_compl_anti h hm))
    · exact Or.inl (Or.inr hm)
    · exact Or.inr hm

private theorem attrStage_eq (α : Player) (U : Set V) :
    ∀ k, a.attrStage α U k = (fun Z => U ∪ a.cpre α Z)^[k] ∅
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', ← attrStage_eq α U k]; rfl

private theorem sattrStage_eq (α : Player) (U : Set V) :
    ∀ k, a.sattrStage α U k = (fun Z => U ∪ a.spre α Z)^[k] ∅
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', ← sattrStage_eq α U k]; rfl

end Sets

end IncompleteGame

/-! ### The computations -/

namespace Incomplete

variable (a : IncompleteGame V)

omit [DecidableEq V] in
private theorem coe_vs [DecidablePred (· ∈ a.vs)] : (vs a : Set V) = a.vs := by
  ext v; simp [vs]

omit [DecidableEq V] in
private theorem coe_I [DecidablePred (· ∈ a.I)] : (I a : Set V) = a.I := by
  ext v; simp [I]

omit [DecidableEq V] in
private theorem coe_own [DecidablePred (· ∈ a.vs)] (α : Player) :
    (own a α : Set V) = a.own α := by
  ext v; simp [own, vs, IncompleteGame.own]

omit [DecidableEq V] in
private theorem coe_pre [DecidablePred (· ∈ a.vs)] [DecidableRel a.edge] (U : Finset V) :
    (pre a U : Set V) = a.pre U := by
  ext v; simp [pre, vs, IncompleteGame.pre]

omit [DecidableEq V] in
private theorem coe_sinks [DecidablePred (· ∈ a.vs)] [DecidableRel a.edge] :
    (sinks a : Set V) = a.sinks := by
  ext v; simp [sinks, vs, IncompleteGame.sinks]

private theorem coe_cpre [DecidablePred (· ∈ a.vs)] [DecidableRel a.edge]
    (α : Player) (U : Finset V) : (cpre a α U : Set V) = a.cpre α U := by
  simp only [cpre, IncompleteGame.cpre, Finset.coe_union, Finset.coe_inter, Finset.coe_sdiff,
    coe_own, coe_pre, coe_sinks, coe_vs]

private theorem coe_spre [DecidablePred (· ∈ a.vs)] [DecidablePred (· ∈ a.I)]
    [DecidableRel a.edge] (α : Player) (U : Finset V) :
    (spre a α U : Set V) = a.spre α U := by
  simp only [spre, IncompleteGame.spre, Finset.coe_union, Finset.coe_inter, Finset.coe_sdiff,
    coe_own, coe_pre, coe_sinks, coe_vs, coe_I]

variable [DecidablePred (· ∈ a.vs)] [DecidablePred (· ∈ a.I)] [DecidableRel a.edge]

omit [DecidablePred (· ∈ a.I)] in
private theorem attr_eq (α : Player) (U : Finset V) :
    (attr a α U : Set V) = a.attr α U := by
  rw [attr, lfp_eq _ (fun Z => (U : Set V) ∪ a.cpre α Z) (a.cpre_mono α U)
    (fun Z => by rw [Finset.coe_union, coe_cpre])]
  ext v
  simp only [IncompleteGame.attr, a.attrStage_eq, Set.mem_ofPred_eq]

private theorem safe_eq (α : Player) : (safe a α : Set V) = a.safe α := by
  rw [safe, Finset.coe_sdiff, attr_eq, Finset.coe_inter, coe_own, coe_I, coe_vs,
    IncompleteGame.safe]

private theorem sattr_eq (α : Player) (U : Finset V) :
    (sattr a α U : Set V) = a.sattr α U := by
  rw [sattr, lfp_eq _ (fun Z => (U : Set V) ∪ a.spre α Z) (a.spre_mono α U)
    (fun Z => by rw [Finset.coe_union, coe_spre])]
  ext v
  simp only [IncompleteGame.sattr, a.sattrStage_eq, Set.mem_ofPred_eq]

end Incomplete

end MercLib.ParityGame
