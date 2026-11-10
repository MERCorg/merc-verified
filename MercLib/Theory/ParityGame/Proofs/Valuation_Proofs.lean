module

public import MercLib.Theory.ParityGame.Valuation
import all MercLib.Theory.ParityGame.Proofs.Lasso_Proofs
import all MercLib.Theory.ParityGame.Proofs.Key_Proofs
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

`key` is faithful to the play-profile order `≺` of Vöge and Jurdziński. -/

namespace MercLib.HybridSI

open Function MercLib.ParityGame

variable {V : Type*} [Fintype V] [LinearOrder V] (G : Game V)

private def reward (u : V) : ℤ := if G.prio u % 2 = 0 then (rank u : ℤ) + 1 else -((rank u : ℤ) + 1)

private theorem reward_eq_iff {u v : V} : reward G u = reward G v ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  apply rank_injective
  unfold reward at h
  split_ifs at h <;> omega

private theorem reward_lt_iff {u v : V} : reward G u < reward G v ↔ rewardLt G u v := by
  by_cases huv : u = v
  · subst huv; simp [rewardLt]
  have hr : rank u ≠ rank v := fun h => huv (rank_injective h)
  have h1 := rank_lt_rank_iff (x := u) (y := v)
  have h2 := rank_lt_rank_iff (x := v) (y := u)
  by_cases hu : G.prio u % 2 = 0 <;> by_cases hv : G.prio v % 2 = 0 <;>
    simp [reward, rewardLt, IsPos, hu, hv, ← h1, ← h2] <;> omega

private def signed (Q : Finset V) (y : V) : ℤ := if y ∈ Q then weight G y else -weight G y

private theorem signed_pow (Q : Finset V) : SignedPow (signed G Q) := by
  intro y
  unfold signed weight
  split_ifs <;> simp

private theorem sum_diff (P Q : Finset V) :
    Q.sum (weight G) - P.sum (weight G) = ∑ y ∈ symmDiff P Q, signed G Q y := by
  have hdisj : Disjoint (P \ Q) (Q \ P) := Finset.disjoint_left.2 fun y h1 h2 =>
    (Finset.mem_sdiff.1 h1).2 (Finset.mem_sdiff.1 h2).1
  have split : ∀ A B : Finset V, A.sum (weight G) = ∑ y ∈ A \ B, weight G y + ∑ y ∈ A ∩ B, weight G y :=
    fun A B => by
      rw [← Finset.sdiff_inter_self_left A B, Finset.sum_sdiff Finset.inter_subset_left]
  rw [show symmDiff P Q = (P \ Q) ∪ (Q \ P) from rfl, Finset.sum_union hdisj, split P Q, split Q P,
    Finset.inter_comm Q P]
  have e1 : ∑ y ∈ P \ Q, signed G Q y = -∑ y ∈ P \ Q, weight G y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y hy => by simp [signed, (Finset.mem_sdiff.1 hy).2]
  have e2 : ∑ y ∈ Q \ P, signed G Q y = ∑ y ∈ Q \ P, weight G y :=
    Finset.sum_congr rfl fun y hy => by simp [signed, (Finset.mem_sdiff.1 hy).1]
  rw [e1, e2]; ring

private theorem signed_pos_iff (Q : Finset V) (x : V) :
    0 < signed G Q x ↔ (x ∈ Q ↔ IsPos G x) := by
  have hp : (0 : ℤ) < 2 ^ rank x := by positivity
  unfold signed weight IsPos
  by_cases hq : x ∈ Q <;> by_cases he : G.prio x % 2 = 0 <;> simp [hq, he]

private theorem exists_top {P Q : Finset V} (h : P ≠ Q) :
    ∃ x ∈ symmDiff P Q, ∀ y ∈ symmDiff P Q, y ≤ x := by
  have hne : (symmDiff P Q).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun h' => h (symmDiff_eq_bot.1 h')
  exact ⟨_, Finset.max'_mem _ hne, fun y hy => Finset.le_max' _ y hy⟩

private theorem sum_eq_iff {P Q : Finset V} : P.sum (weight G) = Q.sum (weight G) ↔ P = Q := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  by_contra hne
  obtain ⟨x, hx, hmax⟩ := exists_top hne
  have := (top_dominates (signed G Q) (signed_pow G Q) _ x hx hmax).2
  rw [← sum_diff, h, sub_self] at this
  exact this rfl

private theorem sum_lt_iff {P Q : Finset V} :
    P.sum (weight G) < Q.sum (weight G) ↔ setLt G P Q := by
  constructor
  · intro h
    have hne : P ≠ Q := fun e => by subst e; exact lt_irrefl _ h
    obtain ⟨x, hx, hmax⟩ := exists_top hne
    refine ⟨x, hx, hmax, (signed_pos_iff G Q x).1 ?_⟩
    apply (top_dominates (signed G Q) (signed_pow G Q) _ x hx hmax).1.1
    rw [← sum_diff]; omega
  · rintro ⟨x, hx, hmax, hq⟩
    have := (top_dominates (signed G Q) (signed_pow G Q) _ x hx hmax).1.2
      ((signed_pos_iff G Q x).2 hq)
    rw [← sum_diff] at this; omega

/-- A positional play repeats no vertex before its first visit of the cycle maximum. -/
private theorem card_visitedBefore (f : V → V) (x : V) :
    (visitedBefore f x).card = stepsTo f x := by
  obtain ⟨hhit, hmin⟩ := stepsTo_spec (f := f) x
  have inj : ∀ i j, i < j → j < stepsTo f x → f^[i] x ≠ f^[j] x := by
    intro i j hij hj e
    have hper : IsPeriodicPt f (j - i) (f^[i] x) := by
      show f^[j - i] (f^[i] x) = f^[i] x
      rw [← iterate_add_apply, Nat.sub_add_cancel hij.le, ← e]
    have hk : f^[((stepsTo f x - i) % (j - i)) + i] x = cycMax f x := by
      rw [iterate_add_apply, hper.iterate_mod_apply, ← iterate_add_apply,
        Nat.sub_add_cancel (by omega), hhit]
    have hlt : (stepsTo f x - i) % (j - i) < j - i := Nat.mod_lt _ (by omega)
    exact hmin _ (by omega) hk
  unfold visitedBefore playPrefix
  rw [List.toFinset_card_of_nodup]
  · simp
  · refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    rw [iter_eq, iter_eq] at e
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd e (inj a b h hb')
    · exact h
    · exact absurd e.symm (inj b a h ha')

private theorem key_parts (f : V → V) (x : V) : key G f x =
    toLex (reward G (cycMax f x), toLex ((bSet f x).sum (weight G),
      if G.prio (cycMax f x) % 2 = 0 then -((visitedBefore f x).card : ℤ)
      else ((visitedBefore f x).card : ℤ))) := by
  rw [card_visitedBefore]; rfl

/-- **`key` is an order embedding of the play profiles.** -/
public theorem keyOrderEmbedding : KeyOrderEmbedding G := by
  intro f g x y
  rw [key_parts, key_parts]
  constructor
  · simp only [Prod.Lex.toLex_lt_toLex, reward_lt_iff, reward_eq_iff, sum_lt_iff, sum_eq_iff,
      profileLt, playProfile, IsPos]
    by_cases hu : cycMax f x = cycMax g y
    · rw [hu]
      by_cases he : G.prio (cycMax g y) % 2 = 0 <;> simp [he]
    · simp [hu]
  · simp only [toLex_inj, Prod.mk.injEq, reward_eq_iff, sum_eq_iff, PlayProfile.ext_iff, playProfile]
    by_cases hu : cycMax f x = cycMax g y
    · rw [hu]
      by_cases he : G.prio (cycMax g y) % 2 = 0 <;> simp [he]
    · simp [hu]

end MercLib.HybridSI
