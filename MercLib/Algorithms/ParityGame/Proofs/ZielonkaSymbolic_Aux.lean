module

public import MercLib.Algorithms.ParityGame.ZielonkaSymbolic
public import MercLib.Algorithms.ParityGame.Proofs.Zielonka_Proofs
import all MercLib.Theory.ParityGame.Proofs.Attractor_Proofs
import Std.Tactic.Do

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The fixed-point iteration `attrSym` passes through the stages of `Game.attr`, and the symbolic
recursion returns the regions of `Game.zielonkaAux`. `ZielonkaSymbolic_Proofs` imports this module
privately, so that the lemmas `mvcgen` and `simp` generate are not exported. -/

namespace MercLib.ParityGame

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Game V} [DecidableRel G.edge]

/-! ### The attractor -/

private theorem coe_step (X : Finset V) (α : Player) (Z : Finset V) :
    ((Z ∪ G.cpre X α Z : Finset V) : Set V) = (Z : Set V) ∪
      {v | v ∈ (X : Set V) ∧ ((G.owner v = α ∧ ∃ w ∈ (Z : Set V), G.edge v w) ∨
        (G.owner v ≠ α ∧ ∀ w ∈ (X : Set V), G.edge v w → w ∈ (Z : Set V)))} := by
  ext v
  simp [Game.cpre]

private theorem stage_succ {X : Finset V} {α : Player} {U Z : Finset V} {k : ℕ}
    (h : (Z : Set V) = G.attrStage X α U k) :
    ((Z ∪ G.cpre X α Z : Finset V) : Set V) = G.attrStage X α U (k + 1) := by
  rw [coe_step, Game.attrStage, h]

omit [Fintype V] [DecidableRel G.edge] in
private theorem stage_subset {X : Finset V} {α : Player} {U : Finset V} :
    ∀ k, G.attrStage X α U k ⊆ ((X ∪ U : Finset V) : Set V)
  | 0 => by simp [Game.attrStage]
  | k + 1 => by
    intro v hv
    rcases hv with hv | hv
    · exact stage_subset k hv
    · simp [hv.1]

omit [Fintype V] [DecidableEq V] [DecidableRel G.edge] in
/-- A stage that equals the next one is the attractor. -/
private theorem attr_of_stable {X : Set V} {α : Player} {U : Set V} {k : ℕ}
    (h : G.attrStage X α U (k + 1) = G.attrStage X α U k) :
    G.attr X α U = G.attrStage X α U k := by
  have key : ∀ n, G.attrStage X α U n = G.attrStage X α U k →
      G.attrStage X α U (n + 1) = G.attrStage X α U k := by
    intro n hn
    have e : ∀ m, G.attrStage X α U (m + 1) = G.attrStage X α U m ∪
        {v | v ∈ X ∧ ((G.owner v = α ∧ ∃ w ∈ G.attrStage X α U m, G.edge v w) ∨
          (G.owner v ≠ α ∧ ∀ w ∈ X, G.edge v w → w ∈ G.attrStage X α U m))} := fun _ => rfl
    rw [e n, hn, ← e k, h]
  have hall : ∀ j, G.attrStage X α U (k + j) = G.attrStage X α U k := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => exact key (k + j) ih
  ext v
  constructor
  · rintro ⟨n, hn⟩
    rcases le_total n k with hnk | hkn
    · exact G.attrStage_mono X α U hnk hn
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
      rwa [hall j] at hn
  · intro hv
    exact ⟨k, hv⟩

/-- The loop invariant of `attrSym`. -/
private structure AInv (G : Game V) [DecidableRel G.edge] (X : Finset V) (α : Player)
    (U Z : Finset V) : Prop where
  stage : ∃ k, (Z : Set V) = G.attrStage X α U k
  sub : Z ⊆ X ∪ U

private theorem eval_iff.{u} {σ : Type u} (f : σ → ℕ) (s : σ) (m : ℕ) :
    (Std.Do.WhileVariant.eval (ps := Std.Do.PostShape.pure)
        (fun s : σ => (⟨f s⟩ : ULift.{u} ℕ)) s m).down ↔ f s = m := by
  simp [Std.Do.WhileVariant.eval, Std.Do.SVal.evalsTo, eq_comm]

open Std.Do in
set_option linter.deprecated.syntax false in
private theorem attrSym_spec (X : Finset V) (α : Player) (U : Finset V) :
    ∃ k, (G.attrSym X α U : Set V) = G.attrStage X α U k ∧
      G.attrStage X α U (k + 1) = G.attrStage X α U k := by
  generalize h : G.attrSym X α U = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => fun Z => ⟨(X ∪ U).card - Z.card⟩
  | inv2 => ⇓ x => match x with
      | .inl Z => ⌜AInv G X α U Z⌝
      | .inr Z => ⌜AInv G X α U Z ∧ Z ∪ G.cpre X α Z = Z⌝
  case vc1.step.isTrue =>
    rename_i Z mb hne hi
    obtain ⟨hev, ⟨k, hk⟩, hsub⟩ := hi
    have hsub' : Z ∪ G.cpre X α Z ⊆ X ∪ U := by
      refine Finset.union_subset hsub fun v hv => ?_
      exact Finset.mem_union_left _ (Finset.mem_filter.1 hv).1
    have hlt : Z ⊂ Z ∪ G.cpre X α Z :=
      (Finset.subset_union_left).ssubset_of_ne (Ne.symm hne)
    have hc := Finset.card_lt_card hlt
    have hc' := Finset.card_le_card hsub'
    refine ⟨_, (eval_iff _ _ _).2 rfl, ?_, ⟨k + 1, stage_succ hk⟩, hsub'⟩
    rw [← (eval_iff _ Z mb).1 hev]
    omega
  case vc2.step.isFalse hne hi => exact ⟨hi.2, not_not.1 hne⟩
  case vc3.pre =>
    exact ⟨⟨0, rfl⟩, Finset.subset_union_right⟩
  case vc4.post.success r hi =>
    obtain ⟨⟨⟨k, hk⟩, -⟩, hfix⟩ := hi
    refine ⟨k, hk, ?_⟩
    rw [← stage_succ hk, hfix, hk]

private theorem attrSym_eq (X : Finset V) (α : Player) (U : Finset V) :
    (G.attrSym X α U : Set V) = G.attr (X : Set V) α (U : Set V) := by
  obtain ⟨k, hk, hs⟩ := attrSym_spec (G := G) X α U
  rw [hk, attr_of_stable hs]

/-! ### The recursion -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.edge] in
private theorem maxPrio_eq {X : Finset V} (hX : X.Nonempty) :
    G.maxPrio (X : Set V) = X.sup G.prio := by
  rw [Game.maxPrio, ← Finset.sup'_eq_sup hX, Finset.sup'_eq_csSup_image]

private theorem zielonkaSymAux_eq : ∀ (n : ℕ) (X : Finset V), X.card ≤ n → ∀ p,
    (G.zielonkaSymAux X p : Set V) = (G.zielonkaAux (X : Set V)).win p := by
  intro n
  induction n with
  | zero =>
    intro X hX p
    have : X = ∅ := Finset.card_eq_zero.1 (by omega)
    subst this
    rw [Game.zielonkaSymAux, Game.zielonkaAux]
    simp [Solution.empty]
  | succ n ih =>
    intro X hn p
    by_cases hX : X.Nonempty
    swap
    · rw [Game.zielonkaSymAux, Game.zielonkaAux]
      simp [Solution.empty, Finset.not_nonempty_iff_eq_empty.1 hX]
    have hX' : (X : Set V).Nonempty := Finset.coe_nonempty.2 hX
    have hm := maxPrio_eq (G := G) hX
    set d := X.sup G.prio with hd
    set α := Player.ofPrio d with hα
    set Uf := X.filter fun v => G.prio v = d with hUf
    have hU : (Uf : Set V) = {v | v ∈ (X : Set V) ∧ G.prio v = d} := by
      ext v; simp [hUf]
    set A := G.attrSym X α Uf with hAdef
    have hA : (A : Set V) = G.attr (X : Set V) α {v | v ∈ (X : Set V) ∧ G.prio v = d} := by
      rw [hAdef, attrSym_eq, hU]
    have h₁ : (X \ A).card < X.card := by
      obtain ⟨v, hv, hvd⟩ := Finset.exists_mem_eq_sup X hX G.prio
      refine Finset.card_lt_card ⟨Finset.sdiff_subset, fun hsub => ?_⟩
      have hvA : v ∈ (A : Set V) := by
        rw [hA]; exact ⟨0, hv, hvd.symm⟩
      exact (Finset.mem_sdiff.1 (hsub hv)).2 hvA
    have ih1 : ∀ p, (G.zielonkaSymAux (X \ A) p : Set V) =
        (G.zielonkaAux ((X : Set V) \ G.attr (X : Set V) α
          {v | v ∈ (X : Set V) ∧ G.prio v = d})).win p := by
      intro p; rw [ih _ (by omega), Finset.coe_sdiff, hA]
    rw [Game.zielonkaSymAux, Game.zielonkaAux]
    simp only [hX, hX', ↓reduceDIte, hm, ← hd, ← hα, ← hUf, ← hAdef, h₁]
    set W' := G.zielonkaSymAux (X \ A) with hW'
    set r₁ := G.zielonkaAux ((X : Set V) \ G.attr (X : Set V) α
      {v | v ∈ (X : Set V) ∧ G.prio v = d}) with hr₁
    have hE : W' α.opp = ∅ ↔ r₁.win α.opp = ∅ := by rw [← ih1, Finset.coe_eq_empty]
    by_cases hW : W' α.opp = ∅
    · have hr := hE.1 hW
      simp only [hW, hr, ↓reduceIte, Game.wonAll]
      by_cases hp : p = α <;> simp [hp]
    · have hr : ¬ r₁.win α.opp = ∅ := fun h => hW (hE.2 h)
      simp only [hW, hr, ↓reduceIte]
      set B := G.attrSym X α.opp (W' α.opp) with hBdef
      have hB : (B : Set V) = G.attr (X : Set V) α.opp (r₁.win α.opp) := by
        rw [hBdef, attrSym_eq, ih1]
      have hXB : ((X \ B : Finset V) : Set V) = (X : Set V) \ G.attr (X : Set V) α.opp (r₁.win α.opp) := by
        rw [Finset.coe_sdiff, hB]
      have hiff : (X \ B).card < X.card ↔
          (X : Set V) \ G.attr (X : Set V) α.opp (r₁.win α.opp) ⊂ (X : Set V) := by
        rw [← hXB, Finset.coe_ssubset]
        exact ⟨fun h => ⟨Finset.sdiff_subset, fun hs => absurd (Finset.card_le_card hs) (by omega)⟩,
          Finset.card_lt_card⟩
      by_cases h₂ : (X \ B).card < X.card
      · have hc : (X : Set V) \ G.attr (X : Set V) (Player.ofPrio (G.maxPrio (X : Set V))).opp
            ((G.zielonkaAux ((X : Set V) \ G.attr (X : Set V) (Player.ofPrio (G.maxPrio (X : Set V)))
              {v | v ∈ (X : Set V) ∧ G.prio v = G.maxPrio (X : Set V)})).win
              (Player.ofPrio (G.maxPrio (X : Set V))).opp) ⊂ (X : Set V) := by
          rw [hm]; exact hiff.1 h₂
        have ih2 : ∀ p, (G.zielonkaSymAux (X \ B) p : Set V) =
            (G.zielonkaAux ((X : Set V) \ G.attr (X : Set V) α.opp (r₁.win α.opp))).win p := by
          intro p; rw [ih _ (by omega), hXB]
        simp only [h₂, ↓reduceDIte, hc]
        by_cases hp : p = α
        · simp [hp, Game.wonSplit, ih2]
        · simp [hp, Game.wonSplit, ih2, hB]
      · have hc : ¬ (X : Set V) \ G.attr (X : Set V) (Player.ofPrio (G.maxPrio (X : Set V))).opp
            ((G.zielonkaAux ((X : Set V) \ G.attr (X : Set V) (Player.ofPrio (G.maxPrio (X : Set V)))
              {v | v ∈ (X : Set V) ∧ G.prio v = G.maxPrio (X : Set V)})).win
              (Player.ofPrio (G.maxPrio (X : Set V))).opp) ⊂ (X : Set V) := by
          rw [hm]; exact fun h => h₂ (hiff.2 h)
        simp only [h₂, ↓reduceDIte, hc, Solution.empty, Finset.coe_empty]

end MercLib.ParityGame
