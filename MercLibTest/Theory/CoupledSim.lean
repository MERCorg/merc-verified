import MercLib.Theory.CoupledSim.Basic

/-!
# Tests for `MercLib.Theory.CoupledSim`

Concrete small LTSs exercising the coupled similarity theory of Bisping & Nestmann 2019:
coupled similarity on a `τ`-cycle (Corollary 1), `τ`-loop ignorance (Lemma 5), the game
characterisation (Theorem 3), the sink reduction (Theorem 1), and a pair that is *not*
coupled similar.
-/

namespace MercLibTest.CoupledSim

open Cslib (LTS HasTau)
open MercLib.CoupledSim

/-- Labels: one observable action `act` plus the internal action `int` (= `τ`). -/
inductive L | act | int

instance : HasTau L where τ := .int

/-- A two-state LTS whose states form a `τ`-cycle: `p ⇄τ q`. -/
inductive St | p | q

def cycle : LTS St L where
  Tr s μ s' :=
    match s, μ, s' with
    | .p, .int, .q => True
    | .q, .int, .p => True
    | _, _, _ => False

/-- A two-state LTS: `p` has a `τ`-loop and an `act`-step to `q`; `q` only loops on `act`.
By Lemma 5 of [Bisping2019], `p` and `q` are coupled similar. -/
inductive St2 | p | q

def loop : LTS St2 L where
  Tr s μ s' :=
    match s, μ, s' with
    | .p, .int, .p => True
    | .p, .act, .q => True
    | .q, .act, .q => True
    | _, _, _ => False

/-- A two-state LTS where `p` takes a visible step to the deadlocked state `q`. -/
inductive St3 | p | q

def dead : LTS St3 L where
  Tr s μ s' :=
    match s, μ, s' with
    | .p, .act, .q => True
    | _, _, _ => False

/-! ## Corollary 1: states on a `τ`-cycle are coupled similar -/

theorem cycle_tr_pq : LTS.Tr.toRelation cycle HasTau.τ St.p St.q := by trivial

theorem cycle_tr_qp : LTS.Tr.toRelation cycle HasTau.τ St.q St.p := by trivial

/-- `p` and `q` on the `τ`-cycle are coupled similar (Corollary 1). -/
example : St.p ≡cs[cycle] St.q :=
  tauCycle_coupledSimilarity (Relation.ReflTransGen.single cycle_tr_pq)
    (Relation.ReflTransGen.single cycle_tr_qp)

/-- The converse direction also holds. -/
example : St.q ≡cs[cycle] St.p :=
  tauCycle_coupledSimilarity (Relation.ReflTransGen.single cycle_tr_qp)
    (Relation.ReflTransGen.single cycle_tr_pq)

/-! ## Lemma 5: a `τ`-loop can be ignored -/

/-- The outgoing transitions of `p` in `loop` are those of `q` plus a `τ`-loop. -/
theorem loop_p_iff : ∀ ⦃α : L⦄ ⦃p' : St2⦄,
    loop.Tr St2.p α p' ↔ (loop.Tr St2.q α p' ∨ (α = HasTau.τ ∧ p' = St2.p)) := by
  intro α p'
  cases α with
  | act =>
    cases p' with
    | p => exact ⟨fun h => h.elim,
        fun h => Or.elim h (fun h2 => h2.elim) (fun h3 => by cases h3.1)⟩
    | q => exact ⟨fun _ => Or.inl True.intro,
        fun h => Or.elim h (fun _ => True.intro) (fun h3 => by cases h3.1)⟩
  | int =>
    cases p' with
    | p => exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩,
        fun h => Or.elim h (fun h2 => h2.elim) (fun _ => True.intro)⟩
    | q => exact ⟨fun h => h.elim,
        fun h => Or.elim h (fun h2 => h2.elim) (fun h3 => by cases h3.2)⟩

/-- By Lemma 5, `p` (with its `τ`-loop) and `q` are coupled similar in `loop`. -/
example : St2.p ≡cs[loop] St2.q :=
  tauLoopIgnorance loop_p_iff

/-! ## A negative example: `p` is not coupled similar to the deadlock `q` -/

/-- In `dead`, `τ`-reachability is the identity. -/
theorem dead_τSTr_eq : ∀ {x y : St3}, dead.τSTr x y → x = y := by
  intro x y h
  cases x with
  | p => cases h with
    | refl => rfl
    | @tail b _ _ hLast => cases b <;> simp [LTS.Tr.toRelation, dead, HasTau.τ] at hLast
  | q => cases h with
    | refl => rfl
    | @tail b _ _ hLast => cases b <;> simp [LTS.Tr.toRelation, dead, HasTau.τ] at hLast

/-- In `dead`, the state `p` is **not** coupled similar to the deadlock `q`: `p` can do an
`act`-step that `q` cannot match. -/
example : ¬ (St3.p ≡cs[dead] St3.q) := by
  rintro ⟨⟨r, hr, hpq⟩, -⟩
  obtain ⟨q', -, hst⟩ := hr.1 hpq L.act St3.q (by trivial)
  cases hst with
  | tr h1 htr' _ =>
    have hq2 : St3.q = _ := dead_τSTr_eq h1
    subst hq2
    exact (htr' : False).elim

/-! ## The game characterisation (Theorem 3) -/

/-- By Theorem 3, the defender wins the game at `att p q` in `cycle` — because `p ≼cs q`
(Corollary 1). -/
example : DefenderWinning cycle (.att St.p St.q) :=
  (defenderWinning_iff_preorder cycle St.p St.q).mpr
    ((tauCycle_coupledSimilarity (Relation.ReflTransGen.single cycle_tr_pq)
      (Relation.ReflTransGen.single cycle_tr_qp)).1)

/-! ## The sink reduction (Theorem 1) -/

/-- In `cycle`, every state can weakly match every actually occurring transition, so the
universal relation is a weak simulation and `p ≼ws[cycle] q`. -/
theorem cycle_ws_pq : St.p ≼ws[cycle] St.q := by
  refine ⟨fun _ _ => True, ?_, True.intro⟩
  rintro x y - μ x' htr
  cases x <;> cases y <;> cases μ <;> cases x' <;>
    first
      | exact (htr : False).elim
      | exact ⟨St.q, True.intro, LTS.STr.tr LTS.τSTr.refl (by trivial) LTS.τSTr.refl⟩
      | exact ⟨St.q, True.intro, LTS.STr.tr (Relation.ReflTransGen.single cycle_tr_qp)
          (by trivial) LTS.τSTr.refl⟩

/-- By Theorem 1, weak similarity in `cycle` gives coupled similarity in its sink extension. -/
example : (some St.p) ≼cs[extendSink cycle] (some St.q) :=
  (extendSink_ws_iff_cs cycle (some St.p) (some St.q)).mp
    ((extendSink_ws_some_iff cycle St.p St.q).mp cycle_ws_pq)

end MercLibTest.CoupledSim
