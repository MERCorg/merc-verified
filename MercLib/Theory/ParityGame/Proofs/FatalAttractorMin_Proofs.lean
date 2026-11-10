module

public import MercLib.Theory.ParityGame.FatalAttractor
import MercLib.Theory.ParityGame.Proofs.FatalAttractor_Proofs
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Theorem 2 of Huth, Kuo and Piterman in the convention of the paper (least colour), from the proof
for the greatest priority, by reversing the priorities: `M - prio v` for an even bound `M`. -/

namespace MercLib.ParityGame

open Cslib (ωSequence)

variable {V : Type*}

/-- The game with reversed priorities. -/
private def Game.dual (G : Game V) (M : ℕ) : Game V := { G with prio := fun v => M - G.prio v }

private theorem ofPrio_sub {M n : ℕ} (hM : M % 2 = 0) (hn : n ≤ M) :
    Player.ofPrio (M - n) = Player.ofPrio n := by
  unfold Player.ofPrio
  have : (M - n) % 2 = 0 ↔ n % 2 = 0 := by omega
  simp only [this]

variable (G : Game V) {M : ℕ}

private theorem mpre_dual (hb : ∀ v, G.prio v ≤ M) {c : ℕ} (hc : c ≤ M) (X : Set V) (i : Player)
    (T A : Set V) : (G.dual M).mpre X i (M - c) T A = G.mpreMin X i c T A := by
  ext v
  have h := hb v
  have : M - G.prio v ≤ M - c ↔ c ≤ G.prio v := by omega
  simp only [Game.mpre, Game.mpreMin, Game.dual, this, Set.mem_ofPred_eq]

private theorem stage_dual (hb : ∀ v, G.prio v ≤ M) {c : ℕ} (hc : c ≤ M) (X : Set V) (i : Player)
    (T : Set V) : (G.dual M).mattrStage X i (M - c) T = G.mattrStageMin X i c T := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih => simp only [Game.mattrStage, Game.mattrStageMin, ih, mpre_dual G hb hc]

private theorem mattr_dual (hb : ∀ v, G.prio v ≤ M) {c : ℕ} (hc : c ≤ M) (X : Set V) (i : Player)
    (T : Set V) : (G.dual M).mattr X i (M - c) T = G.mattrMin X i c T := by
  simp only [Game.mattr, Game.mattrMin, stage_dual G hb hc]

open scoped Classical in
/-- The rank function of a sequence of stages. -/
private noncomputable def rankOf (s : ℕ → Set V) (v : V) : ℕ :=
  if h : ∃ k, v ∈ s k then Nat.find h else 0

open scoped Classical in
/-- The strategy of a sequence of stages and its rank function. -/
private noncomputable def stratOf (X : Set V) (E : V → V → Prop) (T : Set V) (s : ℕ → Set V)
    (r : V → ℕ) : Strategy V := fun v =>
  if h : 0 < r v ∧ ∃ w ∈ X, E v w ∧ w ∈ s (r v - 1) ∪ T then h.2.choose else v

private theorem rank_dual (hb : ∀ v, G.prio v ≤ M) {c : ℕ} (hc : c ≤ M) (X : Set V) (i : Player)
    (T : Set V) : (G.dual M).mattrRank X i (M - c) T = G.mattrRankMin X i c T := by
  have e1 : (G.dual M).mattrRank X i (M - c) T = rankOf ((G.dual M).mattrStage X i (M - c) T) := rfl
  have e2 : G.mattrRankMin X i c T = rankOf (G.mattrStageMin X i c T) := rfl
  rw [e1, e2, stage_dual G hb hc]

private theorem strategy_dual (hb : ∀ v, G.prio v ≤ M) {c : ℕ} (hc : c ≤ M) (X : Set V) (i : Player)
    (T : Set V) : (G.dual M).mattrStrategy X i (M - c) T = G.mattrStrategyMin X i c T := by
  have e1 : (G.dual M).mattrStrategy X i (M - c) T =
      stratOf X G.edge T ((G.dual M).mattrStage X i (M - c) T)
        ((G.dual M).mattrRank X i (M - c) T) := rfl
  have e2 : G.mattrStrategyMin X i c T =
      stratOf X G.edge T (G.mattrStageMin X i c T) (G.mattrRankMin X i c T) := rfl
  rw [e1, e2, stage_dual G hb hc, rank_dual G hb hc]

/-- A win in the dual game is a win in the convention of the paper. -/
private theorem wonByMin_of_dual (hb : ∀ v, G.prio v ≤ M) (hM : M % 2 = 0) {i : Player}
    {p : ωSequence V} (h : (G.dual M).PlayWonBy i p) : G.PlayWonByMin i p := by
  obtain ⟨n, ⟨hn, hmax⟩, hi⟩ := h
  have back : ∀ m, m ∈ (p.map (G.dual M).prio).infOcc →
      M - m ∈ (p.map G.prio).infOcc ∧ m ≤ M := by
    intro m hm
    obtain ⟨k, hk⟩ := hm.exists
    have hk' : M - G.prio (p k) = m := hk
    refine ⟨hm.mono fun j hj => ?_, by omega⟩
    have hj' : M - G.prio (p j) = m := hj
    have hle := hb (p j)
    change G.prio (p j) = M - m
    omega
  have forth : ∀ m, m ∈ (p.map G.prio).infOcc → M - m ∈ (p.map (G.dual M).prio).infOcc := by
    intro m hm
    refine hm.mono fun j hj => ?_
    have hj' : G.prio (p j) = m := hj
    change M - G.prio (p j) = M - m
    omega
  obtain ⟨hmem, hnM⟩ := back n hn
  refine ⟨M - n, ⟨hmem, fun m hm => ?_⟩, by rw [ofPrio_sub hM hnM]; exact hi⟩
  have := hmax _ (forth m hm)
  have hmM : m ≤ M := by
    obtain ⟨k, hk⟩ := hm.exists
    have hk' : G.prio (p k) = m := hk
    have := hb (p k)
    omega
  omega

/-- **Fatal attractors are won, in the convention of the paper.** -/
public theorem Game.fatalAttractorWinsMin [Finite V] (X : Set V) (c : ℕ) (T : Set V) :
    G.FatalAttractorWinsMin X c T := by
  intro hsub hTX hTc hfat v hv
  obtain ⟨B, hB⟩ := (Set.finite_range G.prio).bddAbove
  have hB' : ∀ v, G.prio v ≤ B := fun v => hB ⟨v, rfl⟩
  have hb : ∀ v, G.prio v ≤ 2 * (B + c) := fun v => by have := hB' v; omega
  have hM : 2 * (B + c) % 2 = 0 := by omega
  have hc : c ≤ 2 * (B + c) := by omega
  have hp : Player.ofPrio (2 * (B + c) - c) = Player.ofPrio c := ofPrio_sub hM hc
  have hfat' : (G.dual (2 * (B + c))).IsFatal X (2 * (B + c) - c) T := by
    unfold Game.IsFatal Game.ma
    rw [hp, mattr_dual G hb hc]
    exact hfat
  have hv' : v ∈ (G.dual (2 * (B + c))).ma X (2 * (B + c) - c) T := by
    unfold Game.ma
    rw [hp, mattr_dual G hb hc]
    exact hv
  have hw := Game.fatalAttractorWins (G.dual (2 * (B + c))) X (2 * (B + c) - c) T hsub hTX
    (fun u hu => by simp only [Game.dual, hTc u hu]) hfat' v hv'
  rw [hp, strategy_dual G hb hc] at hw
  exact ⟨hw.1, fun q hq hc' => wonByMin_of_dual G hb hM (hw.2 q hq hc')⟩

end MercLib.ParityGame
