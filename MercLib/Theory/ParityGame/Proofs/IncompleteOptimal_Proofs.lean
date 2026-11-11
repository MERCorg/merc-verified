module

public import MercLib.Theory.ParityGame.Incomplete
import all MercLib.Theory.ParityGame.Proofs.Game_Proofs
import Mathlib.Basic.Finite.Sum
import all MercLib.Theory.ParityGame.Proofs.Region_Proofs
import all MercLib.Algorithms.ParityGame.Proofs.Zielonka_Proofs
import all MercLib.Theory.ParityGame.Proofs.Incomplete_Proofs
import all MercLib.Theory.ParityGame.Proofs.IncompleteDominion_Proofs
import all MercLib.Theory.ParityGame.Proofs.IncompleteAttr_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Theorem 1 of [Laveaux2022]: the vertices in no safe dominion are exactly those whose winner
depends on the extension. Besides Lemmas 1 and 2 it needs determinacy of finite incomplete games
(from Zielonka's algorithm on the total encoding), that no vertex is in dominions of both players,
and the transfer of a dominion between two games that agree on it.

The proof of the paper claims that a safe vertex won by `α` in `G` lies in an `α`-dominion of
`G ∩ safe_α(a)`. That is false (a vertex of `α` may win only by moving into the unsafe part); the
proof below uses the extension of Lemma 2 for every vertex of `W_?` instead. -/

namespace MercLib.ParityGame

open Cslib (ωSequence)

variable {V : Type*}

namespace IncompleteGame

/-! ### Transfer of a dominion -/

/-- Two incomplete games agree on `D` for player `α`: same owners and priorities, the opponent's
moves in `c` are moves in `b`, and the moves of `b` inside `D` are moves of `c`. -/
private structure Agree (b c : IncompleteGame V) (α : Player) (D : Set V) : Prop where
  vs : D ⊆ c.vs
  owner : ∀ v ∈ D, c.owner v = b.owner v
  prio : ∀ v ∈ D, c.prio v = b.prio v
  opp : ∀ v ∈ D, b.owner v ≠ α → ∀ w, c.edge v w → b.edge v w
  fwd : ∀ v ∈ D, ∀ w ∈ D, b.edge v w → c.edge v w

variable {b c : IncompleteGame V} {α : Player} {D : Set V} {σ : Strategy (V ⊕ Player)}

/-- A winning strategy never reaches a sink of its own player. -/
private theorem no_own_sink' {v₀ v : V} (hvD : v ∈ D)
    (hW : b.toGame.WinsFrom (embed D) α σ (.inl v₀))
    (hr : Relation.ReflTransGen (b.toGame.Step (embed D) α σ) (.inl v₀) (.inl v))
    (ho : b.owner v = α) : v ∉ b.sinks := by
  intro hs
  have hσ : σ (.inl v) = .inr α.opp := by
    obtain ⟨u, -, -, he, hown⟩ := hW.1 _ hr
    have hu' := hown ho
    rcases u with w | q
    · exact absurd he (hs.2 w)
    · rcases he with ⟨-, hq⟩ | ⟨hnv, -⟩
      · rw [← hu', hq]
        show Sum.inr (b.owner v).opp = _
        rw [ho]
      · exact absurd hs.1 hnv
  obtain ⟨n, f, h0, hn, hsteps⟩ := exists_path hr
  let g : ωSequence (V ⊕ Player) := ⟨fun i => if i ≤ n then f i else .inr α.opp⟩
  have hg : b.toGame.ConformingPlay (embed D) α σ g := by
    intro i
    show b.toGame.Step (embed D) α σ (if i ≤ n then f i else .inr α.opp)
      (if i + 1 ≤ n then f (i + 1) else .inr α.opp)
    by_cases hi : i + 1 ≤ n
    · simp only [show i ≤ n by omega, hi, ↓reduceIte]; exact hsteps i (by omega)
    · by_cases hin : i = n
      · subst hin
        simp only [le_refl, hi, ↓reduceIte, hn]
        refine ⟨mem_embed_inl.2 hvD, mem_embed_inr, Or.inl ⟨hs, ?_⟩, fun _ => hσ.symm⟩
        show α.opp = (b.owner v).opp
        rw [ho]
      · simp only [show ¬ i ≤ n by omega, hi, ↓reduceIte]
        exact ⟨mem_embed_inr, mem_embed_inr, rfl, fun h => absurd h (opp_ne' α)⟩
  have hg0 : g 0 = .inl v₀ := by
    show (if 0 ≤ n then f 0 else Sum.inr α.opp) = Sum.inl v₀
    simp [h0]
  obtain ⟨m, ⟨hm, -⟩, hmα⟩ := hW.2 g hg0 hg
  have hmeq : m = b.toGame.prio (.inr α.opp) := by
    obtain ⟨k, hk, e⟩ := Filter.frequently_atTop.1 hm (n + 1)
    rw [← e]
    show b.toGame.prio (if k ≤ n then f k else .inr α.opp) = _
    simp only [show ¬ k ≤ n by omega, ↓reduceIte]
  rw [hmeq, ofPrio_inr] at hmα
  exact opp_ne' α hmα

private theorem Agree.step_cb (A : Agree b c α D) (hD : b.IsDominion α D) {v₀ : V}
    (hW : b.toGame.WinsFrom (embed D) α σ (.inl v₀)) {x y : V ⊕ Player}
    (hr : Relation.ReflTransGen (b.toGame.Step (embed D) α σ) (.inl v₀) x)
    (h : c.toGame.Step (embed D) α σ x y) : b.toGame.Step (embed D) α σ x y := by
  obtain ⟨hx, hy, he, hown⟩ := h
  rcases x with v | q
  · have hvD := mem_embed_inl.1 hx
    by_cases ho : b.owner v = α
    · obtain ⟨u, hu⟩ := hW.1 _ hr
      have e₁ : u = σ (.inl v) := hu.2.2.2 ho
      have e₂ : y = σ (.inl v) := hown (show c.owner v = α by rw [A.owner v hvD]; exact ho)
      rw [e₂, ← e₁]; exact hu
    · refine ⟨hx, hy, ?_, fun h => absurd h ho⟩
      rcases y with w | q
      · exact A.opp v hvD ho w he
      · rcases he with ⟨hs, hq⟩ | ⟨hnv, -⟩
        · refine Or.inl ⟨⟨hD.1 hvD, fun w hw => hs.2 w ?_⟩, ?_⟩
          · exact A.fwd v hvD w (hD.2.1 v hvD ho w hw) hw
          · rw [hq, A.owner v hvD]
        · exact absurd (A.vs hvD) hnv
  · rcases y with w | q'
    · exact he.elim
    · exact ⟨hx, hy, he, hown⟩

private theorem Agree.reach (A : Agree b c α D) (hD : b.IsDominion α D) {v₀ : V}
    (hW : b.toGame.WinsFrom (embed D) α σ (.inl v₀)) {x : V ⊕ Player}
    (h : Relation.ReflTransGen (c.toGame.Step (embed D) α σ) (.inl v₀) x) :
    Relation.ReflTransGen (b.toGame.Step (embed D) α σ) (.inl v₀) x := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (A.step_cb hD hW ih hs)

private theorem Agree.step_bc (A : Agree b c α D) (hDb : D ⊆ b.vs) {v₀ : V}
    (hW : b.toGame.WinsFrom (embed D) α σ (.inl v₀)) {x u : V ⊕ Player}
    (hr : Relation.ReflTransGen (b.toGame.Step (embed D) α σ) (.inl v₀) x)
    (h : b.toGame.Step (embed D) α σ x u) : c.toGame.Step (embed D) α σ x u := by
  obtain ⟨hx, hu, he, hown⟩ := h
  rcases x with v | q
  · have hvD := mem_embed_inl.1 hx
    have hown' : c.owner v = α → u = σ (.inl v) := fun h' =>
      hown (show b.owner v = α by rw [← A.owner v hvD]; exact h')
    refine ⟨hx, hu, ?_, hown'⟩
    rcases u with w | q
    · exact A.fwd v hvD w (mem_embed_inl.1 hu) he
    · rcases he with ⟨hs, hq⟩ | ⟨hnv, -⟩
      · by_cases ho : b.owner v = α
        · exact absurd hs (no_own_sink' hvD hW hr ho)
        · refine Or.inl ⟨⟨A.vs hvD, fun w hw => hs.2 w (A.opp v hvD ho w hw)⟩, ?_⟩
          rw [hq, A.owner v hvD]
      · exact absurd (hDb hvD) hnv
  · rcases u with w | q'
    · exact he.elim
    · exact ⟨hx, hu, he, hown⟩

/-- **Transfer.** A dominion of `b` is a dominion of a game `c` that agrees with `b` on it. -/
private theorem Agree.dominion (A : Agree b c α D) (hD : b.IsDominion α D) :
    c.IsDominion α D := by
  have hD' : b.IsDominion α D := hD
  obtain ⟨hDb, hcl, σ, hW⟩ := hD
  refine ⟨A.vs, fun v hv ho w he => ?_, σ, fun v₀ hv₀ => ⟨fun w hw => ?_, fun p hp0 hp => ?_⟩⟩
  · have ho' : b.owner v ≠ α := by rw [← A.owner v hv]; exact ho
    exact hcl v hv ho' w (A.opp v hv ho' w he)
  · have hr := A.reach hD' (hW v₀ hv₀) hw
    obtain ⟨u, hu⟩ := (hW v₀ hv₀).1 w hr
    exact ⟨u, A.step_bc hDb (hW v₀ hv₀) hr hu⟩
  · have hreach : ∀ n, Relation.ReflTransGen (c.toGame.Step (embed D) α σ) (.inl v₀) (p n) := by
      intro n
      induction n with
      | zero => rw [hp0]
      | succ n ih => exact ih.tail (hp n)
    have hp₁ : b.toGame.ConformingPlay (embed D) α σ p := fun n =>
      A.step_cb hD' (hW v₀ hv₀) (A.reach hD' (hW v₀ hv₀) (hreach n)) (hp n)
    have hwon := (hW v₀ hv₀).2 p hp0 hp₁
    have hprio : ∀ n, c.toGame.prio (p n) = b.toGame.prio (p n) := by
      intro n
      have hmem := (hp n).1
      rcases hpn : p n with v | q
      · rw [hpn] at hmem
        exact A.prio v (mem_embed_inl.1 hmem)
      · cases q <;> rfl
    have hmap : p.map c.toGame.prio = p.map b.toGame.prio := by
      unfold ωSequence.map
      congr 1
      funext n
      exact hprio n
    unfold Game.PlayWonBy Game.MaxInfPrio at hwon ⊢
    rw [hmap]
    exact hwon

/-! ### No vertex is won by both players -/

/-- The dominions of the two players are disjoint. -/
private theorem not_both {i : Player} {v : V} (h₁ : b.Wins i v) (h₂ : b.Wins i.opp v) : False := by
  classical
  obtain ⟨D, ⟨-, hcl, σ, hW⟩, hv⟩ := h₁
  obtain ⟨D', ⟨-, hcl', τ, hW'⟩, hv'⟩ := h₂
  set T := b.toGame
  let nxt : V ⊕ Player → V ⊕ Player := fun x => if T.owner x = i then σ x else τ x
  let r : ωSequence (V ⊕ Player) := ⟨fun n => nxt^[n] (.inl v)⟩
  have hrs : ∀ n, r (n + 1) = nxt (r n) := fun n => by
    show nxt^[n + 1] (.inl v) = nxt (nxt^[n] (.inl v))
    rw [Function.iterate_succ_apply']
  -- the successor of a vertex reachable for both is a step for both
  have hstep : ∀ x, Relation.ReflTransGen (T.Step (embed D) i σ) (.inl v) x →
      Relation.ReflTransGen (T.Step (embed D') i.opp τ) (.inl v) x →
      T.Step (embed D) i σ x (nxt x) ∧ T.Step (embed D') i.opp τ x (nxt x) := by
    intro x h₁ h₂
    have hxD : x ∈ embed D := by
      rcases Relation.ReflTransGen.cases_tail h₁ with rfl | ⟨_, -, hs⟩
      · exact mem_embed_inl.2 hv
      · exact hs.2.1
    have hxD' : x ∈ embed D' := by
      rcases Relation.ReflTransGen.cases_tail h₂ with rfl | ⟨_, -, hs⟩
      · exact mem_embed_inl.2 hv'
      · exact hs.2.1
    -- a move along an edge from `x` that the closure of the other dominion keeps inside
    have hin : ∀ (E : Set V) (j : Player), (∀ u ∈ E, b.owner u ≠ j → ∀ w, b.edge u w → w ∈ E) →
        x ∈ embed E → T.owner x ≠ j → ∀ y, T.edge x y → y ∈ embed E := by
      intro E j hclE hxE ho y he
      rcases x with u | q
      · rcases y with w | q'
        · exact mem_embed_inl.2 (hclE u (mem_embed_inl.1 hxE) ho w he)
        · exact mem_embed_inr
      · rcases y with w | q'
        · exact he.elim
        · exact mem_embed_inr
    by_cases ho : T.owner x = i
    · obtain ⟨y, hy⟩ := (hW v hv).1 x h₁
      have e : y = nxt x := by rw [hy.2.2.2 ho]; simp [nxt, ho]
      rw [← e]
      refine ⟨hy, hxD', hin D' i.opp hcl' hxD' (by rw [ho]; exact (opp_ne' i).symm) y hy.2.2.1,
        hy.2.2.1, fun h => absurd (ho.symm.trans h) (opp_ne' i).symm⟩
    · obtain ⟨y, hy⟩ := (hW' v hv').1 x h₂
      have ho' : T.owner x = i.opp := owner_ne ho
      have e : y = nxt x := by rw [hy.2.2.2 ho']; simp [nxt, ho]
      rw [← e]
      exact ⟨⟨hxD, hin D i hcl hxD ho y hy.2.2.1, hy.2.2.1, fun h => absurd h ho⟩, hy⟩
  have hboth : ∀ n, Relation.ReflTransGen (T.Step (embed D) i σ) (.inl v) (r n) ∧
      Relation.ReflTransGen (T.Step (embed D') i.opp τ) (.inl v) (r n) := by
    intro n
    induction n with
    | zero => exact ⟨.refl, .refl⟩
    | succ n ih =>
      have h := hstep _ ih.1 ih.2
      rw [hrs]
      exact ⟨ih.1.tail h.1, ih.2.tail h.2⟩
  have hr0 : r 0 = .inl v := rfl
  have hc₁ : T.ConformingPlay (embed D) i σ r := fun n => by
    rw [hrs]; exact (hstep _ (hboth n).1 (hboth n).2).1
  have hc₂ : T.ConformingPlay (embed D') i.opp τ r := fun n => by
    rw [hrs]; exact (hstep _ (hboth n).1 (hboth n).2).2
  obtain ⟨m, hm, e⟩ := (hW v hv).2 r hr0 hc₁
  obtain ⟨m', hm', e'⟩ := (hW' v hv').2 r hr0 hc₂
  rw [T.maxInfPrio_unique hm hm', e'] at e
  exact opp_ne' i e

/-! ### Determinacy -/

private instance : Finite Player :=
  Finite.of_surjective (fun b : Bool => if b then Player.zero else Player.one)
    fun p => by cases p
                · exact ⟨true, rfl⟩
                · exact ⟨false, rfl⟩

/-- Every vertex of a finite incomplete game is won by one of the players. -/
private theorem determined [Finite V] (b : IncompleteGame V) {v : V} (hv : v ∈ b.vs) :
    ∃ i, b.Wins i v := by
  classical
  set T := b.toGame
  have hsub : T.IsSubgame Set.univ := fun x _ => by
    obtain ⟨y, hy⟩ := T.total x
    exact ⟨y, Set.mem_univ _, hy⟩
  have hS := T.zielonkaAux_strong _ Set.univ rfl hsub
  set r := T.zielonkaAux Set.univ
  have hcov : Sum.inl v ∈ r.win .zero ∪ r.win .one := by rw [hS.cover]; trivial
  have key : ∀ i, Sum.inl v ∈ r.win i → b.Wins i v := by
    intro i hvi
    have hreg := hS.region i
    let D : Set V := {u | u ∈ b.vs ∧ Sum.inl u ∈ r.win i}
    have hmem : ∀ x y, x ∈ r.win i → T.edge x y → y ∈ r.win i → x ∈ embed D → y ∈ embed D := by
      intro x y _ he hy hx
      rcases x with u | q
      · rcases y with w | q'
        · exact mem_embed_inl.2 ⟨(b.edge_mem u w he).2, hy⟩
        · exact mem_embed_inr
      · rcases y with w | q'
        · exact he.elim
        · exact mem_embed_inr
    have hstep : ∀ x y, x ∈ r.win i → T.Step (embed D) i (r.strat i) x y → y ∈ r.win i := by
      rintro x y hx ⟨-, -, he, hs⟩
      by_cases ho : T.owner x = i
      · rw [hs ho]; exact (hreg.mine x hx ho).1
      · exact hreg.theirs x hx ho y (Set.mem_univ _) he
    refine ⟨D, ⟨fun u hu => hu.1, fun u hu ho w he => ⟨(b.edge_mem u w he).2,
      hreg.theirs _ hu.2 ho _ (Set.mem_univ _) he⟩, r.strat i, fun u hu => ⟨?_, ?_⟩⟩,
      hv, hvi⟩
    · intro x hx
      have hxW : x ∈ r.win i ∧ x ∈ embed D := by
        induction hx with
        | refl => exact ⟨hu.2, mem_embed_inl.2 hu⟩
        | tail _ hs ih => exact ⟨hstep _ _ ih.1 hs, hs.2.1⟩
      by_cases ho : T.owner x = i
      · obtain ⟨hσ, he⟩ := hreg.mine x hxW.1 ho
        exact ⟨_, hxW.2, hmem x _ hxW.1 he hσ hxW.2, he, fun _ => rfl⟩
      · obtain ⟨y, hy⟩ := T.total x
        have hyW := hreg.theirs x hxW.1 ho y (Set.mem_univ _) hy
        exact ⟨y, hxW.2, hmem x y hxW.1 hy hyW hxW.2, hy, fun h => absurd h ho⟩
    · intro p hp0 hp
      have hall : ∀ n, p n ∈ r.win i := by
        intro n
        induction n with
        | zero => rw [hp0]; exact hu.2
        | succ n ih => exact hstep _ _ ih (hp n)
      exact hreg.won p fun n => ⟨hall n, (hp n).2.2.1, (hp n).2.2.2⟩
  rcases hcov with h | h
  · exact ⟨_, key _ h⟩
  · exact ⟨_, key _ h⟩

/-! ### Theorem 1 -/

private theorem extends_refl (a : IncompleteGame V) : a.Extends a :=
  ⟨subset_rfl, fun _ _ => rfl, fun _ _ h => h, fun _ _ _ h => h, fun _ _ => rfl,
    Set.inter_subset_left⟩

private theorem safeOptimal_aux [Finite V] (a : IncompleteGame V) : a.SafeOptimal := by
  classical
  rintro ⟨z, hz⟩ v hv
  constructor
  · intro hund
    obtain ⟨α, hα⟩ := determined a hv
    refine ⟨α, a, withSink a α z hz, extends_refl a, (withSink_dom a α z hz).1, hα, ?_⟩
    obtain ⟨hext, hE, hunsafe⟩ := withSink_dom a α z hz
    set a₂ := withSink a α z hz with ha₂
    have hzE : z ∈ a₂.attr α.opp {z} := ⟨1, Or.inl rfl⟩
    obtain ⟨j, hj⟩ := determined a₂ (Set.mem_insert_of_mem _ hv)
    rcases Player.eq_or_eq_opp j α with rfl | rfl
    · -- if `j` wins `v` in `a₂`, its dominion lies in the safe part, so `v ∈ W_j`
      exfalso
      obtain ⟨D', hD', hvD'⟩ := hj
      have hsafe : ∀ u ∈ D', u ∈ a.vs ∧ u ∈ a.safe j := by
        intro u hu
        have hboth : u ∉ a₂.attr j.opp {z} := fun hE' =>
          not_both ⟨D', hD', hu⟩ ⟨_, hE, hE'⟩
        rcases hD'.1 hu with rfl | hua
        · exact absurd hzE hboth
        · exact ⟨hua, by_contra fun hns => hboth (hunsafe ⟨hua, hns⟩)⟩
      have A : Agree a₂ (a.restrict (a.safe j)) j D' := by
        refine ⟨fun u hu => ⟨(hsafe u hu).1, (hsafe u hu).2⟩, fun u hu => ?_, fun _ _ => rfl,
          fun u hu _ w he => Or.inl he.1, fun u hu w hw he => ?_⟩
        · show a.owner u = (if u = z then j else a.owner u)
          have hne : u ≠ z := fun (e : u = z) => hz (e ▸ (hsafe u hu).1)
          simp only [hne, ↓reduceIte]
        · rcases he with he | ⟨-, rfl⟩
          · exact ⟨he, (hsafe u hu).2, (hsafe w hw).2⟩
          · exact absurd (hsafe w hw).1 hz
      have hwon : v ∈ a.safeWon j := ⟨D', A.dominion hD', hvD'⟩
      rcases j with _ | _
      · exact hund.2 (Or.inl hwon)
      · exact hund.2 (Or.inr hwon)
    · exact hj
  · rintro ⟨α, a₁, a₂, h₁, h₂, hw₁, hw₂⟩
    refine ⟨hv, fun hwon => ?_⟩
    have hβ : ∃ β, v ∈ a.safeWon β := by
      rcases hwon with h | h
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    obtain ⟨β, D, hD, hvD⟩ := hβ
    rcases Player.eq_or_eq_opp β α with rfl | rfl
    · exact not_both ⟨D, a.dominionsSurvive_aux β D a₂ h₂ hD, hvD⟩ hw₂
    · exact not_both hw₁ ⟨D, a.dominionsSurvive_aux α.opp D a₁ h₁ hD, hvD⟩

end IncompleteGame

/-- **Theorem 1 of [Laveaux2022].** -/
public theorem IncompleteGame.safeOptimal [Finite V] (a : IncompleteGame V) : a.SafeOptimal :=
  a.safeOptimal_aux

end MercLib.ParityGame
