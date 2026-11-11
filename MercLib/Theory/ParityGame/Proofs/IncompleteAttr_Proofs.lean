module

public import MercLib.Theory.ParityGame.Incomplete
import all MercLib.Theory.ParityGame.Proofs.Game_Proofs
import all MercLib.Theory.ParityGame.Proofs.Incomplete_Proofs
import all MercLib.Theory.ParityGame.Proofs.IncompleteDominion_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The attractor of a dominion is a dominion, and Corollaries 2 and 3 of [Laveaux2022]. The strategy
on the attractor moves each vertex of `α` outside the dominion to a lower stage of the attractor,
and follows the dominion's strategy inside it; the opponent's vertices outside the dominion have
all their successors in a lower stage, so every play reaches the dominion and stays there. -/

namespace MercLib.ParityGame

open Cslib (ωSequence)

variable {V : Type*}

namespace IncompleteGame

variable {b : IncompleteGame V} {α : Player} {D : Set V}

/-! ### Stages and ranks -/

private theorem cpre_mono {U U' : Set V} (h : U ⊆ U') : b.cpre α U ⊆ b.cpre α U' := by
  rintro v (⟨ho, hv, w, hw, he⟩ | ⟨ho, hn⟩)
  · exact Or.inl ⟨ho, hv, w, h hw, he⟩
  · refine Or.inr ⟨ho, fun hc => hn ?_⟩
    rcases hc with ⟨hv, w, hw, he⟩ | hs
    · exact Or.inl ⟨hv, w, ⟨hw.1, fun hwU => hw.2 (h hwU)⟩, he⟩
    · exact Or.inr hs

private theorem stage_succ_mono (k : ℕ) : b.attrStage α D k ⊆ b.attrStage α D (k + 1) := by
  induction k with
  | zero => exact Set.empty_subset _
  | succ k ih => exact Set.union_subset_union_right _ (cpre_mono ih)

private theorem stage_mono : Monotone (b.attrStage α D) :=
  monotone_nat_of_le_succ stage_succ_mono

private theorem stage_subset_attr (k : ℕ) : b.attrStage α D k ⊆ b.attr α D :=
  fun _ hv => ⟨k, hv⟩

private theorem attr_subset_vs (hD : D ⊆ b.vs) : b.attr α D ⊆ b.vs := by
  rintro v ⟨k, hk⟩
  cases k with
  | zero => exact hk.elim
  | succ k =>
    rcases hk with hk | ⟨⟨hv, -⟩, -⟩ | ⟨⟨hv, -⟩, -⟩
    · exact hD hk
    · exact hv
    · exact hv

open scoped Classical in
/-- The first stage of the attractor that contains `v`. -/
private noncomputable def rank (b : IncompleteGame V) (α : Player) (D : Set V) (v : V) : ℕ :=
  if h : ∃ k, v ∈ b.attrStage α D k then Nat.find h else 0

private theorem mem_rank {v : V} (hv : v ∈ b.attr α D) : v ∈ b.attrStage α D (b.rank α D v) := by
  classical
  have hv' : ∃ k, v ∈ b.attrStage α D k := hv
  rw [rank, dite_eq_left_of_eq_true (eq_true hv')]; exact Nat.find_spec hv'

private theorem rank_le {v : V} {k : ℕ} (hv : v ∈ b.attrStage α D k) : b.rank α D v ≤ k := by
  classical
  rw [rank, dite_eq_left_of_eq_true (eq_true ⟨k, hv⟩)]; exact Nat.find_min' _ hv

/-- A vertex of the attractor outside `D` is in the control predecessor of the stage before its
own. -/
private theorem mem_cpre_of_out {v : V} (hv : v ∈ b.attr α D) (hvD : v ∉ D) :
    v ∈ b.cpre α (b.attrStage α D (b.rank α D v - 1)) := by
  have h := mem_rank hv
  cases hr : b.rank α D v with
  | zero => rw [hr] at h; exact h.elim
  | succ k =>
    rw [hr] at h
    rcases h with h | h
    · exact absurd h hvD
    · simpa using h

/-! ### The strategy on the attractor -/

open scoped Classical in
/-- On a vertex of the attractor outside `D`, move to a successor in a lower stage; elsewhere
follow `σ`. -/
private noncomputable def attrStrat (b : IncompleteGame V) (α : Player) (D : Set V)
    (σ : Strategy (V ⊕ Player)) : Strategy (V ⊕ Player)
  | .inl v =>
    if v ∈ D then σ (.inl v)
    else if h : ∃ w ∈ b.attrStage α D (b.rank α D v - 1), b.edge v w then .inl h.choose
    else σ (.inl v)
  | .inr q => σ (.inr q)

variable {σ : Strategy (V ⊕ Player)}

/-- The successors of a vertex of the attractor outside `D` lie in a lower stage. -/
private theorem out_step {v : V} (hv : v ∈ b.attr α D) (hvD : v ∉ D) {y : V ⊕ Player}
    (he : b.toGame.edge (.inl v) y) (hown : b.owner v = α → y = attrStrat b α D σ (.inl v)) :
    ∃ w, y = .inl w ∧ w ∈ b.attr α D ∧ b.rank α D w < b.rank α D v := by
  have hc := mem_cpre_of_out hv hvD
  have hpos : 0 < b.rank α D v := by
    rcases Nat.eq_zero_or_pos (b.rank α D v) with h | h
    · have := mem_rank hv; rw [h] at this; exact this.elim
    · exact h
  have hlow : ∀ w, w ∈ b.attrStage α D (b.rank α D v - 1) →
      w ∈ b.attr α D ∧ b.rank α D w < b.rank α D v := fun w hw =>
    ⟨⟨_, hw⟩, lt_of_le_of_lt (rank_le hw) (by omega)⟩
  rcases hc with ⟨⟨hvs, ho⟩, -, w, hw, hew⟩ | ⟨⟨hvs, ho⟩, hn⟩
  · -- `α` moves to the chosen successor in the lower stage
    have hex : ∃ w ∈ b.attrStage α D (b.rank α D v - 1), b.edge v w := ⟨w, hw, hew⟩
    have hy := hown ho
    simp only [attrStrat, hvD, ↓reduceIte, hex, ↓reduceDIte] at hy
    exact ⟨_, hy, hlow _ hex.choose_spec.1⟩
  · -- the opponent has all successors in the lower stage and is not a sink
    rcases y with w | q
    · refine ⟨w, rfl, hlow w ?_⟩
      by_contra hw
      exact hn (Or.inl ⟨hvs, w, ⟨(b.edge_mem v w he).2, hw⟩, he⟩)
    · rcases he with ⟨hs, -⟩ | ⟨hnv, -⟩
      · exact absurd (Or.inr hs) hn
      · exact absurd hvs hnv

/-- A vertex of the attractor outside `D` can move. -/
private theorem out_move {v : V} (hv : v ∈ b.attr α D) (hvD : v ∉ D) :
    ∃ y, b.toGame.edge (.inl v) y ∧ (b.owner v = α → y = attrStrat b α D σ (.inl v)) := by
  have hc := mem_cpre_of_out hv hvD
  rcases hc with ⟨⟨-, ho⟩, -, w, hw, hew⟩ | ⟨⟨hvs, ho⟩, hn⟩
  · have hex : ∃ w ∈ b.attrStage α D (b.rank α D v - 1), b.edge v w := ⟨w, hw, hew⟩
    refine ⟨.inl hex.choose, hex.choose_spec.2, fun _ => ?_⟩
    simp only [attrStrat, hvD, ↓reduceIte, hex, ↓reduceDIte]
  · have : ∃ w, b.edge v w := by
      by_contra h
      exact hn (Or.inr ⟨hvs, fun w hw => h ⟨w, hw⟩⟩)
    obtain ⟨w, hw⟩ := this
    refine ⟨.inl w, hw, fun h => absurd (h.symm.trans ho) ?_⟩
    exact (opp_ne' α).symm

private theorem embed_mono {U U' : Set V} (h : U ⊆ U') : embed U ⊆ embed U' := by
  rintro x (⟨v, hv, rfl⟩ | ⟨q, rfl⟩)
  · exact Or.inl ⟨v, h hv, rfl⟩
  · exact Or.inr ⟨q, rfl⟩

private theorem subset_attr' : D ⊆ b.attr α D := fun _ hv => ⟨1, Or.inl hv⟩

/-- Inside the dominion, the steps of the attractor strategy are those of `σ`. -/
private theorem in_step (hD : b.IsDominion α D) {u : V} (hu : u ∈ D)
    (hW : b.toGame.WinsFrom (embed D) α σ (.inl u)) {x y : V ⊕ Player}
    (hr : Relation.ReflTransGen (b.toGame.Step (embed D) α σ) (.inl u) x)
    (h : b.toGame.Step (embed (b.attr α D)) α (attrStrat b α D σ) x y) :
    b.toGame.Step (embed D) α σ x y := by
  have hxD : x ∈ embed D := by
    rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨_, -, hs⟩
    · exact mem_embed_inl.2 hu
    · exact hs.2.1
  obtain ⟨-, -, he, hown⟩ := h
  rcases x with v | q
  · have hvD := mem_embed_inl.1 hxD
    by_cases ho : b.owner v = α
    · obtain ⟨y', hy'⟩ := hW.1 _ hr
      have e₁ : y' = σ (.inl v) := hy'.2.2.2 ho
      have e₂ : y = σ (.inl v) := by
        rw [hown ho]; simp [attrStrat, hvD]
      rw [e₂, ← e₁]; exact hy'
    · refine ⟨hxD, ?_, he, fun h => absurd h ho⟩
      rcases y with w | q
      · exact mem_embed_inl.2 (hD.2.1 v hvD ho w he)
      · exact mem_embed_inr
  · rcases y with w | q'
    · exact he.elim
    · exact ⟨hxD, mem_embed_inr, he, fun h => hown h⟩

/-- A step of `σ` inside the dominion is a step of the attractor strategy. -/
private theorem in_step' {x y : V ⊕ Player} (h : b.toGame.Step (embed D) α σ x y) :
    b.toGame.Step (embed (b.attr α D)) α (attrStrat b α D σ) x y := by
  obtain ⟨hx, hy, he, hown⟩ := h
  refine ⟨embed_mono subset_attr' hx, embed_mono subset_attr' hy, he, fun ho => ?_⟩
  rcases x with v | q
  · rw [hown ho]; simp [attrStrat, mem_embed_inl.1 hx]
  · exact hown ho

/-- A reachable vertex is outside the dominion in the attractor, or reachable inside the dominion
from one of its vertices. -/
private theorem reach_cases (hD : b.IsDominion α D)
    (hW : ∀ u ∈ D, b.toGame.WinsFrom (embed D) α σ (.inl u)) {v₀ : V}
    (hv₀ : v₀ ∈ b.attr α D) {x : V ⊕ Player}
    (h : Relation.ReflTransGen (b.toGame.Step (embed (b.attr α D)) α (attrStrat b α D σ))
      (.inl v₀) x) :
    (∃ v, x = .inl v ∧ v ∈ b.attr α D ∧ v ∉ D) ∨
      ∃ u ∈ D, Relation.ReflTransGen (b.toGame.Step (embed D) α σ) (.inl u) x := by
  induction h with
  | refl =>
    by_cases h : v₀ ∈ D
    · exact Or.inr ⟨v₀, h, .refl⟩
    · exact Or.inl ⟨v₀, rfl, hv₀, h⟩
  | tail _ hs ih =>
    rcases ih with ⟨v, rfl, hv, hvD⟩ | ⟨u, hu, hr⟩
    · obtain ⟨w, rfl, hw, -⟩ := out_step hv hvD hs.2.2.1 hs.2.2.2
      by_cases hwD : w ∈ D
      · exact Or.inr ⟨w, hwD, .refl⟩
      · exact Or.inl ⟨w, rfl, hw, hwD⟩
    · exact Or.inr ⟨u, hu, hr.tail (in_step hD hu (hW u hu) hr hs)⟩

/-- **The attractor of a dominion is a dominion.** -/
private theorem attr_dominion (hD : b.IsDominion α D) : b.IsDominion α (b.attr α D) := by
  obtain ⟨hDvs, hcl, σ, hW⟩ := hD
  have hD : b.IsDominion α D := ⟨hDvs, hcl, σ, hW⟩
  refine ⟨attr_subset_vs hDvs, ?_, attrStrat b α D σ, fun v₀ hv₀ => ⟨?_, ?_⟩⟩
  · intro v hv ho w he
    by_cases hvD : v ∈ D
    · exact subset_attr' (hcl v hvD ho w he)
    · obtain ⟨w', e, hw', -⟩ := out_step (σ := σ) (y := .inl w) hv hvD he fun h => absurd h ho
      exact (Sum.inl_injective e) ▸ hw'
  · intro x hx
    rcases reach_cases hD hW hv₀ hx with ⟨v, rfl, hv, hvD⟩ | ⟨u, hu, hr⟩
    · obtain ⟨y, he, hown⟩ := out_move (σ := σ) hv hvD
      obtain ⟨w, rfl, hw, -⟩ := out_step hv hvD he hown
      exact ⟨_, Or.inl ⟨v, hv, rfl⟩, Or.inl ⟨w, hw, rfl⟩, he, hown⟩
    · obtain ⟨y, hy⟩ := (hW u hu).1 _ hr
      exact ⟨y, in_step' hy⟩
  · intro p hp0 hp
    -- the play reaches the dominion
    have hreach : ∀ r n v, p n = .inl v → v ∈ b.attr α D → b.rank α D v ≤ r →
        ∃ N u, u ∈ D ∧ p N = .inl u := by
      intro r
      induction r with
      | zero =>
        intro n v hn hv hr
        by_cases hvD : v ∈ D
        · exact ⟨n, v, hvD, hn⟩
        · have := mem_rank hv
          rw [show b.rank α D v = 0 by omega] at this
          exact this.elim
      | succ r ih =>
        intro n v hn hv hr
        by_cases hvD : v ∈ D
        · exact ⟨n, v, hvD, hn⟩
        · have hs := hp n
          rw [hn] at hs
          obtain ⟨w, hw, hwa, hlt⟩ := out_step hv hvD hs.2.2.1 hs.2.2.2
          exact ih (n + 1) w hw hwa (by omega)
    obtain ⟨N, u, hu, hN⟩ := hreach _ 0 v₀ hp0 hv₀ le_rfl
    -- from there on, it is a play of `σ` in the dominion
    have hsuf : ∀ i, Relation.ReflTransGen (b.toGame.Step (embed D) α σ) (.inl u) (p (i + N)) := by
      intro i
      induction i with
      | zero => rw [Nat.zero_add, hN]
      | succ i ih =>
        have hs := hp (i + N)
        rw [show i + N + 1 = i + 1 + N by omega] at hs
        exact ih.tail (in_step hD hu (hW u hu) ih hs)
    have hconf : b.toGame.ConformingPlay (embed D) α σ (p.drop N) := by
      intro i
      have hs := hp (i + N)
      rw [show i + N + 1 = i + 1 + N by omega] at hs
      exact in_step hD hu (hW u hu) (hsuf i) hs
    have hwon := (hW u hu).2 (p.drop N) (by simp [hN]) hconf
    exact (b.toGame.playWonBy_drop α p N).1 hwon

/-! ### Corollaries 2 and 3 -/

/-- A play that ends in the self-loop `inr q` is won by `q`. -/
private theorem wonBy_inr {p : ωSequence (V ⊕ Player)} {N : ℕ} {q : Player}
    (h : ∀ k, N ≤ k → p k = .inr q) : b.toGame.PlayWonBy q p := by
  refine ⟨b.toGame.prio (.inr q), ⟨?_, fun m hm => ?_⟩, ofPrio_inr q b⟩
  · refine Filter.frequently_atTop.2 fun c => ⟨max c N, le_max_left _ _, ?_⟩
    show b.toGame.prio (p (max c N)) = _
    rw [h _ (le_max_right _ _)]
  · obtain ⟨k, hk, e⟩ := Filter.frequently_atTop.1 hm N
    have e' : b.toGame.prio (p k) = m := e
    rw [h k hk] at e'
    exact e'.symm.le

end IncompleteGame

variable (a : IncompleteGame V)

namespace IncompleteGame

private theorem sAttrDominion_aux : a.SAttrDominion := by
  intro α X a' hext hX hdom
  rw [← a.safeAttrEq_aux α X hX]
  exact a.dominionsSurvive_aux α _ a' hext (attr_dominion hdom)

/-- A set of sinks of the opponent of `β` is a `β`-dominion: the opponent cannot move there. -/
private theorem sinks_dominion (b : IncompleteGame V) (β : Player) (X : Set V)
    (hX : ∀ v ∈ X, v ∈ b.vs ∧ b.owner v = β.opp ∧ ∀ w, ¬ b.edge v w) : b.IsDominion β X := by
  refine ⟨fun v hv => (hX v hv).1, fun v hv _ w he => absurd he ((hX v hv).2.2 w), id,
    fun v hv => ?_⟩
  obtain ⟨hvb, hvo, hsink⟩ := hX v hv
  have hoβ : (b.owner v).opp = β := by rw [hvo, opp_opp']
  -- every step from `inl v` goes to `inr β`, and from `inr β` back to it
  have hstep : ∀ x y, b.toGame.Step (embed X) β id x y →
      (x = .inl v ∨ x = .inr β) → y = .inr β := by
    rintro x y ⟨-, -, he, -⟩ (rfl | rfl)
    · rcases y with w | q
      · exact absurd he (hsink w)
      · rcases he with ⟨-, hq⟩ | ⟨hnv, -⟩
        · rw [hq, hoβ]
        · exact absurd hvb hnv
    · rcases y with w | q
      · exact he.elim
      · rw [show q = β from he]
  have hreach : ∀ x, Relation.ReflTransGen (b.toGame.Step (embed X) β id) (.inl v) x →
      x = .inl v ∨ x = .inr β := by
    intro x hx
    induction hx with
    | refl => exact Or.inl rfl
    | tail _ hs ih => exact Or.inr (hstep _ _ hs ih)
  refine ⟨fun x hx => ?_, fun p hp0 hp => ?_⟩
  · refine ⟨.inr β, ?_⟩
    rcases hreach x hx with rfl | rfl
    · refine ⟨mem_embed_inl.2 hv, mem_embed_inr, Or.inl ⟨⟨hvb, hsink⟩, hoβ.symm⟩, fun h => ?_⟩
      exact absurd (h.symm.trans hvo) (opp_ne' β).symm
    · exact ⟨mem_embed_inr, mem_embed_inr, rfl, fun _ => rfl⟩
  · have hall : ∀ n, p n = .inl v ∨ p n = .inr β := by
      intro n
      induction n with
      | zero => exact Or.inl hp0
      | succ n ih => exact Or.inr (hstep _ _ (hp n) ih)
    exact wonBy_inr (N := 1) fun k hk => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [Nat.add_comm]
      exact hstep _ _ (hp k) (hall k)

private theorem sinkAttrDominion_aux : a.SinkAttrDominion := by
  intro α a' hext
  set X := (a.own α.opp ∩ a.sinks) \ a.I with hXdef
  have hXsafe : X ⊆ a.safe α := by
    rintro v ⟨⟨⟨hv, ho⟩, -, hs⟩, hI⟩
    exact ⟨hv, a.not_mem_attr_of_own (fun h => hI h.2) ho fun w he => absurd he (hs w)⟩
  have hdom : (a.restrict (a.safe α)).IsDominion α X := by
    refine sinks_dominion _ α X fun v hv => ⟨⟨hv.1.1.1, hXsafe hv⟩, hv.1.1.2, fun w he => ?_⟩
    exact hv.1.2.2 w he.1
  rw [← a.safeAttrEq_aux α X hXsafe]
  exact a.dominionsSurvive_aux α _ a' hext (attr_dominion hdom)

open scoped Classical in
/-- The extension of Lemma 2: a fresh sink `z` of `α`, reachable from every incomplete vertex,
and no incomplete vertices left. -/
private noncomputable def withSink (a : IncompleteGame V) (α : Player) (z : V) (hz : z ∉ a.vs) :
    IncompleteGame V where
  vs := insert z a.vs
  owner v := if v = z then α else a.owner v
  edge v w := a.edge v w ∨ (v ∈ a.I ∧ w = z)
  prio := a.prio
  edge_mem v w h := by
    rcases h with h | ⟨hv, rfl⟩
    · exact ⟨Set.mem_insert_of_mem _ (a.edge_mem v w h).1,
        Set.mem_insert_of_mem _ (a.edge_mem v w h).2⟩
    · exact ⟨Set.mem_insert_of_mem _ (a.I_sub hv), Set.mem_insert _ _⟩
  I := ∅
  I_sub := Set.empty_subset _

/-- The extension `withSink` of Lemma 2, and the opponent's dominion in it. -/
private theorem withSink_dom (α : Player) (z : V) (hz : z ∉ a.vs) :
    a.Extends (withSink a α z hz) ∧
      (withSink a α z hz).IsDominion α.opp ((withSink a α z hz).attr α.opp {z}) ∧
      a.vs \ a.safe α ⊆ (withSink a α z hz).attr α.opp {z} := by
  set a' := withSink a α z hz with ha'
  have hne : ∀ {v}, v ∈ a.vs → v ≠ z := fun hv e => hz (e ▸ hv)
  have hown : ∀ {v}, v ∈ a.vs → a'.owner v = a.owner v := fun hv => by
    simp [ha', withSink, hne hv]
  have hext : a.Extends a' := by
    refine ⟨fun v hv => Set.mem_insert_of_mem _ hv, fun v hv => hown hv, fun v w h => Or.inl h,
      fun v hv w h => ?_, fun _ _ => rfl, fun v hv => hv.1.elim⟩
    rcases h with h | ⟨hI, -⟩
    · exact h
    · exact absurd hI hv.2
  -- the fresh sink is won by the opponent, and so is its attractor
  have hzdom : a'.IsDominion α.opp {z} := by
    refine sinks_dominion a' α.opp {z} fun v hv => ?_
    rw [Set.mem_singleton_iff.1 hv]
    refine ⟨Set.mem_insert _ _, by simp [ha', withSink, opp_opp'], fun w he => ?_⟩
    rcases he with he | ⟨hI, -⟩
    · exact hz (a.edge_mem z w he).1
    · exact hz (a.I_sub hI)
  refine ⟨hext, attr_dominion hzdom, ?_⟩
  -- the opponent's attractor in `a` lies in the attractor of `z` in `a'`, one stage later
  have hz1 : ∀ k, z ∈ a'.attrStage α.opp {z} (k + 1) := fun k => Or.inl rfl
  have hstage : ∀ k, a.attrStage α.opp (a.own α.opp ∩ a.I) k ⊆
      a'.attrStage α.opp {z} (k + 1) := by
    intro k
    induction k with
    | zero => exact Set.empty_subset _
    | succ k ih =>
      rintro u (⟨⟨hu, ho⟩, hI⟩ | ⟨⟨hu, ho⟩, -, w, hw, he⟩ | ⟨⟨hu, ho⟩, hn⟩)
      · -- an incomplete vertex of the opponent moves to `z`
        refine Or.inr (Or.inl ⟨⟨Set.mem_insert_of_mem _ hu, (hown hu).trans ho⟩,
          Set.mem_insert_of_mem _ hu, z, hz1 k, Or.inr ⟨hI, rfl⟩⟩)
      · refine Or.inr (Or.inl ⟨⟨Set.mem_insert_of_mem _ hu, (hown hu).trans ho⟩,
          Set.mem_insert_of_mem _ hu, w, ih hw, Or.inl he⟩)
      · refine Or.inr (Or.inr ⟨⟨Set.mem_insert_of_mem _ hu, (hown hu).trans ho⟩, ?_⟩)
        rintro (⟨-, w, ⟨-, hw⟩, he⟩ | ⟨-, hs⟩)
        · rcases he with he | ⟨-, rfl⟩
          · refine hn (Or.inl ⟨hu, w, ⟨(a.edge_mem u w he).2, fun hwk => hw (ih hwk)⟩, he⟩)
          · exact hw (hz1 k)
        · exact hn (Or.inr ⟨hu, fun w he => hs w (Or.inl he)⟩)
  rintro v ⟨hv, hvs⟩
  have hvT : v ∈ a.attr α.opp (a.own α.opp ∩ a.I) := by
    by_contra h; exact hvs ⟨hv, h⟩
  obtain ⟨k, hk⟩ := hvT
  exact ⟨k + 1, hstage k hk⟩

private theorem unsafeLost_aux : a.UnsafeLost := by
  rintro ⟨z, hz⟩ α
  obtain ⟨h₁, h₂, h₃⟩ := withSink_dom a α z hz
  exact ⟨_, h₁, _, h₂, h₃⟩

end IncompleteGame

/-- **Corollary 2 of [Laveaux2022].** -/
public theorem IncompleteGame.sAttrDominion (a : IncompleteGame V) : a.SAttrDominion :=
  a.sAttrDominion_aux

/-- **Corollary 3 of [Laveaux2022].** -/
public theorem IncompleteGame.sinkAttrDominion (a : IncompleteGame V) : a.SinkAttrDominion :=
  a.sinkAttrDominion_aux

/-- **Lemma 2 of [Laveaux2022].** -/
public theorem IncompleteGame.unsafeLost (a : IncompleteGame V) : a.UnsafeLost :=
  a.unsafeLost_aux

end MercLib.ParityGame
