module

public import MercLib.Theory.ParityGame.Incomplete
import all MercLib.Theory.ParityGame.Proofs.Incomplete_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Lemma 1 of [Laveaux2022]: an `α`-dominion of `a ∩ safe_α(a)` is an `α`-dominion of every
extension `a'` of `a`. The same strategy wins: a conforming play of `a'` from the dominion only
uses edges of the safe subgame, since the opponent's vertices there are complete and all their
successors are safe, and the strategy never reaches a sink of `α` (it would lose there). -/

namespace MercLib.ParityGame

open Cslib (ωSequence)

variable {V : Type*}

/-- A finite path of a reflexive-transitive closure, as a function on `0, …, n`. -/
private theorem exists_path {β : Type*} {R : β → β → Prop} {x y : β}
    (h : Relation.ReflTransGen R x y) :
    ∃ (n : ℕ) (f : ℕ → β), f 0 = x ∧ f n = y ∧ ∀ i < n, R (f i) (f (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => x, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, f, h0, hn, hs⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n then f i else c, by simp [h0], by simp, fun i hi => ?_⟩
    by_cases hin : i + 1 ≤ n
    · simp only [show i ≤ n by omega, hin, ↓reduceIte]; exact hs i (by omega)
    · have : i = n := by omega
      subst this
      simp only [le_refl, show ¬ i + 1 ≤ i by omega, ↓reduceIte, hn]
      exact hbc

namespace IncompleteGame

variable {a a' : IncompleteGame V} {α : Player} {D : Set V}

private theorem ofPrio_inr (q : Player) (b : IncompleteGame V) :
    Player.ofPrio (b.toGame.prio (.inr q)) = q := by
  cases q <;> rfl

private theorem mem_embed_inl {v : V} : Sum.inl v ∈ embed D ↔ v ∈ D := by
  constructor
  · rintro (⟨w, hw, e⟩ | ⟨q, e⟩)
    · exact Sum.inl_injective e ▸ hw
    · cases e
  · intro hv; exact Or.inl ⟨v, hv, rfl⟩

private theorem mem_embed_inr {q : Player} : (Sum.inr q : V ⊕ Player) ∈ embed D :=
  Or.inr ⟨q, rfl⟩

private theorem owner_ne {o α : Player} (h : o ≠ α) : o = α.opp := by
  cases o <;> cases α <;> simp_all [Player.opp]

/-- The assumptions of Lemma 1. -/
private structure Ctx (a a' : IncompleteGame V) (α : Player) (D : Set V) : Prop where
  ext : a.Extends a'
  dom : (a.restrict (a.safe α)).IsDominion α D

variable (C : Ctx a a' α D)

include C

private theorem Ctx.vs {v : V} (hv : v ∈ D) : v ∈ a.vs ∧ v ∈ a.safe α :=
  C.dom.1 hv

private theorem Ctx.owner {v : V} (hv : v ∈ D) : a'.owner v = a.owner v :=
  C.ext.2.1 v (C.vs hv).1

private theorem Ctx.prio {v : V} (hv : v ∈ D) : a'.prio v = a.prio v :=
  C.ext.2.2.2.2.1 v (C.vs hv).1

/-- An opponent vertex of the dominion is complete, and its successors in `a'` are its
successors in the safe subgame. -/
private theorem Ctx.opp_edge {v : V} (hv : v ∈ D) (ho : a.owner v ≠ α) (w : V) :
    a'.edge v w ↔ (a.restrict (a.safe α)).edge v w := by
  obtain ⟨hva, hvs⟩ := C.vs hv
  have hvI : v ∉ a.I := fun hI => hvs.2 (a.subset_attr ⟨⟨hva, owner_ne ho⟩, hI⟩)
  constructor
  · intro he
    have he' : a.edge v w := C.ext.2.2.2.1 v ⟨hva, hvI⟩ w he
    exact ⟨he', hvs, (a.edge_mem v w he').2,
      fun hwT => hvs.2 (a.mem_attr_of_edge hva (owner_ne ho) he' hwT)⟩
  · intro he; exact C.ext.2.2.1 v w he.1

omit C

variable {σ : Strategy (V ⊕ Player)}

/-- The step relations of the two encodings. -/
private abbrev S₁ (a : IncompleteGame V) (α : Player) (D : Set V) (σ : Strategy (V ⊕ Player)) :=
  (a.restrict (a.safe α)).toGame.Step (embed D) α σ

private abbrev S₂ (a' : IncompleteGame V) (α : Player) (D : Set V) (σ : Strategy (V ⊕ Player)) :=
  a'.toGame.Step (embed D) α σ

/-- A winning strategy never reaches a sink of its own player. -/
private theorem no_own_sink {v₀ v : V} (hvD : v ∈ D)
    (hW : (a.restrict (a.safe α)).toGame.WinsFrom (embed D) α σ (.inl v₀))
    (hr : Relation.ReflTransGen (S₁ a α D σ) (.inl v₀) (.inl v)) (ho : a.owner v = α) :
    v ∉ (a.restrict (a.safe α)).sinks := by
  intro hs
  set G₁ := a.restrict (a.safe α) with hG₁
  -- the strategy moves from the sink to the self-loop of the opponent
  have hσ : σ (.inl v) = .inr α.opp := by
    obtain ⟨u, -, -, he, hown⟩ := hW.1 _ hr
    have hu' := hown ho
    rcases u with w | q
    · exact absurd he (hs.2 w)
    · rcases he with ⟨-, hq⟩ | ⟨hnv, -⟩
      · rw [← hu', hq]
        show Sum.inr (a.owner v).opp = _
        rw [ho]
      · exact absurd hs.1 hnv
  obtain ⟨n, f, h0, hn, hsteps⟩ := exists_path hr
  let g : ωSequence (V ⊕ Player) := ⟨fun i => if i ≤ n then f i else .inr α.opp⟩
  have hg : G₁.toGame.ConformingPlay (embed D) α σ g := by
    intro i
    show S₁ a α D σ (if i ≤ n then f i else .inr α.opp)
      (if i + 1 ≤ n then f (i + 1) else .inr α.opp)
    by_cases hi : i + 1 ≤ n
    · simp only [show i ≤ n by omega, hi, ↓reduceIte]; exact hsteps i (by omega)
    · by_cases hin : i = n
      · subst hin
        simp only [le_refl, hi, ↓reduceIte, hn]
        refine ⟨mem_embed_inl.2 hvD, mem_embed_inr, Or.inl ⟨hs, ?_⟩, fun _ => hσ.symm⟩
        show α.opp = (a.owner v).opp
        rw [ho]
      · simp only [show ¬ i ≤ n by omega, hi, ↓reduceIte]
        refine ⟨mem_embed_inr, mem_embed_inr, rfl, fun h => absurd h (opp_ne' α)⟩
  have hg0 : g 0 = .inl v₀ := by
    show (if 0 ≤ n then f 0 else Sum.inr α.opp) = Sum.inl v₀
    simp [h0]
  obtain ⟨m, ⟨hm, -⟩, hmα⟩ := hW.2 g hg0 hg
  have hmeq : m = G₁.toGame.prio (.inr α.opp) := by
    obtain ⟨k, hk, e⟩ := Filter.frequently_atTop.1 hm (n + 1)
    rw [← e]
    show G₁.toGame.prio (if k ≤ n then f k else .inr α.opp) = _
    simp only [show ¬ k ≤ n by omega, ↓reduceIte]
  rw [hmeq, ofPrio_inr] at hmα
  exact opp_ne' α hmα

include C

/-- Along the plays of the safe subgame, the steps of `a'` are steps of the safe subgame. -/
private theorem Ctx.step₂₁ {v₀ : V}
    (hW : (a.restrict (a.safe α)).toGame.WinsFrom (embed D) α σ (.inl v₀))
    {x y : V ⊕ Player} (hr : Relation.ReflTransGen (S₁ a α D σ) (.inl v₀) x)
    (h : S₂ a' α D σ x y) : S₁ a α D σ x y := by
  obtain ⟨hx, hy, he, hown⟩ := h
  rcases x with v | q
  · have hvD := mem_embed_inl.1 hx
    by_cases ho : a.owner v = α
    · obtain ⟨u, hu⟩ := hW.1 _ hr
      have e₁ : u = σ (.inl v) := hu.2.2.2 ho
      have e₂ : y = σ (.inl v) := hown (show a'.owner v = α by rw [C.owner hvD]; exact ho)
      rw [e₂, ← e₁]; exact hu
    · refine ⟨hx, hy, ?_, fun h => absurd h ho⟩
      rcases y with w | q
      · exact (C.opp_edge hvD ho w).1 he
      · rcases he with ⟨hs, hq⟩ | ⟨hnv, -⟩
        · refine Or.inl ⟨⟨C.vs hvD, fun w hw => hs.2 w ((C.opp_edge hvD ho w).2 hw)⟩, ?_⟩
          rw [hq, C.owner hvD]; rfl
        · exact absurd (C.ext.1 (C.vs hvD).1) hnv
  · rcases y with w | q'
    · exact he.elim
    · exact ⟨hx, hy, he, hown⟩

/-- The plays of `a'` from the dominion stay on plays of the safe subgame. -/
private theorem Ctx.reach {v₀ : V}
    (hW : (a.restrict (a.safe α)).toGame.WinsFrom (embed D) α σ (.inl v₀))
    {x : V ⊕ Player} (h : Relation.ReflTransGen (S₂ a' α D σ) (.inl v₀) x) :
    Relation.ReflTransGen (S₁ a α D σ) (.inl v₀) x := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (C.step₂₁ hW ih hs)

/-- Along the plays of the safe subgame, its steps are steps of `a'`. -/
private theorem Ctx.step₁₂ {v₀ : V}
    (hW : (a.restrict (a.safe α)).toGame.WinsFrom (embed D) α σ (.inl v₀))
    {x u : V ⊕ Player} (hr : Relation.ReflTransGen (S₁ a α D σ) (.inl v₀) x)
    (h : S₁ a α D σ x u) : S₂ a' α D σ x u := by
  obtain ⟨hx, hu, he, hown⟩ := h
  rcases x with v | q
  · have hvD := mem_embed_inl.1 hx
    have hown' : a'.owner v = α → u = σ (.inl v) := fun h' =>
      hown (show a.owner v = α by rw [← C.owner hvD]; exact h')
    refine ⟨hx, hu, ?_, hown'⟩
    rcases u with w | q
    · exact C.ext.2.2.1 v w he.1
    · rcases he with ⟨hs, hq⟩ | ⟨hnv, -⟩
      · by_cases ho : a.owner v = α
        · exact absurd hs (no_own_sink hvD hW hr ho)
        · refine Or.inl ⟨⟨C.ext.1 (C.vs hvD).1,
            fun w hw => hs.2 w ((C.opp_edge hvD ho w).1 hw)⟩, ?_⟩
          rw [hq, C.owner hvD]; rfl
      · exact absurd ⟨(C.vs hvD).1, (C.vs hvD).2⟩ hnv
  · rcases u with w | q'
    · exact he.elim
    · exact ⟨hx, hu, he, hown⟩

omit C

private theorem dominionsSurvive_aux (a : IncompleteGame V) : a.DominionsSurvive := by
  intro α D a' hext hdom
  have C : Ctx a a' α D := ⟨hext, hdom⟩
  obtain ⟨hsub, hcl, σ, hW⟩ := hdom
  refine ⟨fun v hv => hext.1 (hsub hv).1, ?_, σ, fun v₀ hv₀ => ⟨?_, ?_⟩⟩
  · intro v hv ho w he
    have ho' : a.owner v ≠ α := by rw [← C.owner hv]; exact ho
    exact hcl v hv ho' w ((C.opp_edge hv ho' w).1 he)
  · intro w hw
    have hr := C.reach (hW v₀ hv₀) hw
    obtain ⟨u, hu⟩ := (hW v₀ hv₀).1 w hr
    exact ⟨u, C.step₁₂ (hW v₀ hv₀) hr hu⟩
  · intro p hp0 hp
    have hreach : ∀ n, Relation.ReflTransGen (S₂ a' α D σ) (.inl v₀) (p n) := by
      intro n
      induction n with
      | zero => rw [hp0]
      | succ n ih => exact ih.tail (hp n)
    have hp₁ : (a.restrict (a.safe α)).toGame.ConformingPlay (embed D) α σ p := fun n =>
      C.step₂₁ (hW v₀ hv₀) (C.reach (hW v₀ hv₀) (hreach n)) (hp n)
    have hwon := (hW v₀ hv₀).2 p hp0 hp₁
    have hprio : ∀ n, a'.toGame.prio (p n) = (a.restrict (a.safe α)).toGame.prio (p n) := by
      intro n
      have hmem := (hp n).1
      rcases hpn : p n with v | q
      · rw [hpn] at hmem
        exact C.prio (mem_embed_inl.1 hmem)
      · cases q <;> rfl
    have hmap : p.map a'.toGame.prio = p.map (a.restrict (a.safe α)).toGame.prio := by
      unfold ωSequence.map
      congr 1
      funext n
      exact hprio n
    unfold Game.PlayWonBy Game.MaxInfPrio at hwon ⊢
    rw [hmap]
    exact hwon

end IncompleteGame

/-- **Lemma 1 of [Laveaux2022].** -/
public theorem IncompleteGame.dominionsSurvive (a : IncompleteGame V) : a.DominionsSurvive :=
  a.dominionsSurvive_aux

end MercLib.ParityGame
