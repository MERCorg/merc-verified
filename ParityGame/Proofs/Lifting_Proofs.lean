module

public import ParityGame.Lifting
public import ParityGame.Proofs.TwoSidedLifting_Proofs
public import ParityGame.Proofs.Zielonka_Proofs
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.PiLex
public import Mathlib.Data.Finset.Sort

@[expose] public section LiftingProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/Lifting_Pins.lean`.

* `leastProg` is monotone because progressing to a larger value implies progressing to a smaller
  one (`ProgVal.mono_right`); hence `Game.lift` is monotone and Mathlib's `OrderHom.lfp` on the
  complete lattice `V → T` is its least fixpoint.
* Soundness: at a fixpoint `ν` the proper part is a progress measure (`Game.fix_measure`): player
  `0` follows a successor attaining the `sInf` (attained by well-foundedness), player `1`'s
  successors all progress because `ν v` is above their least progressing values
  (`ProgVal.mono_left`). `Game.progressMeasureSound` concludes.
* Completeness: by Zielonka (`Game.zielonkaAux_strong`) player `0`'s winning region `W` in `X` is
  a closed region with one positional strategy, and any node won by player `0` lies in it
  (`Game.no_both`). A complete codomain gives a progress measure on `W`; extended by `⊤` it is a
  pre-fixpoint, so the least fixpoint lies below it.
* Acceleration: following the fixpoint's own strategy on player `0`'s nodes and `τ` on player
  `1`'s from `s`, the orbit inside `S` must leave `S` (`Game.strategyExit`); composing the least
  progressing values backwards along it from the exit gives an `ExitPath` value `≤ ν s`.
* Representation: `Fin (n + 1)` with the `n` chain-tree leaves sorted by the lexicographic order
  of `Lex (ℕ → ℕ)` (`Finset.orderIsoOfFin`), which agrees with `LexLE (2h)` on tuples vanishing
  from coordinate `2h` on (`toLex_le_iff_lexLE`). -/

variable {V M T : Type*}

/-! ### Least progressing values -/

section Generic

variable [CompleteLinearOrder T] {C : Codomain M} {val : T → M}

theorem ProgVal.mono_right (hv : ValMono C val) {p : ℕ} {a b b' : T} (h : ProgVal C val p a b')
    (hbb : b ≤ b') (hb : b ≠ ⊤) : ProgVal C val p a b := by
  obtain ⟨ha, hb', h1, h2⟩ := h
  have hle := hv p b b' hb hb' hbb
  exact ⟨ha, hb, C.trans p _ _ _ hle h1, fun hp h3 => h2 hp (C.trans p _ _ _ h3 hle)⟩

theorem ProgVal.mono_left (hv : ValMono C val) {p : ℕ} {a a' b : T} (h : ProgVal C val p a b)
    (haa : a ≤ a') (ha' : a' ≠ ⊤) : ProgVal C val p a' b := by
  obtain ⟨ha, hb, h1, h2⟩ := h
  have hle := hv p a a' ha ha' haa
  exact ⟨ha', hb, C.trans p _ _ _ h1 hle, fun hp h3 => h2 hp (C.trans p _ _ _ hle h3)⟩

theorem leastProg_le {p : ℕ} {a b : T} (h : ProgVal C val p a b) : leastProg C val p b ≤ a :=
  sInf_le h

theorem leastProg_top (p : ℕ) : leastProg C val p (⊤ : T) = ⊤ := by
  have : {a : T | ProgVal C val p a ⊤} = ∅ := by
    ext a; simp [ProgVal]
  unfold leastProg; rw [this, sInf_empty]

theorem leastProg_mono (hv : ValMono C val) (p : ℕ) {b b' : T} (h : b ≤ b') :
    leastProg C val p b ≤ leastProg C val p b' := by
  by_cases hb : b = ⊤
  · subst hb; rw [top_le_iff.mp h]
  · exact sInf_le_sInf fun a ha => ha.mono_right hv h hb

theorem leastProg_spec [WellFoundedLT T] {p : ℕ} {b : T} (h : leastProg C val p b ≠ ⊤) :
    ProgVal C val p (leastProg C val p b) b := by
  have hne : {a | ProgVal C val p a b}.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    exact h (by unfold leastProg; rw [hc, sInf_empty])
  exact csInf_mem hne

/-! ### The lifting operator -/

theorem Game.lift_of_not_mem (G : Game V) {X : Set V} {μ : V → T} {v : V} (hv : v ∉ X) :
    G.lift X C val μ v = ⊤ := by
  simp [Game.lift, hv]

/-- The lifting operator is monotone (headline). -/
theorem Game.liftMonotone (G : Game V) (X : Set V) (C : Codomain M) (val : T → M) :
    G.LiftMonotone X C val := by
  intro hv μ μ' hμ v
  unfold Game.lift
  split_ifs
  · apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    exact (sInf_le (s := G.succProg X C val μ v) ⟨w, hw, rfl⟩).trans (leastProg_mono hv _ (hμ w))
  · apply sSup_le
    rintro _ ⟨w, hw, rfl⟩
    exact (leastProg_mono hv _ (hμ w)).trans (le_sSup ⟨w, hw, rfl⟩)
  · exact le_rfl

/-- The lifting operator as a bundled monotone map. -/
noncomputable def Game.liftHom (G : Game V) (X : Set V) (C : Codomain M) (val : T → M)
    (hv : ValMono C val) : (V → T) →o (V → T) :=
  OrderHom.mk (G.lift X C val) (G.liftMonotone X C val hv)

theorem Game.lfp_isLeast (G : Game V) (X : Set V) (C : Codomain M) (val : T → M)
    (hv : ValMono C val) :
    IsLeast {μ | G.lift X C val μ = μ} (OrderHom.lfp (G.liftHom X C val hv)) :=
  ⟨OrderHom.map_lfp (G.liftHom X C val hv), fun _ h => OrderHom.lfp_le_fixed (G.liftHom X C val hv) h⟩

/-- At a fixpoint `ν`, the proper part `{v | ν v ≠ ⊤}` is the domain of a progress measure, whose
    strategy moves inside `X` along edges from every player-`0` node of `X`. -/
theorem Game.fix_measure [Finite V] [WellFoundedLT T] (G : Game V) {X : Set V}
    (hX : G.IsSubgame X) (hv : ValMono C val) {ν : V → T} (hfix : G.lift X C val ν = ν) :
    ∃ σ : Strategy V, (∀ v ∈ X, G.owner v = .zero → σ v ∈ X ∧ G.edge v (σ v)) ∧
      G.IsProgressMeasure X C {v | ν v ≠ ⊤} (fun v => val (ν v)) σ := by
  classical
  have hν : ∀ v, G.lift X C val ν v = ν v := fun v => congrFun hfix v
  have hex : ∀ v ∈ X, ∃ w, w ∈ X ∧ G.edge v w ∧
      leastProg C val (G.prio v) (ν w) = sInf (G.succProg X C val ν v) := by
    intro v hv
    obtain ⟨w, hw, he⟩ := hX v hv
    have hne : (G.succProg X C val ν v).Nonempty := ⟨_, w, ⟨hw, he⟩, rfl⟩
    obtain ⟨w', hw', heq⟩ := csInf_mem hne
    exact ⟨w', hw'.1, hw'.2, heq⟩
  choose! σ hσX hσe hσeq using hex
  have hDX : ∀ v, ν v ≠ ⊤ → v ∈ X := by
    intro v hne
    by_contra hvX
    exact hne (by rw [← hν v, G.lift_of_not_mem hvX])
  refine ⟨σ, fun v hv _ => ⟨hσX v hv, hσe v hv⟩, fun v hv => hDX v hv, ?_, ?_⟩
  · intro v (hne : ν v ≠ ⊤) ho
    have hvX := hDX v hne
    have heq : ν v = leastProg C val (G.prio v) (ν (σ v)) := by
      rw [← hν v, hσeq v hvX]; simp [Game.lift, hvX, ho]
    have hp := leastProg_spec (heq ▸ hne)
    rw [← heq] at hp
    exact ⟨hp.2.1, hσe v hvX, hp.2.2⟩
  · intro v (hne : ν v ≠ ⊤) ho w hwX he
    have hvX := hDX v hne
    have hle : leastProg C val (G.prio v) (ν w) ≤ ν v := by
      rw [← hν v]
      simp only [Game.lift, hvX, if_true, ho, reduceCtorEq, if_false]
      exact le_sSup ⟨w, ⟨hwX, he⟩, rfl⟩
    have hp := (leastProg_spec (ne_top_of_le_ne_top hne hle)).mono_left hv hle hne
    exact ⟨hp.2.1, hp.2.2⟩

/-- Soundness of fixpoints: player `0` wins (positionally) from every node with a proper value. -/
theorem Game.fix_sound [Finite V] [WellFoundedLT T] (G : Game V) {X : Set V}
    (hX : G.IsSubgame X) (hv : ValMono C val) {ν : V → T} (hfix : G.lift X C val ν = ν) :
    ∃ σ : Strategy V, ∀ v, ν v ≠ ⊤ → G.WinsFrom X .zero σ v := by
  obtain ⟨σ, -, hm⟩ := G.fix_measure hX hv hfix
  exact ⟨σ, fun v hne => G.progressMeasureSound X C _ _ σ hX hm v hne⟩

end Generic

/-- A node won by player `0` (with any positional strategy) lies in the player-`0` region computed
    by Zielonka's algorithm. -/
theorem Game.winsFrom_mem_zielonka [Finite V] (G : Game V) {X : Set V} (hX : G.IsSubgame X)
    {σ : Strategy V} {v : V} (h : G.WinsFrom X .zero σ v) :
    v ∈ (G.zielonkaAux X).win .zero := by
  have hs := G.zielonkaAux_strong _ X rfl hX
  have reg := hs.region .one
  obtain ⟨u, hu⟩ := h.1 v Relation.ReflTransGen.refl
  have hvX : v ∈ X := hu.1
  rw [← hs.cover] at hvX
  rcases hvX with hv0 | hv1
  · exact hv0
  · exfalso
    have hstep : ∃ w ∈ (G.zielonkaAux X).win .one, G.Step X .zero σ v w := by
      cases ho : G.owner v with
      | zero =>
        refine ⟨u, reg.theirs v hv1 (by rw [ho]; simp) u hu.2.1 hu.2.2.1, hu⟩
      | one =>
        obtain ⟨hw, he⟩ := reg.mine v hv1 ho
        exact ⟨_, hw, hu.1, reg.sub hw, he, fun h => by rw [ho] at h; cases h⟩
    obtain ⟨w, hw, hst⟩ := hstep
    exact G.no_both (i := .zero) h (reg.winsFrom hX hw) hst

section Generic2

variable [CompleteLinearOrder T]

/-- The least fixpoint is not `⊤` exactly on player `0`'s winning region (headline, generic). -/
theorem Game.liftingLfpCorrect [Finite V] [WellFoundedLT T] (G : Game V) (X : Set V)
    (C : Codomain M) (val : T → M) : G.LiftingLfpCorrect X C val := by
  classical
  intro hX hv hcomp
  refine ⟨⟨_, G.lfp_isLeast X C val hv⟩, fun ν hν v => ⟨fun hne => ?_, fun ⟨σ', hσ'⟩ => ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := G.fix_sound hX hv hν.1
    exact ⟨σ, hσ v hne⟩
  · have hs := G.zielonkaAux_strong _ X rfl hX
    have reg := hs.region .zero
    have hvW := G.winsFrom_mem_zielonka hX hσ'
    generalize G.zielonkaAux X = r at hs reg hvW
    obtain ⟨μ, hμtop, hμ⟩ := hcomp (r.win .zero) (r.strat .zero)
      (fun u hu => reg.winsFrom hX hu) (by
        rintro u hu w ⟨-, hwX, he, hs⟩
        cases ho : G.owner u with
        | zero => rw [hs ho]; exact (reg.mine u hu ho).1
        | one => exact reg.theirs u hu (by rw [ho]; simp) w hwX he)
    let ν' : V → T := fun u => if u ∈ r.win .zero then μ u else ⊤
    have hpre : G.lift X C val ν' ≤ ν' := by
      intro u
      by_cases hu : u ∈ r.win .zero
      · have huX := reg.sub hu
        simp only [ν', hu, if_true]
        unfold Game.lift
        cases ho : G.owner u with
        | zero =>
          obtain ⟨hσW, he, hp⟩ := hμ.2.1 u hu ho
          simp only [huX, if_true]
          refine (sInf_le (s := G.succProg X C val ν' u)
            ⟨r.strat .zero u, ⟨reg.sub hσW, he⟩, rfl⟩).trans ?_
          simp only [ν', hσW, if_true]
          exact leastProg_le ⟨hμtop u hu, hμtop _ hσW, hp⟩
        | one =>
          simp only [huX, if_true, reduceCtorEq, if_false]
          apply sSup_le
          rintro _ ⟨w, ⟨hwX, he⟩, rfl⟩
          obtain ⟨hwW, hp⟩ := hμ.2.2 u hu ho w hwX he
          simp only [hwW, if_true]
          exact leastProg_le ⟨hμtop u hu, hμtop _ hwW, hp⟩
      · simp [ν', hu]
    have h1 : ν ≤ OrderHom.lfp (G.liftHom X C val hv) := hν.2 (OrderHom.map_lfp (G.liftHom X C val hv))
    have h2 := OrderHom.lfp_le (G.liftHom X C val hv) hpre
    have h3 : ν v ≤ ν' v := (h1.trans h2) v
    exact ne_top_of_le_ne_top (by simpa [ν', hvW] using hμtop v hvW) h3

end Generic2

/-! ### Chain tree instance -/

theorem Game.levelDepth_le_height [Finite V] (G : Game V) (X : Set V) (p : ℕ) :
    G.levelDepth X p ≤ G.height X := by
  classical
  unfold Game.levelDepth
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem Game.chainDepth_le [Finite V] (G : Game V) (X : Set V) (p : ℕ) :
    G.chainDepth X p ≤ 2 * G.height X := by
  unfold Game.chainDepth; have := G.levelDepth_le_height X p; omega

theorem isProgressMeasure_congr {G : Game V} {X : Set V} {C : Codomain M} {D : Set V}
    {μ μ' : V → M} {σ : Strategy V} (h : G.IsProgressMeasure X C D μ σ)
    (he : ∀ v ∈ D, μ v = μ' v) : G.IsProgressMeasure X C D μ' σ := by
  obtain ⟨hD, h0, h1⟩ := h
  refine ⟨hD, fun v hv ho => ?_, fun v hv ho w hw hedge => ?_⟩
  · obtain ⟨hσ, he', hp⟩ := h0 v hv ho
    refine ⟨hσ, he', ?_⟩
    unfold Game.Prog at hp ⊢
    rwa [← he v hv, ← he _ hσ]
  · obtain ⟨hwD, hp⟩ := h1 v hv ho w hw hedge
    refine ⟨hwD, ?_⟩
    unfold Game.Prog at hp ⊢
    rwa [← he v hv, ← he _ hwD]

/-- Lifting over the chain tree computes player `0`'s winning region (headline). -/
theorem Game.chainLiftingCorrect [Finite V] [CompleteLinearOrder T] [WellFoundedLT T]
    (G : Game V) (X : Set V) (C : Codomain (ℕ → ℕ)) (val : T → ℕ → ℕ) :
    G.ChainLiftingCorrect X C val := by
  intro hX hC hrep
  have hv : ValMono C val := fun p a b ha hb hab =>
    (hC _ _ _).2 (LexLE.mono (G.chainDepth_le X p) ((hrep.1 a b ha hb).1 hab))
  refine G.liftingLfpCorrect X C val hX hv ?_
  intro W σ hwin hcl
  obtain ⟨μ, hμ, hleaf⟩ := G.chainTreeComplete X C hC W σ hwin hcl
  choose! e he using fun v (hv : v ∈ W) => hrep.2.2 (μ v) (hleaf v hv)
  exact ⟨e, fun v hv => (he v hv).1, isProgressMeasure_congr hμ fun v hv => (he v hv).2.symm⟩

/-! ### A representation of the chain tree -/

theorem toLex_le_iff_lexLE {n : ℕ} {f g : ℕ → ℕ} (hf : ∀ i, n ≤ i → f i = 0)
    (hg : ∀ i, n ≤ i → g i = 0) : toLex f ≤ toLex g ↔ LexLE n f g := by
  rw [le_iff_lt_or_eq]
  constructor
  · rintro (⟨i, hlt, hi⟩ | heq)
    · right
      refine ⟨i, ?_, fun j hj => hlt j hj, hi⟩
      by_contra hn
      push Not at hn
      have h1 := hf i hn; have h2 := hg i hn
      simp only [Pi.toLex_apply] at hi
      omega
    · left
      intro i _
      exact congrFun (toLex.injective heq) i
  · rintro (heq | ⟨i, -, hlt, hi⟩)
    · right
      congr 1
      funext i
      by_cases hi : i < n
      · exact heq i hi
      · rw [hf i (by omega), hg i (by omega)]
    · exact Or.inl ⟨i, hlt, hi⟩

theorem Game.chainBound_le [Finite V] (G : Game V) (R : Set V) (q : ℕ) :
    G.chainBound R q ≤ Nat.card V := by
  unfold Game.chainBound
  rcases Set.eq_empty_or_nonempty {n | G.ChainPath R q n} with h | h
  · rw [h, csSup_empty]; exact bot_le
  · exact csSup_le h fun _ hn => G.chainPath_le hn

theorem Game.chainLeaf_le [Finite V] (G : Game V) (X : Set V) {a : ℕ → ℕ}
    (ha : G.IsChainLeaf X a) (i : ℕ) : a i ≤ Nat.card (Set V) + Nat.card V := by
  obtain ⟨h0, hk, hc, hz⟩ := ha
  by_cases hi : 2 * G.height X ≤ i
  · rw [hz i hi]; exact Nat.zero_le _
  · rcases Nat.even_or_odd' i with ⟨l, rfl | rfl⟩
    · rcases l with _ | l
      · rw [h0]; exact Nat.zero_le _
      · have h1 := hk l (by omega)
        have h2 : Nat.card ↥(G.lowComps (G.leafRegion X a l) (G.level X l)) ≤ Nat.card (Set V) :=
          Finite.card_subtype_le _
        have h3 : max 1 (Nat.card ↥(G.lowComps (G.leafRegion X a l) (G.level X l))) ≤
            1 + Nat.card (Set V) := by omega
        omega
    · have := (hc l (by omega)).trans (G.chainBound_le _ _)
      omega

theorem Game.chainLeaves_finite [Finite V] (G : Game V) (X : Set V) :
    {a : Lex (ℕ → ℕ) | G.IsChainLeaf X (ofLex a)}.Finite := by
  set n := 2 * G.height X
  set B := Nat.card (Set V) + Nat.card V
  let ext : (Fin n → Fin (B + 1)) → Lex (ℕ → ℕ) := fun g =>
    toLex fun i => if h : i < n then (g ⟨i, h⟩ : ℕ) else 0
  refine (Set.finite_range ext).subset ?_
  intro a ha
  refine ⟨fun i => ⟨ofLex a i, Nat.lt_succ_of_le (G.chainLeaf_le X ha i)⟩, ?_⟩
  simp only [ext]
  apply ofLex.injective
  funext i
  simp only [ofLex_toLex]
  split_ifs with h
  · rfl
  · exact (ha.2.2.2 i (by omega)).symm

/-- A representation of the chain tree exists (headline): `Fin (n + 1)`, `n` the number of
    leaves, sorted lexicographically, with `⊤ = Fin.last n`. -/
theorem Game.chainReprExists [Finite V] (G : Game V) (X : Set V) : G.ChainReprExists X := by
  classical
  set s := (G.chainLeaves_finite X).toFinset
  set k := s.card
  let e := s.orderIsoOfFin rfl
  let val : Fin (k + 1) → ℕ → ℕ := fun i =>
    if h : (i : ℕ) < k then ofLex (e ⟨i, h⟩).1 else 0
  have htop : ∀ a : Fin (k + 1), a ≠ ⊤ ↔ (a : ℕ) < k := by
    intro a
    rw [Fin.top_eq_last, ne_eq, Fin.ext_iff, Fin.val_last]
    have := a.isLt
    omega
  have hleaf : ∀ j : Fin k, G.IsChainLeaf X (ofLex (e j).1) := by
    intro j
    have h : ((e j) : Lex (ℕ → ℕ)) ∈ (G.chainLeaves_finite X).toFinset := (e j).2
    rw [Set.Finite.mem_toFinset] at h
    exact h
  refine ⟨Fin (k + 1), inferInstance, inferInstance, val, ?_, ?_, ?_⟩
  · intro a b ha hb
    rw [htop] at ha hb
    simp only [val, ha, hb, dif_pos]
    rw [← toLex_le_iff_lexLE (hleaf _).2.2.2 (hleaf _).2.2.2]
    simp only [toLex_ofLex, Subtype.coe_le_coe, OrderIso.le_iff_le, Fin.le_iff_val_le_val]
  · intro a ha
    rw [htop] at ha
    simp only [val, ha, dif_pos]
    exact hleaf _
  · intro l hl
    have hmem : toLex l ∈ s := by simpa [s] using hl
    refine ⟨Fin.castSucc (e.symm ⟨toLex l, hmem⟩), ?_, ?_⟩
    · rw [htop]; simp
    · simp [val]

/-! ### Acceleration -/

section Accel

variable [CompleteLinearOrder T]

theorem Game.OddCyclesIn.mono {G : Game V} {f : V → V} {S S' : Set V} (h : G.OddCyclesIn f S)
    (hS : S' ⊆ S) : G.OddCyclesIn f S' := fun s hs k hk hc hin =>
  h s (hS hs) k hk hc fun j hj => hS (hin j hj)

/-- Acceleration soundness (headline). -/
theorem Game.accelSound [Finite V] [WellFoundedLT T] (G : Game V) (X : Set V) (C : Codomain M)
    (val : T → M) (ν μ : V → T) (S : Set V) (τ : Strategy V) :
    G.AccelSound X C val ν μ S τ := by
  classical
  intro hX hv hfix hμν hSX hS hτ hodd s hs
  by_cases hνs : ν s = ⊤
  · rw [hνs]; exact le_top
  obtain ⟨σ, hσ, hm⟩ := G.fix_measure hX hv hfix
  set D := {v | ν v ≠ ⊤}
  set f : V → V := fun v => if G.owner v = .zero then σ v else τ v with hf
  -- one move from a node of `S ∩ D`
  have hmove : ∀ u ∈ S, u ∈ D → G.AccelMove X τ u (f u) ∧ f u ∈ D ∧
      ProgVal C val (G.prio u) (ν u) (ν (f u)) := by
    intro u hu huD
    cases ho : G.owner u with
    | zero =>
      obtain ⟨hD', he, hp⟩ := hm.2.1 u huD ho
      have hfu : f u = σ u := by simp [hf, ho]
      rw [hfu]
      refine ⟨?_, hD', huD, hD', hp⟩
      simp only [Game.AccelMove, ho, if_true]
      exact ⟨he, (hσ u (hSX hu) ho).1⟩
    | one =>
      have hfu : f u = τ u := by simp [hf, ho]
      rw [hfu]
      obtain ⟨hD', hp⟩ := hm.2.2 u huD ho (τ u) (hτ u hu ho).1 (hτ u hu ho).2
      refine ⟨?_, hD', huD, hD', hp⟩
      simp [Game.AccelMove, ho]
  -- the orbit of `s` while it stays in `S`
  set S' : Set V := {u | ∃ i, u = f^[i] s ∧ ∀ j ≤ i, f^[j] s ∈ S} with hS'
  have horbD : ∀ i, (∀ j ≤ i, f^[j] s ∈ S) → f^[i] s ∈ D := by
    intro i
    induction i with
    | zero => intro _; exact hνs
    | succ i ih =>
      intro hin
      rw [Function.iterate_succ_apply']
      exact (hmove _ (hin i (by omega)) (ih fun j hj => hin j (by omega))).2.1
  have hS'S : S' ⊆ S := by
    rintro _ ⟨i, rfl, hin⟩; exact hin i le_rfl
  have hS'D : S' ⊆ D := by
    rintro _ ⟨i, rfl, hin⟩; exact horbD i hin
  have hfS : ∀ u ∈ S, G.owner u = .zero → G.edge u (f u) ∧ f u ∈ X := by
    intro u hu ho
    have hfu : f u = σ u := by simp [hf, ho]
    rw [hfu]; exact ⟨(hσ u (hSX hu) ho).2, (hσ u (hSX hu) ho).1⟩
  have hfτ : ∀ u ∈ S, G.owner u = .one → f u = τ u := by
    intro u _ ho; simp [hf, ho]
  obtain ⟨u, ⟨i, rfl, hin⟩, hexit⟩ := G.strategyExit X C D (fun v => val (ν v)) σ τ S' hm hS'D
    (hS.subset hS'S) ⟨s, 0, rfl, fun j hj => by
      rw [Nat.le_zero.mp hj]; exact hs⟩
    (fun v hv ho => hτ v (hS'S hv) ho) ((hodd f hfS hfτ).mono hS'S)
  change f (f^[i] s) ∉ S' at hexit
  have hout : f^[i + 1] s ∉ S := by
    intro hin'
    apply hexit
    refine ⟨i + 1, by rw [Function.iterate_succ_apply'], fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (i + 1) with h | h
    · exact hin j (by omega)
    · rw [show j = i + 1 by omega]; exact hin'
  -- backwards along the orbit
  have key : ∀ k ≤ i, ∃ t, G.ExitPath X S C val τ μ (f^[i - k] s) t ∧ t ≤ ν (f^[i - k] s) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      obtain ⟨hmv, -, hp⟩ := hmove _ (hin i le_rfl) (horbD i hin)
      refine ⟨_, Game.ExitPath.exit (hin i le_rfl) hmv
        (by rw [← Function.iterate_succ_apply' f]; exact hout), ?_⟩
      exact (leastProg_mono hv _ (hμν _)).trans (leastProg_le hp)
    | succ k ih =>
      intro hk
      obtain ⟨t, hpath, ht⟩ := ih (by omega)
      have hidx : i - k = (i - (k + 1)) + 1 := by omega
      rw [hidx, Function.iterate_succ_apply'] at hpath ht
      have hinS := hin (i - (k + 1)) (by omega)
      obtain ⟨hmv, -, hp⟩ := hmove _ hinS (horbD _ fun j hj => hin j (by omega))
      have hnext : f (f^[i - (k + 1)] s) ∈ S := by
        rw [← Function.iterate_succ_apply' f]; exact hin _ (by omega)
      exact ⟨_, Game.ExitPath.step hinS hmv hnext hpath,
        (leastProg_mono hv _ ht).trans (leastProg_le hp)⟩
  obtain ⟨t, hpath, ht⟩ := key i le_rfl
  rw [Nat.sub_self, Function.iterate_zero_apply] at hpath ht
  exact (sInf_le hpath).trans ht

end Accel

end ParityGame

end LiftingProofs
