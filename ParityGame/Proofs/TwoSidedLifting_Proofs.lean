module

public import ParityGame.TwoSidedLifting
public import ParityGame.Proofs.ProgressMeasure_Proofs
public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Order.Preorder.Finite

open Cslib (ωSequence)

@[expose] public section TwoSidedLiftingProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/TwoSidedLifting_Pins.lean`.

* Codomain: `LexLE n` is a preorder, coarser for smaller `n`, and its strict part is a
  subrelation of the (well-founded) lexicographic order on `Fin n → ℕ` (`Pi.Lex.wellFounded`).
* Acceleration: the `f`-orbit of a node of a finite closed `S` repeats (pigeonhole), giving an
  `f`-cycle in `S`; `Game.progCycleEven` makes its maximum even.
* Completeness: the measure (`Game.chainMeasure`) interleaves, per level `l`, the index of the
  node's nested region (`Game.region`, `Game.kIdx`; `0` once the node's priority is too high for
  the level) with Jurdziński's counter `Game.cnt` (the most priority-`q_l` visits of a
  `σ`-conforming path from the node through priorities `≤ q_l`). A repeated priority-`q_l` node on
  such a path closes a lasso whose recurring maximum is the odd `q_l`, contradicting that `σ` wins
  (`Game.no_odd_repeat`), so the visits form a chain path of the node's region
  (`Game.cntPath_chainPath`), bounding the counter by the chain bound. Along a conforming move
  `v → w` the measure is componentwise non-increasing on the coordinates compared at `prio v`:
  component indices agree where both endpoints belong to the level (`Game.region_eq`) and are `0`
  for `w` otherwise, counters do not increase (`Game.cnt_step`), and the counter at `v`'s own odd
  level strictly decreases. -/

variable {V M : Type*}

/-! ### 1. Truncated lexicographic codomain -/

theorem LexLE.refl (n : ℕ) (a : ℕ → ℕ) : LexLE n a a := Or.inl fun _ _ => rfl

theorem LexLE.trans {n : ℕ} {a b c : ℕ → ℕ} (hab : LexLE n a b) (hbc : LexLE n b c) :
    LexLE n a c := by
  rcases hab with hab | ⟨i, hi, hab, hlt⟩
  · rcases hbc with hbc | ⟨j, hj, hbc, hlt'⟩
    · exact Or.inl fun k hk => (hab k hk).trans (hbc k hk)
    · exact Or.inr ⟨j, hj, fun k hk => (hab k (by omega)).trans (hbc k hk),
        (hab j hj).symm ▸ hlt'⟩
  · rcases hbc with hbc | ⟨j, hj, hbc, hlt'⟩
    · exact Or.inr ⟨i, hi, fun k hk => (hab k hk).trans (hbc k (by omega)),
        (hbc i hi) ▸ hlt⟩
    · rcases lt_trichotomy i j with h | rfl | h
      · exact Or.inr ⟨i, hi, fun k hk => (hab k hk).trans (hbc k (by omega)),
          (hbc i h) ▸ hlt⟩
      · exact Or.inr ⟨i, hi, fun k hk => (hab k hk).trans (hbc k hk), hlt.trans hlt'⟩
      · exact Or.inr ⟨j, hj, fun k hk => (hab k (by omega)).trans (hbc k hk),
          (hab j h).symm ▸ hlt'⟩

theorem LexLE.mono {n n' : ℕ} {a b : ℕ → ℕ} (h : n' ≤ n) (hab : LexLE n a b) : LexLE n' a b := by
  rcases hab with hab | ⟨i, hi, hab, hlt⟩
  · exact Or.inl fun k hk => hab k (by omega)
  · by_cases hin : i < n'
    · exact Or.inr ⟨i, hin, hab, hlt⟩
    · exact Or.inl fun k hk => hab k (by omega)

/-- The strict part of `LexLE n` is well-founded: it is a subrelation of the lexicographic order
    on `Fin n → ℕ`. -/
theorem LexLE.wf (n : ℕ) : WellFounded (fun a b : ℕ → ℕ => LexLE n a b ∧ ¬ LexLE n b a) := by
  have hwf := Pi.Lex.wellFounded (ι := Fin n) (α := fun _ => ℕ) (· < ·)
    (s := fun _ => (· < ·)) (fun _ => wellFounded_lt)
  refine Subrelation.wf ?_ (InvImage.wf (fun a : ℕ → ℕ => fun i : Fin n => a i) hwf)
  intro a b ⟨hab, hba⟩
  rcases hab with hab | ⟨i, hi, hab, hlt⟩
  · exact absurd (Or.inl fun k hk => (hab k hk).symm) hba
  · exact ⟨⟨i, hi⟩, fun j hj => hab j hj, hlt⟩

/-- Componentwise `≤` on the first `n` coordinates implies `LexLE n`. -/
theorem LexLE.of_le {n : ℕ} {a b : ℕ → ℕ} (h : ∀ i < n, a i ≤ b i) : LexLE n a b := by
  classical
  by_cases hall : ∀ i < n, a i = b i
  · exact Or.inl hall
  · push Not at hall
    have hex : ∃ i, i < n ∧ a i ≠ b i := hall
    refine Or.inr ⟨Nat.find hex, (Nat.find_spec hex).1, fun j hj => ?_,
      lt_of_le_of_ne (h _ (Nat.find_spec hex).1) (Nat.find_spec hex).2⟩
    by_contra hne
    exact Nat.find_min hex hj ⟨by have := (Nat.find_spec hex).1; omega, hne⟩

/-- Componentwise `≤` with one strict coordinate on the first `n` excludes the reverse `LexLE n`. -/
theorem LexLE.not_of_lt {n : ℕ} {a b : ℕ → ℕ} (h : ∀ i < n, a i ≤ b i) {i : ℕ} (hi : i < n)
    (hlt : a i < b i) : ¬ LexLE n b a := by
  rintro (hba | ⟨j, hj, -, hlt'⟩)
  · have := hba i hi; omega
  · have := h j hj; omega

/-- The truncated lexicographic order satisfies the `Codomain` axioms (headline). -/
theorem truncLexCodomainAxioms (depth : ℕ → ℕ) : TruncLexCodomainAxioms depth := fun hd =>
  ⟨fun _ a => LexLE.refl _ a, fun _ _ _ _ => LexLE.trans,
    fun _ _ _ _ hpq => LexLE.mono (hd hpq), fun _ => LexLE.wf _⟩

/-- The truncated lexicographic codomain of an antitone depth function. -/
def truncLexCodomain (depth : ℕ → ℕ) (hd : Antitone depth) : Codomain (ℕ → ℕ) where
  le p := LexLE (depth p)
  refl := (truncLexCodomainAxioms depth hd).1
  trans := (truncLexCodomainAxioms depth hd).2.1
  mono := (truncLexCodomainAxioms depth hd).2.2.1
  wf p _ := (truncLexCodomainAxioms depth hd).2.2.2 p

/-! ### 2. Acceleration -/

/-- Set version of `progCycleEven` (headline). -/
theorem Game.funCycleEven (G : Game V) (C : Codomain M) (μ : V → M) (f : V → V) (S : Set V) :
    G.FunCycleEven C μ f S := by
  intro hS ⟨s₀, hs₀⟩ hclosed hprog
  have horb : ∀ n, f^[n] s₀ ∈ S := by
    intro n
    induction n with
    | zero => exact hs₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  obtain ⟨m, n, hmn, heq⟩ := hS.exists_lt_map_eq_of_forall_mem (f := fun n => f^[n] s₀) horb
  set t := f^[m] s₀ with ht
  have hk : f^[n - m] t = t := by
    rw [ht, ← Function.iterate_add_apply, show n - m + m = n by omega]
    exact heq.symm
  have htS : ∀ j, f^[j] t ∈ S := fun j => by rw [ht, ← Function.iterate_add_apply]; exact horb _
  obtain ⟨i, hi, hmax⟩ := (Finset.range (n - m)).exists_max_image (fun j => G.prio (f^[j] t))
    ⟨0, by simp; omega⟩
  rw [Finset.mem_range] at hi
  refine ⟨t, htS 0, n - m, by omega, hk, i, hi, fun j hj => hmax j (Finset.mem_range.mpr hj), ?_⟩
  refine G.progCycleEven C μ (n - m) (fun j => f^[j] t) (by omega) hk (fun j _ => ?_) i hi
    (fun j hj => hmax j (Finset.mem_range.mpr hj))
  simp only [Function.iterate_succ_apply']
  exact hprog _ (htS j)

/-- Acceleration, functional-graph form (headline). -/
theorem Game.funExit (G : Game V) (C : Codomain M) (μ : V → M) (f : V → V) (S : Set V) :
    G.FunExit C μ f S := by
  intro hS hne hprog hodd
  by_contra hcl
  push Not at hcl
  obtain ⟨s, hs, k, hk, hcyc, i, hi, hmax, heven⟩ := G.funCycleEven C μ f S hS hne hcl hprog
  have horb : ∀ n, f^[n] s ∈ S := by
    intro n
    induction n with
    | zero => exact hs
    | succ n ih => rw [Function.iterate_succ_apply']; exact hcl _ ih
  have := hodd s hs k hk hcyc (fun j _ => horb j) i hi hmax
  omega

/-- Acceleration for a progress measure's strategy (headline). -/
theorem Game.strategyExit (G : Game V) (X : Set V) (C : Codomain M) (D : Set V) (μ : V → M)
    (σ τ : Strategy V) (S : Set V) : G.StrategyExit X C D μ σ τ S := by
  intro hμ hSD hS hne hτ hodd
  refine G.funExit C μ _ S hS hne (fun s hs => ?_) hodd
  cases ho : G.owner s with
  | zero => simpa [ho] using (hμ.2.1 s (hSD hs) ho).2.2
  | one =>
    simp only [reduceCtorEq, if_false]
    exact (hμ.2.2 s (hSD hs) ho (τ s) (hτ s hs ho).1 (hτ s hs ho).2).2

/-! ### 3. The chain tree: levels -/

section ChainTree

theorem Game.mem_oddPrios [Finite V] (G : Game V) (X : Set V)
    {p : ℕ} : p ∈ G.oddPrios X ↔ p ∈ G.prio '' X ∧ p % 2 = 1 := by
  unfold Game.oddPrios
  rw [Set.Finite.mem_toFinset]
  rfl

theorem Game.level_of_lt [Finite V] (G : Game V) (X : Set V) {l : ℕ} (hl : l < G.height X) :
    G.level X l = (G.oddPrios X).orderEmbOfFin rfl ⟨(G.oddPrios X).card - 1 - l,
      by unfold Game.height at hl; omega⟩ := by
  unfold Game.level
  rw [dif_pos (by unfold Game.height at hl; exact hl)]

theorem Game.level_mem [Finite V] (G : Game V) (X : Set V) {l : ℕ}
    (hl : l < G.height X) : G.level X l ∈ G.oddPrios X := by
  rw [G.level_of_lt X hl]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem Game.level_odd [Finite V] (G : Game V) (X : Set V) {l : ℕ}
    (hl : l < G.height X) : G.level X l % 2 = 1 :=
  ((G.mem_oddPrios X).mp (G.level_mem X hl)).2

theorem Game.level_lt_level [Finite V] (G : Game V) (X : Set V) {l l' : ℕ} (hll' : l < l')
    (hl' : l' < G.height X) :
    G.level X l' < G.level X l := by
  rw [G.level_of_lt X hl', G.level_of_lt X (by omega)]
  apply (Finset.orderEmbOfFin _ _).strictMono
  show (G.oddPrios X).card - 1 - l' < (G.oddPrios X).card - 1 - l
  unfold Game.height at hl'
  omega

theorem Game.level_le_level_iff [Finite V] (G : Game V) (X : Set V) {l l' : ℕ}
    (hl : l < G.height X) (hl' : l' < G.height X) :
    G.level X l' ≤ G.level X l ↔ l ≤ l' := by
  constructor
  · intro h
    by_contra hc
    have := G.level_lt_level X (show l' < l by omega) hl
    omega
  · intro h
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact (G.level_lt_level X h hl').le
    · exact le_rfl

/-- Every odd priority of a node of `X` is a level. -/
theorem Game.exists_level_eq [Finite V] (G : Game V) (X : Set V) {x : V} (hx : x ∈ X)
    (hodd : G.prio x % 2 = 1) :
    ∃ m < G.height X, G.level X m = G.prio x := by
  have hmem : G.prio x ∈ G.oddPrios X := (G.mem_oddPrios X).mpr ⟨⟨x, hx, rfl⟩, hodd⟩
  have hmem' : G.prio x ∈ Set.range ((G.oddPrios X).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hmem
  obtain ⟨⟨i, hi⟩, hie⟩ := hmem'
  refine ⟨(G.oddPrios X).card - 1 - i, by unfold Game.height; omega, ?_⟩
  rw [G.level_of_lt X (by unfold Game.height; omega), ← hie]
  congr 2
  omega

theorem Game.lt_levelDepth_iff [Finite V] (G : Game V) (X : Set V) {p l : ℕ} :
    l < G.levelDepth X p ↔ l < G.height X ∧ p ≤ G.level X l := by
  classical
  unfold Game.levelDepth
  set F := (Finset.range (G.height X)).filter fun l => p ≤ G.level X l with hF
  have hdown : ∀ k ∈ F, ∀ l ≤ k, l ∈ F := by
    intro k hk l hlk
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hk ⊢
    refine ⟨by omega, hk.2.trans ((G.level_le_level_iff X (by omega) hk.1).mpr hlk)⟩
  have hmemF : l ∈ F ↔ l < G.height X ∧ p ≤ G.level X l := by simp [hF]
  rw [← hmemF]
  constructor
  · intro hl
    by_contra hn
    have hsub : F ⊆ Finset.range l := by
      intro k hk
      rw [Finset.mem_range]
      by_contra hkl
      exact hn (hdown k hk l (by omega))
    have := Finset.card_le_card hsub
    simp at this
    omega
  · intro hl
    have hsub : Finset.range (l + 1) ⊆ F := fun k hk =>
      hdown l hl k (by simp at hk; omega)
    have := Finset.card_le_card hsub
    simp at this
    omega

theorem Game.levelDepth_antitone [Finite V] (G : Game V) (X : Set V) : Antitone
    (G.levelDepth X) := by
  classical
  intro p p' hpp'
  unfold Game.levelDepth
  apply Finset.card_le_card
  intro l
  simp only [Finset.mem_filter, Finset.mem_range]
  exact fun ⟨h1, h2⟩ => ⟨h1, hpp'.trans h2⟩

theorem Game.chainDepth_antitone [Finite V] (G : Game V) (X : Set V) : Antitone
    (G.chainDepth X) := fun _ _ h => by
  unfold Game.chainDepth
  have := G.levelDepth_antitone X h
  omega

/-! ### Regions along a node -/

/-- The nested regions of a node: `X` at level `0`, then the component of the node in the
    previous region restricted to priorities `< q_l`. -/
def Game.region [Finite V] (G : Game V) (X : Set V) : ℕ → V → Set V
  | 0, _ => X
  | l + 1, v => G.lowComp (G.region X l v) (G.level X l) v

/-- `x` lies below every level above `l` (so it belongs to a region at level `l`). -/
def Game.Belongs [Finite V] (G : Game V) (X : Set V) (l : ℕ)
    (x : V) : Prop := ∀ l' < l, G.prio x < G.level X l'

theorem Game.Belongs.mono [Finite V] {G : Game V} {X : Set V} {l l' : ℕ} {x : V}
    (h : G.Belongs X l x) (hl : l' ≤ l) :
    G.Belongs X l' x := fun k hk => h k (by omega)

/-- A node of priority `≤ q_l` belongs to level `l`. -/
theorem Game.belongs_of_le [Finite V] (G : Game V) (X : Set V) {l : ℕ} {x : V}
    (hl : l < G.height X) (hx : G.prio x ≤ G.level X l) :
    G.Belongs X l x := fun _ hl' => lt_of_le_of_lt hx (G.level_lt_level X hl' hl)

theorem Game.self_mem_region [Finite V] (G : Game V) (X : Set V) {x : V}
    (hx : x ∈ X) : ∀ l, x ∈ G.region X l x
  | 0 => hx
  | _ + 1 => Relation.EqvGen.refl _

theorem Game.lowComp_eq (G : Game V) {R : Set V} {q : ℕ} {x y : V} (h : Relation.EqvGen
    (G.LowEdge R q) x y) :
    G.lowComp R q x = G.lowComp R q y := by
  ext z
  exact ⟨fun hz => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hz,
    fun hz => Relation.EqvGen.trans _ _ _ h hz⟩

/-- Two nodes joined by an edge that both belong to level `l` lie in the same region there. -/
theorem Game.region_eq [Finite V] (G : Game V) (X : Set V) {x y : V} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : G.edge x y) :
    ∀ l, G.Belongs X l x → G.Belongs X l y → G.region X l x = G.region X l y
  | 0, _, _ => rfl
  | l + 1, bx, by' => by
    have ih := G.region_eq X hx hy hxy l (bx.mono (by omega)) (by'.mono (by omega))
    show G.lowComp (G.region X l x) (G.level X l) x = G.lowComp (G.region X l y) (G.level X l) y
    rw [ih]
    apply G.lowComp_eq
    refine Relation.EqvGen.rel _ _ ⟨?_, G.self_mem_region X hy l, bx l (by omega), by' l (by omega),
      hxy⟩
    rw [← ih]; exact G.self_mem_region X hx l

theorem Game.region_mem_lowComps [Finite V] (G : Game V) (X : Set V) {x : V} (hx : x ∈ X) {l : ℕ}
    (hb : G.Belongs X (l + 1) x) :
    G.region X (l + 1) x ∈ G.lowComps (G.region X l x) (G.level X l) :=
  ⟨x, G.self_mem_region X hx l, hb l (by omega), rfl⟩

/-- A path from `v` through `X` all of whose nodes belong to level `l` stays in `v`'s region. -/
theorem Game.path_mem_region [Finite V] (G : Game V) (X : Set V) {v : V} {m : ℕ} {a : ℕ → V}
    (ha0 : a 0 = v)
    (haX : ∀ i ≤ m, a i ∈ X) (hedge : ∀ i < m, G.edge (a i) (a (i + 1))) :
    ∀ l, (∀ i ≤ m, G.Belongs X l (a i)) → ∀ i ≤ m, a i ∈ G.region X l v
  | 0, _, i, hi => haX i hi
  | l + 1, hb, i, hi => by
    have ih := G.path_mem_region X ha0 haX hedge l (fun i hi => (hb i hi).mono (by omega))
    show Relation.EqvGen _ v (a i)
    induction i with
    | zero => rw [ha0]; exact Relation.EqvGen.refl _
    | succ i ihi =>
      refine Relation.EqvGen.trans _ _ _ (ihi (by omega)) (Relation.EqvGen.rel _ _ ?_)
      exact ⟨ih i (by omega), ih (i + 1) hi, hb i (by omega) l (by omega),
        hb (i + 1) hi l (by omega), hedge i (by omega)⟩

theorem Game.compAt_compIdx [Finite V] (G : Game V) {R : Set V} {q : ℕ} {K : Set V}
    (hK : K ∈ G.lowComps R q) :
    G.compAt R q (G.compIdx R q K) = K := by
  unfold Game.compAt Game.compIdx
  rw [dif_pos hK, dif_pos (Fin.isLt _)]
  simp

theorem Game.compIdx_lt [Finite V] (G : Game V) {R : Set V} {q : ℕ} {K : Set V}
    (hK : K ∈ G.lowComps R q) :
    G.compIdx R q K < Nat.card (G.lowComps R q) := by
  unfold Game.compIdx
  rw [dif_pos hK]
  exact Fin.isLt _

/-! ### Lassos: a repeated maximal odd node on a conforming path refutes a winning strategy -/

/-- Positions of the lasso `a 0 … a (j-1)` followed by `a i … a (j-1)` forever. -/
def lassoPos (i j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if lassoPos i j n + 1 < j then lassoPos i j n + 1 else i

theorem lassoPos_succ (i j n : ℕ) :
    lassoPos i j (n + 1) = if lassoPos i j n + 1 < j then lassoPos i j n + 1 else i := rfl

theorem lassoPos_lt {i j : ℕ} (hij : i < j) : ∀ n, lassoPos i j n < j
  | 0 => by simp [lassoPos]; omega
  | n + 1 => by rw [lassoPos_succ]; split_ifs <;> omega

theorem lassoPos_self {i j : ℕ} (hij : i < j) : ∀ n ≤ i, lassoPos i j n = n
  | 0, _ => rfl
  | n + 1, hn => by rw [lassoPos_succ, lassoPos_self hij n (by omega), if_pos (by omega)]

theorem lassoPos_ge {i j : ℕ} (hij : i < j) : ∀ n, i ≤ n → i ≤ lassoPos i j n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [lassoPos_self hij i le_rfl]
  | succ n _ ih => rw [lassoPos_succ]; split_ifs <;> omega

theorem lassoPos_hits {i j : ℕ} :
    ∀ k n, j - lassoPos i j n = k → i ≤ lassoPos i j n → ∃ d, lassoPos i j (n + d) = i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hi
    by_cases hlt : lassoPos i j n + 1 < j
    · have h1 : lassoPos i j (n + 1) = lassoPos i j n + 1 := by rw [lassoPos_succ, if_pos hlt]
      obtain ⟨d, hd⟩ := ih (j - lassoPos i j (n + 1)) (by omega) (n + 1) rfl (by omega)
      exact ⟨d + 1, by rw [show n + (d + 1) = n + 1 + d by omega]; exact hd⟩
    · exact ⟨1, by rw [lassoPos_succ, if_neg hlt]⟩

/-- No conforming path from a node won by `σ` repeats a node whose (odd) priority is maximal on
    the path. -/
theorem Game.no_odd_repeat [Finite V] (G : Game V) (X : Set V) {σ : Strategy V} {v : V}
    (hwin : G.WinsFrom X .zero σ v) {m : ℕ}
    {a : ℕ → V} (ha0 : a 0 = v) (hstep : ∀ t < m, G.Step X .zero σ (a t) (a (t + 1)))
    {i j : ℕ} (hij : i < j) (hjm : j ≤ m) (heq : a i = a j)
    (hmax : ∀ t ≤ m, G.prio (a t) ≤ G.prio (a i)) (hodd : G.prio (a i) % 2 = 1) : False := by
  let p : ωSequence V := ⟨fun n => a (lassoPos i j n)⟩
  have hpn : ∀ n, p n = a (lassoPos i j n) := fun _ => rfl
  have hconf : G.ConformingPlay X .zero σ p := by
    intro n
    rw [hpn, hpn, lassoPos_succ]
    have hlt := lassoPos_lt hij n
    split_ifs with h
    · exact hstep (lassoPos i j n) (by omega)
    · have hj : a i = a (lassoPos i j n + 1) := heq.trans (by congr 1; omega)
      rw [hj]
      exact hstep (lassoPos i j n) (by omega)
  obtain ⟨P, hP, hPo⟩ := hwin.2 p (by rw [hpn]; simp [lassoPos, ha0]) hconf
  have hM : G.MaxInfPrio p (G.prio (a i)) := by
    rw [G.maxInfPrio_iff]
    refine ⟨⟨a i, ?_, rfl⟩, fun x hx => ?_⟩
    · rw [nodeInf, Set.mem_setOf_eq, Filter.frequently_atTop]
      intro N
      obtain ⟨d, hd⟩ := lassoPos_hits _ (max N i) rfl (lassoPos_ge hij _ (by omega))
      exact ⟨max N i + d, by omega, by rw [hpn, hd]⟩
    · rw [nodeInf, Set.mem_setOf_eq, Filter.frequently_atTop] at hx
      obtain ⟨n, -, hn⟩ := hx 0
      rw [← hn, hpn]
      exact hmax (lassoPos i j n) (by have := lassoPos_lt hij n; omega)
  rw [G.maxInfPrio_unique hP hM] at hPo
  simp [Player.ofPrio, hodd] at hPo

/-! ### Counters: Jurdziński's measure for a winning strategy -/

/-- Number of priority-`q` positions among `a 0, …, a m`. -/
def Game.qCount (G : Game V) (q : ℕ) (a : ℕ → V) (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter fun i => G.prio (a i) = q).card

/-- `n` priority-`q` positions on a `σ`-conforming path from `v` through priorities `≤ q`. -/
def Game.CntPath (G : Game V) (X : Set V) (σ : Strategy V) (q : ℕ) (v : V) (n : ℕ) : Prop :=
  ∃ (m : ℕ) (a : ℕ → V), a 0 = v ∧ (∀ i < m, G.Step X .zero σ (a i) (a (i + 1))) ∧
    (∀ i ≤ m, G.prio (a i) ≤ q) ∧ n = G.qCount q a m

/-- The counter at level `q`: the most priority-`q` visits of a `σ`-conforming play from `v` before
    the first priority `> q` (`0` if `prio v > q`). -/
noncomputable def Game.cnt (G : Game V) (X : Set V) (σ : Strategy V) (q : ℕ) (v : V) : ℕ :=
  sSup {n | G.CntPath X σ q v n}

/-- `v` followed by `a`. -/
def consSeq (v : V) (a : ℕ → V) : ℕ → V
  | 0 => v
  | i + 1 => a i

theorem Game.qCount_cons (G : Game V) (q : ℕ) (v : V) (a : ℕ → V) (m : ℕ) :
    G.qCount q (consSeq v a) (m + 1) = G.qCount q a m + if G.prio v = q then 1 else 0 := by
  unfold Game.qCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
  rfl

theorem Game.qCount_single (G : Game V) (q : ℕ) (v : V) :
    G.qCount q (fun _ => v) 0 = if G.prio v = q then 1 else 0 := by
  unfold Game.qCount
  rw [Finset.card_filter, Finset.sum_range_one]

theorem Game.winsFrom_mem {X : Set V} {σ : Strategy V} {v : V} (G : Game V)
    (h : G.WinsFrom X .zero σ v) : v ∈ X := by
  obtain ⟨u, hu⟩ := h.1 v Relation.ReflTransGen.refl
  exact hu.1

theorem Game.path_mem_X (G : Game V) (X : Set V) {σ : Strategy V} {v : V} (hv : v ∈ X) {m : ℕ}
    {a : ℕ → V} (ha0 : a 0 = v) (hstep : ∀ i < m, G.Step X .zero σ (a i) (a (i + 1))) :
    ∀ i ≤ m, a i ∈ X
  | 0, _ => ha0 ▸ hv
  | i + 1, hi => (hstep i (by omega)).2.1

theorem Game.chainPath_le [Finite V] (G : Game V) {R : Set V} {q n : ℕ} (h : G.ChainPath R q n) :
    n ≤ Nat.card V := by
  classical
  obtain ⟨m, a, -, -, hinj, rfl⟩ := h
  haveI := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, ← Finset.card_image_of_injOn (f := a)]
  · exact Finset.card_le_univ _
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
    exact hinj x (by omega) y (by omega) hx.2 hxy

theorem Game.chainPath_bdd [Finite V] (G : Game V) (R : Set V) (q : ℕ) :
    BddAbove {n | G.ChainPath R q n} :=
  ⟨Nat.card V, fun _ hn => G.chainPath_le hn⟩

/-- The positions counted by a counter path from a won node lie on a chain path of the node's
    region: they stay in the region, and no priority-`q_l` node repeats (`Game.no_odd_repeat`). -/
theorem Game.cntPath_chainPath [Finite V] (G : Game V) (X : Set V) {σ : Strategy V} {v : V}
    (hwin : G.WinsFrom X .zero σ v) {l : ℕ} (hl : l < G.height X) {n : ℕ}
    (h : G.CntPath X σ (G.level X l) v n) : G.ChainPath (G.region X l v) (G.level X l) n := by
  obtain ⟨m, a, ha0, hstep, hle, rfl⟩ := h
  have haX := G.path_mem_X X (G.winsFrom_mem hwin) ha0 hstep
  have hreg := G.path_mem_region X ha0 haX (fun i hi => (hstep i hi).2.2.1) l
    (fun i hi => G.belongs_of_le X hl (hle i hi))
  refine ⟨m, a, fun i hi => ⟨hreg i hi, hle i hi⟩, fun i hi => (hstep i hi).2.2.1, ?_, rfl⟩
  intro i hi j hj hq heq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact G.no_odd_repeat X hwin ha0 hstep h hj heq (fun t ht => hq ▸ hle t ht)
      (hq ▸ G.level_odd X hl)
  · have hq' : G.prio (a j) = G.level X l := heq ▸ hq
    exact G.no_odd_repeat X hwin ha0 hstep h hi heq.symm (fun t ht => hq' ▸ hle t ht)
      (hq' ▸ G.level_odd X hl)

theorem Game.cnt_bdd [Finite V] (G : Game V) (X : Set V) {σ : Strategy V} {v : V}
    (hwin : G.WinsFrom X .zero σ v) {l : ℕ} (hl : l < G.height X) :
    BddAbove {n | G.CntPath X σ (G.level X l) v n} :=
  ⟨Nat.card V, fun _ hn => G.chainPath_le (G.cntPath_chainPath X hwin hl hn)⟩

/-- The counter is bounded by the chain bound of the node's region. -/
theorem Game.cnt_le_chainBound [Finite V] (G : Game V) (X : Set V) {σ : Strategy V} {v : V}
    (hwin : G.WinsFrom X .zero σ v) {l : ℕ} (hl : l < G.height X) :
    G.cnt X σ (G.level X l) v ≤ G.chainBound (G.region X l v) (G.level X l) :=
  csSup_le_csSup' (G.chainPath_bdd _ _) (fun _ hn => G.cntPath_chainPath X hwin hl hn)

theorem Game.cnt_eq_zero (G : Game V) (X : Set V) (σ : Strategy V) {q : ℕ} {v : V}
    (hv : q < G.prio v) : G.cnt X σ q v = 0 := by
  have : {n | G.CntPath X σ q v n} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨m, a, rfl, -, hle, -⟩
    have := hle 0 (by omega)
    omega
  unfold Game.cnt
  rw [this]
  simp

theorem Game.cntPath_single (G : Game V) (X : Set V) (σ : Strategy V) {q : ℕ} {v : V}
    (hv : G.prio v ≤ q) : G.CntPath X σ q v (if G.prio v = q then 1 else 0) :=
  ⟨0, fun _ => v, rfl, fun _ h => absurd h (by omega), fun _ _ => hv,
    (G.qCount_single q v).symm⟩

theorem Game.cntPath_cons (G : Game V) (X : Set V) {σ : Strategy V} {q : ℕ} {v w : V}
    (hs : G.Step X .zero σ v w) (hv : G.prio v ≤ q) {n : ℕ} (h : G.CntPath X σ q w n) :
    G.CntPath X σ q v (n + if G.prio v = q then 1 else 0) := by
  obtain ⟨m, a, ha0, hstep, hle, rfl⟩ := h
  refine ⟨m + 1, consSeq v a, rfl, fun i hi => ?_, fun i hi => ?_, (G.qCount_cons q v a m).symm⟩
  · cases i with
    | zero => rw [← ha0] at hs; exact hs
    | succ i => exact hstep i (by omega)
  · cases i with
    | zero => exact hv
    | succ i => exact hle i (by omega)

/-- Along a `σ`-conforming move `v → w` with `prio v ≤ q_l`, the counter at level `l` does not
    increase, and strictly decreases if `prio v = q_l`. -/
theorem Game.cnt_step [Finite V] (G : Game V) (X : Set V) {σ : Strategy V} {v w : V}
    (hwv : G.WinsFrom X .zero σ v) (hww : G.WinsFrom X .zero σ w) (hs : G.Step X .zero σ v w)
    {l : ℕ} (hl : l < G.height X) (hle : G.prio v ≤ G.level X l) :
    G.cnt X σ (G.level X l) w + (if G.prio v = G.level X l then 1 else 0) ≤
      G.cnt X σ (G.level X l) v := by
  by_cases hne : {n | G.CntPath X σ (G.level X l) w n}.Nonempty
  · exact le_csSup (G.cnt_bdd X hwv hl)
      (G.cntPath_cons X hs hle (Nat.sSup_mem hne (G.cnt_bdd X hww hl)))
  · have h0 : G.cnt X σ (G.level X l) w = 0 := by
      unfold Game.cnt
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp
    rw [h0, zero_add]
    exact le_csSup (G.cnt_bdd X hwv hl) (G.cntPath_single X σ hle)

/-! ### The measure: component indices interleaved with counters -/

open scoped Classical in
/-- The component index of `v` at level `l` (`0` where `v` does not belong). -/
noncomputable def Game.kIdx [Finite V] (G : Game V) (X : Set V) : ℕ → V → ℕ
  | 0, _ => 0
  | l + 1, v => if G.Belongs X (l + 1) v then
      G.compIdx (G.region X l v) (G.level X l) (G.region X (l + 1) v) else 0

/-- The chain-tree measure of a strategy: `(k₀, c₀, k₁, c₁, …)`. -/
noncomputable def Game.chainMeasure [Finite V] (G : Game V) (X : Set V) (σ : Strategy V) (v : V)
    (i : ℕ) : ℕ :=
  if i < 2 * G.height X then
    (if i % 2 = 0 then G.kIdx X (i / 2) v else G.cnt X σ (G.level X (i / 2)) v)
  else 0

theorem Game.chainMeasure_even [Finite V] (G : Game V) (X : Set V) (σ : Strategy V) (v : V)
    {l : ℕ} (hl : l < G.height X) : G.chainMeasure X σ v (2 * l) = G.kIdx X l v := by
  unfold Game.chainMeasure
  rw [if_pos (by omega), if_pos (by omega), show 2 * l / 2 = l by omega]

theorem Game.chainMeasure_odd [Finite V] (G : Game V) (X : Set V) (σ : Strategy V) (v : V)
    {l : ℕ} (hl : l < G.height X) :
    G.chainMeasure X σ v (2 * l + 1) = G.cnt X σ (G.level X l) v := by
  unfold Game.chainMeasure
  rw [if_pos (by omega), if_neg (by omega), show (2 * l + 1) / 2 = l by omega]

theorem Game.leafRegion_chainMeasure [Finite V] (G : Game V) (X : Set V) (σ : Strategy V) {v : V}
    (hv : v ∈ X) : ∀ l, l < G.height X → G.Belongs X l v →
      G.leafRegion X (G.chainMeasure X σ v) l = G.region X l v
  | 0, _, _ => rfl
  | l + 1, hl, hb => by
    show G.compAt (G.leafRegion X (G.chainMeasure X σ v) l) (G.level X l)
      (G.chainMeasure X σ v (2 * (l + 1))) = G.region X (l + 1) v
    rw [G.leafRegion_chainMeasure X σ hv l (by omega) (hb.mono (by omega)),
      G.chainMeasure_even X σ v hl, Game.kIdx, if_pos hb,
      G.compAt_compIdx (G.region_mem_lowComps X hv hb)]

/-- The measure of a won node is a chain-tree leaf. -/
theorem Game.chainMeasure_isChainLeaf [Finite V] (G : Game V) (X : Set V) {σ : Strategy V}
    {v : V} (hwin : G.WinsFrom X .zero σ v) : G.IsChainLeaf X (G.chainMeasure X σ v) := by
  have hv := G.winsFrom_mem hwin
  refine ⟨?_, fun l hl => ?_, fun l hl => ?_, fun i hi => ?_⟩
  · unfold Game.chainMeasure
    split_ifs <;> simp_all [Game.kIdx]
  · rw [G.chainMeasure_even X σ v hl, Game.kIdx]
    split_ifs with hb
    · rw [G.leafRegion_chainMeasure X σ hv l (by omega) (hb.mono (by omega))]
      exact lt_max_of_lt_right (G.compIdx_lt (G.region_mem_lowComps X hv hb))
    · exact lt_max_of_lt_left zero_lt_one
  · rw [G.chainMeasure_odd X σ v hl]
    by_cases hp : G.prio v ≤ G.level X l
    · rw [G.leafRegion_chainMeasure X σ hv l hl (G.belongs_of_le X hl hp)]
      exact G.cnt_le_chainBound X hwin hl
    · rw [G.cnt_eq_zero X σ (by omega)]
      exact Nat.zero_le _
  · unfold Game.chainMeasure
    rw [if_neg (by omega)]

/-- The measure satisfies the progress condition along every conforming move between won
    nodes: it is componentwise non-increasing on the compared coordinates (component indices are
    equal, or `0` where the target leaves the source's region), and the counter at the source's
    own odd level strictly decreases. -/
theorem Game.chainMeasure_prog [Finite V] (G : Game V) (X : Set V) (C : Codomain (ℕ → ℕ))
    (hC : ∀ p a b, C.le p a b ↔ LexLE (G.chainDepth X p) a b) {σ : Strategy V} {v w : V}
    (hwv : G.WinsFrom X .zero σ v) (hww : G.WinsFrom X .zero σ w) (hs : G.Step X .zero σ v w) :
    G.Prog C (G.chainMeasure X σ) v w := by
  obtain ⟨hvX, hwX, hedge, -⟩ := id hs
  have hle : ∀ i < G.chainDepth X (G.prio v),
      G.chainMeasure X σ w i ≤ G.chainMeasure X σ v i := by
    intro i hi
    unfold Game.chainDepth at hi
    obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' i
    · obtain ⟨hlh, hpl⟩ := (G.lt_levelDepth_iff X).mp (show l < G.levelDepth X (G.prio v) by omega)
      rw [G.chainMeasure_even X σ w hlh, G.chainMeasure_even X σ v hlh]
      cases l with
      | zero => simp [Game.kIdx]
      | succ l =>
        have hbv : G.Belongs X (l + 1) v := G.belongs_of_le X hlh hpl
        by_cases hbw : G.Belongs X (l + 1) w
        · rw [Game.kIdx, Game.kIdx, if_pos hbv, if_pos hbw,
            G.region_eq X hvX hwX hedge (l + 1) hbv hbw,
            G.region_eq X hvX hwX hedge l (hbv.mono (by omega)) (hbw.mono (by omega))]
        · rw [Game.kIdx, if_neg hbw]
          exact Nat.zero_le _
    · obtain ⟨hlh, hpl⟩ := (G.lt_levelDepth_iff X).mp (show l < G.levelDepth X (G.prio v) by omega)
      rw [G.chainMeasure_odd X σ w hlh, G.chainMeasure_odd X σ v hlh]
      exact le_trans (Nat.le_add_right _ _) (G.cnt_step X hwv hww hs hlh hpl)
  refine ⟨(hC _ _ _).mpr (LexLE.of_le hle), fun hodd => ?_⟩
  rw [hC]
  obtain ⟨m, hm, hqm⟩ := G.exists_level_eq X hvX hodd
  have hdep : m < G.levelDepth X (G.prio v) := (G.lt_levelDepth_iff X).mpr ⟨hm, hqm.ge⟩
  apply LexLE.not_of_lt hle (i := 2 * m + 1) (by unfold Game.chainDepth; omega)
  rw [G.chainMeasure_odd X σ w hm, G.chainMeasure_odd X σ v hm]
  have := G.cnt_step X hwv hww hs hm hqm.ge
  rw [if_pos hqm.symm] at this
  omega

/-- Completeness of the chain tree (headline). -/
theorem Game.chainTreeComplete [Finite V] (G : Game V) (X : Set V) (C : Codomain (ℕ → ℕ)) :
    G.ChainTreeComplete X C := by
  intro hC W σ hwin hclosed
  refine ⟨G.chainMeasure X σ, ⟨fun v hv => G.winsFrom_mem (hwin v hv), ?_, ?_⟩,
    fun v hv => G.chainMeasure_isChainLeaf X (hwin v hv)⟩
  · intro v hv ho
    obtain ⟨u, hu⟩ := (hwin v hv).1 v Relation.ReflTransGen.refl
    obtain rfl : u = σ v := hu.2.2.2 ho
    have hu' := hclosed v hv _ hu
    exact ⟨hu', hu.2.2.1, G.chainMeasure_prog X C hC (hwin v hv) (hwin _ hu') hu⟩
  · intro v hv ho w hwX hedge
    have hs : G.Step X .zero σ v w :=
      ⟨G.winsFrom_mem (hwin v hv), hwX, hedge, fun h => by rw [ho] at h; cases h⟩
    exact ⟨hclosed v hv w hs, G.chainMeasure_prog X C hC (hwin v hv) (hwin w
      (hclosed v hv w hs)) hs⟩

/-- Completeness instantiated at the concrete truncated lexicographic codomain. -/
theorem Game.chainTreeComplete_truncLex [Finite V] (G : Game V) (X : Set V) :
    G.ChainTreeComplete X (truncLexCodomain (G.chainDepth X) (G.chainDepth_antitone X)) :=
  G.chainTreeComplete X _

end ChainTree

end ParityGame

end TwoSidedLiftingProofs
