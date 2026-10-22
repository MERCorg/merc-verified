module

public import MercLib.HybridSI.Bounds
public import MercLib.HybridSI.Proofs.Potential_Proofs

@[expose] public section HybridSIBoundsSubgameProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Keys on a closed subgame (`HybridSI.Bounds`, `subgame`). A profile `fD : D → D` of the subgame
*restricts* `f : V → V` if `(fD a).1 = f a.1`. Plays, cycle maxima, step counts and the sets `B`
of play values commute with the restriction (`cycMax_val`, `stepsTo_val`, `bSet_val`). The keys
themselves differ (ranks in `D` are not ranks in `V`), but their comparisons agree
(`key_le_val`): a comparison of signed sums of distinct powers of two is decided by the most
relevant element of the symmetric difference (`sum_lt_iff`), which only depends on the order. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### Signed sums -/

/-- A signed sum of distinct powers of two is smaller than another iff the most relevant element
    of the symmetric difference is in the second set exactly when its weight is positive. -/
theorem sum_lt_iff (δ : V → ℤ) (hδ : SignedPow δ) (A B : Finset V) :
    ∑ y ∈ A, δ y < ∑ y ∈ B, δ y ↔
      ∃ t, (t ∈ A ↔ t ∉ B) ∧ (∀ y, (y ∈ A ↔ y ∉ B) → y ≤ t) ∧ (t ∈ B ↔ 0 < δ t) := by
  classical
  have hm : ∀ y, y ∈ symmDiff A B ↔ (y ∈ A ↔ y ∉ B) := fun y => by
    rw [Finset.mem_symmDiff]; tauto
  simp only [← hm]
  let ε : V → ℤ := fun y => if y ∈ B then δ y else -δ y
  have hε : SignedPow ε := fun y => by
    simp only [ε]; split_ifs
    · exact hδ y
    · rcases hδ y with h | h <;> rw [h] <;> simp
  have hd : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]; intro y h1 h2
    simp only [Finset.mem_sdiff] at h1 h2; tauto
  have hdiff : ∑ y ∈ B, δ y - ∑ y ∈ A, δ y = ∑ y ∈ symmDiff A B, ε y := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.sum_union hd, ← Finset.sum_sdiff_sub_sum_sdiff]
    have e1 : ∑ y ∈ A \ B, ε y = -∑ y ∈ A \ B, δ y := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y hy => ?_
      simp [ε, (Finset.mem_sdiff.1 hy).2]
    have e2 : ∑ y ∈ B \ A, ε y = ∑ y ∈ B \ A, δ y :=
      Finset.sum_congr rfl fun y hy => by simp [ε, (Finset.mem_sdiff.1 hy).1]
    rw [e1, e2]; ring
  have hpos : ∀ t, δ t ≠ 0 := fun t => by
    rcases hδ t with h | h <;> rw [h] <;> simp
  by_cases hS : symmDiff A B = ∅
  · rw [hS, Finset.sum_empty] at hdiff
    constructor
    · intro h; omega
    · rintro ⟨t, ht, -⟩; rw [hS] at ht; exact absurd ht (Finset.notMem_empty t)
  · obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (symmDiff A B) id
      (Finset.nonempty_iff_ne_empty.2 hS)
    simp only [id] at hmax
    have hdom := (top_dominates ε hε _ t ht hmax).1
    have het : 0 < ε t ↔ (t ∈ B ↔ 0 < δ t) := by
      have := hpos t
      simp only [ε]; split_ifs with h <;> simp [h]
      omega
    constructor
    · intro h
      exact ⟨t, ht, fun y hy => hmax y hy, het.1 (hdom.1 (by omega))⟩
    · rintro ⟨t', ht', hmax', hb⟩
      have : t' = t := le_antisymm (hmax t' ht') (hmax' t ht)
      subst this
      have := hdom.2 (het.2 hb)
      omega

/-! ### Restriction to a closed subgame -/

variable (G : Game V) {D : Finset V} (hD : Closed G D)

section Restrict

variable {f : V → V} {fD : D → D} (hf : ∀ a, (fD a).1 = f a.1)
include hf

theorem iterate_val : ∀ (i : ℕ) (a : D), (fD^[i] a).1 = f^[i] a.1
  | 0, _ => rfl
  | i + 1, a => by rw [iterate_succ_apply, iterate_succ_apply, iterate_val i, hf]

theorem recurs_val {a b : D} : Recurs fD a b ↔ Recurs f a.1 b.1 := by
  simp only [Recurs, ← iterate_val hf, Subtype.ext_iff]

theorem cycMax_val (a : D) : (cycMax fD a).1 = cycMax f a.1 := by
  refine le_antisymm (le_cycMax ((recurs_val hf).1 (recurs_cycMax a))) ?_
  obtain ⟨i, -, hi⟩ := recurs_cycMax (f := f) a.1 0
  have hb : Recurs fD a (fD^[i] a) := by
    rw [recurs_val hf, iterate_val hf, hi]; exact recurs_cycMax a.1
  have := le_cycMax hb
  rw [← iterate_val hf, ← hi] at *
  exact this

theorem stepsTo_val (a : D) : stepsTo fD a = stepsTo f a.1 := by
  obtain ⟨h1, h2⟩ := stepsTo_spec (f := fD) a
  obtain ⟨h1', h2'⟩ := stepsTo_spec (f := f) a.1
  rcases lt_trichotomy (stepsTo fD a) (stepsTo f a.1) with h | h | h
  · exact absurd (by rw [← iterate_val hf, h1, cycMax_val hf]) (h2' _ h)
  · exact h
  · exact absurd (Subtype.ext (by rw [iterate_val hf, h1', cycMax_val hf])) (h2 _ h)

theorem bSet_val (a : D) : bSet f a.1 = (bSet fD a).map (Embedding.subtype _) := by
  ext y
  simp only [Finset.mem_map, Embedding.coe_subtype, mem_bSet, stepsTo_val hf]
  constructor
  · rintro ⟨⟨i, hi, e⟩, hlt⟩
    refine ⟨fD^[i] a, ⟨⟨i, hi, rfl⟩, ?_⟩, by rw [iterate_val hf, e]⟩
    show (cycMax fD a).1 < (fD^[i] a).1
    rw [cycMax_val hf, iterate_val hf, e]; exact hlt
  · rintro ⟨b, ⟨⟨i, hi, rfl⟩, hlt⟩, rfl⟩
    refine ⟨⟨i, hi, (iterate_val hf i a).symm⟩, ?_⟩
    have : (cycMax fD a).1 < (fD^[i] a).1 := hlt
    rwa [cycMax_val hf] at this

end Restrict

theorem rI_lt_val (i : Player) (x y : D) :
    rI G i x.1 < rI G i y.1 ↔ rI (subgame G D hD) i x < rI (subgame G D hD) i y := by
  have e : ∀ z : D, Good i ((subgame G D hD).prio z) ↔ Good i (G.prio z.1) := fun _ => Iff.rfl
  rcases lt_trichotomy x y with h | h | h
  · have h1 := rank_lt_rank h
    have h2 := rank_lt_rank (show x.1 < y.1 from h)
    unfold rI
    simp only [e]
    split_ifs <;> constructor <;> intro _ <;> omega
  · subst h; simp
  · have h1 := rank_lt_rank h
    have h2 := rank_lt_rank (show y.1 < x.1 from h)
    unfold rI
    simp only [e]
    split_ifs <;> constructor <;> intro _ <;> omega

theorem rI_eq_val (i : Player) (x y : D) :
    rI G i x.1 = rI G i y.1 ↔ rI (subgame G D hD) i x = rI (subgame G D hD) i y := by
  constructor
  · intro h; rw [Subtype.ext (rI_injective h)]
  · intro h; rw [rI_injective h]

theorem wI_pos_val (i : Player) (x : D) :
    0 < wI G i x.1 ↔ 0 < wI (subgame G D hD) i x := by
  have p1 := pow_pos (two_pos (α := ℤ)) (rank x.1)
  have p2 := pow_pos (two_pos (α := ℤ)) (rank x)
  unfold wI
  split_ifs with h1 h2 h2 <;>
    first
    | exact absurd h1 h2
    | exact absurd h2 h1
    | (constructor <;> intro _ <;> linarith)

theorem sum_lt_val (i : Player) (A B : Finset D) :
    ∑ y ∈ A.map (Embedding.subtype _), wI G i y < ∑ y ∈ B.map (Embedding.subtype _), wI G i y ↔
      ∑ y ∈ A, wI (subgame G D hD) i y < ∑ y ∈ B, wI (subgame G D hD) i y := by
  rw [sum_lt_iff _ (wI_signed G i), sum_lt_iff _ (wI_signed _ i)]
  have hmA : ∀ s : D, s.1 ∈ A.map (Embedding.subtype _) ↔ s ∈ A := fun s => by
    simp only [Finset.mem_map, Embedding.coe_subtype]
    exact ⟨fun ⟨s', h, e⟩ => by rwa [Subtype.ext e] at h, fun h => ⟨s, h, rfl⟩⟩
  have hmB : ∀ s : D, s.1 ∈ B.map (Embedding.subtype _) ↔ s ∈ B := fun s => by
    simp only [Finset.mem_map, Embedding.coe_subtype]
    exact ⟨fun ⟨s', h, e⟩ => by rwa [Subtype.ext e] at h, fun h => ⟨s, h, rfl⟩⟩
  have hD' : ∀ t : V, (t ∈ A.map (Embedding.subtype _) ↔ t ∉ B.map (Embedding.subtype _)) →
      t ∈ D := fun t ht => by
    by_cases hA : t ∈ A.map (Embedding.subtype _)
    · obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 hA; exact s.2
    · obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 (not_not.1 (fun h => hA (ht.2 h))); exact s.2
  constructor
  · rintro ⟨t, ht, hmax, hb⟩
    refine ⟨⟨t, hD' t ht⟩, by rw [← hmA, ← hmB]; exact ht, fun y hy => hmax y.1
      (by rw [hmA, hmB]; exact hy), ?_⟩
    rw [← wI_pos_val G hD, ← hb]; exact (hmB _).symm
  · rintro ⟨s, hs, hmax, hb⟩
    refine ⟨s.1, by rw [hmA, hmB]; exact hs, fun y hy => ?_, by rw [wI_pos_val G hD, ← hb, hmB]⟩
    exact hmax ⟨y, hD' y hy⟩ (by rw [← hmA, ← hmB]; exact hy)

theorem eI_val (i : Player) (x : D) (k : ℕ) : eI G i x.1 k = eI (subgame G D hD) i x k := rfl

/-- Comparisons of keys agree on a closed subgame. -/
theorem key_le_val {f g : V → V} {fD gD : D → D} (hf : ∀ a, (fD a).1 = f a.1)
    (hg : ∀ a, (gD a).1 = g a.1) (a b : D) :
    key G f a.1 ≤ key G g b.1 ↔ key (subgame G D hD) fD a ≤ key (subgame G D hD) gD b := by
  have k1 : key G f a.1 ≤ key G g b.1 ↔ K G f .zero a.1 ≤ K G g .zero b.1 := by simp [K, kfor]
  have k2 : key (subgame G D hD) fD a ≤ key (subgame G D hD) gD b ↔
      K (subgame G D hD) fD .zero a ≤ K (subgame G D hD) gD .zero b := by simp [K, kfor]
  rw [k1, k2, K_le_iff', K_le_iff', ← cycMax_val hf, ← cycMax_val hg, rI_lt_val G hD,
    rI_eq_val G hD, bSet_val hf, bSet_val hg, sum_lt_val G hD,
    ← stepsTo_val hf, ← stepsTo_val hg, eI_val G hD, eI_val G hD]
  have hs : ∀ A B : Finset D,
      ∑ y ∈ A.map (Embedding.subtype _), wI G .zero y =
          ∑ y ∈ B.map (Embedding.subtype _), wI G .zero y ↔
        ∑ y ∈ A, wI (subgame G D hD) .zero y = ∑ y ∈ B, wI (subgame G D hD) .zero y := by
    intro A B
    rw [← not_iff_not, ← ne_eq, ← ne_eq, ← lt_or_lt_iff_ne, ← lt_or_lt_iff_ne, sum_lt_val G hD,
      sum_lt_val G hD]
  rw [hs]

theorem key_lt_val {f g : V → V} {fD gD : D → D} (hf : ∀ a, (fD a).1 = f a.1)
    (hg : ∀ a, (gD a).1 = g a.1) (a b : D) :
    key G f a.1 < key G g b.1 ↔ key (subgame G D hD) fD a < key (subgame G D hD) gD b := by
  rw [← not_le, ← not_le, key_le_val G hD hg hf]

theorem key_eq_val {f g : V → V} {fD gD : D → D} (hf : ∀ a, (fD a).1 = f a.1)
    (hg : ∀ a, (gD a).1 = g a.1) (a b : D) :
    key G f a.1 = key G g b.1 ↔ key (subgame G D hD) fD a = key (subgame G D hD) gD b := by
  rw [le_antisymm_iff, le_antisymm_iff, key_le_val G hD hf hg, key_le_val G hD hg hf]

end MercLib.HybridSI

end HybridSIBoundsSubgameProofs
