module

public import MercLib.HybridSI.Proofs.Key_Proofs
public import MercLib.ParityGame.Proofs.Game_Proofs

@[expose] public section HybridSIWinProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The core lemma `winsFrom_of_saddle`: if no move of the opponent improves on the profile's key
(from player `i`'s point of view), then from every vertex whose cycle maximum favours `i`,
player `i` wins with the profile as positional strategy. Along a conforming play the reward is
non-decreasing, hence eventually constant with a cycle maximum `L` favouring `i`. Let `M` be the
greatest vertex visited infinitely often. If `M < L` the key strictly increases forever; if
`L < M` and `M` does not favour `i`, the part of the signed sum at or above `M` never decreases
and strictly increases at every visit of `M`. Both contradict finiteness. -/

open Function MercLib.ParityGame Filter

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem eventually_const_of_monotone {g : ℕ → ℤ} (hg : Monotone g) (hfin : (Set.range g).Finite) :
    ∃ N, ∀ n ≥ N, g n = g N := by
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ := Set.exists_max_image _ id hfin ⟨g 0, 0, rfl⟩
  exact ⟨N, fun n hn => le_antisymm (hmax (g n) ⟨n, rfl⟩) (hg hn)⟩

variable {G : Game V} {f : V → V} {i : Player}

/-- Player `i`'s view of the key of `x` under `f`. -/
abbrev K (G : Game V) (f : V → V) (i : Player) (x : V) : Key := kfor i (key G f x)

theorem K_le_iff (a b : V) :
    K G f i a ≤ K G f i b ↔ rI G i (cycMax f a) < rI G i (cycMax f b) ∨
      (rI G i (cycMax f a) = rI G i (cycMax f b) ∧
        (∑ y ∈ bSet f a, wI G i y < ∑ y ∈ bSet f b, wI G i y ∨
          (∑ y ∈ bSet f a, wI G i y = ∑ y ∈ bSet f b, wI G i y ∧
            eI G i (cycMax f a) (stepsTo f a) ≤ eI G i (cycMax f b) (stepsTo f b)))) := by
  rw [K, K, kfor_key, kfor_key, lex_le_iff, lex2_le_iff]

theorem rI_le_of_K_le {a b : V} (h : K G f i a ≤ K G f i b) :
    rI G i (cycMax f a) ≤ rI G i (cycMax f b) := by
  rcases (K_le_iff a b).1 h with h | ⟨h, -⟩ <;> omega

theorem sum_le_of_K_le {a b : V} (h : K G f i a ≤ K G f i b)
    (hr : rI G i (cycMax f a) = rI G i (cycMax f b)) :
    ∑ y ∈ bSet f a, wI G i y ≤ ∑ y ∈ bSet f b, wI G i y := by
  rcases (K_le_iff a b).1 h with h | ⟨-, h | ⟨h, -⟩⟩ <;> omega

theorem rI_bound (l : V) : rI G i l ≤ Fintype.card V + 1 := by
  have : rank l ≤ Fintype.card V := by
    rw [rank_eq_card]; exact Finset.card_le_univ _
  unfold rI; split_ifs <;> omega

/-- The core lemma. -/
theorem winsFrom_of_saddle (hrel : G.Relabelled)
    (hown : ∀ v, G.owner v = i → G.edge v (f v))
    (hloc : ∀ v, G.owner v ≠ i → ∀ w, G.edge v w → K G f i (f v) ≤ K G f i w)
    (v : V) (hv : 0 < rI G i (cycMax f v)) : G.WinsFrom Set.univ i f v := by
  refine ⟨fun w _ => ?_, fun p hp0 hp => ?_⟩
  · by_cases hw : G.owner w = i
    · exact ⟨f w, Set.mem_univ _, Set.mem_univ _, hown w hw, fun _ => rfl⟩
    · obtain ⟨u, hu⟩ := G.total w
      exact ⟨u, Set.mem_univ _, Set.mem_univ _, hu, fun h => absurd h hw⟩
  -- one step of the play
  have hstep : ∀ n, K G f i (f (p n)) ≤ K G f i (p (n + 1)) := by
    intro n
    obtain ⟨-, -, he, hs⟩ := hp n
    by_cases ho : G.owner (p n) = i
    · rw [hs ho]
    · exact hloc _ ho _ he
  let r : ℕ → ℤ := fun n => rI G i (cycMax f (p n))
  have hr_mono : Monotone r := monotone_nat_of_le_succ fun n => by
    have := rI_le_of_K_le (hstep n)
    simp only [r]
    rwa [cycMax_apply] at this
  have hr_fin : (Set.range r).Finite :=
    (Set.finite_range fun y : V => rI G i (cycMax f y)).subset (by
      rintro _ ⟨n, rfl⟩; exact ⟨p n, rfl⟩)
  obtain ⟨N, hN⟩ := eventually_const_of_monotone hr_mono hr_fin
  have hcpos : 0 < r N := lt_of_lt_of_le (by simpa [r, hp0] using hv) (hr_mono (Nat.zero_le N))
  set L := cycMax f (p N) with hL
  have hLgood : Good i (G.prio L) := (rI_pos_iff i L).1 hcpos
  have hLam : ∀ n ≥ N, cycMax f (p n) = L := fun n hn =>
    (rI_inj (hN n hn).symm hcpos).symm
  -- the recurring vertices and the tail inside them
  let T : Set V := nodeInf p
  have hTev : ∀ᶠ n in atTop, p n ∈ T := by
    have : ∀ y : V, ∀ᶠ n in atTop, y ∉ T → p n ≠ y := fun y => by
      by_cases hy : y ∈ T
      · exact Eventually.of_forall fun _ h => absurd hy h
      · have : ∀ᶠ n in atTop, p n ≠ y := by
          simpa [T, nodeInf, Filter.Frequently] using hy
        exact this.mono fun _ h _ => h
    exact (eventually_all.2 this).mono fun n h => by
      by_contra hn
      exact h (p n) hn rfl
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hTev
  have hTne : T.Nonempty := by
    obtain ⟨x, -, hx⟩ := (Cslib.ωSequence.frequently_in_finite_type (s := Set.univ) (xs := p)).mp
      (Frequently.of_forall fun _ => Set.mem_univ _)
    exact ⟨x, hx⟩
  have hTfin : T.Finite := Set.toFinite T
  obtain ⟨M, hMT, hMge⟩ := Set.exists_max_image T id hTfin hTne
  -- it suffices that `M` favours `i`
  suffices hM : Good i (G.prio M) by
    refine ⟨G.prio M, (G.maxInfPrio_iff p _).2 ⟨⟨M, hMT, rfl⟩, fun y hy => hrel (hMge y hy)⟩, hM⟩
  set N3 := max N N2
  have htail : ∀ n ≥ N3, cycMax f (p n) = L ∧ p n ∈ T := fun n hn =>
    ⟨hLam n (le_of_max_le_left hn), hN2 n (le_of_max_le_right hn)⟩
  rcases lt_trichotomy M L with hML | hML | hML
  · -- `M < L`: the key strictly increases along the tail
    exfalso
    have hinc : ∀ n ≥ N3, K G f i (p n) < K G f i (p (n + 1)) := by
      intro n hn
      obtain ⟨hl, hT⟩ := htail n hn
      have hxL : p n < L := lt_of_le_of_lt (hMge _ hT) hML
      have hne : p n ≠ cycMax f (p n) := by rw [hl]; exact ne_of_lt hxL
      refine lt_of_lt_of_le ?_ (hstep n)
      refine lt_of_not_ge fun hle => ?_
      have hs := stepsTo_apply hne
      have hsum := sum_bSet_apply (G := G) hne i
      rw [ite_eq_right (by rw [hl]; exact not_lt.2 (le_of_lt hxL)), add_zero] at hsum
      rcases (K_le_iff _ _).1 hle with h | ⟨-, h | ⟨-, h⟩⟩
      · rw [cycMax_apply] at h; omega
      · omega
      · have he : eI G i (cycMax f (p n)) (stepsTo f (p n)) =
            eI G i (cycMax f (f (p n))) (stepsTo f (f (p n))) - 1 := by
          unfold eI
          rw [cycMax_apply, hl, hs]
          simp only [ite_eq_left hLgood]
          push_cast; ring
        omega
    have hinj : Injective fun m => p (N3 + m) := by
      intro a b hab
      have hmono : StrictMono fun m => K G f i (p (N3 + m)) :=
        strictMono_nat_of_lt_succ fun m => by
          simpa [Nat.add_assoc] using hinc (N3 + m) (Nat.le_add_right _ _)
      exact hmono.injective (by simp only at hab ⊢; rw [hab])
    exact not_injective_infinite_finite _ hinj
  · rw [hML]; exact hLgood
  · -- `L < M`
    by_contra hbad
    have hw : wI G i M = -(2 ^ rank M) := by unfold wI; rw [ite_eq_right hbad]
    let u : V → ℤ := fun x => ∑ y ∈ (bSet f x).filter (M ≤ ·), wI G i y
    have hu_step : ∀ n ≥ N3, u (p n) ≤ u (p (n + 1)) ∧ (p n = M → u (p n) < u (p (n + 1))) := by
      intro n hn
      obtain ⟨hl, hT⟩ := htail n hn
      obtain ⟨hl', -⟩ := htail (n + 1) (Nat.le_succ_of_le hn)
      have hr : rI G i (cycMax f (f (p n))) = rI G i (cycMax f (p (n + 1))) := by
        rw [cycMax_apply, hl, hl']
      have hup : u (f (p n)) ≤ u (p (n + 1)) :=
        upper_le_of_le _ (wI_signed G i) _ _ M (sum_le_of_K_le (hstep n) hr)
      by_cases hx : p n = cycMax f (p n)
      · have h0 : u (p n) = 0 := by simp [u, bSet_eq_empty hx]
        have h0' : u (f (p n)) = 0 := by
          have := bSet_apply_cycMax (f := f) (p n)
          rw [← hx] at this
          simp [u, this]
        refine ⟨by omega, fun hpM => ?_⟩
        rw [hl] at hx
        exact absurd (hx ▸ hpM) (ne_of_lt hML)
      · have hrec := upper_bSet_apply (G := G) (m := M) hx i
        have hle : p n ≤ M := hMge _ hT
        have hpos : (0 : ℤ) < 2 ^ rank M := by positivity
        refine ⟨?_, fun hpM => ?_⟩
        · by_cases hcond : cycMax f (p n) < p n ∧ M ≤ p n
          · have hwx : wI G i (p n) = -(2 ^ rank M) := by
              rw [le_antisymm hle hcond.2]; exact hw
            rw [ite_eq_left hcond, hwx] at hrec
            simp only [u] at hup ⊢
            omega
          · rw [ite_eq_right hcond, add_zero] at hrec
            simp only [u] at hup ⊢
            omega
        · have hcond : cycMax f (p n) < p n ∧ M ≤ p n :=
            ⟨by rw [hl, hpM]; exact hML, hpM ▸ le_refl _⟩
          have hwx : wI G i (p n) = -(2 ^ rank M) := by rw [hpM]; exact hw
          rw [ite_eq_left hcond, hwx] at hrec
          simp only [u] at hup ⊢
          omega
    let g : ℕ → ℤ := fun m => u (p (N3 + m))
    have hg_mono : Monotone g := monotone_nat_of_le_succ fun m => by
      simpa [g, Nat.add_assoc] using (hu_step (N3 + m) (Nat.le_add_right _ _)).1
    have hg_fin : (Set.range g).Finite :=
      (Set.finite_range u).subset (by rintro _ ⟨m, rfl⟩; exact ⟨p (N3 + m), rfl⟩)
    obtain ⟨N4, hN4⟩ := eventually_const_of_monotone hg_mono hg_fin
    have hMfreq : ∃ᶠ n in atTop, p n = M := hMT
    obtain ⟨n, hn, hpn⟩ := (frequently_atTop.1 hMfreq) (N3 + N4)
    have h1 := (hu_step n (by omega)).2 hpn
    have e1 := hN4 (n - N3) (by omega)
    have e2 := hN4 (n - N3 + 1) (by omega)
    simp only [g, show N3 + (n - N3) = n by omega, show N3 + (n - N3 + 1) = n + 1 by omega] at e1 e2
    omega

end MercLib.HybridSI

end HybridSIWinProofs
