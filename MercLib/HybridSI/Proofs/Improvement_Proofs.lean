module

public import MercLib.HybridSI.Proofs.Correctness_Proofs

@[expose] public section HybridSIImprovementProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The Vöge–Jurdziński improvement theory on profiles, from the point of view of a player `i`
(`K G f i x`: larger is better for `i`).

* `K_le_of_dom` (the master lemma, VJ Lemma 5.5 for profiles): if every move of a profile `g` is
  at least as good as the move of `f`, measured in the keys of `f`
  (`K f (f u) ≤ K f (g u)` for all `u`), then `K f ≤ K g` pointwise. Along the play under `g` the
  reward of `f` is non-decreasing; the reward of `g`'s cycle maximum is at least the eventual one
  (`tail_lt_false`, `tail_upper_false`, the two arguments of `winsFrom_of_saddle`), and if the
  rewards agree, an induction along the path to the cycle maximum compares the remaining
  components (`K_le_path`).
* `respond_odd_optimal` / `respond_even_optimal` (one-player optimality, VJ Lemmas 5.2/5.5/5.9):
  a returned best response is at least as good for its player as any other strategy of it.
* `improvement` (VJ Lemma 5.7): switching Even's improving edges against an Odd best response
  gives keys that are pointwise at least as large against *every* Odd counter-strategy, and the
  keys of the chosen successors increase strictly at every switched vertex.

**Note on strictness.** The valuation itself need not increase strictly (so VJ's Lemma 5.8,
2 ⇒ 3, fails for these keys): with Even vertices `v` (the top priority, even), `a`, `b` and edges
`v → a, v → b, a → b, b → v`, switching `v` from `a` to `b` is improving (`b` reaches the even
cycle maximum `v` sooner) but every key stays the same (`v` is the cycle maximum either way).
What does increase strictly is the key of the successor chosen at a switched vertex, which is the
potential used for termination (`Termination_Proofs`). -/

open Function MercLib.ParityGame Filter

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable {G : Game V} {f g : V → V} {i : Player}

/-! ### Rewards -/

theorem rI_injective {l l' : V} (h : rI G i l = rI G i l') : l = l' := by
  unfold rI at h
  split_ifs at h <;> exact rank_injective (by omega)

theorem rI_lt_of_bad {l m : V} (hbad : ¬ Good i (G.prio l)) (hml : m < l) :
    rI G i l < rI G i m := by
  have := rank_lt_rank hml
  unfold rI; split_ifs <;> omega

theorem rI_lt_of_good {l m : V} (hgood : Good i (G.prio m)) (hlm : l < m) :
    rI G i l < rI G i m := by
  have := rank_lt_rank hlm
  unfold rI; split_ifs <;> omega

/-- Comparison of keys of two profiles, in components. -/
theorem K_le_iff' (a b : V) :
    K G f i a ≤ K G g i b ↔ rI G i (cycMax f a) < rI G i (cycMax g b) ∨
      (rI G i (cycMax f a) = rI G i (cycMax g b) ∧
        (∑ y ∈ bSet f a, wI G i y < ∑ y ∈ bSet g b, wI G i y ∨
          (∑ y ∈ bSet f a, wI G i y = ∑ y ∈ bSet g b, wI G i y ∧
            eI G i (cycMax f a) (stepsTo f a) ≤ eI G i (cycMax g b) (stepsTo g b)))) := by
  rw [K, K, kfor_key, kfor_key, lex_le_iff, lex2_le_iff]

/-! ### The two tail arguments -/

/-- If from some point on a sequence stays strictly below the common cycle maximum `L` of `f`,
    and `L` favours `i`, the keys of `f` increase strictly forever: impossible. -/
theorem tail_lt_false {p : ℕ → V} (hstep : ∀ n, K G f i (f (p n)) ≤ K G f i (p (n + 1)))
    {N : ℕ} {L : V} (hL : Good i (G.prio L)) (h : ∀ n ≥ N, cycMax f (p n) = L ∧ p n < L) :
    False := by
  have hinc : ∀ n ≥ N, K G f i (p n) < K G f i (p (n + 1)) := by
    intro n hn
    obtain ⟨hl, hxL⟩ := h n hn
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
        simp only [ite_eq_left hL]
        push_cast; ring
      omega
  have hinj : Injective fun m => p (N + m) := by
    intro a b hab
    have hmono : StrictMono fun m => K G f i (p (N + m)) :=
      strictMono_nat_of_lt_succ fun m => by
        simpa [Nat.add_assoc] using hinc (N + m) (Nat.le_add_right _ _)
    exact hmono.injective (by simp only at hab ⊢; rw [hab])
  exact not_injective_infinite_finite _ hinj

/-- If from some point on a sequence has the common cycle maximum `L` of `f`, stays at or below
    `M > L` and visits `M` infinitely often, then `M` favours `i`. -/
theorem tail_upper_false {p : ℕ → V} (hstep : ∀ n, K G f i (f (p n)) ≤ K G f i (p (n + 1)))
    {N : ℕ} {L M : V} (hML : L < M) (hbad : ¬ Good i (G.prio M))
    (h : ∀ n ≥ N, cycMax f (p n) = L ∧ p n ≤ M) (hfreq : ∀ n, ∃ m ≥ n, p m = M) : False := by
  have hw : wI G i M = -(2 ^ rank M) := by unfold wI; rw [ite_eq_right hbad]
  let u : V → ℤ := fun x => ∑ y ∈ (bSet f x).filter (M ≤ ·), wI G i y
  have hu_step : ∀ n ≥ N, u (p n) ≤ u (p (n + 1)) ∧ (p n = M → u (p n) < u (p (n + 1))) := by
    intro n hn
    obtain ⟨hl, hle⟩ := h n hn
    obtain ⟨hl', -⟩ := h (n + 1) (Nat.le_succ_of_le hn)
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
  let g' : ℕ → ℤ := fun m => u (p (N + m))
  have hg_mono : Monotone g' := monotone_nat_of_le_succ fun m => by
    simpa [g', Nat.add_assoc] using (hu_step (N + m) (Nat.le_add_right _ _)).1
  have hg_fin : (Set.range g').Finite :=
    (Set.finite_range u).subset (by rintro _ ⟨m, rfl⟩; exact ⟨p (N + m), rfl⟩)
  obtain ⟨N4, hN4⟩ := eventually_const_of_monotone hg_mono hg_fin
  obtain ⟨n, hn, hpn⟩ := hfreq (N + N4)
  have h1 := (hu_step n (by omega)).2 hpn
  have e1 := hN4 (n - N) (by omega)
  have e2 := hN4 (n - N + 1) (by omega)
  simp only [g', show N + (n - N) = n by omega, show N + (n - N + 1) = n + 1 by omega] at e1 e2
  omega

/-! ### The master lemma -/

/-- Along the path of `g` to its cycle maximum `M`, if `f` has cycle maximum `M` everywhere on
    the play of `g`, the keys of `f` are at most those of `g`. -/
theorem K_le_path (hdom : ∀ u, K G f i (f u) ≤ K G f i (g u)) (M : V) :
    ∀ (k : ℕ) (x : V), stepsTo g x = k → cycMax g x = M → (∀ m, cycMax f (g^[m] x) = M) →
      K G f i x ≤ K G g i x
  | 0, x, hk, hg, hf => by
    have hx : x = M := by
      have := (stepsTo_spec (f := g) x).1
      rw [hk, hg] at this
      simpa using this
    have hfM : cycMax f x = M := by simpa using hf 0
    have hfx : x = cycMax f x := by rw [hfM, hx]
    have hgx : x = cycMax g x := by rw [hg, hx]
    rw [K_le_iff', sum_bSet_self hfx, sum_bSet_self hgx, stepsTo_eq_zero hfx,
      stepsTo_eq_zero hgx, hfM, hg]
    right; simp
  | k + 1, x, hk, hg, hf => by
    have hgx : x ≠ cycMax g x := fun h => by rw [stepsTo_eq_zero h] at hk; omega
    have hfM : cycMax f x = M := by simpa using hf 0
    have hfx : x ≠ cycMax f x := by rw [hfM, ← hg]; exact hgx
    have ih := K_le_path hdom M k (g x) (by rw [stepsTo_apply hgx] at hk; omega)
      (by rw [cycMax_apply, hg]) (fun m => by rw [← iterate_succ_apply]; exact hf (m + 1))
    have h1 := (hdom x).trans ih
    rw [K_le_iff'] at h1 ⊢
    simp only [cycMax_apply] at h1
    rw [sum_bSet_apply hfx, sum_bSet_apply hgx, stepsTo_apply hfx, stepsTo_apply hgx]
    rw [hfM, hg] at h1 ⊢
    unfold eI at h1 ⊢
    split_ifs at h1 ⊢ <;> push_cast at h1 ⊢ <;> omega

/-- **Master lemma** (VJ Lemma 5.5 for profiles): if every move of `g` is at least as good for
    `i` as the move of `f`, measured in the keys of `f`, then the keys of `g` dominate those of
    `f` pointwise. -/
theorem K_le_of_dom (hdom : ∀ u, K G f i (f u) ≤ K G f i (g u)) (v : V) :
    K G f i v ≤ K G g i v := by
  let p : ℕ → V := fun n => g^[n] v
  have hstep : ∀ n, K G f i (f (p n)) ≤ K G f i (p (n + 1)) := fun n => by
    simp only [p, iterate_succ_apply']; exact hdom _
  let r : ℕ → ℤ := fun n => rI G i (cycMax f (p n))
  have hr_mono : Monotone r := monotone_nat_of_le_succ fun n => by
    have := rI_le_of_K_le (hstep n)
    simp only [r]
    rwa [cycMax_apply] at this
  have hr_fin : (Set.range r).Finite :=
    (Set.finite_range fun y : V => rI G i (cycMax f y)).subset (by
      rintro _ ⟨n, rfl⟩; exact ⟨p n, rfl⟩)
  obtain ⟨N, hN⟩ := eventually_const_of_monotone hr_mono hr_fin
  set L := cycMax f (p N) with hL
  have hLam : ∀ n ≥ N, cycMax f (p n) = L := fun n hn => rI_injective (hN n hn)
  set M := cycMax g v with hM
  have hle : ∀ n ≥ Fintype.card V, p n ≤ M := by
    intro n hn
    obtain ⟨q, hq, -, hc⟩ := exists_period (f := g) v
    have := recurs_of_periodic hq hc rfl (n - Fintype.card V)
    rw [← iterate_add_apply, show n - Fintype.card V + Fintype.card V = n by omega] at this
    exact le_cycMax this
  have hfreq : ∀ n, ∃ m ≥ n, p m = M := fun n => recurs_cycMax (f := g) v n
  set N3 := max N (Fintype.card V)
  have htail : ∀ n ≥ N3, cycMax f (p n) = L ∧ p n ≤ M := fun n hn =>
    ⟨hLam n (le_of_max_le_left hn), hle n (le_of_max_le_right hn)⟩
  have hA : rI G i L ≤ rI G i M := by
    rcases lt_trichotomy M L with h | h | h
    · have hbad : ¬ Good i (G.prio L) := fun hg =>
        tail_lt_false hstep hg fun n hn => ⟨(htail n hn).1, lt_of_le_of_lt (htail n hn).2 h⟩
      exact le_of_lt (rI_lt_of_bad hbad h)
    · rw [h]
    · have hgood : Good i (G.prio M) := by
        by_contra hbad
        exact tail_upper_false hstep h hbad htail hfreq
      exact le_of_lt (rI_lt_of_good hgood h)
  have h0 : r 0 = rI G i (cycMax f v) := rfl
  by_cases hlt : rI G i (cycMax f v) < rI G i (cycMax g v)
  · exact (K_le_iff' v v).2 (Or.inl hlt)
  · have hall : ∀ m, cycMax f (g^[m] v) = M := by
      intro m
      have hm : r m ≤ rI G i M := by
        rcases le_total m N with hmN | hmN
        · exact (hr_mono hmN).trans (le_of_eq_of_le rfl hA)
        · rw [hN m hmN]; exact hA
      have h0m : r 0 ≤ r m := hr_mono (Nat.zero_le m)
      have hrm : r m = rI G i (cycMax f (g^[m] v)) := rfl
      exact rI_injective (le_antisymm (hrm ▸ hm) (by rw [← hM] at hlt; omega))
    exact K_le_path (fun u => hdom u) M _ v rfl rfl hall

/-! ### One-player optimality and the improvement lemma -/

variable (G) [DecidableRel G.edge]

theorem ownedBy_true_iff (v : V) : ownedBy G true v = true ↔ G.owner v = .one := by
  simp [ownedBy]

theorem ownedBy_false_iff (v : V) : ownedBy G false v = true ↔ G.owner v = .zero := by
  simp [ownedBy]

theorem owner_one_of_ne {v : V} (h : G.owner v ≠ .zero) : G.owner v = .one := by
  cases hv : G.owner v <;> simp_all

/-- (a) One-player optimality for Odd: a best response `q` of Odd (returned by `respond`) gives
    keys at most those of any profile with the same Even moves. -/
theorem respond_odd_optimal {bf : ℕ} {p q : V → V} (hq : respond G true bf p = some q)
    (g : V → V) (hg : ∀ v, G.edge v (g v)) (hgq : ∀ v, G.owner v = .zero → g v = q v) (v : V) :
    key G q v ≤ key G g v := by
  have hodd := (respond_spec G true bf p q hq).2.2
  have := K_le_of_dom (G := G) (f := q) (g := g) (i := .zero) (fun u => by
    by_cases hu : G.owner u = .zero
    · rw [hgq u hu]
    · have := hodd u ((ownedBy_true_iff G u).2 (owner_one_of_ne G hu)) (g u) (hg u)
      show key G q (q u) ≤ key G q (g u)
      simpa using this) v
  simpa [K, kfor] using this

/-- (a) One-player optimality for Even (dual). -/
theorem respond_even_optimal {bf : ℕ} {p q : V → V} (hq : respond G false bf p = some q)
    (g : V → V) (hg : ∀ v, G.edge v (g v)) (hgq : ∀ v, G.owner v = .one → g v = q v) (v : V) :
    key G g v ≤ key G q v := by
  have heven := (respond_spec G false bf p q hq).2.2
  have := K_le_of_dom (G := G) (f := q) (g := g) (i := .one) (fun u => by
    by_cases hu : G.owner u = .zero
    · have := heven u ((ownedBy_false_iff G u).2 hu) (g u) (hg u)
      simp only [K, kfor, negK_le_negK]
      simpa using this
    · rw [hgq u (owner_one_of_ne G hu)]) v
  simpa [K, kfor, negK_le_negK] using this

/-- (b) The improvement lemma (VJ Lemma 5.7). `f` is a profile in which Odd has no strictly
    improving move; `g` keeps or improves (in the keys of `f`) every Even move of `f` and plays
    arbitrary edges at Odd vertices. Then the keys of `g` dominate those of `f`, and at every Even
    vertex the key of the chosen successor does not decrease, and increases strictly where `g`
    switches. -/
theorem improvement (hodd : ∀ u, G.owner u = .one → ∀ w, G.edge u w → key G f (f u) ≤ key G f w)
    (hg : ∀ u, G.owner u = .one → G.edge u (g u))
    (hsw : ∀ u, G.owner u = .zero → g u = f u ∨ key G f (f u) < key G f (g u)) :
    (∀ v, key G f v ≤ key G g v) ∧
      ∀ u, G.owner u = .zero → key G f (f u) ≤ key G g (g u) ∧
        (g u ≠ f u → key G f (f u) < key G g (g u)) := by
  have hle : ∀ v, key G f v ≤ key G g v := fun v => by
    have := K_le_of_dom (G := G) (f := f) (g := g) (i := .zero) (fun u => by
      by_cases hu : G.owner u = .zero
      · rcases hsw u hu with h | h
        · rw [h]
        · exact le_of_lt h
      · have hu1 := owner_one_of_ne G hu
        exact hodd u hu1 _ (hg u hu1)) v
    simpa [K, kfor] using this
  refine ⟨hle, fun u hu => ?_⟩
  rcases hsw u hu with h | h
  · exact ⟨by rw [h]; exact hle _, fun hne => absurd h hne⟩
  · exact ⟨le_of_lt (lt_of_lt_of_le h (hle _)), fun _ => lt_of_lt_of_le h (hle _)⟩

theorem mem_improving {ks : V → Key} {p : V → V} {v w : V} (h : w ∈ improving G ks p v) :
    G.owner v = .zero ∧ ks (p v) < ks w := by
  unfold improving at h
  split_ifs at h with hv
  · simp at h
  · refine ⟨?_, by simpa using (List.mem_filter.1 h).2⟩
    by_contra h0
    exact hv ((ownedBy_true_iff G v).2 (owner_one_of_ne G h0))

end MercLib.HybridSI

end HybridSIImprovementProofs
