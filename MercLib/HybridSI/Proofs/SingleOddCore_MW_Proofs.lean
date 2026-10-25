module

public import MercLib.HybridSI.SingleOddCore
public import MercLib.HybridSI.Proofs.SingleOdd_Proofs
public import MercLib.HybridSI.Proofs.Termination_Proofs
public import MercLib.HybridSI.Proofs.SingleOddCore_Proofs
public import MercLib.HybridSI.Proofs.SingleOddPoly_KStar_Proofs

@[expose] public section HybridSISingleOddCoreMWProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Monotone worlds (`MonotoneWorlds` of `HybridSI.SingleOddCore`, MW of
`~/parity-polynomial/experiments/hb_k1proof/LROUNDS.md` §1). Let `qa`, `qb` be Even's best
responses (returned by `respond false`) in two worlds that differ only in Odd's move at `u`
(`a = qa u`, `b = qb u`), with keys `K_a`, `K_b` and world values `c_a = K_a(u)`, `c_b = K_b(u)`.
The fact (SI1) of the paper proof is the master lemma `K_le_of_dom` (`even_opt`).

* MW1 (`a = b`): both profiles are Even best responses against the same Odd strategy, so their
  keys dominate each other (`even_opt`).
* MW2 (`world_mono`: `c_a ≤ c_b ⇒ K_a ≤ K_b`), avoiding the lasso case analysis of the paper:
  - Case I, `K_b(a) ≤ K_b(b)`: `K_le_of_dom` for Odd from `qb` to `qa`.
  - Case II, `K_b(b) < K_b(a)`: `K_le_of_dom` for Even from `qb` to `qb[u ↦ a]`, a world-`a`
    profile, gives `K_b ≤ K_a`, hence `c_a = c_b`.
    - `K_a(a) ≤ K_a(b)`: `K_le_of_dom` for Even from `qa` to `g = qa[u ↦ b]` gives
      `K_a ≤ key g ≤ K_b`.
    - `K_a(b) < K_a(a)`: if `u` is not its own cycle maximum in either world,
      `c = u ⊕ K(succ)` (`key_le_step`) and `K_b(b) ≤ K_a(b) < K_a(a)` contradict `c_a = c_b`;
      the cycle maxima of `u` in the two worlds agree (`c_a = c_b`). If `u` is the cycle maximum
      in both worlds (case D), `K_b(b) ≤ K_a(b) < K_a(a)` forces the `qa`-play from `b` to reach
      `u` through vertices below `u`, so `u` is also the cycle maximum of `u` under `g`, and then
      `key g = K_a` (`key_eq_of_top`: the keys only depend on the plays up to `u`). -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### Plays and keys -/

section Plays

variable {G : Game V}

theorem mw_cycMax_iterate (f : V → V) : ∀ (k : ℕ) (v : V), cycMax f (f^[k] v) = cycMax f v
  | 0, _ => rfl
  | k + 1, v => by rw [iterate_succ_apply', cycMax_apply, mw_cycMax_iterate f k v]

/-- The key of `v` depends only on the play from `v`. -/
theorem key_congr_play {f g : V → V} {v : V} (h : ∀ j, f^[j] v = g^[j] v) :
    key G f v = key G g v := by
  have hc : cycMax f v = cycMax g v := by
    simp only [cycMax, playPrefix, iter_eq, ← iterate_add_apply]; simp only [h]
  have hs : stepsTo f v = stepsTo g v := by
    simp only [stepsTo, iter_eq, h, hc]
  have hb : bSet f v = bSet g v := by
    simp only [bSet, playPrefix, iter_eq, h, hc, hs]
  simp only [key, hc, hs, hb]

/-- Two profiles that agree off `u` have the same plays from `v` until `u` is reached. -/
theorem iterate_agree {f g : V → V} {u v : V} (hfg : ∀ x, x ≠ u → f x = g x) {i : ℕ}
    (hmin : ∀ j < i, f^[j] v ≠ u) : ∀ j ≤ i, g^[j] v = f^[j] v
  | 0, _ => rfl
  | j + 1, hj => by
    rw [iterate_succ_apply', iterate_succ_apply', iterate_agree hfg hmin j (by omega),
      hfg _ (hmin j (by omega))]

/-- One step along the play: if `x` is not its own cycle maximum under `f` nor under `g`, the
    keys of `x` compare like the keys of the successors. -/
theorem key_le_step {f g : V → V} {x : V} (hf : x ≠ cycMax f x) (hg : x ≠ cycMax g x) :
    key G f x ≤ key G g x ↔ key G f (f x) ≤ key G g (g x) := by
  have e1 := K_le_iff' (G := G) (f := f) (g := g) (i := .zero) x x
  have e2 := K_le_iff' (G := G) (f := f) (g := g) (i := .zero) (f x) (g x)
  simp only [K, kfor] at e1 e2
  rw [e1, e2, cycMax_apply, cycMax_apply, sum_bSet_apply hf, sum_bSet_apply hg, stepsTo_apply hf,
    stepsTo_apply hg]
  by_cases hr : rI G .zero (cycMax f x) = rI G .zero (cycMax g x)
  · have hc : cycMax f x = cycMax g x := rI_injective hr
    rw [hc]
    unfold eI
    split_ifs <;> push_cast <;> omega
  · constructor <;> intro h <;> omega

/-- If `f` and `g` agree off `u` and `u` is its own cycle maximum under both, then `f` and `g`
    have the same keys. -/
theorem key_eq_of_top {f g : V → V} {u : V} (hfg : ∀ x, x ≠ u → f x = g x)
    (hf : u = cycMax f u) (hg : u = cycMax g u) (v : V) : key G f v = key G g v := by
  classical
  by_cases hhit : ∃ i, f^[i] v = u
  · suffices H : ∀ i v, f^[i] v = u → (∀ j < i, f^[j] v ≠ u) → key G f v = key G g v from
      H (Nat.find hhit) v (Nat.find_spec hhit) fun j hj => Nat.find_min hhit hj
    intro i
    induction i with
    | zero =>
      intro v hv _
      simp only [iterate_zero, id_eq] at hv
      subst hv
      have e1 := bSet_eq_empty hf
      have e2 := bSet_eq_empty hg
      have e3 := stepsTo_eq_zero hf
      have e4 := stepsTo_eq_zero hg
      simp only [key, e1, e2, e3, e4, ← hf, ← hg]
    | succ i ih =>
      intro v hv hmin
      have hvu : v ≠ u := by simpa using hmin 0 (by omega)
      have hfv : f v = g v := hfg v hvu
      have ih' := ih (f v) (by rw [← iterate_succ_apply]; exact hv)
        fun j hj => by rw [← iterate_succ_apply]; exact hmin (j + 1) (by omega)
      have hcf : cycMax f v = u := by rw [← mw_cycMax_iterate f (i + 1) v, hv, ← hf]
      have hcg : cycMax g v = u := by
        rw [← mw_cycMax_iterate g (i + 1) v, iterate_agree hfg hmin (i + 1) le_rfl, hv, ← hg]
      have h1 : v ≠ cycMax f v := by rw [hcf]; exact hvu
      have h2 : v ≠ cycMax g v := by rw [hcg]; exact hvu
      have h3 : key G f (f v) = key G g (g v) := by rw [ih', hfv]
      exact le_antisymm ((key_le_step h1 h2).2 h3.le) ((key_le_step h2 h1).2 h3.ge)
  · push Not at hhit
    refine key_congr_play fun j => ?_
    induction j with
    | zero => rfl
    | succ j ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih, hfg _ (hhit j)]

/-- A sum of signed powers of two over a set vanishes only for the empty set. -/
theorem eq_empty_of_sum_eq_zero {δ : V → ℤ} (hδ : SignedPow δ) {D : Finset V}
    (h : ∑ y ∈ D, δ y = 0) : D = ∅ := by
  by_contra hne
  have hn : D.Nonempty := Finset.nonempty_iff_ne_empty.2 hne
  exact (top_dominates δ hδ D (D.max' hn) (D.max'_mem hn) fun y hy => D.le_max' y hy).2 h

end Plays

/-! ### Two worlds -/

section Worlds

variable (G : Game V) [DecidableRel G.edge]

theorem mw_owner_cases (v : V) : G.owner v = .zero ∨ G.owner v = .one := by
  cases G.owner v <;> simp

/-- (SI1) A profile without improving Even switch has keys at least those of every profile with
    the same Odd moves. -/
theorem even_opt {q g : V → V}
    (hloc : ∀ v, G.owner v = .zero → ∀ w, G.edge v w → key G q w ≤ key G q (q v))
    (hg : ∀ v, G.edge v (g v)) (hgq : ∀ v, G.owner v = .one → g v = q v) (v : V) :
    key G g v ≤ key G q v := by
  have := K_le_of_dom (G := G) (f := q) (g := g) (i := .one) (fun x => by
    rcases mw_owner_cases G x with hx | hx
    · simp only [K, kfor, negK_le_negK]; exact hloc x hx _ (hg x)
    · rw [hgq x hx]) v
  simpa [K, kfor, negK_le_negK] using this

/-- MW2 for two worlds: Even best responses `qa`, `qb` against Odd strategies that differ only
    at `u`; if the key of `u` under `qa` is at most that under `qb`, so are all keys. -/
theorem world_mono {qa qb : V → V} {u : V} (hu : G.owner u = .one)
    (ea : ∀ v, G.edge v (qa v)) (eb : ∀ v, G.edge v (qb v))
    (la : ∀ v, G.owner v = .zero → ∀ w, G.edge v w → key G qa w ≤ key G qa (qa v))
    (lb : ∀ v, G.owner v = .zero → ∀ w, G.edge v w → key G qb w ≤ key G qb (qb v))
    (hodd : ∀ v, G.owner v = .one → v ≠ u → qa v = qb v)
    (hc : key G qa u ≤ key G qb u) (v : V) : key G qa v ≤ key G qb v := by
  by_cases h1 : key G qb (qa u) ≤ key G qb (qb u)
  · -- Case I: `qb` has no improving switch even with `u` made an Even vertex.
    have := K_le_of_dom (G := G) (f := qb) (g := qa) (i := .one) (fun x => by
      simp only [K, kfor, negK_le_negK]
      rcases mw_owner_cases G x with hx | hx
      · exact lb x hx _ (ea x)
      · by_cases hxu : x = u
        · subst hxu; exact h1
        · rw [hodd x hx hxu]) v
    simpa [K, kfor, negK_le_negK] using this
  push Not at h1
  -- Case II: `K_b ≤ K_a`.
  have hτ1 : ∀ x, key G qb x ≤ key G (update qb u (qa u)) x := fun x => by
    have := K_le_of_dom (G := G) (f := qb) (g := update qb u (qa u)) (i := .zero) (fun y => by
      by_cases hyu : y = u
      · subst hyu; simpa [K, kfor] using h1.le
      · simp [hyu]) x
    simpa [K, kfor] using this
  have hτ2 : ∀ x, key G (update qb u (qa u)) x ≤ key G qa x :=
    even_opt G la (fun y => by
        by_cases hyu : y = u
        · subst hyu; simpa using ea y
        · simpa [hyu] using eb y)
      (fun y hy => by
        by_cases hyu : y = u
        · subst hyu; simp
        · simp [hyu, hodd y hy hyu])
  have hba : ∀ x, key G qb x ≤ key G qa x := fun x => (hτ1 x).trans (hτ2 x)
  have hceq : key G qa u = key G qb u := le_antisymm hc (hba u)
  -- the world-`b` profile `g = qa[u ↦ b]`
  have hgb : ∀ x, key G (update qa u (qb u)) x ≤ key G qb x :=
    even_opt G lb (fun y => by
        by_cases hyu : y = u
        · subst hyu; simpa using eb y
        · simpa [hyu] using ea y)
      (fun y hy => by
        by_cases hyu : y = u
        · subst hyu; simp
        · simp [hyu, hodd y hy hyu])
  by_cases h2 : key G qa (qa u) ≤ key G qa (qb u)
  · have := K_le_of_dom (G := G) (f := qa) (g := update qa u (qb u)) (i := .zero) (fun y => by
      by_cases hyu : y = u
      · subst hyu; simpa [K, kfor] using h2
      · simp [hyu]) v
    exact (by simpa [K, kfor] using this : key G qa v ≤ _).trans (hgb v)
  push Not at h2
  have hcm : cycMax qa u = cycMax qb u :=
    rI_injective (G := G) (i := .zero)
      (le_antisymm (rI_le_of_key_le G hceq.le) (rI_le_of_key_le G hceq.ge))
  by_cases hA : u = cycMax qa u
  · -- Case D: `u` is its own cycle maximum in both worlds.
    have hB : u = cycMax qb u := hA.trans hcm
    have cA : cycMax qa (qa u) = u := by rw [cycMax_apply, ← hA]
    have cB : cycMax qb (qb u) = u := by rw [cycMax_apply, ← hB]
    have bA : bSet qa (qa u) = ∅ := by
      have := bSet_apply_cycMax (f := qa) u; rwa [← hA] at this
    have bB : bSet qb (qb u) = ∅ := by
      have := bSet_apply_cycMax (f := qb) u; rwa [← hB] at this
    have k1 := hba (qb u)
    have k2 := h2.le
    have r1 := rI_le_of_key_le G k1
    have r2 := rI_le_of_key_le G k2
    rw [cB] at r1
    rw [cA] at r2
    have cAb : cycMax qa (qb u) = u := rI_injective (G := G) (i := .zero) (le_antisymm r2 r1)
    have s1 := sum_le_of_key_le G k1 (by rw [cB, cAb])
    have s2 := sum_le_of_key_le G k2 (by rw [cA, cAb])
    rw [bB, Finset.sum_empty] at s1
    rw [bA, Finset.sum_empty] at s2
    have bAb : bSet qa (qb u) = ∅ :=
      eq_empty_of_sum_eq_zero (wI_signed G .zero) (le_antisymm s2 s1)
    -- the `qa`-play from `b` reaches `u` through vertices below `u`
    obtain ⟨hm, hmin⟩ := stepsTo_spec (f := qa) (qb u)
    rw [cAb] at hm hmin
    set m := stepsTo qa (qb u)
    have hle : ∀ j < m, qa^[j] (qb u) ≤ u := fun j hj => by
      by_contra hlt
      push Not at hlt
      have : qa^[j] (qb u) ∈ bSet qa (qb u) := mem_bSet.2 ⟨⟨j, hj, rfl⟩, by rwa [cAb]⟩
      rw [bAb] at this
      simp at this
    set g := update qa u (qb u)
    have hfg : ∀ x, x ≠ u → qa x = g x := fun x hx => by simp [g, hx]
    have hag := iterate_agree hfg hmin
    have hgu : g u = qb u := by simp [g]
    have hper : IsPeriodicPt g (m + 1) u := by
      show g^[m + 1] u = u
      rw [iterate_succ_apply, hgu, hag m le_rfl, hm]
    have horb : ∀ j, g^[j] u ≤ u := fun j => by
      rw [← hper.iterate_mod_apply]
      have hj : j % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
      rcases hr : j % (m + 1) with _ | r
      · simp
      · rw [hr] at hj
        rw [iterate_succ_apply, hgu, hag r (by omega)]
        exact hle r (by omega)
    have hgtop : u = cycMax g u := by
      apply le_antisymm
      · simpa using le_cycMax (recurs_of_periodic (a := 0) (by omega) hper rfl 0)
      · obtain ⟨i, -, hi⟩ := recurs_cycMax (f := g) u 0
        rw [← hi]; exact horb i
    rw [key_eq_of_top hfg hA hgtop v]
    exact hgb v
  · exfalso
    have hB : u ≠ cycMax qb u := by rw [← hcm]; exact hA
    have := (key_le_step hA hB).1 hceq.le
    exact lt_irrefl _ (lt_of_le_of_lt (this.trans (hba _)) h2)

end Worlds

/-! ### Traces -/

section Trace

variable (G : Game V) [DecidableRel G.edge]

/-- Even's best response at state `k` of a trace, with its properties. -/
theorem trace_world {bf L : ℕ} (hbf : hbFuel V ≤ bf) {p ps : ℕ → V → V}
    (h : RunTrace G bf L p ps) {k : ℕ} (hk : k ≤ L) : ∃ q : V → V,
      kstarOf G bf ps k = key G q ∧ (∀ u, worldValue G bf ps u k = key G q u) ∧
      (∀ v, G.owner v = .one → q v = ps k v) ∧ (∀ v, G.edge v (q v)) ∧
      ∀ v, G.owner v = .zero → ∀ w, G.edge v w → key G q w ≤ key G q (q v) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (respond_isSome G false hbf (ps k))
  obtain ⟨hkeep, hedge, hloc⟩ := respond_spec G false bf (ps k) q hq
  refine ⟨q, funext fun v => by simp [kstarOf, hq], fun u => by simp [worldValue, hq],
    fun v hv => hkeep v (by simp [ownedBy, hv]), hedge (runTrace_ps_edge G h k hk),
    fun v hv w hw => by simpa using hloc v ((ownedBy_false_iff G v).2 hv) w hw⟩

/-- Monotone worlds for a trace on any vertex type, with enough fuel. -/
theorem monotoneWorlds_of_fuel {bf : ℕ} (hbf : hbFuel V ≤ bf) {u : V} (hu : G.owner u = .one)
    (hs : SingleOddChoice G u) {L : ℕ} {p ps : ℕ → V → V} (h : RunTrace G bf L p ps)
    {j k : ℕ} (hj : j ≤ L) (hk : k ≤ L) :
    (ps j u = ps k u → kstarOf G bf ps j = kstarOf G bf ps k) ∧
      (worldValue G bf ps u j ≤ worldValue G bf ps u k →
        ∀ v, kstarOf G bf ps j v ≤ kstarOf G bf ps k v) := by
  obtain ⟨qa, ka, wa, oa, ea, la⟩ := trace_world G hbf h hj
  obtain ⟨qb, kb, wb, ob, eb, lb⟩ := trace_world G hbf h hk
  have e := runTrace_ps_edge G h
  have hodd : ∀ v, G.owner v = .one → v ≠ u → qa v = qb v := fun v hv hvu => by
    rw [oa v hv, ob v hv]
    exact hs v hv hvu _ _ (e j hj v) (e k hk v)
  rw [ka, kb, wa, wb]
  refine ⟨fun hu' => ?_, fun hc v => world_mono G hu ea eb la lb hodd hc v⟩
  have hodd' : ∀ v, G.owner v = .one → qa v = qb v := fun v hv => by
    by_cases hvu : v = u
    · subst hvu; rw [oa v hv, ob v hv, hu']
    · exact hodd v hv hvu
  funext v
  exact le_antisymm (even_opt G lb ea hodd' v)
    (even_opt G la eb (fun v hv => (hodd' v hv).symm) v)

end Trace

/-- MW, monotone worlds (headline). -/
theorem monotoneWorlds : MonotoneWorlds := by
  intro n G _ _ u hu hs L p ps h j k hj hk
  exact monotoneWorlds_of_fuel G le_rfl hu hs h hj hk

theorem upPoly : UpPoly := fun h => kChangeReduction (upReduction monotoneWorlds h)

end MercLib.HybridSI

end HybridSISingleOddCoreMWProofs
