module

public import MercLib.HybridSI.Epoch
public import MercLib.HybridSI.Proofs.Filter_Proofs

@[expose] public section HybridSIEpochProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorem
`epochBound` is to be stated in `Challenges/HybridSI.lean` (human-vetted).

The epoch-length bound (`experiments/hb_epoch/README.md`, theorem A5). Fix Odd's response `τ` of
the epoch and let `K*` be the keys of Even's best response `σ*` to `τ` (the same for every
iteration of the epoch: two best responses to the same `τ` have equal keys). `D σ` is the set of
Even vertices whose move under `σ` is `K*`-maximal (`Mx`). In each iteration (`epoch_round`):
* `D` does not shrink: every switch goes to a filtered edge, which is `K*`-maximal;
* `D` grows: some vertex outside `D` has the improving edge `(v, σ* v)` (else the profile `g`
  playing `σ` on `D` and `σ*` elsewhere has keys `K*` (Lemma M) and at most `Ξ` (Lemma NI, by the
  master lemma), so `Ξ = K*` and an improving edge contradicts maximality), and that edge is
  filtered, so `v` switches into `D`;
* `D` is not all of `V_E` (else `Ξ = K*` by Lemma M, and no edge is improving). -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-- `w` is a best successor of `v` for the keys `κ`. -/
def Mx (κ : V → Key) (v w : V) : Prop := ∀ x, G.edge v x → κ x ≤ κ w

theorem filtered_max {ks kstar : V → Key} {p : V → V} {v w : V}
    (h : w ∈ filtered G ks kstar p v) : Mx G kstar v w := by
  intro x hx
  unfold filtered at h
  obtain ⟨-, hw⟩ := List.mem_filter.1 h
  simp only [beq_iff_eq] at hw
  rw [hw]
  exact le_foldl_max_of_mem _ _ (Or.inr (List.mem_map_of_mem ((mem_succList G).2 hx)))

theorem mem_filtered {ks kstar : V → Key} {p : V → V} {v w : V}
    (hi : w ∈ improving G ks p v) (hm : Mx G kstar v w) : w ∈ filtered G ks kstar p v := by
  have hmem := improving_sub G ks p v w hi
  unfold filtered
  refine List.mem_filter.2 ⟨hi, ?_⟩
  simp only [beq_iff_eq]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have hvals : ∀ y ∈ (succList G v).map kstar, y ≤ kstar w := by
    intro y hy
    obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hy
    exact hm x' ((mem_succList G).1 hx')
  refine le_antisymm (le_foldl_max_of_mem _ _ (Or.inr (List.mem_map_of_mem hmem)))
    (foldl_max_le _ _ ?_ hvals)
  rw [hx]
  exact hm x ((mem_succList G).1 (by rw [hx]; exact List.mem_cons_self))

theorem hbStep_next_pstar {bf : ℕ} {p ps : V → V} {qt : List (V × V)}
    (hps : respond G true bf p = some ps) (h : hbStep G bf p = .next qt) :
    ∃ pstar, respond G false bf ps = some pstar := by
  unfold hbStep at h
  rw [hps] at h
  dsimp only at h
  split_ifs at h
  rcases h2 : respond G false bf ps with _ | pstar
  · rw [h2] at h; cases h
  · exact ⟨pstar, rfl⟩

/-- A non-final iteration: some edge is improving, and once some filtered edge exists, every
    vertex keeps its move (and has no filtered edge) or switches to a filtered edge. -/
theorem hbStep_next_filtered {bf : ℕ} {p ps pstar : V → V} {qt : List (V × V)}
    (hps : respond G true bf p = some ps) (hpstar : respond G false bf ps = some pstar)
    (h : hbStep G bf p = .next qt) :
    (∃ v, improving G (key G ps) p v ≠ []) ∧
    ((∃ v, filtered G (key G ps) (key G pstar) p v ≠ []) → ∀ v,
      (look qt v v = p v ∧ filtered G (key G ps) (key G pstar) p v = []) ∨
        look qt v v ∈ filtered G (key G ps) (key G pstar) p v) := by
  unfold hbStep at h
  rw [hps] at h
  have hks : (fun v => look (keyTable G ps) keyDefault v) = key G ps :=
    funext (look_keyTable G ps)
  have hkst : (fun v => look (keyTable G pstar) keyDefault v) = key G pstar :=
    funext (look_keyTable G pstar)
  dsimp only at h
  simp only [hks] at h
  split_ifs at h with hall
  rw [hpstar] at h
  dsimp only at h
  simp only [hkst] at h
  injection h with h
  subst h
  refine ⟨?_, fun hF v => ?_⟩
  · simp only [List.all_eq_true, List.isEmpty_iff, not_forall] at hall
    obtain ⟨v, -, hv⟩ := hall
    exact ⟨v, hv⟩
  · have huse : ((univList V).any fun v =>
        !(filtered G (key G ps) (key G pstar) p v).isEmpty) = true := by
      obtain ⟨u, hu⟩ := hF
      simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.isEmpty_eq_false_iff]
      exact ⟨u, mem_univList u, hu⟩
    rw [look_tabulate]
    simp only [huse, ite_true]
    by_cases hv : filtered G (key G ps) (key G pstar) p v = []
    · left; simp [hv]
    · right
      obtain ⟨w, ws, hw⟩ := List.exists_cons_of_ne_nil hv
      rw [hw]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
      exact argmaxKey_mem _ _ w ws

/-- One iteration of an epoch, measured with the keys `K*` of Even's best response `pstar`. -/
theorem epoch_round {bf : ℕ} {p ps pstar : V → V} {qt : List (V × V)}
    (he : ∀ v, G.edge v (p v)) (hps : respond G true bf p = some ps)
    (hpstar : respond G false bf ps = some pstar) (h : hbStep G bf p = .next qt) :
    (∀ v, Mx G (key G pstar) v (p v) → Mx G (key G pstar) v (look qt v v)) ∧
    (∃ v, G.owner v = .zero ∧ ¬ Mx G (key G pstar) v (p v) ∧
      Mx G (key G pstar) v (look qt v v)) ∧
    (∃ v, G.owner v = .zero ∧ ¬ Mx G (key G pstar) v (p v)) := by
  classical
  obtain ⟨⟨v0, hv0⟩, hsw⟩ := hbStep_next_filtered G hps hpstar h
  obtain ⟨hk, hedge, -⟩ := respond_spec G true bf p ps hps
  obtain ⟨hk2, hedge2, heven⟩ := respond_spec G false bf ps pstar hpstar
  have hpse := hedge he
  have hpste := hedge2 hpse
  have hEven : ∀ u, G.owner u = .zero → ownedBy G true u = false := fun u hu => by
    simp [ownedBy, hu]
  have hOdd : ∀ u, G.owner u = .one → ownedBy G false u = false := fun u hu => by
    simp [ownedBy, hu]
  have hmaxst : ∀ v, G.owner v = .zero → Mx G (key G pstar) v (pstar v) := fun v hv x hx => by
    simpa using heven v ((ownedBy_false_iff G v).2 hv) x hx
  have hZ : ∀ x, key G ps x ≤ key G pstar x :=
    respond_even_optimal G hpstar ps hpse fun x hx => (hk2 x (hOdd x hx)).symm
  -- Lemma M: a strategy with `K*`-maximal Even moves against `τ` has keys `K*`
  have hY : ∀ g : V → V, (∀ v, G.edge v (g v)) → (∀ v, G.owner v = .one → g v = ps v) →
      (∀ v, G.owner v = .zero → Mx G (key G pstar) v (g v)) → ∀ x, key G g x = key G pstar x := by
    intro g hg hgo hgm x
    refine le_antisymm (respond_even_optimal G hpstar g hg
      (fun v hv => by rw [hgo v hv, hk2 v (hOdd v hv)]) x) ?_
    have := K_le_of_dom (G := G) (f := pstar) (g := g) (i := .zero) (fun u => by
      by_cases hu : G.owner u = .zero
      · exact hgm u hu _ (hpste u)
      · have hu1 := owner_one_of_ne G hu
        show key G pstar (pstar u) ≤ key G pstar (g u)
        rw [hgo u hu1, hk2 u (hOdd u hu1)]) x
    simpa [K, kfor] using this
  obtain ⟨w0, hw0⟩ := List.exists_mem_of_ne_nil _ hv0
  obtain ⟨hv0e, hlt0⟩ := mem_improving G hw0
  have hw0e : G.edge v0 w0 := (mem_succList G).1 (improving_sub G _ p v0 w0 hw0)
  -- `D` is not all of `V_E`
  have h3 : ∃ v, G.owner v = .zero ∧ ¬ Mx G (key G pstar) v (p v) := by
    by_contra hc
    push Not at hc
    have hK := hY ps hpse (fun _ _ => rfl) (fun v hv => by rw [hk v (hEven v hv)]; exact hc v hv)
    have hm := hc v0 hv0e w0 hw0e
    rw [← hK w0, ← hK (p v0)] at hm
    exact absurd hlt0 (not_lt.2 hm)
  -- some vertex outside `D` has the improving edge `(v, σ* v)`
  obtain ⟨v, hvE, hvM, hvi⟩ : ∃ v, G.owner v = .zero ∧ ¬ Mx G (key G pstar) v (p v) ∧
      key G ps (p v) < key G ps (pstar v) := by
    by_contra hc
    push Not at hc
    let g : V → V := fun v =>
      if G.owner v = .zero ∧ Mx G (key G pstar) v (p v) then p v else pstar v
    have hg : ∀ v, G.edge v (g v) := fun v => by
      simp only [g]; split_ifs
      · exact he v
      · exact hpste v
    have hgo : ∀ v, G.owner v = .one → g v = ps v := fun v hv => by
      have hn : ¬ (G.owner v = .zero ∧ Mx G (key G pstar) v (p v)) := fun h' => by
        rw [hv] at h'; cases h'.1
      simp only [g, ite_eq_right hn]; exact hk2 v (hOdd v hv)
    have hgm : ∀ v, G.owner v = .zero → Mx G (key G pstar) v (g v) := fun v hv => by
      simp only [g]; split_ifs with h'
      · exact h'.2
      · exact hmaxst v hv
    have hgK := hY g hg hgo hgm
    -- Lemma NI: no improving edge used, so the keys do not increase
    have hNI : ∀ x, key G g x ≤ key G ps x := fun x => by
      have := K_le_of_dom (G := G) (f := ps) (g := g) (i := .one) (fun u => by
        simp only [K, kfor, negK_le_negK]
        by_cases hu : G.owner u = .zero
        · rw [hk u (hEven u hu)]
          by_cases hm : Mx G (key G pstar) u (p u)
          · have : g u = p u := by simp only [g]; rw [ite_eq_left ⟨hu, hm⟩]
            rw [this]
          · have : g u = pstar u := by simp only [g]; rw [ite_eq_right fun h' => hm h'.2]
            rw [this]
            exact hc u hu hm
        · rw [hgo u (owner_one_of_ne G hu)]) x
      simpa [K, kfor, negK_le_negK] using this
    have hEq : ∀ x, key G ps x = key G pstar x := fun x =>
      le_antisymm (hZ x) (by rw [← hgK x]; exact hNI x)
    have hnm : ¬ Mx G (key G pstar) v0 (p v0) := fun hm => by
      have := hm w0 hw0e
      rw [← hEq, ← hEq] at this
      exact absurd hlt0 (not_lt.2 this)
    have h1 := hc v0 hv0e hnm
    have h2 := hmaxst v0 hv0e w0 hw0e
    rw [← hEq, ← hEq] at h2
    exact absurd (lt_of_lt_of_le hlt0 h2) (not_lt.2 h1)
  have hfil : pstar v ∈ filtered G (key G ps) (key G pstar) p v := by
    refine mem_filtered G ?_ (hmaxst v hvE)
    unfold improving
    rw [ite_eq_right (by simp [hEven v hvE])]
    exact List.mem_filter.2 ⟨(mem_succList G).2 (hpste v), by simpa using hvi⟩
  have hsw' := hsw ⟨v, List.ne_nil_of_mem hfil⟩
  refine ⟨fun u hu => ?_, ⟨v, hvE, hvM, ?_⟩, h3⟩
  · rcases hsw' u with ⟨he', -⟩ | hm
    · rw [he']; exact hu
    · exact filtered_max G hm
  · rcases hsw' v with ⟨-, hn⟩ | hm
    · exact absurd hn (List.ne_nil_of_mem hfil)
    · exact filtered_max G hm

/-- The epoch-length bound (headline). -/
theorem epochBound (G : Game V) [DecidableRel G.edge] (bf : ℕ) : EpochBound G bf := by
  classical
  intro L p ps he0 hrun hsame
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact Nat.zero_le _
  have hedge : ∀ k ≤ L, ∀ v, G.edge v (p k v) := by
    intro k
    induction k with
    | zero => intro _; exact he0
    | succ k ih =>
      intro hk
      obtain ⟨-, qt, hqt, hpk⟩ := hrun k (by omega)
      rw [hpk]
      exact hbStep_next G hqt (ih (by omega))
  have hex : ∀ k, ∃ pstar : V → V, k < L → respond G false bf (ps k) = some pstar := by
    intro k
    by_cases hk : k < L
    · obtain ⟨hps, qt, hqt, -⟩ := hrun k hk
      obtain ⟨pstar, h⟩ := hbStep_next_pstar G hps hqt
      exact ⟨pstar, fun _ => h⟩
    · exact ⟨id, fun h => absurd h hk⟩
  choose pstar hpstar using hex
  have hpste : ∀ k < L, ∀ v, G.edge v (pstar k v) := fun k hk =>
    (respond_spec G false bf _ _ (hpstar k hk)).2.1
      ((respond_spec G true bf _ _ (hrun k hk).1).2.1 (hedge k (by omega)))
  have hodd : ∀ k < L, ∀ v, G.owner v = .one → pstar k v = ps 0 v := fun k hk v hv => by
    rw [(respond_spec G false bf _ _ (hpstar k hk)).1 v (by simp [ownedBy, hv]), hsame k hk v hv]
  have hKeq : ∀ k < L, key G (pstar k) = key G (pstar 0) := fun k hk => funext fun x =>
    le_antisymm
      (respond_even_optimal G (hpstar 0 hL) (pstar k) (hpste k hk)
        (fun v hv => by rw [hodd k hk v hv, hodd 0 hL v hv]) x)
      (respond_even_optimal G (hpstar k hk) (pstar 0) (hpste 0 hL)
        (fun v hv => by rw [hodd k hk v hv, hodd 0 hL v hv]) x)
  set Kst := key G (pstar 0)
  let E : Finset V := Finset.univ.filter fun v => G.owner v = .zero
  let D : ℕ → Finset V := fun k =>
    Finset.univ.filter fun v => G.owner v = .zero ∧ Mx G Kst v (p k v)
  have hround : ∀ k < L, D k ⊂ D (k + 1) ∧ D k ⊂ E := by
    intro k hk
    obtain ⟨hps, qt, hqt, hpk⟩ := hrun k hk
    obtain ⟨h1, ⟨v, hvE, hvM, hvM'⟩, ⟨u, huE, huM⟩⟩ :=
      epoch_round G (hedge k (by omega)) hps (hpstar k hk) hqt
    rw [hKeq k hk] at h1 hvM hvM' huM
    have hpk' : ∀ x, p (k + 1) x = look qt x x := fun x => by rw [hpk]
    refine ⟨Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun he => ?_⟩,
      Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun he => ?_⟩⟩
    · simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.1, by rw [hpk']; exact h1 x hx.2⟩
    · have hv : v ∈ D (k + 1) := by
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hvE, by rw [hpk']; exact hvM'⟩
      rw [← he] at hv
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hvM hv.2
    · simp only [D, E, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.1
    · have hu : u ∈ E := by simp [E, huE]
      rw [← he] at hu
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact huM hu.2
  have hcard : ∀ k, k + 1 ≤ L → (D 0).card + k ≤ (D k).card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have := Finset.card_lt_card (hround k (by omega)).1
      have := ih (by omega)
      omega
  have h1 := hcard (L - 1) (by omega)
  have h2 := Finset.card_lt_card (hround (L - 1) (by omega)).2
  have : numEven G = E.card := rfl
  omega

end MercLib.HybridSI

end HybridSIEpochProofs
