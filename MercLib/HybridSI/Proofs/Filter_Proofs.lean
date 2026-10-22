module

public import MercLib.HybridSI.Proofs.Improvement_Proofs

@[expose] public section HybridSIFilterProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorem
`filterNonempty` is to be stated in `Challenges/HybridSI.lean` (human-vetted).

The filter of H-B is never empty while `σ` is not optimal (`hb_lower/README.md`, section 0).
Let `σ̄ = ps` be Odd's best response to `σ` and `σ* = pstar` Even's best response to `σ̄`. If
`σ*` used no improving edge of `σ`, the master lemma (from Odd's point of view) gives
`key σ* ≤ key σ̄`, and optimality of `σ*` gives `key σ̄ ≤ key σ*`; an improving edge `w` of `v`
would then satisfy `key σ̄ w ≤ key σ* (σ* v) ≤ key σ̄ (σ v) < key σ̄ w`. So `σ*` uses an improving
edge `(v, σ* v)`, which is maximal for the keys of `σ*`, hence filtered. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem foldl_max_le {x : Key} : ∀ (l : List Key) (c : Key), c ≤ x → (∀ y ∈ l, y ≤ x) →
    l.foldl max c ≤ x
  | [], _, hc, _ => hc
  | y :: l, c, hc, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le l _ (max_le hc (hl y List.mem_cons_self))
      fun z hz => hl z (List.mem_cons_of_mem _ hz)

theorem le_foldl_max_of_mem {x : Key} : ∀ (l : List Key) (c : Key), (x = c ∨ x ∈ l) →
    x ≤ l.foldl max c
  | [], _, h => by simp at h; simp [h]
  | y :: l, c, h => by
    simp only [List.foldl_cons]
    have hc : ∀ d : Key, d ≤ l.foldl max d := fun d =>
      (le_foldl_max_of_mem l d (Or.inl rfl))
    rcases h with rfl | h
    · exact (le_max_left _ _).trans (hc _)
    · rcases List.mem_cons.1 h with rfl | h
      · exact (le_max_right _ _).trans (hc _)
      · exact le_foldl_max_of_mem l _ (Or.inr h)

variable (G : Game V) [DecidableRel G.edge]

/-- The filter is never empty (headline). -/
theorem filterNonempty (G : Game V) [DecidableRel G.edge] (bf : ℕ) (p : V → V) :
    FilterNonempty G bf p := by
  intro _ he ps pstar hps hpstar
  have hks : (fun v => look (keyTable G ps) keyDefault v) = key G ps :=
    funext (look_keyTable G ps)
  have hkst : (fun v => look (keyTable G pstar) keyDefault v) = key G pstar :=
    funext (look_keyTable G pstar)
  simp only [hks, hkst]
  rintro ⟨v, hv⟩
  obtain ⟨hk, hedge, hodd⟩ := respond_spec G true bf p ps hps
  obtain ⟨hk2, hedge2, heven⟩ := respond_spec G false bf ps pstar hpstar
  have hpse := hedge he
  have hpste := hedge2 hpse
  have hEven : ∀ u, G.owner u = .zero → ownedBy G true u = false := fun u hu => by
    simp [ownedBy, hu]
  have hOdd : ∀ u, G.owner u = .one → ownedBy G false u = false := fun u hu => by
    simp [ownedBy, hu]
  -- `σ*` uses an improving edge
  obtain ⟨u, hu0, hu⟩ : ∃ u, G.owner u = .zero ∧ key G ps (p u) < key G ps (pstar u) := by
    by_contra hc
    push Not at hc
    have hA : ∀ x, key G pstar x ≤ key G ps x := fun x => by
      have := K_le_of_dom (G := G) (f := ps) (g := pstar) (i := .one) (fun u => by
        simp only [K, kfor, negK_le_negK]
        by_cases hu : G.owner u = .zero
        · rw [hk u (hEven u hu)]; exact hc u hu
        · rw [hk2 u (hOdd u (owner_one_of_ne G hu))]) x
      simpa [K, kfor, negK_le_negK] using this
    have hB : ∀ x, key G ps x ≤ key G pstar x :=
      respond_even_optimal G hpstar ps hpse fun x hx => (hk2 x (hOdd x hx)).symm
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hv
    obtain ⟨hv0, hlt⟩ := mem_improving G hw
    have hwe : G.edge v w := (mem_succList G).1 (improving_sub G _ p v w hw)
    have h1 : key G pstar w ≤ key G pstar (pstar v) := by
      simpa using heven v ((ownedBy_false_iff G v).2 hv0) w hwe
    have := (hB w).trans (h1.trans ((hA _).trans (hc v hv0)))
    exact absurd hlt (not_lt.2 this)
  refine ⟨u, ?_⟩
  have hue : G.edge u (pstar u) := hpste u
  have hmem : pstar u ∈ succList G u := (mem_succList G).2 hue
  have himp : pstar u ∈ improving G (key G ps) p u := by
    unfold improving
    rw [ite_eq_right (by simp [hEven u hu0])]
    exact List.mem_filter.2 ⟨hmem, by simpa using hu⟩
  have hmax : ∀ w ∈ succList G u, key G pstar w ≤ key G pstar (pstar u) := fun w hw => by
    simpa using heven u ((ownedBy_false_iff G u).2 hu0) w ((mem_succList G).1 hw)
  refine List.ne_nil_of_mem (a := pstar u) (List.mem_filter.2 ⟨himp, ?_⟩)
  simp only [beq_iff_eq]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have hvals : ∀ y ∈ (succList G u).map (key G pstar), y ≤ key G pstar (pstar u) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
    exact hmax w hw
  refine le_antisymm (le_foldl_max_of_mem _ _ (Or.inr (List.mem_map_of_mem hmem)))
    (foldl_max_le _ _ ?_ hvals)
  rw [hx]
  exact hmax x (by rw [hx]; exact List.mem_cons_self)

end MercLib.HybridSI

end HybridSIFilterProofs
