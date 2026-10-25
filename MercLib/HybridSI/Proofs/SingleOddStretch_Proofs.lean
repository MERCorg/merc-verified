module

public import MercLib.HybridSI.SingleOddStretch
public import MercLib.HybridSI.Proofs.SingleOdd_Proofs
public import MercLib.HybridSI.Proofs.Bounds_Epoch_Proofs
public import MercLib.HybridSI.Proofs.Epoch_Proofs

@[expose] public section HybridSISingleOddStretchProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Lemmas NT and SK of `ST_DEC.md` (`HybridSI.SingleOddStretch`).
* `key_lt_of_succ`: the local key identity. For a vertex that is not its cycle maximum, the key is
  that of its successor shifted by a constant depending only on the vertex and the cycle maximum
  (`bSet_apply`, `stepsTo_apply`), so keys compare like the successors' keys.
* `nonTopStrict` (NT): H-B switches `v` from `s` to `w` with `Ξ_k(s) < Ξ_k(w)` (`hbStep_next_spec`),
  `Ξ_k(w) ≤ Ξ_{k+1}(w)` (P2), and `s`, `w` have the cycle maximum of `v` at `k` and `k + 1`.
* `sameKeysTie` (SK): without an Odd change, `K*` is the same at `k` and `k + 1` (two best
  responses of Even to the same Odd moves have equal keys), and so are the keys `Ξ`; a filtered
  edge at `k + 1` (`filterNonempty`) is then filtered at `k` and beats H-B's choice at `k`, a
  `Ξ_k`-maximum of the filter (`argmaxKey_max`). The escape value is kept by K1 at `k` and `k + 1`. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-- The local key identity, in comparison form: if `v` is not the cycle maximum under `f` nor
    under `g`, with the same cycle maximum, keys of `v` compare like those of its successors. -/
theorem key_lt_of_succ {f g : V → V} {v : V} (hf : v ≠ cycMax f v) (hg : v ≠ cycMax g v)
    (hl : cycMax f v = cycMax g v) (h : key G f (f v) < key G g (g v)) :
    key G f v < key G g v := by
  unfold key at h ⊢
  rw [cycMax_apply, cycMax_apply] at h
  rw [stepsTo_apply hf, stepsTo_apply hg, bSet_apply hf, bSet_apply hg]
  rw [← hl] at h ⊢
  have hsum : ∀ (f : V → V), cycMax f v < v →
      ∑ y ∈ insert v (bSet f (f v)), weight G y = ∑ y ∈ bSet f (f v), weight G y + weight G v :=
    fun f hlt => by rw [Finset.sum_insert (not_mem_bSet_apply hlt), add_comm]
  simp only [] at h ⊢
  have hc : ∃ c : ℤ, (if cycMax f v < v then insert v (bSet f (f v)) else bSet f (f v)).sum
        (weight G) = (bSet f (f v)).sum (weight G) + c ∧
      (if cycMax f v < v then insert v (bSet g (g v)) else bSet g (g v)).sum (weight G) =
        (bSet g (g v)).sum (weight G) + c := by
    by_cases hlt : cycMax f v < v
    · simp only [hlt, ite_true]
      exact ⟨weight G v, hsum f hlt, hsum g (hl ▸ hlt)⟩
    · simp only [hlt, ite_false]
      exact ⟨0, by simp, by simp⟩
  obtain ⟨c, h1, h2⟩ := hc
  rw [h1, h2]
  generalize (bSet f (f v)).sum (weight G) = A at *
  generalize (bSet g (g v)).sum (weight G) = B at *
  generalize stepsTo f (f v) = a at *
  generalize stepsTo g (g v) = b at *
  split_ifs at h ⊢ <;> simp only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and,
    false_or] at h ⊢ <;> omega

/-- Lemma NT (headline): in an `l`-stable iteration a switched non-top Even vertex strictly
    raises its key. -/
theorem nonTopStrict (bf : ℕ) : NonTopStrict G bf := by
  intro L p ps h k hk hls v hv hsw htop
  have hmono := runTrace_step_le G h hk
  have hpe : ∀ j ≤ L, ps j v = p j v := fun j hj => respond_odd_keep G (h.2.1 j hj) hv
  obtain ⟨qt, hqt, hpk⟩ := h.2.2 k hk
  obtain ⟨ps', hps', hmove, -⟩ := hbStep_next_spec G hqt
  rw [h.2.1 k hk.le] at hps'
  cases hps'
  have hlt : key G (ps k) (p k v) < key G (ps k) (p (k + 1) v) := by
    rcases hmove v with h' | h'
    · exact absurd (by rw [hpk]; exact h') hsw
    · rw [hpk]; exact h'.2
  apply key_lt_of_succ G htop (hls v ▸ htop) (hls v)
  rw [hpe k hk.le, hpe (k + 1) hk]
  exact lt_of_lt_of_le hlt (hmono _)

theorem improving_of_filtered {ks kstar : V → Key} {p : V → V} {v w : V}
    (h : w ∈ filtered G ks kstar p v) : w ∈ improving G ks p v := (List.mem_filter.1 h).1

/-- One non-final iteration of a trace on a relabelled game: some edge is improving, and every
    vertex switches to the `Ξ`-best filtered edge, if any. -/
theorem trace_round (hrel : G.Relabelled) {bf L : ℕ} {p ps : ℕ → V → V}
    (h : RunTrace G bf L p ps) {k : ℕ} (hk : k < L) :
    (∃ v, improving G (key G (ps k)) (p k) v ≠ []) ∧
      ∃ pstar, respond G false bf (ps k) = some pstar ∧ ∀ v,
        p (k + 1) v = if (filtered G (key G (ps k)) (key G pstar) (p k) v).isEmpty then p k v
          else argmaxKey (key G (ps k)) (p k v)
            (filtered G (key G (ps k)) (key G pstar) (p k) v) := by
  obtain ⟨qt, hqt, hpk⟩ := h.2.2 k hk
  rw [hbStep_eq G hrel (runTrace_edge G h k hk.le) (h.2.1 k hk.le)] at hqt
  by_cases hall : ∀ v, improving G (key G (ps k)) (p k) v = []
  · rw [ite_eq_left hall] at hqt; cases hqt
  rw [ite_eq_right hall] at hqt
  push Not at hall
  rcases h2 : respond G false bf (ps k) with _ | pstar
  · rw [h2] at hqt; cases hqt
  rw [h2] at hqt
  dsimp only at hqt
  injection hqt with hqt
  refine ⟨hall, pstar, rfl, fun v => ?_⟩
  rw [hpk, ← hqt]; exact look_tabulate _ _ _

/-- Two best responses of Even to profiles with the same Odd moves have the same keys. -/
theorem kstar_eq {bf : ℕ} {q q' pstar pstar' : V → V} (hq : ∀ v, G.edge v (q v))
    (hq' : ∀ v, G.edge v (q' v)) (hodd : ∀ u, G.owner u = .one → q u = q' u)
    (h : respond G false bf q = some pstar) (h' : respond G false bf q' = some pstar') :
    key G pstar = key G pstar' := by
  have eA := (respond_spec G false bf _ _ h).2.1 hq
  have eB := (respond_spec G false bf _ _ h').2.1 hq'
  have hsame : ∀ u, G.owner u = .one → pstar' u = pstar u := fun u hu => by
    rw [respond_even_keep G h' hu, respond_even_keep G h hu, hodd u hu]
  funext v
  exact le_antisymm (respond_even_optimal G h' _ eA (fun u hu => (hsame u hu).symm) v)
    (respond_even_optimal G h _ eB hsame v)

/-- Lemma SK (headline): an iteration that changes no key, followed by a non-final one, is an
    escape tie of every Odd vertex, and switches the single Odd choice vertex. -/
theorem sameKeysTie (bf : ℕ) : SameKeysTie G bf := by
  intro hrel L p ps h k hk hkey u hu
  have e := runTrace_ps_edge G h
  have hesc : escape G ps u (k + 1) = escape G ps u k := by
    unfold escape
    have h1 := oddOptimal G bf L p ps h k (by omega) u hu _ (e (k + 1) (by omega) u)
    have h2 := oddOptimal G bf L p ps h (k + 1) (by omega) u hu _ (e k (by omega) u)
    rw [← hkey] at h2 ⊢
    exact le_antisymm h2 h1
  have hchg : k ∈ oddChangeRounds G L ps := by
    simp only [oddChangeRounds, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    by_contra hno
    push Not at hno
    obtain ⟨-, pstar, hA, hpA⟩ := trace_round G hrel h (k := k) (by omega)
    obtain ⟨himp, pstar1, hB, -⟩ := trace_round G hrel h (k := k + 1) hk
    have hK : key G pstar = key G pstar1 :=
      kstar_eq G (e k (by omega)) (e (k + 1) hk.le) hno hA hB
    have hFN := filterNonempty G bf (p (k + 1)) hrel (runTrace_edge G h (k + 1) hk.le) _ _
      (h.2.1 (k + 1) hk.le) hB
    simp only [look_keyTable] at hFN
    obtain ⟨v, hv⟩ := hFN himp
    obtain ⟨w', hw'⟩ := List.exists_mem_of_ne_nil _ hv
    rw [← hkey, ← hK] at hw'
    have hw'I := improving_of_filtered G hw'
    obtain ⟨hv0, hlt'⟩ := mem_improving G hw'I
    have hw'e : G.edge v w' := (mem_succList G).1 (improving_sub G _ _ v w' hw'I)
    have hmx := filtered_max G hw'
    have hp := hpA v
    rcases hF : filtered G (key G (ps k)) (key G pstar) (p k) v with _ | ⟨w2, ws2⟩
    · rw [hF] at hp
      simp only [List.isEmpty_nil, ite_true] at hp
      have hm : w' ∈ filtered G (key G (ps k)) (key G pstar) (p k) v :=
        mem_filtered G (mem_improving_of G hv0 hw'e (by rw [← hp]; exact hlt')) hmx
      rw [hF] at hm
      simp at hm
    · rw [hF] at hp
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at hp
      have hwF : p (k + 1) v ∈ filtered G (key G (ps k)) (key G pstar) (p k) v := by
        rw [hF, hp]; exact argmaxKey_mem _ _ w2 ws2
      have hlt0 := (mem_improving G (improving_of_filtered G hwF)).2
      have hm : w' ∈ filtered G (key G (ps k)) (key G pstar) (p k) v :=
        mem_filtered G (mem_improving_of G hv0 hw'e (hlt0.trans hlt')) hmx
      rw [hF] at hm
      have hle := argmaxKey_max (key G (ps k)) (p k v) w2 ws2 w' hm
      rw [← hp] at hle
      exact absurd hlt' (not_lt.2 hle)
  refine ⟨?_, fun hs => (oddChange_single G h hs hchg).2⟩
  simp only [escapeTieRounds, Finset.mem_filter]
  exact ⟨hchg, hesc⟩

end MercLib.HybridSI

end HybridSISingleOddStretchProofs
