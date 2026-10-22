module

public import MercLib.HybridSI.Proofs.Improvement_Proofs
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section HybridSITerminationProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorem
`hbTerminates` is to be stated in `Challenges/HybridSI.lean` (human-vetted).

Termination of H-B (`HBTerminates`). Both loops strictly increase a potential in the pointwise
order on `V → Key`, so they never revisit a profile, and there are `|V|^|V|` profiles
(`chain_bound`):
* a round of `respond` for player `pl`: the potential is the key (from `pl`'s point of view) of the
  move of every vertex of `pl` (`respondRound_lt`, by the master lemma `K_le_of_dom`);
* an H-B iteration: the potential is the key, under Odd's best response, of Even's move at every
  Even vertex (`hbStep_lt`, by the improvement lemma). -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### Strictly increasing chains in a finite type -/

theorem chain_bound {α β : Type*} [Fintype α] [Preorder β] (s : ℕ → α) (Φ : α → β) (n : ℕ)
    (h : ∀ k, k + 1 ≤ n → Φ (s k) < Φ (s (k + 1))) : n + 1 ≤ Fintype.card α := by
  have hlt : ∀ a b, a < b → b ≤ n → Φ (s a) < Φ (s b) := by
    intro a b hab hbn
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
      · exact (ih h' (by omega)).trans (h b hbn)
      · rw [h']; exact h b hbn
  have hinj : Injective fun k : Fin (n + 1) => s k := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h' | h'
    · exact (hlt a b h' (by omega)).ne (by simp only at hab; rw [hab])
    · exact (hlt b a h' (by omega)).ne (by simp only at hab; rw [hab])
  simpa using Fintype.card_le_of_injective _ hinj

/-! ### `bestOf` only switches to strictly better moves -/

theorem bestOf_max_strict (κ : V → Key) : ∀ (ws : List V) (cur : V),
    bestOf (fun a b => decide (b < a)) κ cur ws = cur ∨
      κ cur < κ (bestOf (fun a b => decide (b < a)) κ cur ws)
  | [], cur => Or.inl rfl
  | x :: ws, cur => by
    have hdef : bestOf (fun a b => decide (b < a)) κ cur (x :: ws) =
        bestOf (fun a b => decide (b < a)) κ (if decide (κ cur < κ x) then x else cur) ws := rfl
    rw [hdef]
    by_cases hb : κ cur < κ x
    · simp only [hb, decide_true, ite_true]
      rcases bestOf_max_strict κ ws x with h | h
      · rw [h]; exact Or.inr hb
      · exact Or.inr (hb.trans h)
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false]
      exact bestOf_max_strict κ ws cur

theorem bestOf_min_strict (κ : V → Key) : ∀ (ws : List V) (cur : V),
    bestOf (fun a b => decide (a < b)) κ cur ws = cur ∨
      κ (bestOf (fun a b => decide (a < b)) κ cur ws) < κ cur
  | [], cur => Or.inl rfl
  | x :: ws, cur => by
    have hdef : bestOf (fun a b => decide (a < b)) κ cur (x :: ws) =
        bestOf (fun a b => decide (a < b)) κ (if decide (κ x < κ cur) then x else cur) ws := rfl
    rw [hdef]
    by_cases hb : κ x < κ cur
    · simp only [hb, decide_true, ite_true]
      rcases bestOf_min_strict κ ws x with h | h
      · rw [h]; exact Or.inr hb
      · exact Or.inr (h.trans hb)
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false]
      exact bestOf_min_strict κ ws cur

variable (G : Game V) [DecidableRel G.edge]

/-! ### Termination of `respond` -/

/-- The player whose point of view `respond pl` takes. -/
def plPlayer (pl : Bool) : Player := if pl then .one else .zero

/-- The potential of a profile for `respond pl`: the key of the move of each vertex of `pl`. -/
def respondPot (pl : Bool) (p : V → V) : V → Key :=
  fun u => if ownedBy G pl u then kfor (plPlayer pl) (key G p (p u)) else keyDefault

/-- One round of `respond` either changes nothing or strictly increases the potential. -/
theorem respondRound_lt (pl : Bool) (p : V → V)
    (hne : ¬ ((univList V).all fun v => look (respondRound G pl p) v v == p v) = true) :
    respondPot G pl p < respondPot G pl fun v => look (respondRound G pl p) v v := by
  set q : V → V := fun v => look (respondRound G pl p) v v with hq
  have hround := respondRound_apply G pl p
  -- every move of `q` is at least as good as that of `p`, strictly where it differs
  have hmove : ∀ u, q u = p u ∨
      (ownedBy G pl u = true ∧ K G p (plPlayer pl) (p u) < K G p (plPlayer pl) (q u)) := by
    intro u
    simp only [hq, hround]
    by_cases hu : ownedBy G pl u = true
    · rw [ite_eq_left hu]
      cases pl
      · simp only [Bool.false_eq_true, ite_false]
        rcases bestOf_max_strict (key G p) (succList G u) (p u) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hu, by simpa [K, kfor, plPlayer] using h⟩
      · simp only [ite_true]
        rcases bestOf_min_strict (key G p) (succList G u) (p u) with h | h
        · exact Or.inl h
        · refine Or.inr ⟨hu, ?_⟩
          simp only [K, kfor, plPlayer, ite_true]
          rw [lt_iff_le_not_ge, negK_le_negK, negK_le_negK]
          exact lt_iff_le_not_ge.1 h
    · rw [ite_eq_right hu]; exact Or.inl rfl
  have hdom : ∀ u, K G p (plPlayer pl) (p u) ≤ K G p (plPlayer pl) (q u) := fun u => by
    rcases hmove u with h | h
    · rw [h]
    · exact le_of_lt h.2
  have hK := K_le_of_dom (G := G) (f := p) (g := q) (i := plPlayer pl) hdom
  have hle : respondPot G pl p ≤ respondPot G pl q := fun u => by
    unfold respondPot
    split_ifs
    · exact (hdom u).trans (hK _)
    · exact le_rfl
  obtain ⟨v, hv⟩ : ∃ v, q v ≠ p v := by
    by_contra hall
    push Not at hall
    exact hne (by simp only [List.all_eq_true, beq_iff_eq]; exact fun x _ => hall x)
  rcases hmove v with h | ⟨hown, h⟩
  · exact absurd h hv
  · refine lt_of_le_of_ne hle fun heq => ?_
    have := congrFun heq v
    simp only [respondPot, ite_eq_left hown] at this
    exact absurd (lt_of_lt_of_le h (hK _)) (by simp only [K]; rw [this]; exact lt_irrefl _)

theorem respond_none_chain (pl : Bool) : ∀ (F : ℕ) (p : V → V), respond G pl F p = none →
    ∃ s : ℕ → V → V, s 0 = p ∧ ∀ k, k + 1 < F → respondPot G pl (s k) < respondPot G pl (s (k + 1))
  | 0, p, _ => ⟨fun _ => p, rfl, fun k hk => absurd hk (by omega)⟩
  | F + 1, p, h => by
    simp only [respond] at h
    split_ifs at h with hall
    obtain ⟨s', hs0, hs⟩ := respond_none_chain pl F _ h
    refine ⟨fun k => match k with | 0 => p | k + 1 => s' k, rfl, fun k hk => ?_⟩
    rcases k with _ | k
    · simp only
      rw [hs0]
      exact respondRound_lt G pl p hall
    · exact hs k (by omega)

/-- `respond` returns within `|V|^|V| + 1` rounds. -/
theorem respond_isSome (pl : Bool) {F : ℕ} (hF : hbFuel V ≤ F) (p : V → V) :
    (respond G pl F p).isSome := by
  by_contra hn
  obtain ⟨s, -, hs⟩ := respond_none_chain G pl F p (Option.not_isSome_iff_eq_none.1 hn)
  have := chain_bound s (respondPot G pl) (F - 1) fun k hk => hs k (by unfold hbFuel at hF; omega)
  rw [Fintype.card_fun] at this
  unfold hbFuel at hF
  omega

/-! ### Termination of H-B -/

/-- What a non-final H-B iteration does: every Even move is kept or switched to a strictly
    better successor (in the keys of Odd's best response), and some move is switched. -/
theorem hbStep_next_spec {bf : ℕ} {p : V → V} {qt : List (V × V)}
    (h : hbStep G bf p = .next qt) : ∃ ps, respond G true bf p = some ps ∧
      (∀ v, look qt v v = p v ∨ (G.owner v = .zero ∧ key G ps (p v) < key G ps (look qt v v))) ∧
      ∃ v, G.owner v = .zero ∧ key G ps (p v) < key G ps (look qt v v) := by
  unfold hbStep at h
  rcases h1 : respond G true bf p with _ | ps
  · rw [h1] at h; cases h
  · rw [h1] at h
    have hks : (fun v => look (keyTable G ps) keyDefault v) = key G ps :=
      funext (look_keyTable G ps)
    simp only [hks] at h
    split_ifs at h with hall
    rcases h2 : respond G false bf ps with _ | pstar
    · rw [h2] at h; cases h
    · rw [h2] at h
      dsimp only at h
      injection h with h
      subst h
      refine ⟨ps, rfl, ?_⟩
      generalize hsrc : (if ((univList V).any fun v =>
          !(filtered G (key G ps) (fun v => look (keyTable G pstar) keyDefault v) p v).isEmpty)
          = true then filtered G (key G ps) (fun v => look (keyTable G pstar) keyDefault v) p
          else improving G (key G ps) p) = src
      have hsub : ∀ v w, w ∈ src v → w ∈ improving G (key G ps) p v := by
        intro v w hw
        rw [← hsrc] at hw
        split_ifs at hw
        · exact (List.mem_filter.1 hw).1
        · exact hw
      have hchoose : ∀ v, src v ≠ [] →
          (if (src v).isEmpty = true then p v else argmaxKey (key G ps) (p v) (src v)) ∈
            improving G (key G ps) p v := by
        intro v hv
        obtain ⟨w, ws, hw⟩ := List.exists_cons_of_ne_nil hv
        rw [hw]
        simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
        exact hsub v _ (by rw [hw]; exact argmaxKey_mem _ _ w ws)
      refine ⟨fun v => ?_, ?_⟩
      · rw [look_tabulate]
        by_cases hv : src v = []
        · left; simp [hv]
        · exact Or.inr (mem_improving G (hchoose v hv))
      · obtain ⟨v, hv⟩ : ∃ v, src v ≠ [] := by
          rw [← hsrc]
          split_ifs with hF
          · simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              List.isEmpty_eq_false_iff] at hF
            obtain ⟨v, -, hv⟩ := hF
            exact ⟨v, hv⟩
          · simp only [List.all_eq_true, List.isEmpty_iff, not_forall] at hall
            obtain ⟨v, -, hv⟩ := hall
            exact ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [look_tabulate]
        exact mem_improving G (hchoose v hv)

/-- The potential of a profile for H-B: the key, under Odd's best response, of Even's move. -/
def hbPot (bf : ℕ) (p : V → V) : V → Key :=
  match respond G true bf p with
  | some ps => fun u => if G.owner u = .zero then key G ps (p u) else keyDefault
  | none => fun _ => keyDefault

theorem hbStep_lt {bf : ℕ} (hbf : hbFuel V ≤ bf) {p : V → V} {qt : List (V × V)}
    (h : hbStep G bf p = .next qt) (he : ∀ v, G.edge v (p v)) :
    hbPot G bf p < hbPot G bf fun v => look qt v v := by
  obtain ⟨ps, hps, hmove, v, hv0, hv⟩ := hbStep_next_spec G h
  set q : V → V := fun v => look qt v v with hq
  obtain ⟨ps', hps'⟩ := Option.isSome_iff_exists.1 (respond_isSome G true hbf q)
  obtain ⟨hk, -, hodd⟩ := respond_spec G true bf p ps hps
  obtain ⟨hk', he', -⟩ := respond_spec G true bf q ps' hps'
  have hqe := hbStep_next G h he
  have heven : ∀ u, G.owner u = .zero → ownedBy G true u = false := fun u hu => by
    simp [ownedBy, hu]
  have himp := improvement G (f := ps) (g := ps')
    (fun u hu w hw => by simpa using hodd u ((ownedBy_true_iff G u).2 hu) w hw)
    (fun u _ => he' hqe u)
    (fun u hu => by
      rw [hk' u (heven u hu), hk u (heven u hu)]
      rcases hmove u with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.2)
  have hpot : hbPot G bf p = fun u => if G.owner u = .zero then key G ps (ps u) else keyDefault := by
    funext u; simp only [hbPot, hps]; split_ifs with hu
    · rw [hk u (heven u hu)]
    · rfl
  have hpot' : hbPot G bf q =
      fun u => if G.owner u = .zero then key G ps' (ps' u) else keyDefault := by
    funext u; simp only [hbPot, hps']; split_ifs with hu
    · rw [hk' u (heven u hu)]
    · rfl
  rw [hpot, hpot']
  refine lt_of_le_of_ne (fun u => ?_) fun heq => ?_
  · split_ifs with hu
    · exact (himp.2 u hu).1
    · exact le_rfl
  · have := congrFun heq v
    simp only [ite_eq_left hv0] at this
    have hne : ps' v ≠ ps v := by
      rw [hk' v (heven v hv0), hk v (heven v hv0)]
      exact fun he => (ne_of_lt hv) (by rw [show look qt v v = p v from he])
    exact absurd ((himp.2 v hv0).2 hne) (by rw [this]; exact lt_irrefl _)

theorem hbStep_ne_stuck {bf : ℕ} (hbf : hbFuel V ≤ bf) (p : V → V) : hbStep G bf p ≠ .stuck := by
  obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.1 (respond_isSome G true hbf p)
  obtain ⟨pstar, hpstar⟩ := Option.isSome_iff_exists.1 (respond_isSome G false hbf ps)
  unfold hbStep
  rw [hps]
  dsimp only
  split_ifs
  · simp
  · rw [hpstar]; simp

theorem hbRun_none_chain {bf : ℕ} (hbf : hbFuel V ≤ bf) : ∀ (F it : ℕ) (p : V → V),
    hbRun G bf F it p = none → (∀ v, G.edge v (p v)) →
    ∃ s : ℕ → V → V, s 0 = p ∧ ∀ k, k + 1 < F → hbPot G bf (s k) < hbPot G bf (s (k + 1))
  | 0, _, p, _, _ => ⟨fun _ => p, rfl, fun k hk => absurd hk (by omega)⟩
  | F + 1, it, p, h, he => by
    unfold hbRun at h
    split at h
    · cases h
    · rename_i qt hstep
      obtain ⟨s', hs0, hs⟩ := hbRun_none_chain hbf F (it + 1) _ h (hbStep_next G hstep he)
      refine ⟨fun k => match k with | 0 => p | k + 1 => s' k, rfl, fun k hk => ?_⟩
      rcases k with _ | k
      · simp only
        rw [hs0]
        exact hbStep_lt G hbf hstep he
      · exact hs k (by omega)
    · rename_i hstep
      exact absurd hstep (hbStep_ne_stuck G hbf p)

/-- Termination of H-B (headline). -/
theorem hbTerminates (G : Game V) [DecidableRel G.edge] (bf fuel : ℕ) :
    HBTerminates G bf fuel := by
  intro _ hbf hfuel
  by_contra hn
  obtain ⟨s, -, hs⟩ := hbRun_none_chain G hbf fuel 0 _ (Option.not_isSome_iff_eq_none.1 hn)
    (initProfile_edge G)
  have := chain_bound s (hbPot G bf) (fuel - 1) fun k hk =>
    hs k (by unfold hbFuel at hfuel; omega)
  rw [Fintype.card_fun] at this
  unfold hbFuel at hfuel
  omega

end MercLib.HybridSI

end HybridSITerminationProofs
