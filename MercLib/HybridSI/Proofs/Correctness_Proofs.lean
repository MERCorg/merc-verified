module

public import MercLib.HybridSI.Correctness
public import MercLib.HybridSI.Proofs.Win_Proofs

@[expose] public section HybridSICorrectnessProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems
are stated in `Challenges/HybridSI.lean` (human-vetted).

`HBCorrect`: when `hbRun` returns, the last best response `ps` of Odd and Even's strategy form a
profile in which neither player has a strictly improving move (`respond_spec`, `hbRun_spec`);
`winsFrom_of_saddle` then makes the winner of each key win with the profile, and exclusivity
(`not_winsFrom_both`) gives the converse. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### Tables -/

theorem lookup_map_self {α : Type*} (g : V → α) :
    ∀ (l : List V) (v : V), v ∈ l → (l.map fun x => (x, g x)).lookup v = some (g v)
  | [], _, h => absurd h (List.not_mem_nil)
  | x :: l, v, h => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases hv : v = x
    · subst hv; simp
    · have : (v == x) = false := by simpa using hv
      rw [this]
      exact lookup_map_self g l v ((List.mem_cons.1 h).resolve_left hv)

theorem mem_univList (v : V) : v ∈ univList V := by simp [univList]

theorem look_tabulate {α : Type*} (g : V → α) (d : α) (v : V) : look (tabulate g) d v = g v := by
  simp [look, tabulate, lookup_map_self g _ v (mem_univList v)]

variable (G : Game V) [DecidableRel G.edge]

theorem mem_succList {v w : V} : w ∈ succList G v ↔ G.edge v w := by
  simp [succList, mem_univList]

/-! ### Best responses -/

/-- `bestOf` for a maximising player: the result is at least the current move and every listed
    successor, and it is the current move or one of them. -/
theorem bestOf_max (κ : V → Key) : ∀ (ws : List V) (cur : V),
    (∀ w ∈ ws, κ w ≤ κ (bestOf (fun a b => decide (b < a)) κ cur ws)) ∧
      κ cur ≤ κ (bestOf (fun a b => decide (b < a)) κ cur ws) ∧
      (bestOf (fun a b => decide (b < a)) κ cur ws = cur ∨
        bestOf (fun a b => decide (b < a)) κ cur ws ∈ ws)
  | [], cur => by simp [bestOf]
  | x :: ws, cur => by
    have hdef : bestOf (fun a b => decide (b < a)) κ cur (x :: ws) =
        bestOf (fun a b => decide (b < a)) κ (if decide (κ cur < κ x) then x else cur) ws := rfl
    obtain ⟨h1, h2, h3⟩ := bestOf_max κ ws (if decide (κ cur < κ x) then x else cur)
    rw [hdef]
    by_cases hb : κ cur < κ x
    · simp only [hb, decide_true, ite_true] at h1 h2 h3 ⊢
      refine ⟨?_, le_of_lt (lt_of_lt_of_le hb h2), ?_⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact h2
        · exact h1 w hw
      · rcases h3 with h | h
        · rw [h]; exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false] at h1 h2 h3 ⊢
      refine ⟨?_, h2, ?_⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact (not_lt.1 hb).trans h2
        · exact h1 w hw
      · rcases h3 with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- `bestOf` for a minimising player. -/
theorem bestOf_min (κ : V → Key) : ∀ (ws : List V) (cur : V),
    (∀ w ∈ ws, κ (bestOf (fun a b => decide (a < b)) κ cur ws) ≤ κ w) ∧
      κ (bestOf (fun a b => decide (a < b)) κ cur ws) ≤ κ cur ∧
      (bestOf (fun a b => decide (a < b)) κ cur ws = cur ∨
        bestOf (fun a b => decide (a < b)) κ cur ws ∈ ws)
  | [], cur => by simp [bestOf]
  | x :: ws, cur => by
    have hdef : bestOf (fun a b => decide (a < b)) κ cur (x :: ws) =
        bestOf (fun a b => decide (a < b)) κ (if decide (κ x < κ cur) then x else cur) ws := rfl
    obtain ⟨h1, h2, h3⟩ := bestOf_min κ ws (if decide (κ x < κ cur) then x else cur)
    rw [hdef]
    by_cases hb : κ x < κ cur
    · simp only [hb, decide_true, ite_true] at h1 h2 h3 ⊢
      refine ⟨?_, le_of_lt (lt_of_le_of_lt h2 hb), ?_⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact h2
        · exact h1 w hw
      · rcases h3 with h | h
        · rw [h]; exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false] at h1 h2 h3 ⊢
      refine ⟨?_, h2, ?_⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact h2.trans (not_lt.1 hb)
        · exact h1 w hw
      · rcases h3 with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem look_keyTable (p : V → V) (v : V) : look (keyTable G p) keyDefault v = key G p v :=
  look_tabulate _ _ _

theorem respondRound_apply (pl : Bool) (p : V → V) (v : V) :
    look (respondRound G pl p) v v = if ownedBy G pl v then
      bestOf (fun a b => if pl then decide (a < b) else decide (b < a)) (key G p) (p v)
        (succList G v) else p v := by
  unfold respondRound
  rw [look_tabulate]
  have : (fun v => look (keyTable G p) keyDefault v) = key G p := funext (look_keyTable G p)
  simp only [this]

/-- What a returned best response satisfies: the other player's moves are unchanged, moves follow
    edges, and no owned vertex has a strictly better successor under the returned profile. -/
theorem respond_spec (pl : Bool) : ∀ (bf : ℕ) (p q : V → V), respond G pl bf p = some q →
    (∀ v, ownedBy G pl v = false → q v = p v) ∧
    ((∀ v, G.edge v (p v)) → ∀ v, G.edge v (q v)) ∧
    (∀ v, ownedBy G pl v = true → ∀ w, G.edge v w →
      if pl then key G q (q v) ≤ key G q w else key G q w ≤ key G q (q v))
  | 0, _, _, h => by simp [respond] at h
  | bf + 1, p, q, h => by
    have hround := respondRound_apply G pl p
    simp only [respond] at h
    split_ifs at h with hall
    · cases h
      refine ⟨fun _ _ => rfl, fun h => h, fun v hv w hw => ?_⟩
      have hv' := hall
      simp only [List.all_eq_true, beq_iff_eq] at hv'
      have heq := hv' v (mem_univList v)
      rw [hround, ite_eq_left hv] at heq
      have hws := (mem_succList G).2 hw
      cases pl
      · simp only [Bool.false_eq_true, ite_false] at heq ⊢
        have := (bestOf_max (key G p) (succList G v) (p v)).1 w hws
        rwa [heq] at this
      · simp only [ite_true] at heq ⊢
        have := (bestOf_min (key G p) (succList G v) (p v)).1 w hws
        rwa [heq] at this
    · obtain ⟨ih1, ih2, ih3⟩ := respond_spec pl bf _ q h
      have hedge : ∀ v, G.edge v (p v) → G.edge v (bestOf (fun a b => if pl then decide (a < b)
          else decide (b < a)) (key G p) (p v) (succList G v)) := by
        intro v hv
        cases pl
        · simp only [Bool.false_eq_true, ite_false]
          rcases (bestOf_max (key G p) (succList G v) (p v)).2.2 with h' | h'
          · rw [h']; exact hv
          · exact (mem_succList G).1 h'
        · simp only [ite_true]
          rcases (bestOf_min (key G p) (succList G v) (p v)).2.2 with h' | h'
          · rw [h']; exact hv
          · exact (mem_succList G).1 h'
      refine ⟨fun v hv => ?_, fun he v => ih2 (fun v => ?_) v, ih3⟩
      · rw [ih1 v hv, hround, ite_eq_right (by simp [hv])]
      · rw [hround]
        by_cases hv : ownedBy G pl v = true
        · rw [ite_eq_left hv]; exact hedge v (he v)
        · rw [ite_eq_right hv]; exact he v

/-! ### Exclusivity -/

/-- The two players cannot both win from the same vertex. -/
theorem not_winsFrom_both {σ τ : V → V} {v : V} (h0 : G.WinsFrom Set.univ .zero σ v)
    (h1 : G.WinsFrom Set.univ .one τ v) : False := by
  classical
  let g : V → V := fun u => if G.owner u = .zero then σ u else τ u
  let p : Cslib.ωSequence V := ⟨fun n => g^[n] v⟩
  have hp : ∀ n, p (n + 1) = g (p n) := fun n => iterate_succ_apply' g n v
  -- every position is reachable for both strategies, and the moves are legal
  have hreach : ∀ n, Relation.ReflTransGen (G.Step Set.univ .zero σ) v (p n) ∧
      Relation.ReflTransGen (G.Step Set.univ .one τ) v (p n) := by
    intro n
    induction n with
    | zero => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | succ n ih =>
      obtain ⟨r0, r1⟩ := ih
      obtain ⟨u0, -, -, he0, hs0⟩ := h0.1 _ r0
      obtain ⟨u1, -, -, he1, hs1⟩ := h1.1 _ r1
      have hedge : G.edge (p n) (g (p n)) := by
        by_cases ho : G.owner (p n) = .zero
        · simp only [g, ite_eq_left ho]; rw [← hs0 ho]; exact he0
        · have ho1 : G.owner (p n) = .one := by cases h : G.owner (p n) <;> simp_all
          simp only [g, ite_eq_right ho]; rw [← hs1 ho1]; exact he1
      rw [hp]
      refine ⟨r0.tail ⟨Set.mem_univ _, Set.mem_univ _, hedge, fun ho => by simp [g, ho]⟩,
        r1.tail ⟨Set.mem_univ _, Set.mem_univ _, hedge, fun ho => ?_⟩⟩
      have : G.owner (p n) ≠ .zero := by rw [ho]; simp
      simp [g, this]
  have hconf : ∀ n, G.Step Set.univ .zero σ (p n) (p (n + 1)) ∧
      G.Step Set.univ .one τ (p n) (p (n + 1)) := by
    intro n
    obtain ⟨r0, r1⟩ := hreach (n + 1)
    obtain ⟨u0, -, -, he0, hs0⟩ := h0.1 _ (hreach n).1
    obtain ⟨u1, -, -, he1, hs1⟩ := h1.1 _ (hreach n).2
    have hedge : G.edge (p n) (g (p n)) := by
      by_cases ho : G.owner (p n) = .zero
      · simp only [g, ite_eq_left ho]; rw [← hs0 ho]; exact he0
      · have ho1 : G.owner (p n) = .one := by cases h : G.owner (p n) <;> simp_all
        simp only [g, ite_eq_right ho]; rw [← hs1 ho1]; exact he1
    rw [hp]
    refine ⟨⟨Set.mem_univ _, Set.mem_univ _, hedge, fun ho => by simp [g, ho]⟩,
      ⟨Set.mem_univ _, Set.mem_univ _, hedge, fun ho => ?_⟩⟩
    have : G.owner (p n) ≠ .zero := by rw [ho]; simp
    simp [g, this]
  have w0 := h0.2 p rfl fun n => (hconf n).1
  have w1 := h1.2 p rfl fun n => (hconf n).2
  obtain ⟨j, -, hj⟩ := G.playHasUniqueWinner p
  have := (hj _ w0).trans (hj _ w1).symm
  cases this

/-! ### The run of H-B -/

theorem foldl_argmax_mem (ks : V → Key) : ∀ (ws : List V) (w : V),
    ws.foldl (fun b x => if decide (ks b < ks x) then x else b) w ∈ w :: ws
  | [], w => by simp
  | x :: ws, w => by
    simp only [List.foldl_cons]
    have := foldl_argmax_mem ks ws (if decide (ks w < ks x) then x else w)
    split_ifs at this ⊢
    · rcases List.mem_cons.1 this with h' | h'
      · rw [h']; simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')
    · rcases List.mem_cons.1 this with h' | h'
      · rw [h']; simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')

theorem argmaxKey_mem (ks : V → Key) (d : V) (w : V) (ws : List V) :
    argmaxKey ks d (w :: ws) ∈ w :: ws :=
  foldl_argmax_mem ks ws w

theorem improving_sub (ks : V → Key) (p : V → V) (v w : V) (h : w ∈ improving G ks p v) :
    w ∈ succList G v := by
  unfold improving at h
  split_ifs at h
  · simp at h
  · exact (List.mem_filter.1 h).1

theorem filtered_sub (ks kstar : V → Key) (p : V → V) (v w : V)
    (h : w ∈ filtered G ks kstar p v) : w ∈ succList G v :=
  improving_sub G ks p v w (List.mem_filter.1 h).1

theorem hbStep_done {bf : ℕ} {p : V → V} {kt : List (V × Key)} (h : hbStep G bf p = .done kt) :
    ∃ ps, respond G true bf p = some ps ∧ kt = keyTable G ps ∧
      ∀ v, improving G (key G ps) p v = [] := by
  unfold hbStep at h
  split at h
  · cases h
  · rename_i ps hps
    have hks : (fun v => look (keyTable G ps) keyDefault v) = key G ps :=
      funext (look_keyTable G ps)
    simp only [hks] at h
    split_ifs at h with hall
    · cases h
      refine ⟨ps, hps, rfl, fun v => ?_⟩
      simp only [List.all_eq_true, List.isEmpty_iff] at hall
      exact hall v (mem_univList v)
    · split at h <;> cases h

theorem edge_of_sub (p : V → V) (he : ∀ v, G.edge v (p v)) (ks : V → Key) (v : V) (l : List V)
    (hl : ∀ x ∈ l, x ∈ succList G v) :
    G.edge v (if l.isEmpty = true then p v else argmaxKey ks (p v) l) := by
  rcases l with _ | ⟨w, ws⟩
  · exact he v
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
    exact (mem_succList G).1 (hl _ (argmaxKey_mem ks (p v) w ws))

theorem hbStep_next {bf : ℕ} {p : V → V} {qt : List (V × V)} (h : hbStep G bf p = .next qt)
    (he : ∀ v, G.edge v (p v)) : ∀ v, G.edge v (look qt v v) := by
  unfold hbStep at h
  rcases h1 : respond G true bf p with _ | ps
  · rw [h1] at h; cases h
  · rw [h1] at h
    dsimp only at h
    split_ifs at h with hall
    rcases h2 : respond G false bf ps with _ | pstar
    · rw [h2] at h; cases h
    · rw [h2] at h
      dsimp only at h
      injection h with h
      subst h
      intro v
      rw [look_tabulate]
      refine edge_of_sub G p he _ v _ fun x hx => ?_
      split_ifs at hx
      · exact filtered_sub G _ _ p v x hx
      · exact improving_sub G _ p v x hx

theorem hbRun_spec {bf : ℕ} : ∀ (fuel it : ℕ) (p : V → V) (it' : ℕ) (kt : List (V × Key)),
    hbRun G bf fuel it p = some (it', kt) → (∀ v, G.edge v (p v)) →
    ∃ p' ps, (∀ v, G.edge v (p' v)) ∧ respond G true bf p' = some ps ∧ kt = keyTable G ps ∧
      ∀ v, improving G (key G ps) p' v = []
  | 0, _, _, _, _, h, _ => by simp [hbRun] at h
  | fuel + 1, it, p, it', kt, h, he => by
    unfold hbRun at h
    split at h
    · rename_i ks hstep
      cases h
      obtain ⟨ps, h1, h2, h3⟩ := hbStep_done G hstep
      exact ⟨p, ps, he, h1, h2, h3⟩
    · rename_i qt hstep
      exact hbRun_spec fuel (it + 1) _ it' kt h (hbStep_next G hstep he)
    · cases h

/-! ### Correctness -/

theorem rI_one (l : V) : rI G .one l = -rI G .zero l := by
  unfold rI
  by_cases h : G.prio l % 2 = 0
  · rw [ite_eq_right (by rw [good_one_iff]; simpa using h), ite_eq_left ((good_zero_iff _).2 h)]
  · rw [ite_eq_left ((good_one_iff _).2 h), ite_eq_right (by rw [good_zero_iff]; exact h)]; ring

theorem rI_zero_ne (l : V) : rI G .zero l ≠ 0 := by
  unfold rI; split_ifs <;> omega

theorem keyWinner_pos (f : V → V) (x : V) (i : Player) (h : keyWinner (key G f x) = i) :
    0 < rI G i (cycMax f x) := by
  have hr : (ofLex (key G f x)).1 = rI G .zero (cycMax f x) := by
    have := kfor_key G f .zero x
    simp only [kfor] at this
    rw [this]; rfl
  unfold keyWinner at h
  rw [hr] at h
  cases i
  · split_ifs at h with hp
    · exact hp
  · split_ifs at h with hp
    · rw [rI_one]
      have := rI_zero_ne G (cycMax f x)
      omega

theorem initProfile_edge (v : V) : G.edge v (initProfile G v) := by
  obtain ⟨w, hw⟩ := G.total v
  have hne : succList G v ≠ [] := List.ne_nil_of_mem ((mem_succList G).2 hw)
  unfold initProfile
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  rw [hx]
  exact (mem_succList G).1 (by rw [hx]; simp)

/-- Correctness of H-B (headline). -/
theorem hbCorrect (G : Game V) [DecidableRel G.edge] (bf fuel : ℕ) : HBCorrect G bf fuel := by
  intro hrel it kt h
  obtain ⟨p', ps, hedge', hps, rfl, himp⟩ := hbRun_spec G fuel 0 _ it kt h (initProfile_edge G)
  obtain ⟨hkeep, hedge, hodd⟩ := respond_spec G true bf p' ps hps
  have hedgeps := hedge hedge'
  have hlook : ∀ v, look (keyTable G ps) keyDefault v = key G ps v := look_keyTable G ps
  -- the saddle conditions
  have hEven : ∀ v, G.owner v = .zero → ∀ w, G.edge v w → key G ps w ≤ key G ps (ps v) := by
    intro v hv w hw
    have hown : ownedBy G true v = false := by simp [ownedBy, hv]
    have hi := himp v
    unfold improving at hi
    rw [ite_eq_right (by simp [hown])] at hi
    rw [hkeep v hown]
    have := List.filter_eq_nil_iff.1 hi w ((mem_succList G).2 hw)
    simpa using this
  have hOdd : ∀ v, G.owner v = .one → ∀ w, G.edge v w → key G ps (ps v) ≤ key G ps w := by
    intro v hv w hw
    have := hodd v (by simp [ownedBy, hv]) w hw
    simpa using this
  have hwin : ∀ v i, keyWinner (key G ps v) = i → G.WinsFrom Set.univ i ps v := by
    intro v i hi
    refine winsFrom_of_saddle hrel (fun v _ => hedgeps v) (fun u hu w hw => ?_) v
      (keyWinner_pos G ps v i hi)
    cases i
    · have hu1 : G.owner u = .one := by cases h : G.owner u <;> simp_all
      exact hOdd u hu1 w hw
    · have hu0 : G.owner u = .zero := by cases h : G.owner u <;> simp_all
      show negK (key G ps (ps u)) ≤ negK (key G ps w)
      rw [negK_le_negK]
      exact hEven u hu0 w hw
  intro v i
  rw [hlook]
  constructor
  · intro hi
    exact ⟨ps, hwin v i hi⟩
  · rintro ⟨σ, hσ⟩
    by_contra hne
    have hj := hwin v _ rfl
    cases i
    · have : keyWinner (key G ps v) = .one := by
        cases h : keyWinner (key G ps v) <;> simp_all
      rw [this] at hj
      exact not_winsFrom_both G hσ hj
    · have : keyWinner (key G ps v) = .zero := by
        cases h : keyWinner (key G ps v) <;> simp_all
      rw [this] at hj
      exact not_winsFrom_both G hj hσ

end MercLib.HybridSI

end HybridSICorrectnessProofs
