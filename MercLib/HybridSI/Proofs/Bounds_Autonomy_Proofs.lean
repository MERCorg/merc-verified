module

public import MercLib.HybridSI.Proofs.Bounds_Subgame_Proofs

@[expose] public section HybridSIBoundsAutonomyProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The autonomy lemma (`HybridSI.Bounds`, `Autonomy`) and O1 (`ClosedIterations`).
* The vertex list of the subgame is the restricted vertex list (`univList_val`), so successor
  lists (`succList_val`) and all tie-breaking agree; with `key_lt_val` the first best successor
  (`bestOf_val`, `argmaxKey_val`), one switch-all round (`respondRound_val`), a best response
  (`respond_val`: the subgame's part stabilises no later than the whole profile), the improving
  and filtered edges (`improving_val`, `filtered_val`) and one H-B iteration (`hbStep_val`)
  commute with the restriction.
* `autonomy`: induction along the trace, stopping at the first final iteration of the subgame.
* `closedIterations`: after the subgame is final, the restriction to `D` is frozen and the
  profiles are pairwise distinct (the strict potential `hbPot` of `Termination_Proofs`), so they
  differ outside `D`. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge] {D : Finset V} (hD : Closed G D)

local notation "GD" => subgame G D hD

/-! ### Lists -/

theorem univList_val : (univList D).map Subtype.val = (univList V).filter (· ∈ D) := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) ?_ ?_ fun a => ?_
  · exact List.Pairwise.map _ (fun _ _ h => h) (Finset.sortedLT_sort _).pairwise
  · exact List.Pairwise.filter _ (Finset.sortedLT_sort _).pairwise
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨b, -, rfl⟩; exact ⟨mem_univList _, b.2⟩
    · rintro ⟨-, h⟩; exact ⟨⟨a, h⟩, mem_univList _, rfl⟩

theorem succList_val (a : D) : succList G a.1 = (succList GD a).map Subtype.val := by
  unfold succList
  have : (fun w : D => decide ((subgame G D hD).edge a w)) =
      (fun w : V => decide (G.edge a.1 w)) ∘ Subtype.val := rfl
  rw [this, ← List.filter_map, univList_val, List.filter_filter]
  refine List.filter_congr fun w _ => ?_
  by_cases h : G.edge a.1 w
  · simp [h, hD a.1 a.2 w h]
  · simp [h]

/-! ### Best successors -/

theorem foldl_val (F : V → V → V) (FD : D → D → D) (hF : ∀ b x, (FD b x).1 = F b.1 x.1) :
    ∀ (ws : List D) (b : D), (ws.map Subtype.val).foldl F b.1 = (ws.foldl FD b).1
  | [], _ => rfl
  | x :: ws, b => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← hF]
    exact foldl_val F FD hF ws _

theorem bestOf_val (better : Key → Key → Bool) (κ : V → Key) (κD : D → Key)
    (h : ∀ x y : D, better (κ x.1) (κ y.1) = better (κD x) (κD y)) (cur : D) (ws : List D) :
    bestOf better κ cur.1 (ws.map Subtype.val) = (bestOf better κD cur ws).1 := by
  unfold bestOf
  refine foldl_val _ _ (fun b x => ?_) ws cur
  rw [h x b]
  split_ifs <;> rfl

theorem argmaxKey_val (ks : V → Key) (ksD : D → Key)
    (h : ∀ x y : D, ks x.1 < ks y.1 ↔ ksD x < ksD y)
    (d : D) : ∀ ws : List D, argmaxKey ks d.1 (ws.map Subtype.val) = (argmaxKey ksD d ws).1
  | [] => rfl
  | w :: ws => by
    simp only [List.map_cons, argmaxKey]
    refine foldl_val _ _ (fun b x => ?_) ws w
    by_cases hb : ksD b < ksD x
    · rw [ite_eq_left (by simpa using hb), ite_eq_left (by simpa [h] using hb)]
    · rw [ite_eq_right (by simpa using hb), ite_eq_right (by simpa [h] using hb)]

/-! ### Best responses -/

theorem respondRound_val (pl : Bool) {p : V → V} {pD : D → D} (hp : ∀ a, (pD a).1 = p a.1)
    (a : D) : look (respondRound G pl p) a.1 a.1 = (look (respondRound GD pl pD) a a).1 := by
  rw [respondRound_apply, respondRound_apply]
  have hown : ownedBy GD pl a = ownedBy G pl a.1 := rfl
  rw [hown]
  by_cases ho : ownedBy G pl a.1 = true
  · rw [ite_eq_left ho, ite_eq_left ho, succList_val G hD, ← hp a]
    refine bestOf_val _ _ _ (fun x y => ?_) _ _
    cases pl <;> simp [key_lt_val G hD hp hp]
  · rw [ite_eq_right ho, ite_eq_right ho]; exact (hp a).symm

theorem respond_succ {W : Type*} [Fintype W] [LinearOrder W] (H : Game W) [DecidableRel H.edge]
    (pl : Bool) (bf : ℕ) (p : W → W) :
    respond H pl (bf + 1) p = if ∀ v, look (respondRound H pl p) v v = p v then some p
      else respond H pl bf (fun v => look (respondRound H pl p) v v) := by
  rw [respond]
  dsimp only
  by_cases h : ∀ v, look (respondRound H pl p) v v = p v
  · rw [ite_eq_left h, ite_eq_left (by simpa [List.all_eq_true] using fun v _ => h v)]
  · rw [ite_eq_right h, ite_eq_right (by simpa [List.all_eq_true, mem_univList] using h)]

theorem respond_fix {W : Type*} [Fintype W] [LinearOrder W] (H : Game W) [DecidableRel H.edge]
    (pl : Bool) : ∀ (bf : ℕ) (x y : W → W), respond H pl bf x = some y →
      (∀ v, look (respondRound H pl x) v v = x v) → y = x
  | 0, _, _, h, _ => by simp [respond] at h
  | bf + 1, x, y, h, hx => by
    rw [respond_succ, ite_eq_left hx] at h
    exact (Option.some.inj h).symm

/-- A best response restricts to the best response on the subgame. -/
theorem respond_val (pl : Bool) : ∀ (bf : ℕ) (p q : V → V) (pD : D → D),
    (∀ a, (pD a).1 = p a.1) → respond G pl bf p = some q →
    ∃ qD : D → D, (∀ a, (qD a).1 = q a.1) ∧ respond GD pl bf pD = some qD
  | 0, _, _, _, _, h => by simp [respond] at h
  | bf + 1, p, q, pD, hp, h => by
    have hr := respondRound_val G hD pl hp
    rw [respond_succ] at h ⊢
    by_cases hall : ∀ v, look (respondRound G pl p) v v = p v
    · rw [ite_eq_left hall] at h
      cases h
      refine ⟨pD, hp, ?_⟩
      rw [ite_eq_left fun a => Subtype.ext (by rw [← hr, hall, hp])]
    · rw [ite_eq_right hall] at h
      obtain ⟨qD, hq, hqD⟩ := respond_val pl bf _ q _ (fun a => (hr a).symm) h
      by_cases hsub : ∀ a, look (respondRound GD pl pD) a a = pD a
      · rw [ite_eq_left hsub]
        have := respond_fix GD pl bf _ qD (by rwa [show (fun a => look (respondRound GD pl pD) a a)
          = pD from funext hsub] at hqD) hsub
        subst this
        exact ⟨qD, hq, rfl⟩
      · rw [ite_eq_right hsub]
        exact ⟨qD, hq, hqD⟩

/-! ### Improving and filtered edges -/

theorem improving_val {ks : V → Key} {ksD : D → Key}
    (h : ∀ x y : D, ks x.1 < ks y.1 ↔ ksD x < ksD y) {p : V → V} {pD : D → D}
    (hp : ∀ a, (pD a).1 = p a.1) (a : D) :
    improving G ks p a.1 = (improving GD ksD pD a).map Subtype.val := by
  unfold improving
  have hown : ownedBy GD true a = ownedBy G true a.1 := rfl
  rw [hown]
  by_cases ho : ownedBy G true a.1 = true
  · rw [ite_eq_left ho, ite_eq_left ho]; rfl
  · rw [ite_eq_right ho, ite_eq_right ho, succList_val G hD, List.filter_map]
    congr 1
    refine List.filter_congr fun w _ => ?_
    simp only [comp_apply, ← hp a, h]

instance mxDecidable {W : Type*} [Fintype W] (H : Game W) [DecidableRel H.edge] (κ : W → Key)
    (v w : W) : Decidable (Mx H κ v w) := by
  unfold Mx; infer_instance

theorem filtered_eq {W : Type*} [Fintype W] [LinearOrder W] (H : Game W) [DecidableRel H.edge]
    (ks kstar : W → Key) (p : W → W) (v : W) :
    filtered H ks kstar p v = (improving H ks p v).filter fun w => decide (Mx H kstar v w) := by
  unfold filtered
  refine List.filter_congr fun w hw => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨fun h => filtered_max H (List.mem_filter.2 ⟨hw, h⟩),
    fun h => (List.mem_filter.1 (mem_filtered H hw h)).2⟩

theorem mx_val {κ : V → Key} {κD : D → Key} (h : ∀ x y : D, κ x.1 ≤ κ y.1 ↔ κD x ≤ κD y)
    (a w : D) : Mx G κ a.1 w.1 ↔ Mx GD κD a w := by
  constructor
  · intro hm x hx
    exact (h x w).1 (hm x.1 hx)
  · intro hm x hx
    exact (h ⟨x, hD a.1 a.2 x hx⟩ w).2 (hm _ hx)

theorem filtered_val {ks kstar : V → Key} {ksD kstarD : D → Key}
    (h : ∀ x y : D, ks x.1 < ks y.1 ↔ ksD x < ksD y)
    (h' : ∀ x y : D, kstar x.1 ≤ kstar y.1 ↔ kstarD x ≤ kstarD y) {p : V → V} {pD : D → D}
    (hp : ∀ a, (pD a).1 = p a.1) (a : D) :
    filtered G ks kstar p a.1 = (filtered GD ksD kstarD pD a).map Subtype.val := by
  rw [filtered_eq, filtered_eq, improving_val G hD h hp, List.filter_map]
  congr 1
  refine List.filter_congr fun w _ => ?_
  simp only [comp_apply, mx_val G hD h']

/-! ### One iteration -/

/-- One H-B iteration, with the filter known to be used. -/
theorem hbStep_eq {W : Type*} [Fintype W] [LinearOrder W] (H : Game W) [DecidableRel H.edge]
    (hrel : H.Relabelled) {bf : ℕ} {p ps : W → W} (he : ∀ v, H.edge v (p v))
    (hps : respond H true bf p = some ps) :
    hbStep H bf p = if ∀ v, improving H (key H ps) p v = [] then .done (keyTable H ps) else
      match respond H false bf ps with
      | none => .stuck
      | some pstar => .next (tabulate fun v =>
          if (filtered H (key H ps) (key H pstar) p v).isEmpty then p v
          else argmaxKey (key H ps) (p v) (filtered H (key H ps) (key H pstar) p v)) := by
  have hks : (fun v => look (keyTable H ps) keyDefault v) = key H ps :=
    funext (look_keyTable H ps)
  unfold hbStep
  rw [hps]
  dsimp only
  simp only [hks]
  by_cases hall : ∀ v, improving H (key H ps) p v = []
  · rw [ite_eq_left hall, ite_eq_left (by simpa [List.all_eq_true] using fun v _ => hall v)]
  · rw [ite_eq_right hall, ite_eq_right (by simpa [List.all_eq_true, mem_univList] using hall)]
    rcases h2 : respond H false bf ps with _ | pstar
    · rfl
    · dsimp only
      have hkst : (fun v => look (keyTable H pstar) keyDefault v) = key H pstar :=
        funext (look_keyTable H pstar)
      simp only [hkst]
      have hF := filterNonempty H bf p hrel he ps pstar hps h2
      simp only [hks, hkst] at hF
      push Not at hall
      obtain ⟨v, hv⟩ := hall
      obtain ⟨w, hw⟩ := hF ⟨v, hv⟩
      rw [ite_eq_left (by simpa [List.any_eq_true, mem_univList] using ⟨w, hw⟩)]

theorem relabelled_subgame (hrel : G.Relabelled) : (subgame G D hD).Relabelled :=
  fun _ _ hab => hrel hab

/-- One non-final iteration of H-B on `G` restricts to one iteration on the subgame: either a
    non-final one computing the restriction of the next profile, or a final one, and then the
    restriction to `D` is unchanged. -/
theorem hbStep_val (hrel : G.Relabelled) {bf : ℕ} {p ps : V → V} {pD psD : D → D}
    (hp : ∀ a, (pD a).1 = p a.1) (he : ∀ v, G.edge v (p v)) {qt : List (V × V)}
    (h : hbStep G bf p = .next qt) (hps : respond G true bf p = some ps)
    (hpsD : ∀ a, (psD a).1 = ps a.1) (hpsD' : respond GD true bf pD = some psD) :
    (∃ qtD, hbStep GD bf pD = .next qtD ∧ ∀ a, (look qtD a a).1 = look qt a.1 a.1) ∨
      (∃ kt, hbStep GD bf pD = .done kt ∧ ∀ a : D, look qt a.1 a.1 = p a.1) := by
  have heD : ∀ a, (subgame G D hD).edge a (pD a) := fun a => by
    show G.edge a.1 (pD a).1
    rw [hp]; exact he a.1
  rw [hbStep_eq G hrel he hps] at h
  rw [hbStep_eq GD (relabelled_subgame G hD hrel) heD hpsD']
  have hks := key_lt_val G hD hpsD hpsD
  by_cases hall : ∀ v, improving G (key G ps) p v = []
  · rw [ite_eq_left hall] at h; cases h
  rw [ite_eq_right hall] at h
  rcases h2 : respond G false bf ps with _ | pstar
  · rw [h2] at h; cases h
  rw [h2] at h
  dsimp only at h
  injection h with h
  subst h
  obtain ⟨pstarD, hst, hstD⟩ := respond_val G hD false bf ps pstar psD hpsD h2
  have hfil := filtered_val G hD hks (key_le_val G hD hst hst) hp
  by_cases hallD : ∀ a, improving GD (key GD psD) pD a = []
  · right
    refine ⟨_, ite_eq_left hallD, fun a => ?_⟩
    rw [look_tabulate]
    have : filtered G (key G ps) (key G pstar) p a.1 = [] := by
      rw [hfil a, filtered_eq, hallD a]; rfl
    simp [this]
  · left
    rw [ite_eq_right hallD, hstD]
    refine ⟨_, rfl, fun a => ?_⟩
    rw [look_tabulate, look_tabulate, hfil a]
    rcases filtered GD (key GD psD) (key GD pstarD) pD a with _ | ⟨w, ws⟩
    · simp [hp]
    · simp only [List.map_cons, List.isEmpty_cons, Bool.false_eq_true, ite_false]
      rw [← hp a, ← List.map_cons]
      exact (argmaxKey_val _ _ hks (pD a) (w :: ws)).symm

/-! ### The autonomy lemma -/

/-- The autonomy lemma (headline). -/
theorem autonomy (bf : ℕ) : Autonomy G bf := by
  classical
  intro hrel D hD L p ps h
  have hedge := runTrace_edge G h
  obtain ⟨-, hresp, hstep⟩ := h
  have hedgeS : ∀ k ≤ L, ∀ v, G.edge v (ps k v) := fun k hk =>
    (respond_spec G true bf _ _ (hresp k hk)).2.1 (hedge k hk)
  let pD : ℕ → D → D := fun k a => if hk : p k a.1 ∈ D then ⟨_, hk⟩ else a
  let psD : ℕ → D → D := fun k a => if hk : ps k a.1 ∈ D then ⟨_, hk⟩ else a
  have hpD : ∀ k ≤ L, ∀ a, (pD k a).1 = p k a.1 := fun k hk a => by
    simp [pD, hD a.1 a.2 _ (hedge k hk a.1)]
  have hpsD : ∀ k ≤ L, ∀ a, (psD k a).1 = ps k a.1 := fun k hk a => by
    simp [psD, hD a.1 a.2 _ (hedgeS k hk a.1)]
  have hrespD : ∀ k ≤ L, respond (subgame G D hD) true bf (pD k) = some (psD k) := by
    intro k hk
    obtain ⟨qD, hq, hqD⟩ := respond_val G hD true bf _ _ _ (hpD k hk) (hresp k hk)
    rw [hqD]
    congr 1
    funext a
    exact Subtype.ext (by rw [hq, hpsD k hk])
  have hex : ∃ k, k = L ∨ ∃ kt, hbStep (subgame G D hD) bf (pD k) = .done kt :=
    ⟨L, Or.inl rfl⟩
  set LD := Nat.find hex with hLDdef
  have hLD := Nat.find_spec hex
  have hmin : ∀ k < LD, ¬ (k = L ∨ ∃ kt, hbStep (subgame G D hD) bf (pD k) = .done kt) :=
    fun k hk => Nat.find_min hex hk
  have hLDL : LD ≤ L := Nat.find_min' hex (Or.inl rfl)
  rw [← hLDdef] at hLD
  -- one step of the trace, restricted
  have hone : ∀ k < L, (∃ qtD, hbStep (subgame G D hD) bf (pD k) = .next qtD ∧
      pD (k + 1) = fun a => look qtD a a) ∨
      (∃ kt, hbStep (subgame G D hD) bf (pD k) = .done kt ∧ pD (k + 1) = pD k) := by
    intro k hk
    obtain ⟨qt, hqt, hpk⟩ := hstep k hk
    rcases hbStep_val G hD hrel (hpD k hk.le) (hedge k hk.le) hqt (hresp k hk.le)
      (hpsD k hk.le) (hrespD k hk.le) with ⟨qtD, hn, hv⟩ | ⟨kt, hd, hv⟩
    · refine Or.inl ⟨qtD, hn, funext fun a => Subtype.ext ?_⟩
      rw [hpD (k + 1) hk a, hv, hpk]
    · refine Or.inr ⟨kt, hd, funext fun a => Subtype.ext ?_⟩
      rw [hpD (k + 1) hk a, hpk, hpD k hk.le]; exact hv a
  refine ⟨pD, psD, LD, hLDL, fun k hk a => ⟨hpD k hk a, hpsD k hk a⟩,
    ⟨fun a => ?_, fun k hk => hrespD k (hk.trans hLDL), fun k hk => ?_⟩, fun hlt => ?_,
    fun k hk hkL => ?_⟩
  · show G.edge a.1 (pD 0 a).1
    rw [hpD 0 (Nat.zero_le _)]; exact hedge 0 (Nat.zero_le _) a.1
  · rcases hone k (by omega) with ⟨qtD, hn, he⟩ | ⟨kt, hd, -⟩
    · exact ⟨qtD, hn, he⟩
    · exact absurd (Or.inr ⟨kt, hd⟩) (hmin k hk)
  · rcases hLD with h' | h'
    · omega
    · exact h'
  · induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      have hdone : ∃ kt, hbStep (subgame G D hD) bf (pD LD) = .done kt := by
        rcases hLD with h' | h'
        · omega
        · exact h'
      obtain ⟨kt, hkt⟩ := hdone
      rw [← ih (by omega)] at hkt
      rcases hone k (by omega) with ⟨qtD, hn, -⟩ | ⟨-, -, he⟩
      · rw [hn] at hkt; cases hkt
      · rw [he]; exact ih (by omega)

/-! ### O1 -/

/-- Along a trace with enough fuel the potential `hbPot` increases strictly. -/
theorem runTrace_pot_lt {bf L : ℕ} {p ps : ℕ → V → V} (hbf : hbFuel V ≤ bf)
    (h : RunTrace G bf L p ps) {a b : ℕ} (hab : a < b) (hb : b ≤ L) :
    hbPot G bf (p a) < hbPot G bf (p b) := by
  have hedge := runTrace_edge G h
  obtain ⟨-, -, hstep⟩ := h
  induction b, hab using Nat.le_induction with
  | base =>
    obtain ⟨qt, hqt, hpk⟩ := hstep a (by omega)
    rw [hpk]; exact hbStep_lt G hbf hqt (hedge a (by omega))
  | succ b hb' ih =>
    obtain ⟨qt, hqt, hpk⟩ := hstep b (by omega)
    refine (ih (by omega)).trans ?_
    rw [hpk]; exact hbStep_lt G hbf hqt (hedge b (by omega))

/-- O1 (headline). -/
theorem closedIterations (bf : ℕ) : ClosedIterations G bf := by
  classical
  intro hrel hbf D hD L p ps h LD pD psD h0 hsub hdone
  obtain ⟨pD', psD', LD', hLD'L, hval, htr', -, hfroz⟩ := autonomy G bf hrel D hD L p ps h
  -- the two traces of the subgame agree
  have hagree : ∀ k, k ≤ LD → k ≤ LD' → pD k = pD' k := by
    intro k
    induction k with
    | zero =>
      intro _ _
      funext a
      exact Subtype.ext (by rw [h0, (hval 0 (Nat.zero_le _) a).1])
    | succ k ih =>
      intro h1 h2
      obtain ⟨qt1, hq1, hp1⟩ := hsub.2.2 k (by omega)
      obtain ⟨qt2, hq2, hp2⟩ := htr'.2.2 k (by omega)
      rw [ih (by omega) (by omega), hq2] at hq1
      injection hq1 with hq1
      rw [hp1, hp2, hq1]
  have hLD : LD' ≤ LD := by
    by_contra hlt
    obtain ⟨kt, hkt⟩ := hdone
    obtain ⟨qt, hq, -⟩ := htr'.2.2 LD (by omega)
    rw [hagree LD le_rfl (by omega), hq] at hkt
    cases hkt
  -- the profiles from `LD'` on differ outside `D`
  let φ : ℕ → {v // v ∈ Dᶜ} → V := fun k u => p k u.1
  let T := Fintype.piFinset fun u : {v // v ∈ Dᶜ} => Finset.univ.filter (G.edge u.1)
  have hmaps : ∀ k ∈ Finset.Icc LD' L, φ k ∈ T := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ]
    exact runTrace_edge G h k (Finset.mem_Icc.1 hk).2 u.1
  have heq : ∀ k1 ∈ Finset.Icc LD' L, ∀ k2 ∈ Finset.Icc LD' L, φ k1 = φ k2 → p k1 = p k2 := by
    intro k1 hk1 k2 hk2 he
    rw [Finset.mem_Icc] at hk1 hk2
    funext v
    by_cases hv : v ∈ D
    · rw [← (hval k1 hk1.2 ⟨v, hv⟩).1, ← (hval k2 hk2.2 ⟨v, hv⟩).1, hfroz k1 hk1.1 hk1.2,
        hfroz k2 hk2.1 hk2.2]
    · exact congrFun he ⟨v, Finset.mem_compl.2 hv⟩
  have hinj : Set.InjOn φ (Finset.Icc LD' L) := by
    intro k1 hk1 k2 hk2 he
    have hp := heq k1 hk1 k2 hk2 he
    rw [Finset.mem_coe, Finset.mem_Icc] at hk1 hk2
    rcases lt_trichotomy k1 k2 with hlt | hlt | hlt
    · exact absurd (runTrace_pot_lt G hbf h hlt hk2.2) (by rw [hp]; exact lt_irrefl _)
    · exact hlt
    · exact absurd (runTrace_pot_lt G hbf h hlt hk1.2) (by rw [hp]; exact lt_irrefl _)
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Nat.card_Icc, Fintype.card_piFinset,
    Finset.prod_coe_sort Dᶜ fun v => (Finset.univ.filter (G.edge v)).card] at hcard
  omega

end MercLib.HybridSI

end HybridSIBoundsAutonomyProofs
