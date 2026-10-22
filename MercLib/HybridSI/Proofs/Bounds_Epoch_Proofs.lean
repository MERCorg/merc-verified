module

public import MercLib.HybridSI.Proofs.Bounds_Proofs
public import MercLib.HybridSI.Proofs.Bounds_Autonomy_Proofs

@[expose] public section HybridSIBoundsEpochProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

EDEC2, ESEP and LOC (`HybridSI.Bounds`), following `hb_reset/README.md`, session 3. Everything
is measured by the truncated weight `twx x f v` (the signed weight of `B ∩ (x, ∞)`), which inside
an `l`-interval is monotone (`twx_le_of_key_le`, lemma M) and satisfies the local recursion of the
play values (`twx_apply`, [VJ3]).
* `lemmaB`: a round without Odd change whose decisive element is above `x` switches an Even
  vertex `e` whose truncated value changes, into a successor whose truncated value does not.
* `epochDecisive` (EDEC2): the edge `(e, w)` of `lemmaB` was already improving and filtered at
  round `a` (same Odd strategy, so the same `K*`), and then H-B's switch at round `a` would have
  raised the truncated value of `e` (lemma A). -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-! ### Signed sums restricted to an upper set -/

theorem weight_signed : SignedPow (weight G) := fun y => by
  rw [weight_eq_wI]; exact wI_signed G .zero y

/-- Comparisons of signed sums descend to every upward closed part. -/
theorem upper_le_of_le' (δ : V → ℤ) (hδ : SignedPow δ) (P : V → Prop) [DecidablePred P]
    (hP : ∀ y z, P y → y ≤ z → P z) (A B : Finset V) (h : ∑ y ∈ A, δ y ≤ ∑ y ∈ B, δ y) :
    ∑ y ∈ A.filter P, δ y ≤ ∑ y ∈ B.filter P, δ y := by
  by_contra hlt
  rw [not_le, sum_lt_iff δ hδ] at hlt
  obtain ⟨t, ht, hmax, hb⟩ := hlt
  simp only [Finset.mem_filter] at ht hmax hb
  have hPt : P t := by by_cases h : t ∈ B <;> tauto
  have : ∑ y ∈ B, δ y < ∑ y ∈ A, δ y := by
    rw [sum_lt_iff δ hδ]
    refine ⟨t, by tauto, fun y hy => ?_, by tauto⟩
    by_cases hPy : P y
    · exact hmax y (by tauto)
    · exact le_of_lt (lt_of_not_ge fun hty => hPy (hP t y hPt hty))
  omega

/-- Distinct sets have distinct signed sums. -/
theorem sum_ne_of_ne (δ : V → ℤ) (hδ : SignedPow δ) {A B : Finset V} (h : A ≠ B) :
    ∑ y ∈ A, δ y ≠ ∑ y ∈ B, δ y := by
  classical
  intro heq
  have hS : (A \ B ∪ B \ A).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply h
    ext y
    have := Finset.ext_iff.1 he y
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.notMem_empty, iff_false] at this
    tauto
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image _ id hS
  simp only [id, Finset.mem_union, Finset.mem_sdiff] at ht hmax
  have h1 : ¬ ∑ y ∈ A, δ y < ∑ y ∈ B, δ y := by omega
  have h2 : ¬ ∑ y ∈ B, δ y < ∑ y ∈ A, δ y := by omega
  rw [sum_lt_iff δ hδ] at h1 h2
  apply h1 ⟨t, by tauto, fun y hy => hmax y (by tauto), ?_⟩
  by_contra hn
  exact h2 ⟨t, by tauto, fun y hy => hmax y (by tauto), by tauto⟩

/-! ### Truncated weights -/

/-- The signed weight of the part of `B` above `x`. -/
def twx (x : V) (f : V → V) (v : V) : ℤ := ∑ y ∈ (bSet f v).filter (x < ·), weight G y

theorem twx_le_of_key_le {x : V} {f g : V → V} {a b : V} (h : key G f a ≤ key G g b)
    (hl : cycMax f a = cycMax g b) : twx G x f a ≤ twx G x g b := by
  have hs := sum_le_of_key_le G h (by rw [hl])
  simp only [← weight_eq_wI] at hs
  exact upper_le_of_le' _ (weight_signed G) _ (fun y z hy hyz => lt_of_lt_of_le hy hyz) _ _ hs

theorem key_lt_of_twx_lt {x : V} {f g : V → V} {a b : V} (h : twx G x f a < twx G x g b)
    (hl : cycMax f a = cycMax g b) : key G f a < key G g b := by
  by_contra hle
  have := twx_le_of_key_le G (x := x) (not_lt.1 hle) hl.symm
  omega

theorem twx_eq_of_mem {x : V} {f g : V → V} {a b : V}
    (h : ∀ y, x < y → (y ∈ bSet f a ↔ y ∈ bSet g b)) : twx G x f a = twx G x g b := by
  unfold twx
  congr 1
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hxy⟩; exact ⟨(h y hxy).1 hy, hxy⟩
  · rintro ⟨hy, hxy⟩; exact ⟨(h y hxy).2 hy, hxy⟩

theorem twx_ne_of_mem {x : V} {f g : V → V} {a b : V} {y : V} (hxy : x < y)
    (h : ¬ (y ∈ bSet f a ↔ y ∈ bSet g b)) : twx G x f a ≠ twx G x g b := by
  refine sum_ne_of_ne _ (weight_signed G) fun he => h ?_
  have := Finset.ext_iff.1 he y
  simp only [Finset.mem_filter] at this
  tauto

/-- The local recursion of the truncated weight ([VJ3]). -/
theorem twx_apply (x : V) {f : V → V} {v : V} (h : v ≠ cycMax f v) :
    twx G x f v = twx G x f (f v) + if cycMax f v < v ∧ x < v then weight G v else 0 := by
  unfold twx
  rw [bSet_apply h]
  by_cases hlt : cycMax f v < v
  · rw [ite_eq_left hlt, Finset.filter_insert]
    by_cases hxv : x < v
    · rw [ite_eq_left hxv, ite_eq_left ⟨hlt, hxv⟩, Finset.sum_insert
        (fun hm => not_mem_bSet_apply hlt (Finset.mem_filter.1 hm).1), add_comm]
    · rw [ite_eq_right hxv, ite_eq_right fun h' => hxv h'.2, add_zero]
  · rw [ite_eq_right hlt, ite_eq_right fun h' => hlt h'.1, add_zero]

/-! ### First best successors -/

theorem foldl_argmax_max (ks : V → Key) : ∀ (ws : List V) (b : V),
    ks b ≤ ks (ws.foldl (fun b x => if decide (ks b < ks x) then x else b) b) ∧
      ∀ y ∈ ws, ks y ≤ ks (ws.foldl (fun b x => if decide (ks b < ks x) then x else b) b)
  | [], b => ⟨le_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: ws, b => by
    obtain ⟨ih1, ih2⟩ := foldl_argmax_max ks ws (if decide (ks b < ks x) then x else b)
    rw [List.foldl_cons]
    have hb : ks b ≤ ks (if decide (ks b < ks x) then x else b) := by
      split_ifs with h
      · exact le_of_lt (by simpa using h)
      · exact le_rfl
    have hx : ks x ≤ ks (if decide (ks b < ks x) then x else b) := by
      split_ifs with h
      · exact le_rfl
      · exact not_lt.1 (by simpa using h)
    refine ⟨hb.trans ih1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx.trans ih1
    · exact ih2 y hy

theorem argmaxKey_max (ks : V → Key) (d w : V) (ws : List V) :
    ∀ y ∈ w :: ws, ks y ≤ ks (argmaxKey ks d (w :: ws)) := by
  intro y hy
  have := foldl_argmax_max ks ws w
  rcases List.mem_cons.1 hy with rfl | hy
  · exact this.1
  · exact this.2 y hy

theorem mem_improving_of {ks : V → Key} {p : V → V} {v w : V} (hv : G.owner v = .zero)
    (hw : G.edge v w) (hlt : ks (p v) < ks w) : w ∈ improving G ks p v := by
  unfold improving
  rw [ite_eq_right (by rw [ownedBy_true_even G hv]; exact Bool.false_ne_true)]
  exact List.mem_filter.2 ⟨(mem_succList G).2 hw, by simpa using hlt⟩

/-! ### Lemma B -/

/-- Lemma B (truncated form of S1): if `g` follows `f` without Odd change and without change of
    the cycle maxima, and the part above `x` of some `B` changes, then some Even vertex `e` is
    switched, its part above `x` changes, and the part above `x` of its new successor does
    not. -/
theorem lemmaB (x : V) {f g : V → V} (hodd : ∀ u, G.owner u = .one → g u = f u)
    (hl : ∀ v, cycMax f v = cycMax g v) {v y : V} (hxy : x < y)
    (hv : ¬ (y ∈ bSet f v ↔ y ∈ bSet g v)) :
    ∃ e, G.owner e = .zero ∧ g e ≠ f e ∧ (∃ y, x < y ∧ ¬ (y ∈ bSet f e ↔ y ∈ bSet g e)) ∧
      ∀ y, x < y → (y ∈ bSet f (g e) ↔ y ∈ bSet g (g e)) := by
  let C : V → Prop := fun e => ∃ y, x < y ∧ ¬ (y ∈ bSet f e ↔ y ∈ bSet g e)
  have hdom : ∀ c, c = cycMax f c → ¬ C c := by
    rintro c hc ⟨y, -, hy⟩
    rw [bSet_eq_empty hc, bSet_eq_empty (show c = cycMax g c by rw [← hl]; exact hc)] at hy
    exact hy Iff.rfl
  by_contra hno
  have hclos : ∀ e, C e → C (g e) := by
    intro e he
    by_contra hCg
    by_cases hsw : g e = f e
    · have hnd : e ≠ cycMax f e := fun h' => hdom e h' he
      have hnd' : e ≠ cycMax g e := by rw [← hl]; exact hnd
      obtain ⟨y, hxy, hy⟩ := he
      have hmem : y ∈ bSet f (f e) ↔ y ∈ bSet g (f e) := by
        by_contra hm
        exact hCg ⟨y, hxy, by rwa [hsw]⟩
      rw [bSet_apply hnd, bSet_apply hnd', hsw, ← hl] at hy
      split_ifs at hy
      · simp only [Finset.mem_insert] at hy; tauto
      · exact hy hmem
    · refine hno ⟨e, ?_, hsw, he, fun y hxy => ?_⟩
      · by_contra h0
        exact hsw (hodd e (owner_one_of_ne G h0))
      · by_contra hm
        exact hCg ⟨y, hxy, hm⟩
  have hit : ∀ i, C (g^[i] v) := by
    intro i
    induction i with
    | zero => exact ⟨y, hxy, hv⟩
    | succ i ih => rw [iterate_succ_apply']; exact hclos _ ih
  have hc := hit (stepsTo g v)
  rw [(stepsTo_spec (f := g) v).1] at hc
  refine hdom _ ?_ hc
  rw [hl, cycMax_cycMax]

/-! ### EDEC2 -/

/-- EDEC2 (headline). -/
theorem epochDecisive (bf : ℕ) : EpochDecisive G bf := by
  intro hrel L p ps h a j x haj hjL hodd hls hdec
  have hedge := runTrace_edge G h
  have hmono := valuationMonotone G bf L p ps h
  obtain ⟨-, hresp, hstep⟩ := h
  have hlc : ∀ k, a ≤ k → k ≤ j + 1 → ∀ v, cycMax (ps k) v = cycMax (ps a) v := by
    intro k hak hkj
    induction k, hak using Nat.le_induction with
    | base => intro v; rfl
    | succ k hk ih => intro v; rw [← hls k hk (by omega) v, ih (by omega) v]
  have htc : ∀ k, a ≤ k → k ≤ j → ∀ v, twx G x (ps k) v = twx G x (ps a) v := by
    intro k hak hkj
    induction k, hak using Nat.le_induction with
    | base => intro v; rfl
    | succ k hk ih =>
      intro v
      rw [← ih (by omega) v]
      exact (twx_eq_of_mem G (hdec k hk (by omega) v)).symm
  intro v0 y0 hxy0
  by_contra hne
  obtain ⟨e, he0, hsw, ⟨y1, hxy1, hy1⟩, hw⟩ := lemmaB G x (f := ps j) (g := ps (j + 1))
    (fun u hu => by rw [hodd (j + 1) (by omega) le_rfl u hu, hodd j haj.le (by omega) u hu])
    (hls j haj.le le_rfl) hxy0 hne
  set w := ps (j + 1) e with hwdef
  have hpe : ∀ k ≤ L, ps k e = p k e := fun k hk => respond_odd_keep G (hresp k hk) he0
  have hedgeS : ∀ k ≤ L, ∀ v, G.edge v (ps k v) := fun k hk =>
    (respond_spec G true bf _ _ (hresp k hk)).2.1 (hedge k hk)
  -- one round, in the form of `hbStep_eq`
  have hround : ∀ k < L, ∃ pstar, respond G false bf (ps k) = some pstar ∧
      p (k + 1) e = if (filtered G (key G (ps k)) (key G pstar) (p k) e).isEmpty then p k e
        else argmaxKey (key G (ps k)) (p k e)
          (filtered G (key G (ps k)) (key G pstar) (p k) e) := by
    intro k hk
    obtain ⟨qt, hqt, hpk⟩ := hstep k hk
    rw [hbStep_eq G hrel (hedge k hk.le) (hresp k hk.le)] at hqt
    by_cases hall : ∀ v, improving G (key G (ps k)) (p k) v = []
    · rw [ite_eq_left hall] at hqt; cases hqt
    rw [ite_eq_right hall] at hqt
    rcases h2 : respond G false bf (ps k) with _ | pstar
    · rw [h2] at hqt; cases hqt
    rw [h2] at hqt
    dsimp only at hqt
    injection hqt with hqt
    refine ⟨pstar, rfl, ?_⟩
    rw [hpk, ← hqt]; exact look_tabulate _ _ _
  obtain ⟨pstarJ, hJ, hpJ⟩ := hround j hjL
  obtain ⟨pstarA, hA, hpA⟩ := hround a (by omega)
  -- the same `K*` at rounds `a` and `j`
  have hK : key G pstarA = key G pstarJ := by
    have eA := (respond_spec G false bf _ _ hA).2.1 (hedgeS a (by omega))
    have eJ := (respond_spec G false bf _ _ hJ).2.1 (hedgeS j hjL.le)
    have hsame : ∀ u, G.owner u = .one → pstarJ u = pstarA u := fun u hu => by
      rw [respond_even_keep G hJ hu, respond_even_keep G hA hu, hodd j haj.le (by omega) u hu]
    funext v
    exact le_antisymm (respond_even_optimal G hJ _ eA (fun u hu => (hsame u hu).symm) v)
      (respond_even_optimal G hA _ eJ hsame v)
  -- `e` switches to a filtered edge `w` at round `j`
  have hwF : w ∈ filtered G (key G (ps j)) (key G pstarJ) (p j) e := by
    have hw' : w = p (j + 1) e := hpe (j + 1) hjL
    rw [hw', hpJ]
    rcases hF : filtered G (key G (ps j)) (key G pstarJ) (p j) e with _ | ⟨w1, ws⟩
    · exfalso; apply hsw; rw [hw', hpJ, hF, hpe j hjL.le]; rfl
    · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
      exact argmaxKey_mem _ _ w1 ws
  -- cycle maxima
  set l := cycMax (ps a) e with hldef
  have hl1 : cycMax (ps (j + 1)) e = l := hlc (j + 1) (by omega) le_rfl e
  have hlj : cycMax (ps j) e = l := hlc j haj.le (by omega) e
  have hla1 : cycMax (ps (a + 1)) e = l := hlc (a + 1) (by omega) (by omega) e
  have hnd : e ≠ l := by
    intro he
    apply hy1
    rw [bSet_eq_empty (show e = cycMax (ps j) e by rw [hlj]; exact he),
      bSet_eq_empty (show e = cycMax (ps (j + 1)) e by rw [hl1]; exact he)]
  have hwl : cycMax (ps a) w = l := by
    rw [← hlc (j + 1) (by omega) le_rfl w, hwdef, cycMax_apply, hl1]
  -- the truncated weights at `j`, `j + 1` and `a`
  have t1 : twx G x (ps j) e < twx G x (ps (j + 1)) e := by
    refine lt_of_le_of_ne (twx_le_of_key_le G (hmono j (j + 1) (by omega) hjL e)
      (hls j haj.le le_rfl e)) (twx_ne_of_mem G hxy1 hy1)
  have t2 : twx G x (ps (j + 1)) w = twx G x (ps a) w := by
    rw [← twx_eq_of_mem G hw, htc j haj.le le_rfl]
  have t3 := twx_apply G x (f := ps (j + 1)) (v := e) (by rw [hl1]; exact hnd)
  have t4 := twx_apply G x (f := ps a) (v := e) hnd
  rw [hl1, ← hwdef] at t3
  rw [← hldef] at t4
  have t5 := htc j haj.le le_rfl e
  have hs : twx G x (ps a) (ps a e) < twx G x (ps a) w := by omega
  have hk : key G (ps a) (p a e) < key G (ps a) w := by
    rw [← hpe a (by omega)]
    exact key_lt_of_twx_lt G hs (by rw [cycMax_apply, hwl])
  have hwI : w ∈ improving G (key G (ps a)) (p a) e := by
    refine mem_improving_of G he0 ?_ hk
    rw [hwdef, hpe (j + 1) hjL]
    exact hedge (j + 1) hjL e
  have hmx : Mx G (key G pstarA) e w := by rw [hK]; exact filtered_max G hwF
  have hwFa := mem_filtered G hwI hmx
  -- H-B switches `e` at round `a` to a successor `w'` at least as good as `w`
  obtain ⟨w2, ws2, hF2⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hwFa)
  rw [hF2] at hpA hwFa
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at hpA
  set w' := argmaxKey (key G (ps a)) (p a e) (w2 :: ws2) with hw'def
  have hle : key G (ps a) w ≤ key G (ps a) w' := argmaxKey_max _ _ w2 ws2 w hwFa
  have hpa1 : ps (a + 1) e = w' := by rw [hpe (a + 1) (by omega), hpA]
  have hw'l : cycMax (ps a) w' = l := by
    rw [hls a le_rfl (by omega) w', ← hpa1, cycMax_apply, hla1]
  have t6 := twx_apply G x (f := ps (a + 1)) (v := e) (by rw [hla1]; exact hnd)
  rw [hla1, hpa1] at t6
  have t7 := twx_le_of_key_le G (x := x) (hmono a (a + 1) (by omega) (by omega) w')
    (hls a le_rfl (by omega) w')
  have t8 := twx_le_of_key_le G (x := x) hle (by rw [hwl, hw'l])
  have t9 := htc (a + 1) (by omega) (by omega) e
  omega

/-- ESEP (headline). -/
theorem epochNoReset (bf : ℕ) : EpochNoReset G bf := by
  intro hrel L p ps h a b x hbL hodd hls ha k hak hkb
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge a k with hlt | hle
    · exact epochDecisive G bf hrel L p ps h a k x hlt (by omega)
        (fun i hi1 hi2 => hodd i hi1 (by omega)) (fun i hi1 hi2 => hls i hi1 (by omega))
        (fun i hi1 hi2 => ih i hi2 hi1 (by omega))
    · rw [show k = a by omega]; exact ha

/-- LOC (headline). -/
theorem resetLocal (bf : ℕ) : ResetLocal G bf := by
  intro hrel L p ps h j x hj hjL hl1 hl2 hd1 hd2
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  apply hd2
  refine epochDecisive G bf hrel L p ps h (j - 1) j x (by omega) hjL (fun k hk1 hk2 u hu => ?_)
    (fun k hk1 hk2 => ?_) (fun k hk1 hk2 => ?_)
  · rcases (show k = j - 1 ∨ k = j ∨ k = j + 1 by omega) with rfl | rfl | rfl
    · rfl
    · exact (h1 u hu).symm
    · rw [← h2 u hu, ← h1 u hu]
  · rcases (show k = j - 1 ∨ k = j by omega) with rfl | rfl
    · exact hl1
    · exact hl2
  · rw [show k = j - 1 by omega]; exact hd1

end MercLib.HybridSI

end HybridSIBoundsEpochProofs
