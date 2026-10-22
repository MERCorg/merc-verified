module

public import MercLib.HybridSI.Proofs.BestResponse_Graph_Proofs
public import MercLib.HybridSI.Proofs.Key_Proofs

@[expose] public section HybridSIBestResponseClassesProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The cycle-maximum classes computed by `classes` (phase 1 of `bestResponse`). With `rr` the
player's reward of a cycle maximum (`rI`), the candidates come in strictly decreasing `rr`; the
invariant `ClsInv` of the fold says that every class `μ` is exactly the set of vertices that
reach `μ` through `Rset cls μ` (the vertices unclassified when `μ` was processed), that every
processed vertex with a cycle through `Rset ∩ {≤ x}` opens a class, and records a short witness
of the cycle of each class maximum. Consequences: every vertex is classified (`classes_total`),
edges never lead to a class of greater reward (`classes_closed`), and the maximum of any cycle
inside a class has reward at most that of the class (`classes_cycle`). -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge] (pl : Bool) (p : V → V)

/-- The player as a `Player`. -/
def plr (pl : Bool) : Player := if pl then .one else .zero

theorem favours_iff (x : V) : favours G pl x = true ↔ Good (plr pl) (G.prio x) := by
  cases pl <;> simp [favours, plr, good_zero_iff, good_one_iff]

theorem pw_eq (x : V) : pw G pl x = wI G (plr pl) x := by
  unfold pw wI
  by_cases h : favours G pl x = true
  · rw [ite_eq_left h, ite_eq_left ((favours_iff G pl x).1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((favours_iff G pl x).2 h'))]

/-- The player's reward of a cycle maximum. -/
abbrev rr (x : V) : ℤ := rI G (plr pl) x

theorem rr_eq (x : V) : rr G pl x = if favours G pl x then (rank x : ℤ) + 1 else -((rank x : ℤ) + 1) := by
  unfold rr rI
  by_cases h : favours G pl x = true
  · rw [ite_eq_left h, ite_eq_left ((favours_iff G pl x).1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((favours_iff G pl x).2 h'))]

theorem rr_injective {x y : V} (h : rr G pl x = rr G pl y) : x = y := by
  rw [rr_eq, rr_eq] at h
  apply rank_injective
  split_ifs at h <;> omega

/-- A vertex above `λ` with a reward at most that of `λ` is unfavourable. -/
theorem not_favours_of_rr {l m : V} (hlm : l < m) (h : rr G pl m ≤ rr G pl l) :
    favours G pl m = false := by
  have := rank_lt_rank hlm
  rw [rr_eq, rr_eq] at h
  by_contra hf
  simp only [Bool.not_eq_false] at hf
  rw [ite_eq_left hf] at h
  split_ifs at h <;> omega

/-- Below an unfavourable `λ` every vertex has a greater reward. -/
theorem rr_lt_of_lt_unfav {l m : V} (hml : m < l) (hl : favours G pl l = false) :
    rr G pl l < rr G pl m := by
  have := rank_lt_rank hml
  rw [rr_eq, rr_eq, ite_eq_right (by simp [hl])]
  split_ifs <;> omega

theorem hsucc_ne_nil (v : V) : hsucc G pl p v ≠ [] := by
  unfold hsucc
  split_ifs
  · obtain ⟨w, hw⟩ := G.total v
    exact List.ne_nil_of_mem ((mem_succList G).2 hw)
  · simp

/-! ### The candidates -/

theorem mem_cands (x : V) : x ∈ cands G pl := by
  unfold cands
  by_cases h : favours G pl x = true <;> simp [mem_univList, h]

theorem length_cands : (cands G pl).length = Fintype.card V := by
  unfold cands
  rw [List.length_append, List.filter_reverse, List.length_reverse]
  have := List.length_eq_length_filter_add (l := univList V) (f := favours G pl)
  have hu : (univList V).length = Fintype.card V := by simp [univList]
  omega

theorem cands_pairwise : (cands G pl).Pairwise fun a b => rr G pl b < rr G pl a := by
  have hs : (univList V).Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  unfold cands
  rw [List.pairwise_append]
  have hrev : (univList V).reverse.Pairwise fun a b => b < a := List.pairwise_reverse.2 hs
  refine ⟨(hrev.filter _).imp_of_mem fun {a b} ha hb hab => ?_,
    (hs.filter _).imp_of_mem fun {a b} ha hb hab => ?_, ?_⟩
  · simp only [List.mem_filter] at ha hb
    have := rank_lt_rank hab
    rw [rr_eq, rr_eq, ite_eq_left ha.2, ite_eq_left hb.2]
    omega
  · simp only [List.mem_filter, Bool.not_eq_true'] at ha hb
    have := rank_lt_rank hab
    simp only [rr_eq, ha.2, hb.2, Bool.false_eq_true, ite_false]
    omega
  · intro a ha b hb
    simp only [List.mem_filter, Bool.not_eq_true'] at ha hb
    simp only [rr_eq, ha.2, hb.2, Bool.false_eq_true, ite_false, ite_true]
    omega

/-! ### The fold invariant -/

/-- The vertices that were unclassified when `μ` was processed: unclassified ones and those of
    classes of reward at most that of `μ`. -/
def Rset (cls : V → Option V) (μ : V) : V → Bool := fun u =>
  match cls u with
  | none => true
  | some ν => decide (rr G pl ν ≤ rr G pl μ)

/-- The invariant of the fold of `classStep` over the candidates, with `rest` still to do. -/
structure ClsInv (cls : V → Option V) (rest : List V) : Prop where
  sorted : rest.Pairwise fun a b => rr G pl b < rr G pl a
  past : ∀ z x, z ∉ rest → x ∈ rest → rr G pl x < rr G pl z
  cls_max : ∀ v μ, cls v = some μ → cls μ = some μ ∧ ∀ x ∈ rest, rr G pl x < rr G pl μ
  cls_iff : ∀ μ, cls μ = some μ → ∀ v,
    cls v = some μ ↔ Reach (hsucc G pl p) (Rset G pl cls μ) v μ
  opens : ∀ x, x ∉ rest → Rset G pl cls x x = true →
    (∃ y ∈ hsucc G pl p x,
      Reach (hsucc G pl p) (fun u => Rset G pl cls x u && decide (u ≤ x)) y x) →
    cls x = some x
  wit : ∀ μ, cls μ = some μ → ∃ y ∈ hsucc G pl p μ,
    reachFrom (hsucc G pl p) (fun u => Rset G pl cls μ u && decide (u ≤ μ)) μ y = true

theorem Reach.mono {nb : V → List V} {S S' : V → Bool} (h : ∀ u, S u = true → S' u = true)
    {u x : V} (hr : Reach nb S u x) : Reach nb S' u x := by
  unfold Reach at hr ⊢
  induction hr with
  | refl => exact .refl
  | tail _ hab ih => exact ih.tail ⟨h _ hab.1, hab.2⟩

theorem rset_none {cls : V → Option V} {u : V} (μ : V) (h : cls u = none) :
    Rset G pl cls μ u = true := by simp [Rset, h]

theorem rset_some {cls : V → Option V} {u ν : V} (μ : V) (h : cls u = some ν) :
    Rset G pl cls μ u = decide (rr G pl ν ≤ rr G pl μ) := by simp [Rset, h]

theorem Reach.congr {nb : V → List V} {S S' : V → Bool} (h : S = S') {u x : V} :
    Reach nb S u x ↔ Reach nb S' u x := by rw [h]

/-- Before `x` is processed, `Rset … x` is the set of unclassified vertices. -/
theorem rset_cur {cls : V → Option V} {x : V} {rest : List V} (hI : ClsInv G pl p cls (x :: rest)) :
    Rset G pl cls x = unclassified cls := by
  funext u
  unfold Rset unclassified
  rcases h : cls u with _ | ν
  · rfl
  · have := (hI.cls_max u ν h).2 x List.mem_cons_self
    simp only [Option.isNone_some, decide_eq_false_iff_not, not_le]
    exact this

theorem classStep_inv (cls : V → Option V) (x : V) (rest : List V)
    (hI : ClsInv G pl p cls (x :: rest)) : ClsInv G pl p (classStep G pl p cls x) rest := by
  have hsorted := List.pairwise_cons.1 hI.sorted
  have hpast : ∀ z y, z ∉ rest → y ∈ rest → rr G pl y < rr G pl z := by
    intro z y hz hy
    by_cases hzx : z = x
    · subst hzx; exact hsorted.1 y hy
    · exact hI.past z y (by simp [hzx, hz]) (List.mem_cons_of_mem _ hy)
  have hcur := rset_cur G pl p hI
  unfold classStep
  split_ifs with hop
  · -- `x` opens a class
    set A := reachFrom (hsucc G pl p) (unclassified cls) x with hA
    set cls' : V → Option V := mat none fun v => if unclassified cls v && A v then some x else cls v
      with hcls'
    have happ : ∀ v, cls' v = if unclassified cls v && A v then some x else cls v := by
      intro v; rw [hcls', mat_eq]
    unfold opens at hop
    simp only [Bool.and_eq_true] at hop
    obtain ⟨hxu, hany⟩ := hop
    have hxnone : cls x = none := by simpa [unclassified] using hxu
    have hAiff : ∀ v, A v = true ↔ Reach (hsucc G pl p) (unclassified cls) v x :=
      fun v => reachFrom_iff _ _ _ _
    -- the unclassified vertices reaching `x` are exactly the new class
    have hnew : ∀ v, cls' v = some x ↔ Reach (hsucc G pl p) (unclassified cls) v x := by
      intro v
      rw [happ]
      constructor
      · intro h
        split_ifs at h with hv
        · simp only [Bool.and_eq_true] at hv; exact (hAiff v).1 hv.2
        · exact absurd ((hI.cls_max v x h).1) (by rw [hxnone]; simp)
      · intro h
        have hvu : unclassified cls v = true := by
          rcases Relation.ReflTransGen.cases_head h with rfl | ⟨w, hw, _⟩
          · exact hxu
          · exact hw.1
        rw [ite_eq_left (by simp [hvu, (hAiff v).2 h])]
    have hkeep : ∀ v μ, cls v = some μ → cls' v = some μ := by
      intro v μ h
      rw [happ, ite_eq_right (by simp [unclassified, h])]; exact h
    have hcases : ∀ v μ, cls' v = some μ → (μ = x ∧ cls v = none) ∨ cls v = some μ := by
      intro v μ h
      rw [happ] at h
      split_ifs at h with hv
      · simp only [Bool.and_eq_true, unclassified, Option.isNone_iff_eq_none] at hv
        exact Or.inl ⟨(Option.some_injective _ h).symm, hv.1⟩
      · exact Or.inr h
    -- `Rset` is unchanged for every reward above that of `x`
    have hR : ∀ μ, rr G pl x < rr G pl μ → Rset G pl cls' μ = Rset G pl cls μ := by
      intro μ hμ
      funext u
      rcases h' : cls' u with _ | ν'
      · have hu : cls u = none := by
          rcases h : cls u with _ | ν
          · rfl
          · rw [hkeep u ν h] at h'; cases h'
        simp [Rset, h', hu]
      · rcases hcases u ν' h' with ⟨rfl, hu⟩ | hu
        · simp [Rset, h', hu, hμ.le]
        · simp [Rset, h', hu]
    have hRx : Rset G pl cls' x = unclassified cls := by
      funext u
      rcases h' : cls' u with _ | ν'
      · have hu : cls u = none := by
          rcases h : cls u with _ | ν
          · rfl
          · rw [hkeep u ν h] at h'; cases h'
        simp [Rset, unclassified, h', hu]
      · rcases hcases u ν' h' with ⟨rfl, hu⟩ | hu
        · simp [Rset, unclassified, h', hu]
        · have := (hI.cls_max u ν' hu).2 x List.mem_cons_self
          simp [Rset, unclassified, h', hu, this]
    have hxx : cls' x = some x := (hnew x).2 Relation.ReflTransGen.refl
    refine ⟨hsorted.2, hpast, fun v μ h => ?_, fun μ h v => ?_, fun z hz hRz hy => ?_,
      fun μ h => ?_⟩
    · rcases hcases v μ h with ⟨rfl, _⟩ | h
      · exact ⟨hxx, hsorted.1⟩
      · obtain ⟨h1, h2⟩ := hI.cls_max v μ h
        exact ⟨hkeep μ μ h1, fun y hy => h2 y (List.mem_cons_of_mem _ hy)⟩
    · rcases hcases μ μ h with ⟨rfl, _⟩ | hμ
      · rw [hRx]; exact hnew v
      · have hlt := (hI.cls_max μ μ hμ).2 x List.mem_cons_self
        rw [hR μ hlt, ← hI.cls_iff μ hμ v]
        constructor
        · intro hv
          rcases hcases v μ hv with ⟨rfl, _⟩ | hv
          · rw [hxnone] at hμ; cases hμ
          · exact hv
        · exact hkeep v μ
    · by_cases hzx : z = x
      · subst hzx; exact hxx
      · have hlt := hI.past z x (by simp [hzx, hz]) List.mem_cons_self
        rw [hR z hlt] at hRz hy
        exact hkeep z z (hI.opens z (by simp [hzx, hz]) hRz hy)
    · rcases hcases μ μ h with ⟨rfl, _⟩ | hμ
      · rw [hRx]
        simpa only [List.any_eq_true] using hany
      · have hlt := (hI.cls_max μ μ hμ).2 x List.mem_cons_self
        rw [hR μ hlt]
        exact hI.wit μ hμ
  · -- `x` does not open a class
    refine ⟨hsorted.2, hpast, fun v μ h => ?_, hI.cls_iff, fun z hz hRz hy => ?_, hI.wit⟩
    · obtain ⟨h1, h2⟩ := hI.cls_max v μ h
      exact ⟨h1, fun y hy => h2 y (List.mem_cons_of_mem _ hy)⟩
    · by_cases hzx : z = x
      · subst hzx
        exfalso
        apply hop
        rw [hcur] at hRz hy
        obtain ⟨y, hy, hr⟩ := hy
        unfold opens
        simp only [Bool.and_eq_true, List.any_eq_true]
        exact ⟨hRz, y, hy, (reachFrom_iff _ _ _ _).2 hr⟩
      · exact hI.opens z (by simp [hzx, hz]) hRz hy

theorem foldl_classStep_inv : ∀ (rest : List V) (cls : V → Option V), ClsInv G pl p cls rest →
    ClsInv G pl p (rest.foldl (classStep G pl p) cls) []
  | [], _, h => h
  | x :: rest, cls, h => foldl_classStep_inv rest _ (classStep_inv G pl p cls x rest h)

theorem classes_inv : ClsInv G pl p (classes G pl p) [] := by
  refine foldl_classStep_inv G pl p _ _ ⟨cands_pairwise G pl, fun z _ hz _ => absurd (mem_cands G pl z) hz,
    fun v μ h => by simp at h, fun μ h => by simp at h, fun x hx => absurd (mem_cands G pl x) hx,
    fun μ h => by simp at h⟩

/-! ### Properties of the classes -/

theorem reach_of_seq {nb : V → List V} {S : V → Bool} (s : ℕ → V) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → S (s k) = true ∧ s (k + 1) ∈ nb (s k)) : Reach nb S (s a) (s b) := by
  induction b, hab using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ b hab ih =>
    exact Relation.ReflTransGen.tail (ih fun k h1 h2 => h k h1 (by omega)) (h b hab (by omega))

theorem reach_trans {nb : V → List V} {S : V → Bool} {u v x : V} (h1 : Reach nb S u v)
    (h2 : Reach nb S v x) : Reach nb S u x := Relation.ReflTransGen.trans h1 h2

theorem reach_head {nb : V → List V} {S : V → Bool} {u w x : V} (hu : S u = true) (hw : w ∈ nb u)
    (h : Reach nb S w x) : Reach nb S u x := Relation.ReflTransGen.head ⟨hu, hw⟩ h

theorem headD_mem_hsucc (u : V) : (hsucc G pl p u).headD u ∈ hsucc G pl p u := by
  obtain ⟨x, xs, h⟩ := List.exists_cons_of_ne_nil (hsucc_ne_nil G pl p u)
  rw [h]; simp

local notation "CL" => classes G pl p

theorem classes_max {v l : V} (h : CL v = some l) : CL l = some l :=
  ((classes_inv G pl p).cls_max v l h).1

theorem classes_iff {l : V} (hl : CL l = some l) (v : V) :
    CL v = some l ↔ Reach (hsucc G pl p) (Rset G pl CL l) v l :=
  (classes_inv G pl p).cls_iff l hl v

theorem classes_opens (x : V) (hx : Rset G pl CL x x = true)
    (hy : ∃ y ∈ hsucc G pl p x, Reach (hsucc G pl p) (fun u => Rset G pl CL x u && decide (u ≤ x)) y x) :
    CL x = some x :=
  (classes_inv G pl p).opens x (by simp) hx hy

theorem classes_wit {l : V} (hl : CL l = some l) : ∃ y ∈ hsucc G pl p l,
    reachFrom (hsucc G pl p) (fun u => Rset G pl CL l u && decide (u ≤ l)) l y = true :=
  (classes_inv G pl p).wit l hl

/-- Every vertex is classified. -/
theorem classes_total (v : V) : ∃ l, CL v = some l := by
  by_contra hne
  have hv : CL v = none := by
    rcases h : CL v with _ | l
    · rfl
    · exact absurd ⟨l, h⟩ hne
  let g : V → V := fun u => (hsucc G pl p u).headD u
  have hg : ∀ u, g u ∈ hsucc G pl p u := headD_mem_hsucc G pl p
  have hclosed : ∀ u, CL u = none → CL (g u) = none := by
    intro u hu
    rcases h : CL (g u) with _ | μ
    · rfl
    · have hμ := classes_max G pl p h
      have := (classes_iff G pl p hμ (g u)).1 h
      have := (classes_iff G pl p hμ u).2 (reach_head (rset_none G pl μ hu) (hg u) this)
      rw [hu] at this; cases this
  have horb : ∀ k, CL (g^[k] v) = none := by
    intro k
    induction k with
    | zero => exact hv
    | succ k ih => rw [iterate_succ_apply']; exact hclosed _ ih
  set m := cycMax g v
  have hrec : Recurs g v m := recurs_cycMax v
  obtain ⟨P, hP, hper⟩ := periodic_of_recurs hrec
  obtain ⟨i, -, hi⟩ := hrec 0
  have hm : CL m = none := by rw [← hi]; exact horb i
  have hk : ∀ k, CL (g^[k] m) = none ∧ g^[k] m ≤ m := by
    intro k
    refine ⟨by rw [← hi, ← iterate_add_apply]; exact horb _, le_cycMax (recurs_of_periodic hP hper hi k)⟩
  have := classes_opens G pl p m (rset_none G pl m hm) ⟨g m, hg m, by
    have := reach_of_seq (nb := hsucc G pl p)
      (S := fun u => Rset G pl CL m u && decide (u ≤ m)) (fun k => g^[k] m) 1 P hP fun k _ _ => ?_
    · simpa [hper.eq] using this
    · refine ⟨?_, by rw [iterate_succ_apply']; exact hg _⟩
      simp [rset_none G pl m (hk k).1, (hk k).2]⟩
  rw [hm] at this; cases this

/-- Edges never lead to a class of greater reward. -/
theorem classes_closed {v w l μ : V} (hv : CL v = some l) (hw : w ∈ hsucc G pl p v)
    (hwμ : CL w = some μ) : rr G pl μ ≤ rr G pl l := by
  by_contra hlt
  have hμ := classes_max G pl p hwμ
  have hr := (classes_iff G pl p hμ w).1 hwμ
  have hvR : Rset G pl CL μ v = true := by
    rw [rset_some G pl μ hv]; simp only [decide_eq_true_eq]; omega
  have := (classes_iff G pl p hμ v).2 (reach_head hvR hw hr)
  rw [hv] at this
  cases this
  exact hlt le_rfl

/-- The maximum of a closed walk inside a class has reward at most that of the class. -/
theorem classes_cycle {l : V} (s : ℕ → V) (a b : ℕ) (_hab : a < b) (hba : s b = s a)
    (h : ∀ k, a ≤ k → k < b → s (k + 1) ∈ hsucc G pl p (s k) ∧ CL (s k) = some l)
    (j : ℕ) (hj1 : a ≤ j) (hj2 : j < b) (hmax : ∀ k, a ≤ k → k < b → s k ≤ s j) :
    rr G pl (s j) ≤ rr G pl l := by
  by_contra hlt
  have hlt : rr G pl l < rr G pl (s j) := by omega
  set m := s j
  have hS : ∀ k, a ≤ k → k < b → (Rset G pl CL m (s k) && decide (s k ≤ m)) = true := by
    intro k h1 h2
    simp [rset_some G pl m (h k h1 h2).2, hlt.le, hmax k h1 h2]
  have hr1 := reach_of_seq (nb := hsucc G pl p) (S := fun u => Rset G pl CL m u && decide (u ≤ m))
    s (j + 1) b (by omega) fun k h1 h2 => ⟨hS k (by omega) h2, (h k (by omega) h2).1⟩
  have hr2 := reach_of_seq (nb := hsucc G pl p) (S := fun u => Rset G pl CL m u && decide (u ≤ m))
    s a j hj1 fun k h1 h2 => ⟨hS k h1 (by omega), (h k h1 (by omega)).1⟩
  rw [hba] at hr1
  have hm := classes_opens G pl p m (by rw [rset_some G pl m (h j hj1 hj2).2]; simp [hlt.le])
    ⟨s (j + 1), (h j hj1 hj2).1, reach_trans hr1 hr2⟩
  rw [(h j hj1 hj2).2] at hm
  have hlm : l = m := Option.some_injective _ hm
  rw [hlm] at hlt
  exact lt_irrefl _ hlt

end MercLib.HybridSI

end HybridSIBestResponseClassesProofs
