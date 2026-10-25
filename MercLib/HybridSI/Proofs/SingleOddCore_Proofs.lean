module

public import MercLib.HybridSI.SingleOddCore
public import MercLib.HybridSI.Proofs.SingleOddPoly_KStar_Proofs
public import MercLib.HybridSI.Proofs.SingleOdd_Proofs
public import MercLib.HybridSI.Proofs.Bounds_Autonomy_Proofs
public import MercLib.HybridSI.Proofs.Epoch_Proofs

@[expose] public section HybridSISingleOddCoreProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The core of a run with a single Odd choice vertex (`HybridSI.SingleOddCore`).
* `unreachFreeze`: `autonomy` on the closed `unreach G u`; the subgame has no Odd vertex with two
  successors, so its trace is one epoch and `epochBound` bounds its length.
* `upDownCount`: the potential `g m = #{x ∈ S : f m < x}` (`S` the world values) grows at every
  down move, drops by at most `r - 1` at an up move, and stays at most `r - 1`.
* `worldsBound`, `kstarUpDown`, `kstarUpCount`: `C ≤ U + (U + 1)(d - 1)`.
* `upReduction`: `C + 1 ≤ d (n_E + 1) ≤ n²`. -/

open Function MercLib.ParityGame

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge]

/-! ### R2 -/

theorem mem_unreach {u v : V} : v ∈ unreach G u ↔ ¬ Relation.ReflTransGen G.edge v u := by
  classical
  simp [unreach]

theorem unreach_closed (u : V) : Closed G (unreach G u) := by
  intro v hv w hw
  rw [mem_unreach] at hv ⊢
  exact fun h => hv (Relation.ReflTransGen.head hw h)

/-- R2 (headline). -/
theorem unreachFreeze (bf : ℕ) : UnreachFreeze G bf := by
  classical
  intro hrel u hu hs L p ps h
  set D := unreach G u
  have hD := unreach_closed G u
  obtain ⟨pD, psD, LD, hLD, hval, htr, -, hfr⟩ := autonomy G bf hrel D hD L p ps h
  have hpsE := runTrace_ps_edge G h
  have hE : LD ≤ numEven (subgame G D hD) := by
    refine epochBound (subgame G D hD) bf LD pD psD htr.1
      (fun k hk => ⟨htr.2.1 k hk.le, htr.2.2 k hk⟩) fun k hk a ha => Subtype.ext ?_
    have hau : a.1 ≠ u := fun he => by
      have := a.2
      rw [he, mem_unreach] at this
      exact this Relation.ReflTransGen.refl
    rw [(hval k (by omega) a).2, (hval 0 (by omega) a).2]
    exact hs a.1 ha hau _ _ (hpsE k (by omega) a.1) (hpsE 0 (by omega) a.1)
  have hcard : numEven (subgame G D hD) ≤ numEvenIn G D := by
    unfold numEven numEvenIn
    refine Finset.card_le_card_of_injOn (fun a => a.1) (fun a ha => ?_) (fun a _ b _ h => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨a.2, ha⟩
    · exact Subtype.ext h
  refine ⟨LD, hLD, hE.trans hcard, fun k hk hkL v hv => ?_⟩
  rw [← (hval k hkL ⟨v, hv⟩).1, ← (hval LD hLD ⟨v, hv⟩).1, hfr k hk hkL]

/-! ### §2.2 -/

/-- The potential argument for down moves of a sequence with values in `S`. -/
theorem down_le_aux {α : Type*} [LinearOrder α] (f : ℕ → α) (S : Finset α) :
    ∀ m, (∀ i ≤ m, f i ∈ S) →
      ((Finset.range m).filter fun k => f (k + 1) < f k).card ≤
        (S.filter (f m < ·)).card +
          ((Finset.range m).filter fun k => f k < f (k + 1)).card * (S.card - 1) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h := ih fun i hi => hm i (by omega)
    have hfm := hm m (by omega)
    have hfm1 := hm (m + 1) le_rfl
    have hg : (S.filter (f m < ·)).card + 1 ≤ S.card := by
      have : S.filter (f m < ·) ⊂ S :=
        Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun he => by
          have := he ▸ hfm
          simp at this⟩
      have := Finset.card_lt_card this
      omega
    simp only [Finset.range_add_one, Finset.filter_insert]
    rcases lt_trichotomy (f (m + 1)) (f m) with hlt | heq | hgt
    · have hss : S.filter (f m < ·) ⊂ S.filter (f (m + 1) < ·) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun he => ?_⟩
        · simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hlt.trans hx.2⟩
        · have : f m ∈ S.filter (f (m + 1) < ·) := by simp [hfm, hlt]
          rw [← he] at this
          simp at this
      have := Finset.card_lt_card hss
      simp only [hlt, ↓reduceIte, not_lt_of_gt hlt]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp only [heq, lt_irrefl, ↓reduceIte]
      exact h
    · simp only [hgt, ↓reduceIte, not_lt_of_gt hgt]
      rw [Finset.card_insert_of_notMem (by simp), add_mul, one_mul]
      omega

/-- At most `(#up + 1)(r - 1)` down moves of a sequence, `r` its number of values. -/
theorem down_le {α : Type*} [LinearOrder α] (f : ℕ → α) (L : ℕ) :
    ((Finset.range L).filter fun k => k + 1 < L ∧ f (k + 1) < f k).card ≤
      (((Finset.range L).filter fun k => k + 1 < L ∧ f k < f (k + 1)).card + 1) *
        (((Finset.range L).image f).card - 1) := by
  rcases L with _ | L
  · simp
  set S := (Finset.range (L + 1)).image f
  have hrw : ∀ P : ℕ → Prop, [DecidablePred P] →
      ((Finset.range (L + 1)).filter fun k => k + 1 < L + 1 ∧ P k) =
        (Finset.range L).filter P := fun P _ => by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨by omega, h.2.2⟩, fun h => ⟨by omega, by omega, h.2⟩⟩
  rw [hrw, hrw]
  have hmem : ∀ i ≤ L, f i ∈ S := fun i hi =>
    Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩
  have h := down_le_aux f S L hmem
  have hg : (S.filter (f L < ·)).card + 1 ≤ S.card := by
    have : S.filter (f L < ·) ⊂ S :=
      Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun he => by
        have := he ▸ hmem L le_rfl
        simp at this⟩
    have := Finset.card_lt_card this
    omega
  rw [add_mul, one_mul]
  omega

/-- §2.2, down moves (headline). -/
theorem upDownCount (bf : ℕ) : UpDownCount G bf := fun L ps u =>
  down_le (worldValue G bf ps u) L

/-! ### Worlds -/

/-- Few worlds (headline). -/
theorem worldsBound (bf : ℕ) : WorldsBound G bf := by
  classical
  intro L p ps h u _ hw
  have hpsE := runTrace_ps_edge G h
  let F : V → Key := fun a =>
    if hx : ∃ k ∈ Finset.range L, ps k u = a then worldValue G bf ps u hx.choose else keyDefault
  have hsub : worldValues G bf L ps u ⊆ ((Finset.range L).image fun k => ps k u).image F := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    have hex : ∃ k' ∈ Finset.range L, ps k' u = ps k u := ⟨k, hk, rfl⟩
    refine Finset.mem_image.2 ⟨ps k u, Finset.mem_image.2 ⟨k, hk, rfl⟩, ?_⟩
    simp only [F, hex, ↓reduceDIte]
    obtain ⟨hk1, hk2⟩ := hex.choose_spec
    have := hw _ _ (Finset.mem_range.1 hk1).le (Finset.mem_range.1 hk).le hk2
    exact congrFun this u
  have hsucc : ((Finset.range L).image fun k => ps k u) ⊆ Finset.univ.filter (G.edge u) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ha
    simpa using hpsE k (Finset.mem_range.1 hk).le u
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (Finset.card_le_card hsucc))

/-- `K*` changes only at up and down moves (headline). -/
theorem kstarUpDown (bf : ℕ) : KStarUpDown G bf := by
  intro L ps u hw
  refine (Finset.card_le_card fun k hk => ?_).trans (Finset.card_union_le _ _)
  simp only [kstarChangeRounds, Finset.mem_filter, Finset.mem_range] at hk
  simp only [upRounds, downRounds, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  rcases lt_trichotomy (worldValue G bf ps u k) (worldValue G bf ps u (k + 1)) with h | h | h
  · exact Or.inl ⟨hk.1, hk.2.1, h⟩
  · exact absurd (hw _ _ (by omega) (by omega) h.symm) hk.2.2
  · exact Or.inr ⟨hk.1, hk.2.1, h⟩

/-! ### The reduction -/

theorem numEvenIn_le (D : Finset V) : numEvenIn G D ≤ numEven G :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ D))

/-- `#K*-changes + 1 ≤ deg u · (#up + 1)` (headline). -/
theorem kstarUpCount (bf : ℕ) : KStarUpCount G bf := by
  intro L p ps h u hu hw1 hw2
  have hr := worldsBound G bf L p ps h u hu hw1
  have hdn := upDownCount G bf L ps u
  have hC := kstarUpDown G bf L ps u hw2
  have hd1 : 1 ≤ (Finset.univ.filter (G.edge u)).card := by
    obtain ⟨w, hw⟩ := G.total u
    exact Finset.card_pos.2 ⟨w, by simpa using hw⟩
  obtain ⟨d', hd'⟩ : ∃ d', (Finset.univ.filter (G.edge u)).card = d' + 1 := ⟨_, (Nat.sub_add_cancel hd1).symm⟩
  rw [hd'] at hr ⊢
  have hm1 := Nat.mul_le_mul_left ((upRounds G bf L ps u).card + 1)
    (show (worldValues G bf L ps u).card - 1 ≤ d' by omega)
  nlinarith

/-- The reduction of `KChangeConjecture` to `MonotoneWorlds` and `UpConjecture` (headline). -/
theorem upReduction : UpReduction := by
  intro hmw hup n G _ hG u hu hs L p ps h
  have hU := hup n G _ hG u hu hs L p ps h
  have hK := kstarUpCount G _ L p ps h u hu
    (fun j k hj hk he => (hmw n G _ hG u hu hs L p ps h j k hj hk).1 he)
    (fun j k hj hk he => funext fun v =>
      le_antisymm ((hmw n G _ hG u hu hs L p ps h j k hj hk).2 he.le v)
        ((hmw n G _ hG u hu hs L p ps h k j hk hj).2 he.ge v))
  have hdn : (Finset.univ.filter (G.edge u)).card ≤ n := (Finset.card_le_univ _).trans (by simp)
  have he : numEven G + 1 ≤ n := by
    have : (Finset.univ.filter fun v => G.owner v = .zero) ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h' => by
        have := h' ▸ Finset.mem_univ u
        simp [hu] at this⟩
    have := Finset.card_lt_card this
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have := Nat.mul_le_mul hdn (show (upRounds G (hbFuel (Fin n)) L ps u).card + 1 ≤ n by omega)
  nlinarith

end MercLib.HybridSI

end HybridSISingleOddCoreProofs
