module

public import MercLib.HybridSI.Proofs.BestResponse_Classes_Proofs
public import MercLib.HybridSI.Proofs.Win_Proofs

@[expose] public section HybridSIBestResponseProofs

namespace MercLib.HybridSI

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems
are `bestResponse_optimal` (`BestResponseOptimal`) and `bestResponse_cost` (`BestResponseCost`).

Phase 2: every simple cycle inside a class that avoids its maximum `λ` is negative
(`negCyc_classes`: its greatest vertex has reward below `λ`, so it is either an unfavourable
vertex above `λ`, which dominates the signed sum, or all vertices lie below a favourable `λ` and
the step terms are `-1`). Hence Bellman–Ford has converged (`bfVal_fix`), the moves follow
maximal values, the play of the moves from a class reaches `λ` and has cycle maximum `λ`
(a cycle through a greater vertex would have value `≤ -M + n`, but `λ` has a successor on a cycle
below `λ` of value `≥ -n`), and the value of every vertex is `M · Σ_B ± steps`
(`value_eq`), which orders successors exactly as their keys. -/

open Function MercLib.ParityGame Cslib.Algorithms.Lean

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (G : Game V) [DecidableRel G.edge] (pl : Bool) (p : V → V)

local notation "CL" => classes G pl p
local notation "HS" => hsucc G pl p
local notation "AL" => allowed G pl p (classes G pl p)
local notation "TG" => isTarget (classes G pl p)
local notation "CW" => bfWeight G pl (classes G pl p)
local notation "DV" => bfVal (allowed G pl p (classes G pl p)) (isTarget (classes G pl p))
  (bfWeight G pl (classes G pl p))

/-- The signed step term of a class maximum. -/
def eW (l : V) : ℤ := if favours G pl l then -1 else 1

theorem mem_allowed {cls : V → Option V} {v w : V} :
    w ∈ allowed G pl p cls v ↔ w ∈ hsucc G pl p v ∧ cls w = cls v := by
  simp [allowed]

theorem isTarget_of_class {v l : V} (h : CL v = some l) : TG v = true ↔ v = l := by
  simp only [isTarget, h, beq_iff_eq, Option.some.injEq]
  exact eq_comm

theorem cw_eq {v l : V} (h : CL v = some l) :
    CW v = (if l < v then scale V * pw G pl v else 0) + eW G pl l := by
  simp [bfWeight, h, eW]

theorem pw_signed : SignedPow (pw G pl) := fun y => by
  rw [pw_eq]; exact wI_signed G _ y

/-- A nonempty set of vertices whose greatest element is unfavourable has signed sum `≤ -1`. -/
theorem sum_pw_neg (T : Finset V) (m : V) (hm : m ∈ T) (hmax : ∀ y ∈ T, y ≤ m)
    (hf : favours G pl m = false) : ∑ y ∈ T, pw G pl y ≤ -1 := by
  obtain ⟨h1, h2⟩ := top_dominates (pw G pl) (pw_signed G pl) T m hm hmax
  have : pw G pl m < 0 := by
    simp only [pw, hf, Bool.false_eq_true, ite_false]
    have : (0 : ℤ) < 2 ^ rank m := by positivity
    omega
  have := mt h1.1 (by omega)
  omega

/-- The weight of a segment inside class `l`, injective on its indices. -/
theorem sum_cw_seg {l : V} (s : ℕ → V) (a b : ℕ) (hcl : ∀ k, a ≤ k → k < b → CL (s k) = some l)
    (hinj : Set.InjOn s (Set.Ico a b)) :
    ∑ k ∈ Finset.Ico a b, CW (s k) = scale V *
      ∑ z ∈ ((Finset.Ico a b).image s).filter (l < ·), pw G pl z + ((b - a : ℕ) : ℤ) * eW G pl l := by
  classical
  have h1 : ∑ k ∈ Finset.Ico a b, CW (s k) = ∑ k ∈ Finset.Ico a b,
      ((if l < s k then scale V * pw G pl (s k) else 0) + eW G pl l) :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_Ico] at hk; exact cw_eq G pl p (hcl k hk.1 hk.2)
  rw [h1, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  congr 1
  rw [Finset.sum_filter, Finset.mul_sum,
    Finset.sum_image (f := fun z => scale V * if l < z then pw G pl z else 0)
      (fun x hx y hy e => hinj (by simpa using hx) (by simpa using hy) e)]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- Every simple cycle inside a class that avoids the class maximum is negative. -/
theorem negCyc_classes : NegCyc AL TG CW := by
  classical
  intro s a b hab hba hedge hinj
  obtain ⟨l, hl⟩ := classes_total G pl p (s a)
  have hcl : ∀ k, a ≤ k → k ≤ b → CL (s k) = some l := by
    intro k hk1 hk2
    induction k, hk1 using Nat.le_induction with
    | base => exact hl
    | succ k hk ih =>
      rw [((mem_allowed G pl p).1 (hedge k hk (by omega)).1).2]; exact ih (by omega)
  have hne : ∀ k, a ≤ k → k < b → s k ≠ l := fun k h1 h2 he =>
    by have := (hedge k h1 h2).2; rw [(isTarget_of_class G pl p (hcl k h1 h2.le)).2 he] at this; cases this
  set Z := (Finset.Ico a b).image s
  have hZcard : Z.card = b - a := by
    rw [Finset.card_image_of_injOn (by simpa using hinj), Nat.card_Ico]
  have hZle : b - a ≤ Fintype.card V := hZcard ▸ Finset.card_le_univ Z
  have hZne : Z.Nonempty := ⟨s a, Finset.mem_image.2 ⟨a, by simp [hab], rfl⟩⟩
  set m := Z.max' hZne
  obtain ⟨j, hj, hjm⟩ := Finset.mem_image.1 (Finset.max'_mem Z hZne)
  rw [Finset.mem_Ico] at hj
  have hmax : ∀ k, a ≤ k → k < b → s k ≤ s j := fun k h1 h2 => by
    rw [hjm]; exact Finset.le_max' Z _ (Finset.mem_image.2 ⟨k, by simp [h1, h2], rfl⟩)
  have hrr := classes_cycle G pl p s a b hab hba
    (fun k h1 h2 => ⟨((mem_allowed G pl p).1 (hedge k h1 h2).1).1, hcl k h1 h2.le⟩) j hj.1 hj.2 hmax
  have hml : s j ≠ l := hne j hj.1 hj.2
  have hrr' : rr G pl (s j) < rr G pl l :=
    lt_of_le_of_ne hrr fun h => hml (rr_injective G pl h)
  rw [sum_cw_seg G pl p s a b (fun k h1 h2 => hcl k h1 h2.le) hinj]
  have hM : scale V = 4 * Fintype.card V + 1 := rfl
  set T := Z.filter (l < ·)
  by_cases hT : T.Nonempty
  · -- the greatest vertex lies above `l` and is unfavourable
    obtain ⟨t, ht⟩ := hT
    have hlt : l < s j := lt_of_lt_of_le (Finset.mem_filter.1 ht).2
      (by rw [hjm]; exact Finset.le_max' Z _ (Finset.mem_filter.1 ht).1)
    have hmT : s j ∈ T := Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨j, by simp [hj.1, hj.2], rfl⟩, hlt⟩
    have hsum := sum_pw_neg G pl T (s j) hmT
      (fun y hy => by rw [hjm]; exact Finset.le_max' Z _ (Finset.mem_filter.1 hy).1)
      (not_favours_of_rr G pl hlt hrr)
    have he : eW G pl l ≤ 1 := by unfold eW; split_ifs <;> omega
    have : scale V * ∑ z ∈ T, pw G pl z ≤ -scale V := by nlinarith [hM]
    have : ((b - a : ℕ) : ℤ) * eW G pl l ≤ (b - a : ℕ) := by
      have : (0 : ℤ) ≤ ((b - a : ℕ) : ℤ) := by positivity
      nlinarith
    have : ((b - a : ℕ) : ℤ) ≤ Fintype.card V := by exact_mod_cast hZle
    omega
  · -- every vertex lies below `l`
    have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.1 hT
    rw [hT0, Finset.sum_empty, mul_zero, zero_add]
    have hjl : s j < l := by
      rcases lt_or_gt_of_ne hml with h | h
      · exact h
      · exact absurd ⟨s j, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨j, by simp [hj.1, hj.2], rfl⟩, h⟩⟩ hT
    have hfl : favours G pl l = true := by
      by_contra hf
      have := rr_lt_of_lt_unfav G pl hjl (by simpa using hf)
      omega
    have : eW G pl l = -1 := by simp [eW, hfl]
    rw [this]
    have : 0 < b - a := by omega
    push_cast [Nat.cast_sub hab.le]
    omega

/-! ### Values and moves -/

/-- The moves computed from the values. -/
local notation "QM" => movesOf G pl p (allowed G pl p (classes G pl p)) (bfVal (allowed G pl p
  (classes G pl p)) (isTarget (classes G pl p)) (bfWeight G pl (classes G pl p)))

theorem DV_fix (v : V) : DV v = if TG v then 0 else
    (AL v).foldr (fun w a => max ((CW v : WithBot ℤ) + DV w) a) ⊥ := by
  conv_lhs => rw [← bfVal_fix _ _ _ (negCyc_classes G pl p)]
  exact bfRound_apply _ _ _ _ v

theorem DV_tgt {v : V} (h : TG v = true) : DV v = 0 := by rw [DV_fix, ite_eq_left h]

/-- Every classified vertex has an allowed successor. -/
theorem exists_allowed {v l : V} (hv : CL v = some l) : ∃ w, w ∈ AL v := by
  have hl := classes_max G pl p hv
  by_cases hvl : v = l
  · subst hvl
    obtain ⟨y, hy, hr⟩ := classes_wit G pl p hl
    have hr := (reachFrom_iff _ _ _ _).1 hr
    have hr' := Reach.mono (S' := Rset G pl CL v) (fun u hu => by simp at hu; exact hu.1) hr
    exact ⟨y, (mem_allowed G pl p).2 ⟨hy, by rw [(classes_iff G pl p hl y).2 hr', hv]⟩⟩
  · have hr := (classes_iff G pl p hl v).1 hv
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨w, hw, hwr⟩
    · exact absurd h hvl
    · exact ⟨w, (mem_allowed G pl p).2 ⟨hw.2, by rw [(classes_iff G pl p hl w).2 hwr, hv]⟩⟩

theorem moves_apply (v : V) : QM v = if ownedBy G pl v then
    argmaxBy DV (p v) (AL v) else p v := by
  unfold movesOf; rw [matV_eq]

/-- The move of a classified vertex is allowed and of greatest value. -/
theorem moves_spec {v l : V} (hv : CL v = some l) :
    QM v ∈ AL v ∧ ∀ w ∈ AL v, DV w ≤ DV (QM v) := by
  obtain ⟨w0, hw0⟩ := exists_allowed G pl p hv
  rw [moves_apply]
  split_ifs with ho
  · exact argmaxBy_spec _ _ _ (List.ne_nil_of_mem hw0)
  · have hsub : ∀ w ∈ AL v, w = p v := by
      intro w hw
      have := ((mem_allowed G pl p).1 hw).1
      simpa [hsucc, ho] using this
    rw [← hsub w0 hw0]
    exact ⟨hw0, fun w hw => by rw [hsub w hw, ← hsub w0 hw0]⟩

theorem moves_class {v l : V} (hv : CL v = some l) : CL (QM v) = some l := by
  rw [((mem_allowed G pl p).1 (moves_spec G pl p hv).1).2, hv]

theorem moves_hsucc {v l : V} (hv : CL v = some l) : QM v ∈ HS v :=
  ((mem_allowed G pl p).1 (moves_spec G pl p hv).1).1

theorem moves_other {v : V} (h : ownedBy G pl v = false) : QM v = p v := by
  rw [moves_apply, ite_eq_right (by simp [h])]

/-- Off the targets the value is the weight plus the value of the move. -/
theorem DV_step {v l : V} (hv : CL v = some l) (hvl : v ≠ l) :
    DV v = (CW v : WithBot ℤ) + DV (QM v) := by
  have ht : TG v = false := by
    by_contra h; exact hvl ((isTarget_of_class G pl p hv).1 (by simpa using h))
  rw [DV_fix, ite_eq_right (by simp [ht])]
  obtain ⟨h1, h2⟩ := moves_spec G pl p hv
  refine le_antisymm (foldr_max_le _ _ _ fun w hw => add_le_add_right (h2 w hw) _)
    (le_foldr_max (fun w => (CW v : WithBot ℤ) + DV w) _ _ h1)

theorem iterate_class {v l : V} (hv : CL v = some l) : ∀ k, CL (QM^[k] v) = some l
  | 0 => hv
  | k + 1 => by rw [iterate_succ_apply']; exact moves_class G pl p (iterate_class hv k)

/-- Every classified vertex has a finite value. -/
theorem DV_ne_bot {v l : V} (hv : CL v = some l) : DV v ≠ ⊥ := by
  have hl := classes_max G pl p hv
  have hr := (classes_iff G pl p hl v).1 hv
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => rw [DV_tgt G pl p ((isTarget_of_class G pl p hl).2 rfl)]; simp
  | @head u w huw hwr ih =>
    have hw : CL w = some l := (classes_iff G pl p hl w).2 hwr
    have hu : CL u = some l := (classes_iff G pl p hl u).2 (reach_head huw.1 huw.2 hwr)
    by_cases hul : u = l
    · rw [hul, DV_tgt G pl p ((isTarget_of_class G pl p hl).2 rfl)]; simp
    · rw [DV_step G pl p hu hul]
      have := (moves_spec G pl p hu).2 w ((mem_allowed G pl p).2 ⟨huw.2, by rw [hw, hu]⟩)
      have hne := ne_bot_of_le_ne_bot (ih hw) this
      exact WithBot.add_ne_bot.2 ⟨WithBot.coe_ne_bot, hne⟩

/-- Telescoping along the moves. -/
theorem DV_tel (s : ℕ → V) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → DV (s k) = (CW (s k) : WithBot ℤ) + DV (s (k + 1))) :
    DV (s a) = ((∑ k ∈ Finset.Ico a b, CW (s k) : ℤ) : WithBot ℤ) + DV (s b) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [ih fun k h1 h2 => h k h1 (by omega), h b hab (by omega), Finset.sum_Ico_succ_top hab,
      ← add_assoc, WithBot.coe_add]

/-! ### The play of the moves -/

theorem moves_ne_of_class {v l : V} (hv : CL v = some l) (hvl : v ≠ l) : TG v = false := by
  by_contra h; exact hvl ((isTarget_of_class G pl p hv).1 (by simpa using h))

/-- The play from a classified vertex reaches the class maximum. -/
theorem moves_reach {v l : V} (hv : CL v = some l) : ∃ j, QM^[j] v = l := by
  by_contra hne
  push Not at hne
  obtain ⟨P, hP, -, hper⟩ := exists_period (f := QM) v
  set c0 := QM^[Fintype.card V] v
  have hc0 : CL c0 = some l := iterate_class G pl p hv _
  set h := minimalPeriod QM c0
  have hh : 0 < h := hper.minimalPeriod_pos hP
  let s : ℕ → V := fun k => QM^[k] c0
  have hsne : ∀ k, s k ≠ l := fun k => by
    simp only [s, c0, ← iterate_add_apply]; exact hne _
  have hscl : ∀ k, CL (s k) = some l := fun k => iterate_class G pl p hc0 k
  have hinj : Set.InjOn s (Set.Ico 0 h) := by
    intro x hx y hy e
    exact iterate_injOn_Iio_minimalPeriod (by simpa using hx) (by simpa using hy) e
  have hneg := negCyc_classes G pl p s 0 h hh (iterate_minimalPeriod)
    (fun k _ _ => ⟨by simp only [s, iterate_succ_apply']; exact (moves_spec G pl p (hscl k)).1,
      moves_ne_of_class G pl p (hscl k) (hsne k)⟩) hinj
  have htel := DV_tel G pl p s 0 h hh.le fun k _ _ => by
    simp only [s, iterate_succ_apply']; exact DV_step G pl p (hscl k) (hsne k)
  have hs0 : s h = s 0 := iterate_minimalPeriod
  rw [hs0] at htel
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.1 (DV_ne_bot G pl p (hscl 0))
  rw [← hx, ← WithBot.coe_add, WithBot.coe_inj] at htel
  omega

/-- A vertex reaching the class maximum through the class below it has value `≥ -j`. -/
theorem DV_ge_of_reachIt {l : V} (hl : CL l = some l) :
    ∀ (j : ℕ) (u : V), reachIt HS (fun u => Rset G pl CL l u && decide (u ≤ l)) l j u = true →
      ((-(j : ℤ) : ℤ) : WithBot ℤ) ≤ DV u := by
  intro j
  induction j with
  | zero =>
    intro u hu
    rw [(reachIt_zero _ _ _ _).1 hu, DV_tgt G pl p ((isTarget_of_class G pl p hl).2 rfl)]
    simp
  | succ j ih =>
    intro u hu
    rcases reachIt_cases _ _ _ _ _ hu with h | ⟨hS, w, hw, hwj⟩
    · exact le_trans (WithBot.coe_le_coe.2 (by omega)) (ih u h)
    · have hrw := reachIt_sound _ _ _ _ _ hwj
      have hS' : ∀ x, (Rset G pl CL l x && decide (x ≤ l)) = true → Rset G pl CL l x = true :=
        fun x hx => by simp at hx; exact hx.1
      have hwcl : CL w = some l := (classes_iff G pl p hl w).2 (Reach.mono hS' hrw)
      have hucl : CL u = some l :=
        (classes_iff G pl p hl u).2 (reach_head (hS' u hS) hw (Reach.mono hS' hrw))
      by_cases hul : u = l
      · rw [hul, DV_tgt G pl p ((isTarget_of_class G pl p hl).2 rfl)]
        exact WithBot.coe_le_coe.2 (by omega)
      · rw [DV_step G pl p hucl hul]
        have hle := (moves_spec G pl p hucl).2 w ((mem_allowed G pl p).2 ⟨hw, by rw [hwcl, hucl]⟩)
        have hul' : ¬ l < u := by simp at hS; exact not_lt.2 hS.2
        have hcw : CW u = eW G pl l := by rw [cw_eq G pl p hucl, ite_eq_right hul', zero_add]
        have he : -1 ≤ eW G pl l := by unfold eW; split_ifs <;> omega
        calc ((-((j + 1 : ℕ) : ℤ) : ℤ) : WithBot ℤ) ≤ ((CW u : ℤ) : WithBot ℤ) + ((-(j : ℤ) : ℤ) : WithBot ℤ) := by
              rw [← WithBot.coe_add, WithBot.coe_le_coe]; push_cast; omega
          _ ≤ (CW u : WithBot ℤ) + DV (QM u) := add_le_add_right ((ih w hwj).trans hle) _

/-- The cycle maximum of the play from a class maximum is itself. -/
theorem cycMax_moves_max {l : V} (hl : CL l = some l) : cycMax QM l = l := by
  classical
  obtain ⟨j, hj⟩ := moves_reach G pl p (moves_class G pl p hl)
  have hper : IsPeriodicPt QM (j + 1) l := by
    show QM^[j + 1] l = l; rw [iterate_succ_apply]; exact hj
  set h := minimalPeriod QM l
  have hh : 0 < h := hper.minimalPeriod_pos (by omega)
  let s : ℕ → V := fun k => QM^[k] l
  have hscl : ∀ k, CL (s k) = some l := fun k => iterate_class G pl p hl k
  have hinj : Set.InjOn s (Set.Ico 0 h) := by
    intro x hx y hy e
    exact iterate_injOn_Iio_minimalPeriod (by simpa using hx) (by simpa using hy) e
  have hsh : s h = s 0 := iterate_minimalPeriod
  have hrec : ∀ k, Recurs QM l (s k) := fun k =>
    recurs_of_periodic (a := 0) hh (isPeriodicPt_minimalPeriod QM l) rfl k
  set m := cycMax QM l
  obtain ⟨i, -, hi⟩ := recurs_cycMax (f := QM) l 0
  have hmi : s (i % h) = m := by
    simp only [s]; rw [iterate_mod_minimalPeriod_eq]; exact hi
  have hle : ∀ k, s k ≤ m := fun k => le_cycMax (hrec k)
  have hlm : l ≤ m := hle 0
  by_contra hne
  have hlt : l < m := lt_of_le_of_ne hlm (Ne.symm hne)
  have hi0 : i % h ≠ 0 := fun h0 => by rw [h0] at hmi; exact hne hmi.symm
  have himod : i % h < h := Nat.mod_lt _ hh
  have hrr := classes_cycle G pl p s 0 h hh hsh
    (fun k _ _ => ⟨by simp only [s, iterate_succ_apply']; exact moves_hsucc G pl p (hscl k),
      hscl k⟩) (i % h) (Nat.zero_le _) himod (fun k _ _ => by rw [hmi]; exact hle k)
  rw [hmi] at hrr
  have hfm := not_favours_of_rr G pl hlt hrr
  -- the value of the move of `l`
  have hsne : ∀ k, 1 ≤ k → k < h → s k ≠ l := fun k h1 h2 e =>
    absurd (hinj (by simp; omega) (by simp; omega) (e.trans rfl : s k = s 0)) (by omega)
  have htel := DV_tel G pl p s 1 h hh fun k h1 h2 => by
    simp only [s, iterate_succ_apply']; exact DV_step G pl p (hscl k) (hsne k h1 h2)
  rw [hsh, show s 0 = l from rfl, DV_tgt G pl p ((isTarget_of_class G pl p hl).2 rfl), add_zero,
    sum_cw_seg G pl p s 1 h (fun k _ _ => hscl k) (hinj.mono (by
      intro x hx; simp at hx ⊢; omega))] at htel
  set T := ((Finset.Ico 1 h).image s).filter (l < ·)
  have hmT : m ∈ T := Finset.mem_filter.2
    ⟨Finset.mem_image.2 ⟨i % h, by simp; omega, hmi⟩, hlt⟩
  have hsum := sum_pw_neg G pl T m hmT (fun y hy => by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hy).1; exact hle k) hfm
  -- the competitor on a cycle below `l`
  obtain ⟨y, hy, hry⟩ := classes_wit G pl p hl
  have hDy := DV_ge_of_reachIt G pl p hl _ y hry
  have hS' : ∀ x, (Rset G pl CL l x && decide (x ≤ l)) = true → Rset G pl CL l x = true :=
    fun x hx => by simp at hx; exact hx.1
  have hycl : CL y = some l :=
    (classes_iff G pl p hl y).2 (Reach.mono hS' ((reachFrom_iff _ _ _ _).1 hry))
  have hyle := (moves_spec G pl p hl).2 y ((mem_allowed G pl p).2 ⟨hy, by rw [hycl, hl]⟩)
  have h1 : s 1 = QM l := rfl
  rw [h1] at htel
  have := hDy.trans (hyle.trans (le_of_eq htel))
  rw [WithBot.coe_le_coe] at this
  have hhn : h ≤ Fintype.card V := by
    have := Finset.card_image_of_injOn (f := s) (s := Finset.Ico 0 h) (by rw [Finset.coe_Ico]; exact hinj)
    rw [Nat.card_Ico] at this
    have := Finset.card_le_univ ((Finset.Ico 0 h).image s)
    omega
  have he : eW G pl l ≤ 1 := by unfold eW; split_ifs <;> omega
  have hM : scale V = 4 * Fintype.card V + 1 := rfl
  have h3 : scale V * ∑ z ∈ T, pw G pl z ≤ -scale V := by nlinarith [hM]
  have h4 : ((h - 1 : ℕ) : ℤ) * eW G pl l ≤ (h - 1 : ℕ) := by
    have : (0 : ℤ) ≤ ((h - 1 : ℕ) : ℤ) := by positivity
    nlinarith
  have h5 : ((h - 1 : ℕ) : ℤ) ≤ Fintype.card V := by
    have : h - 1 ≤ Fintype.card V := by omega
    exact_mod_cast this
  omega

theorem cycMax_iterate (f : V → V) : ∀ (k : ℕ) (v : V), cycMax f (f^[k] v) = cycMax f v
  | 0, _ => rfl
  | k + 1, v => by rw [iterate_succ_apply', cycMax_apply, cycMax_iterate f k v]

/-- The cycle maximum of the play from a vertex of class `l` is `l`. -/
theorem cycMax_moves {v l : V} (hv : CL v = some l) : cycMax QM v = l := by
  obtain ⟨j, hj⟩ := moves_reach G pl p hv
  rw [← cycMax_iterate QM j v, hj, cycMax_moves_max G pl p (classes_max G pl p hv)]

/-! ### Values are keys -/

theorem stepsTo_le (f : V → V) (x : V) : stepsTo f x ≤ 2 * Fintype.card V := by
  obtain ⟨i, hi, e⟩ := exists_hit (f := f) x
  by_contra h
  exact (stepsTo_spec (f := f) x).2 i (by omega) e

theorem eI_eq (l : V) (k : ℕ) : eI G (plr pl) l k = eW G pl l * k := by
  unfold eI eW
  by_cases h : favours G pl l = true
  · rw [ite_eq_left ((favours_iff G pl l).1 h), ite_eq_left h]; ring
  · rw [ite_eq_right (fun h' => h ((favours_iff G pl l).2 h')), ite_eq_right h]; ring

/-- The value of a vertex: `M` times the signed sum over `B`, plus the signed step count. -/
theorem value_eq {l : V} : ∀ (n : ℕ) (v : V), stepsTo QM v = n → CL v = some l →
    DV v = ((scale V * ∑ y ∈ bSet QM v, wI G (plr pl) y + eW G pl l * stepsTo QM v : ℤ) : WithBot ℤ) := by
  intro n
  induction n with
  | zero =>
    intro v hn hv
    have hc := cycMax_moves G pl p hv
    by_cases hvl : v = l
    · subst hvl
      rw [DV_tgt G pl p ((isTarget_of_class G pl p hv).2 rfl), bSet_eq_empty hc.symm, hn]
      simp
    · have := (stepsTo_spec (f := QM) v).1
      rw [hn, hc] at this
      exact absurd this hvl
  | succ n ih =>
    intro v hn hv
    have hc := cycMax_moves G pl p hv
    have hvl : v ≠ l := by
      rintro rfl; rw [stepsTo_eq_zero hc.symm] at hn; omega
    have hvc : v ≠ cycMax QM v := by rw [hc]; exact hvl
    have hst := stepsTo_apply hvc
    have hqv := moves_class G pl p hv
    rw [DV_step G pl p hv hvl, ih (QM v) (by omega) hqv, sum_bSet_apply hvc, hst, hc,
      cw_eq G pl p hv, pw_eq, ← WithBot.coe_add, WithBot.coe_inj]
    push_cast
    split_ifs <;> ring

/-- No owned vertex has a strictly better successor (player `pl`'s view). -/
theorem moves_stable {v w : V} (hw : w ∈ HS v) :
    K G QM (plr pl) w ≤ K G QM (plr pl) (QM v) := by
  obtain ⟨l, hv⟩ := classes_total G pl p v
  obtain ⟨μ, hwμ⟩ := classes_total G pl p w
  have hq := moves_class G pl p hv
  rw [K_le_iff, cycMax_moves G pl p hwμ, cycMax_moves G pl p hq]
  by_cases hμl : μ = l
  · subst hμl
    right
    refine ⟨rfl, ?_⟩
    have hle := (moves_spec G pl p hv).2 w ((mem_allowed G pl p).2 ⟨hw, by rw [hwμ, hv]⟩)
    rw [value_eq G pl p _ w rfl hwμ, value_eq G pl p _ (QM v) rfl hq, WithBot.coe_le_coe] at hle
    rw [eI_eq, eI_eq]
    have h1 := stepsTo_le QM w
    have h2 := stepsTo_le QM (QM v)
    have he : eW G pl μ = 1 ∨ eW G pl μ = -1 := by unfold eW; split_ifs <;> simp
    have hM : scale V = 4 * Fintype.card V + 1 := rfl
    set A := ∑ y ∈ bSet QM w, wI G (plr pl) y
    set B := ∑ y ∈ bSet QM (QM v), wI G (plr pl) y
    have hAB : A ≤ B := by
      by_contra hlt
      have : scale V * (B + 1) ≤ scale V * A := mul_le_mul_of_nonneg_left (by omega) (by omega)
      rcases he with he | he <;> rw [he] at hle <;> nlinarith
    rcases lt_or_eq_of_le hAB with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rw [h] at hle
      linarith
  · left
    exact lt_of_le_of_ne (classes_closed G pl p hv hw hwμ) fun h => hμl (rr_injective G pl h)

/-! ### The timed program computes the moves -/

theorem ret_foldlM {α β : Type*} (f : β → α → TimeM ℕ β) :
    ∀ (xs : List α) (b : β), (xs.foldlM f b).ret = xs.foldl (fun b a => (f b a).ret) b
  | [], _ => rfl
  | a :: xs, b => by simp [List.foldlM_cons, ret_foldlM f xs]

theorem time_foldlM_le {α β : Type*} (f : β → α → TimeM ℕ β) (K : ℕ)
    (hf : ∀ b a, (f b a).time ≤ K) : ∀ (xs : List α) (b : β), (xs.foldlM f b).time ≤ xs.length * K
  | [], _ => by simp
  | a :: xs, b => by
    simp only [List.foldlM_cons, TimeM.time_bind, List.length_cons]
    have := time_foldlM_le f K hf xs (f b a).ret
    have := hf b a
    rw [Nat.succ_mul]; omega

theorem ret_classStepT (cls : V → Option V) (x : V) :
    (classStepT G pl p cls x).ret = classStep G pl p cls x := by
  unfold classStepT classStep opens
  simp only [TimeM.ret_bind, ret_reachFromT]
  split_ifs <;> simp [ret_reachFromT]

theorem ret_classesT : (classesT G pl p).ret = classes G pl p := by
  unfold classesT classes
  rw [ret_foldlM]
  congr 1
  funext cls x
  exact ret_classStepT G pl p cls x

theorem bestResponse_eq : bestResponse G pl p = QM := by
  unfold bestResponse bestResponseT
  simp only [TimeM.ret_bind, ret_classesT, ret_bfValT, mat_eq]
  rfl

/-- Optimality of the best response (headline). -/
theorem bestResponse_optimal : BestResponseOptimal G pl p := by
  unfold BestResponseOptimal
  rw [bestResponse_eq]
  refine ⟨fun v hv => moves_other G pl p hv, fun he v => ?_, fun v hv w hw => ?_⟩
  · obtain ⟨l, hl⟩ := classes_total G pl p v
    have := moves_hsucc G pl p hl
    unfold hsucc at this
    split_ifs at this with ho
    · exact (mem_succList G).1 this
    · rw [List.mem_singleton.1 this]; exact he v
  · have hws : w ∈ HS v := by simp [hsucc, hv, mem_succList, hw]
    have hK := moves_stable G pl p hws
    cases pl
    · exact hK
    · exact (negK_le_negK _ _).1 hK

/-! ### Cost -/

theorem roundCost_mono {nb nb' : V → List V} (h : ∀ v, (nb v).length ≤ (nb' v).length) :
    roundCost nb ≤ roundCost nb' := by
  unfold roundCost
  exact List.sum_le_sum (fun v _ => by have := h v; omega)

theorem le_roundCost (nb : V → List V) (v : V) : (nb v).length + 1 ≤ roundCost nb := by
  unfold roundCost
  exact List.le_sum_of_mem (List.mem_map.2 ⟨v, mem_univList v, rfl⟩)

theorem roundCost_hsucc : roundCost HS ≤ edgeCount G + 2 * Fintype.card V := by
  have h1 : roundCost HS ≤ ((univList V).map fun v => (succList G v).length + 2).sum := by
    unfold roundCost
    refine List.sum_le_sum (fun v _ => ?_)
    unfold hsucc
    split_ifs <;> simp
  have h2 : ((univList V).map fun v => (succList G v).length + 2).sum =
      edgeCount G + 2 * Fintype.card V := by
    rw [List.sum_map_add, edgeCount]
    simp [univList]
    ring
  omega

theorem time_classStepT (cls : V → Option V) (x : V) :
    (classStepT G pl p cls x).time ≤ 1 + 2 * Fintype.card V * roundCost HS + roundCost HS +
      Fintype.card V := by
  have h1 := time_reachFromT HS (fun v => unclassified cls v && decide (v ≤ x)) x
  have h2 := time_reachFromT HS (unclassified cls) x
  have h3 := le_roundCost HS x
  unfold classStepT
  simp only [TimeM.time_bind, TimeM.time_tick]
  split_ifs
  · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    nlinarith
  · simp only [TimeM.time_pure]
    nlinarith

/-- The cost of the best response (headline). -/
theorem bestResponse_cost : BestResponseCost G pl p := by
  unfold BestResponseCost bestResponseBound
  set n := Fintype.card V
  set W := roundCost HS
  have hW := roundCost_hsucc G pl p
  have hc : (classesT G pl p).time ≤ n * (1 + 2 * n * W + W + n) := by
    unfold classesT
    have := time_foldlM_le (classStepT G pl p) _ (time_classStepT G pl p) (cands G pl) fun _ => none
    rwa [length_cands] at this
  have hal : ∀ cls : V → Option V, roundCost (mat [] (allowed G pl p cls)) ≤ W := fun cls =>
    roundCost_mono fun v => by rw [mat_eq]; exact List.length_filter_le _ _
  have hbf := fun cls : V → Option V =>
    time_bfValT (mat [] (allowed G pl p cls)) (isTarget cls) (mat 0 (bfWeight G pl cls))
  unfold bestResponseT
  simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
  have h1 := hal (classesT G pl p).ret
  have h2 := hbf (classesT G pl p).ret
  have h3 : n * roundCost (mat [] (allowed G pl p (classesT G pl p).ret)) ≤ n * W :=
    Nat.mul_le_mul_left _ h1
  have h4 : W + 1 ≤ edgeCount G + 2 * n + 1 := by omega
  nlinarith

end MercLib.HybridSI

end HybridSIBestResponseProofs
