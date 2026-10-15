module

public import Mathlib.Data.Set.Card
public import MercLib.Refinement.Semantics
public import MercLib.Refinement.Product
public import MercLib.Refinement.Antichain
public import MercLib.Refinement.Algorithm
public import MercLib.Refinement.ImpossibleFutures
public import MercLib.Refinement.AlgorithmImpossibleFutures
public import MercLib.Refinement.Proofs.Antichain_Proofs
public import MercLib.Refinement.Proofs.Product_Proofs
public import MercLib.Refinement.Proofs.Algorithm_Proofs
public import MercLib.Refinement.Proofs.ImpossibleFutures_Proofs

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.Refinement

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline
theorems `weakTraceOptCorrect` and `weakImpossibleFuturesOptCorrect` are stated in
`Challenges/Refinement.lean`.

Both loops reuse the exploration invariant `ExploreInv` of `Algorithm_Proofs.lean`. For
Algorithm 5 (Proposition 3) the explored product is `NormTr lts2 ⋉ lts1`, the witnesses are
TR-witnesses, and successors covered by `antichain⁺` need not be covered by the local antichain
(the `Ex` component of the invariant); soundness of `antichain⁺` makes them harmless. For
Algorithm 6 (Theorem 3) the witnesses are the stable IF-witnesses of Section 4.2, decided at each
popped pair by the inner loop `checkLoop`. -/

/-! ## Algorithm 5 -/

section WeakTrace

variable [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)

/-- Some TR-witness is reachable from `x` in the inner product `NormTr lts2 ⋉ lts1`. -/
def TRReach (x : Set State2 × State1) : Prop :=
  ∃ q, (product (NormTr lts2) lts1).CanReach x q ∧ IsTRWitness q.1 q.2

variable {lts1 lts2}

/-- Reachability of a TR-witness is antitone (Proposition 2 and Lemma 3). -/
theorem TRReach.antitone {x y : Set State2 × State1} (hle : ProductLE x y)
    (h : TRReach lts1 lts2 y) : TRReach lts1 lts2 x := by
  obtain ⟨q, hq, hw⟩ := h
  obtain ⟨q', hq', hq'le⟩ := productLE_canReach (normTr_isMonotone lts2) lts1 hle hq
  exact ⟨q', hq', IsTRWitness.antitone hq'le hw⟩

theorem TRReach.of_canReach {x y : Set State2 × State1}
    (hxy : (product (NormTr lts2) lts1).CanReach x y) (h : TRReach lts1 lts2 y) :
    TRReach lts1 lts2 x := by
  obtain ⟨q, hq, hw⟩ := h
  exact ⟨q, canReach_trans hxy hq, hw⟩

theorem posSound_empty : PosSound lts1 lts2 (Antichain.empty ProductLE) :=
  ⟨rfl, fun _ ⟨_, hy, _⟩ => absurd hy (Set.notMem_empty _)⟩

theorem negSound_empty : NegSound lts1 lts2 (Antichain.empty fun y x => ProductLE x y) :=
  ⟨rfl, fun _ ⟨_, hy, _⟩ => absurd hy (Set.notMem_empty _)⟩

end WeakTrace

open scoped Classical in
theorem forSuccessorsOpt_cons [HasTau Label] (lts2 : LTS State2 Label)
    (pos neg : Antichain (Set State2 × State1)) (spec : Set State2) (a : Label) (t : State1)
    (rest : List (Label × State1)) (w : List (Set State2 × State1))
    (A : Antichain (Set State2 × State1)) :
    forSuccessorsOpt lts2 pos neg spec ((a, t) :: rest) w A =
      if (succSpec lts2 spec a, t) ⊑ neg ∨ succSpec lts2 spec a = ∅ then none
      else if ¬ (succSpec lts2 spec a, t) ⊑ A ∧ ¬ (succSpec lts2 spec a, t) ⊑ pos then
        forSuccessorsOpt lts2 pos neg spec rest ((succSpec lts2 spec a, t) :: w)
          (insert (succSpec lts2 spec a, t) A)
      else forSuccessorsOpt lts2 pos neg spec rest w A := by
  rw [forSuccessorsOpt]; rfl

theorem forSuccessorsOpt_none [HasTau Label] {lts2 : LTS State2 Label}
    {pos neg : Antichain (Set State2 × State1)} {spec : Set State2} :
    ∀ {l : List (Label × State1)} {w : List (Set State2 × State1)}
      {A : Antichain (Set State2 × State1)},
      forSuccessorsOpt lts2 pos neg spec l w A = none →
      ∃ p ∈ l, (succSpec lts2 spec p.1, p.2) ⊑ neg ∨ succSpec lts2 spec p.1 = ∅
  | [], w, A, h => by simp [forSuccessorsOpt] at h
  | (a, t) :: rest, w, A, h => by
    rw [forSuccessorsOpt_cons] at h
    split_ifs at h with h1 h2
    · exact ⟨(a, t), List.mem_cons_self, h1⟩
    all_goals
      obtain ⟨p, hp, he⟩ := forSuccessorsOpt_none h
      exact ⟨p, List.mem_cons_of_mem _ hp, he⟩

theorem forSuccessorsOpt_some [HasTau Label] {lts2 : LTS State2 Label}
    {pos neg : Antichain (Set State2 × State1)} {spec : Set State2} :
    ∀ {l : List (Label × State1)} {w w' : List (Set State2 × State1)}
      {A A' : Antichain (Set State2 × State1)}, A.le = ProductLE →
      forSuccessorsOpt lts2 pos neg spec l w A = some (w', A') →
      SuccFacts lts2 spec (· ⊑ pos) l w A w' A'
  | [], w, w', A, A', hle, h => by
    simp only [forSuccessorsOpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact SuccFacts.nil hle
  | (a, t) :: rest, w, w', A, A', hle, h => by
    rw [forSuccessorsOpt_cons] at h
    split_ifs at h with h1 h2
    · exact SuccFacts.push hle (fun he => h1 (Or.inr he)) h2.1 (forSuccessorsOpt_some hle h)
    · rw [not_and_or, not_not, not_not] at h2
      exact SuccFacts.skip h2 (forSuccessorsOpt_some hle h)

/-- The result of Algorithm 5 started from `init`: the verdict is `true` iff no TR-witness is
    reachable from `init`, and the returned antichain is sound. -/
def InnerOk [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (init : Set State2 × State1) (r : Bool × Antichain (Set State2 × State1)) : Prop :=
  (r.1 = true ↔ ¬ TRReach lts1 lts2 init) ∧
    (if r.1 then PosSound lts1 lts2 r.2 else NegSound lts1 lts2 r.2)

/-- **Proposition 3**, for the `while` loop (lines 8-20). -/
theorem weakTraceLoop_spec [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (init : Set State2 × State1)
    (pos neg : Antichain (Set State2 × State1)) (hpos : PosSound lts1 lts2 pos)
    (hneg : NegSound lts1 lts2 neg) (done : Set (Set State2 × State1))
    (working : List (Set State2 × State1)) (A : Antichain (Set State2 × State1))
    (h : ExploreInv (NormTr lts2) lts1 IsTRWitness (fun _ => False) (· ⊑ pos) init done
      working A) :
    InnerOk lts1 lts2 init (weakTraceLoop lts1 lts2 init pos neg done working A) := by
  fun_induction weakTraceLoop lts1 lts2 init pos neg done working A
  case case1 done A =>
    have hdone : ∀ y ∈ A.set, y ∈ done := fun y hy =>
      (h.set_sub y hy).resolve_left List.not_mem_nil
    have key : ∀ x, (∃ z ∈ done, ProductLE z x) → ¬ TRReach lts1 lts2 x := by
      rintro x hz ⟨q, ⟨σ, hq⟩, hw⟩
      exact h.safe (normTr_isMonotone lts2) (fun hle hw => IsTRWitness.antitone hle hw)
        (fun _ hp => hp) (fun _ hp => hp.elim) (fun x hx => hpos.2 x hx) hq hz id hw
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hyA, hy⟩ := h.init
      rw [h.le_eq] at hy
      exact ⟨fun _ => key init ⟨y, hdone y hyA, hy⟩, fun _ => rfl⟩
    · refine ⟨hpos.1, ?_⟩
      rintro x ⟨y, hy | hy, hyx⟩
      · exact hpos.2 x ⟨y, hy, hyx⟩
      · change pos.le y x at hyx
        rw [hpos.1] at hyx
        exact key x ⟨y, hdone y hy, hyx⟩
  case case2 _ _ spec impl _ _ hnone =>
    obtain ⟨⟨a, t⟩, hp, hbad⟩ := forSuccessorsOpt_none hnone
    have hreach := h.reach_succ (stepsBy_normTr lts2 spec) (mem_outgoing.mp hp)
    have hTR : TRReach lts1 lts2 init := by
      rcases hbad with hn | he
      · exact TRReach.of_canReach hreach (hneg.2 _ hn)
      · exact ⟨_, hreach, he⟩
    refine ⟨⟨fun hf => absurd hf Bool.false_ne_true, fun hn => absurd hTR hn⟩, ?_⟩
    refine ⟨hneg.1, ?_⟩
    rintro x ⟨y, hy, hxy⟩
    change neg.le y x at hxy
    rw [hneg.1] at hxy
    rcases Antichain.mem_set_insert.mp hy with rfl | ⟨hy, _⟩
    · exact TRReach.antitone hxy hTR
    · exact hneg.2 x ⟨y, hy, by rw [hneg.1]; exact hxy⟩
  case case3 _ _ spec impl _ _ _ _ hsome ih =>
    exact ih (h.step (stepsBy_normTr lts2 spec) (fun _ => mem_outgoing)
      (fun he => (h.nonempty _ List.mem_cons_self).ne_empty he)
      (forSuccessorsOpt_some h.le_eq hsome))
  case case4 _ _ _ _ _ hd ih =>
    exact ih (h.skip (not_not.mp hd))

/-- **Proposition 3**, for the whole of Algorithm 5 (including the cached answers of lines 2-5). -/
theorem weakTraceOpt_ok [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (pos neg : Antichain (Set State2 × State1))
    (hpos : PosSound lts1 lts2 pos) (hneg : NegSound lts1 lts2 neg) (t : State1)
    (impl : State2) :
    InnerOk lts1 lts2 (NormInit lts2 impl, t) (weakTraceOpt lts1 lts2 t impl pos neg) := by
  unfold weakTraceOpt
  split_ifs with h1 h2
  · exact ⟨⟨fun _ => hpos.2 _ h1, fun _ => rfl⟩, by simpa using hpos⟩
  · have hTR : TRReach lts1 lts2 (NormInit lts2 impl, t) := hneg.2 _ h2
    exact ⟨⟨fun hf => absurd hf Bool.false_ne_true, fun hn => absurd hTR hn⟩, by simpa using hneg⟩
  · exact weakTraceLoop_spec lts1 lts2 _ pos neg hpos hneg _ _ _
      (ExploreInv.initial ⟨impl, WeakTr.refl impl⟩)

/-- **Proposition 3.** From sound antichains, Algorithm 5 returns `true` iff `t ⊑wt impl`, and the
    returned antichain is sound. -/
theorem weakTraceOptCorrect {State1 State2 Label : Type*} [HasTau Label] [Finite Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Antichain (Set State2 × State1)) (hpos : PosSound lts1 lts2 pos)
    (hneg : NegSound lts1 lts2 neg) (t : State1) (impl : State2) :
    ((weakTraceOpt lts1 lts2 t impl pos neg).1 = true ↔ impl ⊑tr[lts2,lts1] t) ∧
      (if (weakTraceOpt lts1 lts2 t impl pos neg).1 then
        PosSound lts1 lts2 (weakTraceOpt lts1 lts2 t impl pos neg).2
      else NegSound lts1 lts2 (weakTraceOpt lts1 lts2 t impl pos neg).2) := by
  obtain ⟨h1, h2⟩ := weakTraceOpt_ok lts1 lts2 pos neg hpos hneg t impl
  refine ⟨?_, h2⟩
  rw [h1, traceRefines_iff_not_reachable_trWitness lts2 impl lts1 t]
  simp only [TRReach, Prod.exists]

/-! ## Algorithm 6 -/

section CheckLoop

variable [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
  (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)

theorem mem_toList [Finite State] {U : Set State} {t : State} : t ∈ toList U ↔ t ∈ U := by
  simp [toList]

theorem checkLoop_false (impl : State2) :
    ∀ (ts : List State1) (pos neg : Antichain (Set State2 × State1)),
      checkLoop lts1 lts2 impl ts false pos neg = (false, pos, neg)
  | [], _, _ => rfl
  | _ :: _, _, _ => by simp [checkLoop]

theorem checkLoop_unstable {impl : State2} (hst : ¬ Stable lts2 impl) :
    ∀ (ts : List State1) (b : Bool) (pos neg : Antichain (Set State2 × State1)),
      checkLoop lts1 lts2 impl ts b pos neg = (b, pos, neg)
  | [], _, _, _ => rfl
  | _ :: _, _, _, _ => by simp [checkLoop, hst]

/-- Lines 8-14 at a stable implementation state: the loop keeps the antichains sound, and ends
    with `b = true` iff no state of `ts` is weak trace included in `impl`. -/
theorem checkLoop_spec {impl : State2} (hst : Stable lts2 impl) :
    ∀ (ts : List State1) (pos neg : Antichain (Set State2 × State1)),
      PosSound lts1 lts2 pos → NegSound lts1 lts2 neg →
      PosSound lts1 lts2 (checkLoop lts1 lts2 impl ts true pos neg).2.1 ∧
        NegSound lts1 lts2 (checkLoop lts1 lts2 impl ts true pos neg).2.2 ∧
        ((checkLoop lts1 lts2 impl ts true pos neg).1 = true ↔
          ∀ t ∈ ts, ¬ weaktraces lts1 t ⊆ weaktraces lts2 impl)
  | [], pos, neg, hpos, hneg => ⟨hpos, hneg, by simp [checkLoop]⟩
  | t :: ts, pos, neg, hpos, hneg => by
    obtain ⟨hiff, hsound⟩ := weakTraceOptCorrect lts1 lts2 pos neg hpos hneg t impl
    rcases hw : weakTraceOpt lts1 lts2 t impl pos neg with ⟨b', ac'⟩
    rw [hw] at hiff hsound
    simp only [checkLoop, hst, true_and, ite_true, hw]
    cases b'
    · simp only [Bool.false_eq_true, ite_false] at hiff hsound
      dsimp only
      obtain ⟨h1, h2, h3⟩ := checkLoop_spec hst ts pos ac' hpos hsound
      refine ⟨h1, h2, ?_⟩
      rw [h3, List.forall_mem_cons]
      exact ⟨fun h => ⟨fun hsub => hiff.mpr hsub, h⟩, fun h => h.2⟩
    · simp only [ite_true] at hiff hsound
      dsimp only
      rw [checkLoop_false]
      refine ⟨hsound, hneg, ?_⟩
      simp only [Bool.false_eq_true, List.forall_mem_cons, false_iff, not_and]
      exact fun h => absurd (hiff.mp trivial) h

/-- Lines 8-14 keep the antichains sound. -/
theorem checkLoop_sound (impl : State2) (ts : List State1)
    {pos neg : Antichain (Set State2 × State1)} (hpos : PosSound lts1 lts2 pos)
    (hneg : NegSound lts1 lts2 neg) :
    PosSound lts1 lts2 (checkLoop lts1 lts2 impl ts true pos neg).2.1 ∧
      NegSound lts1 lts2 (checkLoop lts1 lts2 impl ts true pos neg).2.2 := by
  by_cases hst : Stable lts2 impl
  · exact ⟨(checkLoop_spec lts1 lts2 hst ts pos neg hpos hneg).1,
      (checkLoop_spec lts1 lts2 hst ts pos neg hpos hneg).2.1⟩
  · rw [checkLoop_unstable lts1 lts2 hst]
    exact ⟨hpos, hneg⟩

/-- Lines 7-16 decide whether a popped, non-empty pair is a stable IF-witness. -/
theorem stableIFWitness_iff_checkLoop {spec : Set State1} {impl : State2} {b : Bool}
    {pos neg pos' neg' : Antichain (Set State2 × State1)} (hne : spec.Nonempty)
    (hpos : PosSound lts1 lts2 pos) (hneg : NegSound lts1 lts2 neg)
    (hcl : checkLoop lts1 lts2 impl (toList spec) true pos neg = (b, pos', neg')) :
    IsStableIFWitness lts1 lts2 spec impl ↔ b = true ∧ Stable lts2 impl := by
  by_cases hst : Stable lts2 impl
  · have h3 := (checkLoop_spec lts1 lts2 hst (toList spec) pos neg hpos hneg).2.2
    rw [hcl] at h3
    constructor
    · rintro (he | ⟨_, hall⟩)
      · exact absurd he hne.ne_empty
      · exact ⟨h3.mpr fun t ht => hall t (mem_toList.mp ht), hst⟩
    · rintro ⟨hb, _⟩
      exact Or.inr ⟨hst, fun t ht => h3.mp hb t (mem_toList.mpr ht)⟩
  · constructor
    · rintro (he | ⟨hs, _⟩)
      · exact absurd he hne.ne_empty
      · exact absurd hs hst
    · rintro ⟨_, hs⟩
      exact absurd hs hst

end CheckLoop

/-- **Theorem 3**, for the outer `while` loop: from the invariant and sound antichains, the loop
    returns `true` iff no stable IF-witness is reachable. -/
theorem impossibleFuturesLoop_spec [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (p0 : Set State1 × State2)
    (done : Set (Set State1 × State2)) (working : List (Set State1 × State2))
    (A : Antichain (Set State1 × State2)) (pos neg : Antichain (Set State2 × State1))
    (h : ExploreInv (NormTr lts1) lts2 (IsStableIFWitness lts1 lts2) (fun _ => False)
      (fun _ => False) p0 done working A)
    (hpos : PosSound lts1 lts2 pos) (hneg : NegSound lts1 lts2 neg) :
    impossibleFuturesLoop lts1 lts2 done working A pos neg = true ↔
      ¬ ∃ q, (product (NormTr lts1) lts2).CanReach p0 q ∧ IsStableIFWitness lts1 lts2 q.1 q.2 := by
  have found : ∀ q, (product (NormTr lts1) lts2).CanReach p0 q →
      IsStableIFWitness lts1 lts2 q.1 q.2 → (false = true ↔
        ¬ ∃ q, (product (NormTr lts1) lts2).CanReach p0 q ∧
          IsStableIFWitness lts1 lts2 q.1 q.2) := fun q hq hw => by
    simp only [Bool.false_eq_true, false_iff, not_not]
    exact ⟨q, hq, hw⟩
  fun_induction impossibleFuturesLoop lts1 lts2 done working A pos neg
  case case1 =>
    simp only [true_iff]
    exact h.no_witness (normTr_isMonotone lts1)
      (fun hle hw => IsStableIFWitness.antitone lts1 lts2 hle hw) (fun _ hp => hp)
      (fun _ hp => hp.elim) (fun _ hp => hp) (fun _ hx => hx.elim)
  case case2 _ _ _ _ spec impl _ _ _ _ _ hcl hbst =>
    exact found _ h.reach_head ((stableIFWitness_iff_checkLoop lts1 lts2
      (h.nonempty _ List.mem_cons_self) hpos hneg hcl).mpr hbst)
  case case3 _ _ _ _ spec impl _ _ _ _ _ _ _ hnone =>
    obtain ⟨⟨a, t⟩, hp, he⟩ := forSuccessors_none hnone
    refine found (succSpec lts1 spec a, t)
      (h.reach_succ (stepsBy_normTr lts1 spec) (mem_outgoing.mp hp)) ?_
    exact Or.inl he
  case case4 _ _ _ _ spec impl _ _ _ _ _ hcl hn _ _ hsome ih =>
    obtain ⟨hpos', hneg'⟩ := checkLoop_sound lts1 lts2 impl (toList spec) hpos hneg
    rw [hcl] at hpos' hneg'
    have hW : ¬ IsStableIFWitness lts1 lts2 spec impl := fun hw =>
      hn ((stableIFWitness_iff_checkLoop lts1 lts2 (h.nonempty _ List.mem_cons_self) hpos hneg
        hcl).mp hw)
    exact ih (h.step (stepsBy_normTr lts1 spec) (fun _ => mem_outgoing) hW
      (forSuccessors_some h.le_eq hsome)) hpos' hneg'
  case case5 _ _ _ _ _ _ _ hd ih =>
    exact ih (h.skip (not_not.mp hd)) hpos hneg

/-- **Theorem 3.** For finite LTSs with a convergent implementation, Algorithm 6 returns `true`
    iff weak impossible futures refinement holds. -/
theorem weakImpossibleFuturesOptCorrect {State1 State2 Label : Type*} [HasTau Label]
    [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hconv : Convergent lts2) :
    weakImpossibleFuturesOpt lts1 s1 lts2 s2 = true ↔ s1 ⊑if[lts1,lts2] s2 := by
  refine (impossibleFuturesLoop_spec lts1 lts2 (NormInit lts1 s1, s2) ∅ [(NormInit lts1 s1, s2)]
    (insert (NormInit lts1 s1, s2) (Antichain.empty ProductLE)) (Antichain.empty ProductLE)
    (Antichain.empty fun y x => ProductLE x y) (ExploreInv.initial ⟨s1, WeakTr.refl s1⟩)
    posSound_empty negSound_empty).trans ?_
  rw [impossibleFuturesRefines_iff_not_reachable_ifWitness,
    reachable_ifWitness_iff_reachable_stableIFWitness lts1 lts2 hconv, Prod.exists]

end MercLib.Refinement
