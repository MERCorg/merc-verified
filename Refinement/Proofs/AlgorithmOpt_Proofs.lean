module

public import Refinement.Semantics
public import Refinement.Product
public import Refinement.Antichain
public import Refinement.Algorithm
public import Refinement.ImpossibleFutures
public import Refinement.AlgorithmOpt
public import Refinement.Proofs.Antichain_Proofs
public import Refinement.Proofs.Product_Proofs
public import Refinement.Proofs.Algorithm_Proofs
public import Refinement.Proofs.ImpossibleFutures_Proofs

open Cslib (LTS HasTau)

@[expose] public section AlgorithmOptProofs

namespace Refinement

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins live in
`Refinement/Pins/AlgorithmOpt_Pins.lean`.

This file first develops the structural theory of Algorithm 5's inner exploration (`OptInnerStep`
runs), mirroring `Refinement/Proofs/Algorithm_Proofs.lean`: the antichain only grows, `working`
and `done` stay disjoint (hence the exploration terminates), every discovered pair is reachable
from the start, no discovered pair is a TR-witness, and - the one statement that genuinely differs
from `AlgRun` - at a terminal configuration every state reachable from the start is either covered
by the antichain or lies in the shadow of the *positive* antichain (that is where the extra
`¬ AntichainMem pos q` conjunct of `optNewSuccessors` shows up). On top of these sit Proposition 3
(`weakTraceOpt_correct`) and the soundness of the empty antichains; Theorem 3
(`optImpossibleFutures_correct`) follows from the corresponding results for Algorithm 4. -/

/-! ## Structural lemmas for the inner exploration -/

/-- One loop iteration of Algorithm 5 only ever adds to the antichain. -/
theorem OptInnerStep.antichain_subset [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {s s' : AlgState State2 State1}
    (h : OptInnerStep lts1 lts2 pos neg s s') : s.antichain ⊆ s'.antichain := by
  obtain ⟨p, _, _, _, hac, _⟩ := h
  rw [hac]
  exact Set.subset_union_left

/-- Across an inner run, the antichain only grows. -/
theorem OptInnerRun.antichain_subset [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {c c' : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) c c') :
    c.antichain ⊆ c'.antichain := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact ih.trans (OptInnerStep.antichain_subset hstep)

/-- Everything in `working` or `done` along a run from the initial configuration is in the
    antichain. -/
theorem OptInnerRun.working_union_done_subset_antichain [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {p0 : Set State2 × State1}
    {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c) :
    c.working ∪ c.done ⊆ c.antichain := by
  induction h with
  | refl => rintro x (hx | hx) <;> simp_all [AlgState.initial]
  | @tail s s' _ hstep ih =>
    have hmono_step := OptInnerStep.antichain_subset hstep
    obtain ⟨p, hp, _, hw, ha, hd⟩ := hstep
    rintro x (hx | hx)
    · rw [hw] at hx
      rcases hx with hx | hx
      · exact hmono_step (ih (Or.inl hx.1))
      · rw [ha]; exact Or.inr hx
    · rw [hd] at hx
      rcases hx with rfl | hx
      · exact hmono_step (ih (Or.inl hp))
      · exact hmono_step (ih (Or.inr hx))

/-- Along a run from the initial configuration, `working` and `done` are disjoint. -/
theorem OptInnerRun.disjoint_working_done [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {p0 : Set State2 × State1}
    {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c) :
    Disjoint c.working c.done := by
  induction h with
  | refl => simp [AlgState.initial]
  | @tail s s' hprev hstep ih =>
    have hinv := OptInnerRun.working_union_done_subset_antichain hprev
    obtain ⟨p, hp, _, hw, ha, hd⟩ := hstep
    rw [Set.disjoint_left]
    rintro x hx hxd
    rw [hw] at hx
    rw [hd] at hxd
    rcases hx with ⟨hxw, hxp⟩ | hxnew
    · rcases hxd with rfl | hxd
      · exact hxp rfl
      · exact (Set.disjoint_left.mp ih) hxw hxd
    · obtain ⟨⟨a, hTr⟩, hncov, _⟩ := hxnew
      apply hncov
      rcases hxd with rfl | hxd
      · exact AntichainMem.self (hinv (Or.inl hp))
      · exact AntichainMem.self (hinv (Or.inr hxd))

/-- The termination measure of one inner step: `done` strictly grows. -/
theorem OptInnerStep.measure_lt [HasTau Label] [Finite State1] [Finite State2]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {s s' : AlgState State2 State1}
    (h : OptInnerStep lts1 lts2 pos neg s s') (hdisj : Disjoint s.working s.done) :
    s'.measure < s.measure := by
  obtain ⟨p, hp, _, _, _, hd⟩ := h
  have hpd : p ∉ s.done := Set.disjoint_left.mp hdisj hp
  have hsub : (Set.univ \ s'.done) ⊆ (Set.univ \ s.done) := by
    rw [hd]; exact Set.sdiff_subset_sdiff_right (Set.subset_insert p s.done)
  have hpmem : p ∈ (Set.univ \ s.done) := ⟨Set.mem_univ p, hpd⟩
  have hpnotmem : p ∉ (Set.univ \ s'.done) := by rw [hd]; simp
  have hssub : (Set.univ \ s'.done) ⊂ (Set.univ \ s.done) :=
    lt_of_le_of_ne hsub (fun heq => hpnotmem (heq ▸ hpmem))
  exact Set.ncard_lt_ncard hssub

/-- Every pair in the antichain of a run from the initial configuration is reachable from it. -/
theorem OptInnerRun.antichain_subset_canReach [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {p0 : Set State2 × State1}
    {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c) :
    c.antichain ⊆ { q | (product (NormTr lts2) lts1).CanReach p0 q } := by
  induction h with
  | refl => simp [AlgState.initial, Cslib.LTS.CanReach.refl]
  | @tail s s' hprev hstep ih =>
    have hinv := OptInnerRun.working_union_done_subset_antichain hprev
    obtain ⟨p, hp, _, hw, ha, _⟩ := hstep
    rw [ha]
    rintro x (hx | ⟨⟨a, hTr⟩, _⟩)
    · exact ih hx
    · have hpr : (product (NormTr lts2) lts1).CanReach p0 p := ih (hinv (Or.inl hp))
      obtain ⟨σ, hσ⟩ := hpr
      exact ⟨σ ++ [a], Cslib.LTS.MTr.stepR (product (NormTr lts2) lts1) hσ hTr⟩

/-- **Invariant, part 2** (converse of part 1). Everything in the antichain is in `working` or
    `done`: combined with part 1, `antichain = working ∪ done` always. -/
theorem OptInnerRun.antichain_subset_working_union_done [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {p0 : Set State2 × State1}
    {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c) :
    c.antichain ⊆ c.working ∪ c.done := by
  induction h with
  | refl => simp [AlgState.initial]
  | @tail s s' _ hstep ih =>
    obtain ⟨p, hp, _, hw, ha, hd⟩ := hstep
    rw [ha, hw, hd]
    rintro x (hx | hx)
    · rcases ih hx with hx | hx
      · by_cases hxp : x = p
        · exact Or.inr (Or.inl hxp)
        · exact Or.inl (Or.inl ⟨hx, hxp⟩)
      · exact Or.inr (Or.inr hx)
    · exact Or.inl (Or.inr hx)

/-- At a terminal configuration of a run from the initial configuration, the antichain coincides
    with `done`. -/
theorem OptInnerRun.terminal_antichain_eq_done [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {p0 : Set State2 × State1}
    {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c)
    (hterm : c.Terminal) : c.antichain = c.done := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases OptInnerRun.antichain_subset_working_union_done h hx with hx | hx
    · rw [hterm] at hx; exact hx.elim
    · exact hx
  · intro x hx
    exact OptInnerRun.working_union_done_subset_antichain h (Or.inr hx)

/-- **Saturation, inner variant.** The successors of a popped pair are either covered by the
    antichain or covered by the positive antichain: `optNewSuccessors` only ever drops pairs the
    exploration pruned against `pos`. Unlike `AlgRun.done_successors_covered` this needs no
    hypothesis about the popped pair beyond it being in `done`. -/
theorem OptInnerRun.done_successors_covered [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {p0 : Set State2 × State1}
    {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c) :
    ∀ p ∈ c.done, ∀ a q, (product (NormTr lts2) lts1).Tr p a q →
      AntichainMem c.antichain q ∨ AntichainMem pos q := by
  induction h with
  | refl => simp [AlgState.initial]
  | @tail s s' _ hstep ih =>
    have hmono_step := OptInnerStep.antichain_subset hstep
    obtain ⟨p, hp, _, hw, ha, hd⟩ := hstep
    intro p' hp' a q hTr
    rw [hd] at hp'
    rcases hp' with rfl | hp'
    · by_cases hcov : AntichainMem s.antichain q
      · exact Or.inl (AntichainMem.mono hmono_step hcov)
      · by_cases hposq : AntichainMem pos q
        · exact Or.inr hposq
        · have hnew : q ∈ optNewSuccessors lts1 lts2 pos s.antichain p' :=
            ⟨⟨a, hTr⟩, hcov, hposq⟩
          rw [ha]
          exact Or.inl (AntichainMem.self (Or.inr hnew))
    · rcases ih p' hp' a q hTr with h | h
      · exact Or.inl (AntichainMem.mono hmono_step h)
      · exact Or.inr h

/-- No pair of the antichain of a run is a TR-witness, provided the start pair is not one: the
    start pair is the (never empty) normal form of `impl`, and every later pair was added as a
    successor that passed the `¬ InnerFailing` guard. -/
theorem OptInnerRun.not_TRWitness [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)} {p0 : Set State2 × State1}
    (hp0 : ¬ IsTRWitness p0.1 p0.2)
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c) :
    ∀ x ∈ c.antichain, ¬ IsTRWitness x.1 x.2 := by
  induction h with
  | refl =>
    intro x hx
    simp only [AlgState.initial] at hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hp0
  | @tail s s' _ hstep ih =>
    obtain ⟨p, hp, hguard, hw, ha, _⟩ := hstep
    intro x hx
    rw [ha] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · obtain ⟨⟨a, hTr⟩, _, _⟩ := hx
      intro hwit
      exact hguard x ⟨a, hTr⟩ (Or.inr hwit)

/-- **Saturation for Algorithm 5.** At a terminal configuration, every pair reachable from the
    start is either covered by the antichain, or lies in the shadow of the positive antichain
    (no TR-witness is reachable from it). The second disjunct is what the extra
    `¬ AntichainMem pos q` conjunct of `optNewSuccessors` buys us: pairs pruned against `pos` are
    not discovered, but `PosSound` tells us exactly what we need about them. -/
theorem OptInnerRun.covered_or_noWitness [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)}
    (hpos : PosSound lts1 lts2 pos)
    {p0 : Set State2 × State1} {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c)
    (hterm : c.Terminal) :
    ∀ q, (product (NormTr lts2) lts1).CanReach p0 q →
      AntichainMem c.antichain q ∨
        ¬ ∃ w, (product (NormTr lts2) lts1).CanReach q w ∧ IsTRWitness w.1 w.2 := by
  have hdone_eq := OptInnerRun.terminal_antichain_eq_done h hterm
  have hmono := normTr_isMonotone lts2
  rintro q ⟨σ, hσ⟩
  induction σ using List.reverseRecOn generalizing q with
  | nil =>
    obtain rfl := Cslib.LTS.MTr.nil_eq (product (NormTr lts2) lts1) hσ
    exact Or.inl (AntichainMem.self
      (OptInnerRun.antichain_subset h (by simp [AlgState.initial])))
  | append_singleton σ' a ih =>
    obtain ⟨q', hq'1, hq'2⟩ := (Cslib.LTS.MTr.append_iff _).mp hσ
    have hTr : (product (NormTr lts2) lts1).Tr q' a q :=
      (Cslib.LTS.MTr.singleton_iff _ _ _ _).mp hq'2
    rcases ih q' hq'1 with hcov | hnow
    · obtain ⟨z, hzA, hzle⟩ := hcov
      have hzdone : z ∈ c.done := hdone_eq ▸ hzA
      obtain ⟨z', hz'step, hz'le⟩ :=
        hmono.simulate lts1 hzle (Cslib.LTS.MTr.single (product (NormTr lts2) lts1) hTr)
      have hzTr : (product (NormTr lts2) lts1).Tr z a z' :=
        (Cslib.LTS.MTr.singleton_iff _ _ _ _).mp hz'step
      rcases OptInnerRun.done_successors_covered h z hzdone a z' hzTr with hcov' | hposz'
      · obtain ⟨w, hwA, hwz'⟩ := hcov'
        exact Or.inl ⟨w, hwA, hwz'.trans hz'le⟩
      · obtain ⟨y, hypos, hyle⟩ := hposz'
        refine Or.inr fun ⟨w, hreach, hwit⟩ => ?_
        obtain ⟨w', hw'reach, hw'le⟩ :=
          productLE_canReach hmono lts1 (hyle.trans hz'le) hreach
        exact hpos y ⟨y, hypos, ProductLE.refl _⟩
          ⟨w', hw'reach, IsTRWitness.antitone hw'le hwit⟩
    · refine Or.inr fun ⟨w, hreach, hwit⟩ => hnow ⟨w, canReach_trans ⟨[a], hq'2⟩ hreach, hwit⟩

/-- **Proposition 3, `true` verdicts.** If the inner exploration runs dry without aborting, no
    TR-witness is reachable from the initial pair - i.e. the verdict is correct. -/
theorem OptInnerRun.no_witness [HasTau Label]
    {lts1 : LTS State1 Label} {lts2 : LTS State2 Label}
    {pos neg : Set (Set State2 × State1)}
    (hpos : PosSound lts1 lts2 pos) {p0 : Set State2 × State1}
    (hp0 : ¬ IsTRWitness p0.1 p0.2) {c : AlgState State2 State1}
    (h : Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg) (AlgState.initial p0) c)
    (hterm : c.Terminal) :
    ¬ ∃ q, (product (NormTr lts2) lts1).CanReach p0 q ∧ IsTRWitness q.1 q.2 := by
  rintro ⟨q, hreach, hwit⟩
  rcases OptInnerRun.covered_or_noWitness hpos h hterm q hreach with hcov | hnow
  · obtain ⟨z, hzA, hzle⟩ := hcov
    exact OptInnerRun.not_TRWitness hp0 h z hzA (IsTRWitness.antitone hzle hwit)
  · exact hnow ⟨q, Cslib.LTS.CanReach.refl (product (NormTr lts2) lts1) q, hwit⟩

/-- **Proposition 3, existence part.** Algorithm 5 always returns a verdict: from the initial
    configuration the exploration either aborts on a failing successor, or runs dry (the measure
    `|univ \ done|` strictly decreases on every iteration). -/
theorem weakTraceOpt_terminates [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Set (Set State2 × State1)) (t : State1) (impl : State2) :
    ∃ b pos' neg', WeakTraceOpt lts1 lts2 pos neg t impl b pos' neg' := by
  by_cases hpos0 : AntichainMem pos (NormInit lts2 impl, t)
  · exact ⟨true, pos, neg, .cachedTrue hpos0⟩
  by_cases hneg0 : NegMem neg (NormInit lts2 impl, t)
  · exact ⟨false, pos, neg, .cachedFalse hpos0 hneg0⟩
  have key : ∀ n c, c.measure = n →
      Relation.ReflTransGen (OptInnerStep lts1 lts2 pos neg)
        (AlgState.initial (NormInit lts2 impl, t)) c →
      ∃ b pos' neg', WeakTraceOpt lts1 lts2 pos neg t impl b pos' neg' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hcn hrun
      by_cases hw : c.working = ∅
      · exact ⟨true, pos ∪ c.antichain, neg, .exploredTrue hpos0 hneg0 hrun hw⟩
      · obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hw
        by_cases hf : ∃ q a, (product (NormTr lts2) lts1).Tr p a q ∧ InnerFailing neg q
        · obtain ⟨q, a, hTr, hfq⟩ := hf
          exact ⟨false, pos, NegInsert neg (NormInit lts2 impl, t),
            .exploredFalse hpos0 hneg0 hrun hp ⟨q, ⟨a, hTr⟩, hfq⟩⟩
        · set c2 : AlgState State2 State1 :=
            { working := (c.working \ {p}) ∪ optNewSuccessors lts1 lts2 pos c.antichain p
              antichain := c.antichain ∪ optNewSuccessors lts1 lts2 pos c.antichain p
              done := insert p c.done }
          have hstep : OptInnerStep lts1 lts2 pos neg c c2 :=
            ⟨p, hp, fun q ⟨a, hTr⟩ hfq => hf ⟨q, a, hTr, hfq⟩, rfl, rfl, rfl⟩
          have hlt : c2.measure < c.measure :=
            OptInnerStep.measure_lt hstep (OptInnerRun.disjoint_working_done hrun)
          exact ih c2.measure (hcn ▸ hlt) c2 rfl (Relation.ReflTransGen.tail hrun hstep)
  exact key _ _ rfl Relation.ReflTransGen.refl

/-- **Proposition 3.** Algorithm 5's verdict is weak trace inclusion, it terminates, and the
    positive/negative antichains stay sound. -/
theorem weakTraceOpt_correct [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (pos neg : Set (Set State2 × State1)) (hpos : PosSound lts1 lts2 pos)
    (hneg : NegSound lts1 lts2 neg) (t : State1) (impl : State2) :
    WeakTraceOptCorrectSpec lts1 lts2 pos neg hpos hneg t impl := by
  refine ⟨weakTraceOpt_terminates lts1 lts2 pos neg t impl, fun b pos' neg' hopt => ?_⟩
  have key_tr : (impl ⊑tr[lts2,lts1] t) ↔
      ¬ ∃ q, (product (NormTr lts2) lts1).CanReach (NormInit lts2 impl, t) q ∧
        IsTRWitness q.1 q.2 :=
    ⟨fun h hnq => (traceRefines_iff_not_reachable_trWitness lts2 impl lts1 t).mp h
        (Prod.exists.mp hnq),
     fun hnq => (traceRefines_iff_not_reachable_trWitness lts2 impl lts1 t).mpr
        fun hB => hnq (Prod.exists.mpr hB)⟩
  have hp0 : ¬ IsTRWitness (NormInit lts2 impl) t := by
    intro h
    have h0 : NormInit lts2 impl = ∅ := h
    exact (Set.eq_empty_iff_forall_notMem.mp h0) impl (WeakTr.refl impl)
  induction hopt with
  | cachedTrue h =>
    exact ⟨⟨fun _ => key_tr.mpr (hpos _ h), fun _ => rfl⟩, hpos, hneg⟩
  | cachedFalse _h1 h2 =>
    exact ⟨⟨fun h => absurd h Bool.false_ne_true,
      fun href => (key_tr.mp href (hneg _ h2)).elim⟩, hpos, hneg⟩
  | @exploredTrue c _ _ hrun hterm =>
    have hno := OptInnerRun.no_witness hpos hp0 hrun hterm
    have hpos' : PosSound lts1 lts2 (pos ∪ c.antichain) := by
      intro x hx
      obtain ⟨y, hy, hyle⟩ := hx
      rcases hy with hy | hy
      · rintro ⟨q, hreach, hwit⟩
        obtain ⟨q', hw'reach, hw'le⟩ :=
          productLE_canReach (normTr_isMonotone lts2) lts1 hyle hreach
        exact hpos y ⟨y, hy, ProductLE.refl _⟩
          ⟨q', hw'reach, IsTRWitness.antitone hw'le hwit⟩
      · rintro ⟨q, hreach, hwit⟩
        obtain ⟨q', hw'reach, hw'le⟩ :=
          productLE_canReach (normTr_isMonotone lts2) lts1 hyle hreach
        exact hno ⟨q', canReach_trans
          (OptInnerRun.antichain_subset_canReach hrun hy) hw'reach,
          IsTRWitness.antitone hw'le hwit⟩
    exact ⟨⟨fun _ => key_tr.mpr hno, fun _ => rfl⟩, hpos', hneg⟩
  | @exploredFalse c p _ _ hrun hp hf =>
    obtain ⟨q, ⟨a, hTr⟩, hfq⟩ := hf
    have hq0 : (product (NormTr lts2) lts1).CanReach (NormInit lts2 impl, t) q :=
      canReach_trans
        (OptInnerRun.antichain_subset_canReach hrun
          (OptInnerRun.working_union_done_subset_antichain hrun (Or.inl hp)))
        ⟨[a], Cslib.LTS.MTr.single (product (NormTr lts2) lts1) hTr⟩
    have hwit0 : ∃ q, (product (NormTr lts2) lts1).CanReach (NormInit lts2 impl, t) q ∧
        IsTRWitness q.1 q.2 := by
      rcases hfq with hn | hmem
      · obtain ⟨w, hwreach, hwit⟩ := hneg _ hn
        exact ⟨w, canReach_trans hq0 hwreach, hwit⟩
      · exact ⟨q, hq0, hmem⟩
    have hneg' : NegSound lts1 lts2 (NegInsert neg (NormInit lts2 impl, t)) := by
      intro z hz
      obtain ⟨y, hy, hyz⟩ := hz
      rcases hy with rfl | ⟨hyn, hynle⟩
      · obtain ⟨w, hwreach, hwit⟩ := hwit0
        obtain ⟨w', hw'reach, hw'le⟩ :=
          productLE_canReach (normTr_isMonotone lts2) lts1 hyz hwreach
        exact ⟨w', hw'reach, IsTRWitness.antitone hw'le hwit⟩
      · exact hneg z ⟨y, hyn, hyz⟩
    exact ⟨⟨fun h => absurd h Bool.false_ne_true,
      fun href => (key_tr.mp href hwit0).elim⟩, hpos, hneg'⟩

/-- The empty antichains are sound (the initial values on line 4 of Algorithm 6). -/
theorem posSound_empty [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    PosSound lts1 lts2 (∅ : Set (Set State2 × State1)) := by
  rintro x ⟨y, hy, _⟩
  exact (Set.mem_empty_iff_false y).mp hy |>.elim

theorem negSound_empty [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    NegSound lts1 lts2 (∅ : Set (Set State2 × State1)) := by
  rintro x ⟨y, hy, _⟩
  exact (Set.mem_empty_iff_false y).mp hy |>.elim

/-- Every finite set is enumerated by its `toFinset` list. -/
theorem Enumerates_finite [Finite State1] [HasTau Label]
    (_lts1 : LTS State1 Label) (_lts2 : LTS State2 Label) (U : Set State1) :
    ∃ ts, Enumerates ts U := by
  have hfin : U.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ U)
  refine ⟨hfin.toFinset.toList, Finset.nodup_toList _, ?_⟩
  intro t
  rw [Finset.mem_toList, Set.Finite.mem_toFinset hfin]

/-- A `CheckLoop` returning `true` means every element of `ts` is not refined;
returning `false` means the loop preserves soundness (Lemma 15 of the report). -/
theorem checkLoop_verdict [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (s : State2)
    (ts : List State1) (pos neg : Set (Set State2 × State1)) (b : Bool)
    (pos' neg' : Set (Set State2 × State1))
    (h : CheckLoop lts1 lts2 s ts pos neg b pos' neg') :
    PosSound lts1 lts2 pos → NegSound lts1 lts2 neg →
    (b = true ↔ ∀ t ∈ ts, ¬ (s ⊑tr[lts2,lts1] t)) ∧ PosSound lts1 lts2 pos' ∧ NegSound lts1 lts2 neg' := by
  induction h with
  | nil =>
    intro hpos hneg
    exact ⟨⟨fun _ t ht => absurd ht (List.not_mem_nil (a := t)), fun _ => rfl⟩, hpos, hneg⟩
  | @pass t ts pos neg pos' neg' hwt =>
    intro hpos hneg
    have spec := (weakTraceOpt_correct lts1 lts2 pos neg hpos hneg t s).2 true pos' neg' hwt
    exact ⟨⟨fun hft => absurd hft Bool.false_ne_true,
      fun hall => False.elim (absurd (spec.1.mp rfl) (hall t List.mem_cons_self))⟩, spec.2.1, spec.2.2⟩
  | @fail t ts pos neg pos' neg' b pos'' neg'' hwt hloop ih =>
    intro hpos hneg
    have spec := (weakTraceOpt_correct lts1 lts2 pos neg hpos hneg t s).2 false pos' neg' hwt
    have ih' := ih spec.2.1 spec.2.2
    refine ⟨⟨?_, ?_⟩, ih'.2.1, ih'.2.2⟩
    · intro hb u hu
      rw [List.mem_cons] at hu
      rcases hu with rfl | hu
      · intro hsub
        exact Bool.false_ne_true (spec.1.mpr hsub)
      · exact ih'.1.mp hb u hu
    · intro hall
      exact ih'.1.mpr (fun u hu => hall u (List.mem_cons.mpr (Or.inr hu)))

/-- If every `t` is not refined, `CheckLoop` terminates with `true`. -/
theorem checkLoop_true_of_all_fail [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (s : State2) :
    ∀ pos neg, PosSound lts1 lts2 pos → NegSound lts1 lts2 neg →
    ∀ ts, (∀ u ∈ ts, ¬ (s ⊑tr[lts2,lts1] u)) →
      ∃ pos' neg', CheckLoop lts1 lts2 s ts pos neg true pos' neg' := by
  intro pos neg hpos hneg ts
  induction ts generalizing pos neg with
  | nil => intro hall; exact ⟨pos, neg, CheckLoop.nil⟩
  | cons t ts ih =>
    intro hall
    obtain ⟨b, pos', neg', hwt⟩ := weakTraceOpt_terminates lts1 lts2 pos neg t s
    by_cases hb : b = true
    · rw [hb] at hwt
      have spec := (weakTraceOpt_correct lts1 lts2 pos neg hpos hneg t s).2 true pos' neg' hwt
      exact False.elim (absurd (spec.1.mp rfl) (hall t List.mem_cons_self))
    · have hbf : b = false := Bool.eq_false_of_not_eq_true hb
      rw [hbf] at hwt
      have spec := (weakTraceOpt_correct lts1 lts2 pos neg hpos hneg t s).2 false pos' neg' hwt
      obtain ⟨pos'', neg'', hloop⟩ := ih pos' neg' spec.2.1 spec.2.2
        (fun u hu => hall u (List.mem_cons.mpr (Or.inr hu)))
      exact ⟨pos'', neg'', CheckLoop.fail hwt hloop⟩

/-- If `CheckLoop` cannot return `true`, it instead returns `false` with new sound sets. -/
theorem checkLoop_false_of_not_true [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (s : State2) :
    ∀ pos neg, PosSound lts1 lts2 pos → NegSound lts1 lts2 neg →
    ∀ ts, ¬ (∃ pos' neg', CheckLoop lts1 lts2 s ts pos neg true pos' neg') →
      ∃ pos' neg', CheckLoop lts1 lts2 s ts pos neg false pos' neg' := by
  intro pos neg hpos hneg ts
  induction ts generalizing pos neg with
  | nil =>
    intro hnot
    exact False.elim (hnot ⟨pos, neg, CheckLoop.nil⟩)
  | cons t ts ih =>
    intro hnot
    obtain ⟨b, pos', neg', hwt⟩ := weakTraceOpt_terminates lts1 lts2 pos neg t s
    by_cases hb : b = true
    · rw [hb] at hwt
      exact ⟨pos', neg', CheckLoop.pass hwt⟩
    · have hbf : b = false := Bool.eq_false_of_not_eq_true hb
      rw [hbf] at hwt
      have spec := (weakTraceOpt_correct lts1 lts2 pos neg hpos hneg t s).2 false pos' neg' hwt
      obtain ⟨pos'', neg'', hloop⟩ := ih pos' neg' spec.2.1 spec.2.2
        (fun ⟨p, n, hl⟩ => hnot ⟨p, n, CheckLoop.fail hwt hl⟩)
      exact ⟨pos'', neg'', CheckLoop.fail hwt hloop⟩

/-- A stable-IF witness discovered during the traversal makes the algorithm fail at `p`. -/
theorem isStableIFWitness_optFailsAt [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    {s : OptState State1 State2} {p : Set State1 × State2}
    (hpos : PosSound lts1 lts2 s.pos) (hneg : NegSound lts1 lts2 s.neg)
    (hw : IsStableIFWitness lts1 lts2 p.1 p.2) :
    OptFailsAt lts1 lts2 s p := by
  rcases hw with hU | ⟨hstab, hmem⟩
  · by_cases hst : Stable lts2 p.2
    · refine Or.inr ⟨hst, [], ⟨List.nodup_nil, ?_⟩, s.pos, s.neg, CheckLoop.nil⟩
      intro t
      simp [hU]
    · have hout : lts2.HasOutLabel p.2 HasTau.τ := by
        by_contra hno
        exact hst (by simpa [Stable] using hno)
      obtain ⟨p2', hτ⟩ := hout
      exact Or.inl ⟨(p.1, p2'), ⟨HasTau.τ, Or.inl ⟨rfl, rfl, hτ⟩⟩, hU⟩
  · obtain ⟨ts, henum⟩ := Enumerates_finite lts1 lts2 p.1
    obtain ⟨pos', neg', hloop⟩ :=
      checkLoop_true_of_all_fail lts1 lts2 p.2 s.pos s.neg hpos hneg ts
        (fun u (hu : u ∈ ts) => hmem u ((henum.2 u).mp hu))
    exact Or.inr ⟨hstab, ts, henum, pos', neg', hloop⟩

theorem OptAlgRun.working_canReach [HasTau Label]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    {p0 : Set State1 × State2} {s : OptState State1 State2}
    (h : OptAlgRun lts1 lts2 (OptState.initial p0) s) :
    ∀ x ∈ s.core.working, (product (NormTr lts1) lts2).CanReach p0 x := by
  induction h with
  | refl =>
    intro x hx
    simp [OptState.initial, AlgState.initial] at hx
    subst hx
    exact Cslib.LTS.CanReach.refl (product (NormTr lts1) lts2) _
  | @tail s0 s1 _ hstep ih =>
    obtain ⟨p, hp, _, _, _, hw, _, _⟩ := hstep
    intro x hx
    rw [hw] at hx
    rcases hx with hx | hx
    · exact ih x hx.1
    · obtain ⟨⟨a, hTr⟩, _⟩ := hx
      exact canReach_trans (ih p hp) ⟨[a], Cslib.LTS.MTr.single (product (NormTr lts1) lts2) hTr⟩

theorem OptAlgRun.sound [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    {p0 : Set State1 × State2} {s : OptState State1 State2}
    (h : OptAlgRun lts1 lts2 (OptState.initial p0) s) :
    PosSound lts1 lts2 s.pos ∧ NegSound lts1 lts2 s.neg := by
  induction h with
  | refl =>
    exact ⟨posSound_empty lts1 lts2, negSound_empty lts1 lts2⟩
  | @tail s0 s1 _ hstep ih =>
    obtain ⟨p, _, _, hstab, hnst, _, _, _⟩ := hstep
    by_cases hst : Stable lts2 p.2
    · obtain ⟨ts, henum, hloop⟩ := hstab hst
      have hv := checkLoop_verdict lts1 lts2 p.2 ts s0.pos s0.neg false s1.pos s1.neg hloop ih.1 ih.2
      exact ⟨hv.2.1, hv.2.2⟩
    · obtain ⟨hp', hn'⟩ := hnst hst
      rw [hp', hn']
      exact ih

/-- One algorithm step can be lifted: either it already failed on `st` or it is simulated
on a fresh `OptState` (AlgorithmOpt lifting lemma). -/
theorem optState_lift_step [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    {p0 : Set State1 × State2} {s s' : AlgState State1 State2} {st : OptState State1 State2}
    (hstep : AlgStep (NormTr lts1) lts2 s s')
    (hcore : st.core = s)
    (hpos : PosSound lts1 lts2 st.pos) (hneg : NegSound lts1 lts2 st.neg)
    (hrun : OptAlgRun lts1 lts2 (OptState.initial p0) st) :
    OptFoundFailure lts1 lts2 p0 ∨
      ∃ st', OptAlgRun lts1 lts2 (OptState.initial p0) st' ∧ st'.core = s' ∧
        PosSound lts1 lts2 st'.pos ∧ NegSound lts1 lts2 st'.neg := by
  classical
  have hstep' : AlgStep (NormTr lts1) lts2 st.core s' := by simpa [hcore] using hstep
  obtain ⟨p, hp, hw, ha, hd⟩ := hstep'
  by_cases hfail : OptFailsAt lts1 lts2 st p
  · exact Or.inl ⟨st, hrun, p, hp, hfail⟩
  by_cases hst : Stable lts2 p.2
  · obtain ⟨ts, henum⟩ := Enumerates_finite lts1 lts2 p.1
    by_cases htru : ∃ pos' neg', CheckLoop lts1 lts2 p.2 ts st.pos st.neg true pos' neg'
    · obtain ⟨pos₀, neg₀, hloop⟩ := htru
      exact Or.inl ⟨st, hrun, p, hp, Or.inr ⟨hst, ts, henum, pos₀, neg₀, hloop⟩⟩
    · obtain ⟨pos', neg', hloop⟩ :=
        checkLoop_false_of_not_true lts1 lts2 p.2 st.pos st.neg hpos hneg ts htru
      have hv := checkLoop_verdict lts1 lts2 p.2 ts st.pos st.neg false pos' neg' hloop hpos hneg
      refine Or.inr ⟨{ core := s', pos := pos', neg := neg' }, ?_, rfl, hv.2.1, hv.2.2⟩
      exact Relation.ReflTransGen.tail hrun
        ⟨p, hp, hfail, fun _ => ⟨ts, henum, hloop⟩,
          fun hns => False.elim (absurd hst hns), hw, ha, hd⟩
  · refine Or.inr ⟨{ core := s', pos := st.pos, neg := st.neg }, ?_, rfl, hpos, hneg⟩
    exact Relation.ReflTransGen.tail hrun
      ⟨p, hp, hfail, fun hstab => False.elim (absurd hstab hst),
        fun _ => ⟨rfl, rfl⟩, hw, ha, hd⟩

/-- Whole-run lifting: soundness of step 2 of Algorithm 6. -/
theorem optState_lift [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    {p0 : Set State1 × State2} {c : AlgState State1 State2}
    (hrun : AlgRun (NormTr lts1) lts2 (AlgState.initial p0) c) :
    OptFoundFailure lts1 lts2 p0 ∨
      ∃ st, OptAlgRun lts1 lts2 (OptState.initial p0) st ∧ st.core = c ∧
        PosSound lts1 lts2 st.pos ∧ NegSound lts1 lts2 st.neg := by
  induction hrun with
  | refl =>
    exact Or.inr ⟨OptState.initial _, Relation.ReflTransGen.refl, rfl,
      posSound_empty lts1 lts2, negSound_empty lts1 lts2⟩
  | @tail s s' hprev hstep ih =>
    rcases ih with hfail | ⟨st, hrunS, hcore, hs1, hn1⟩
    · exact Or.inl hfail
    · rcases optState_lift_step lts1 lts2 hstep hcore hs1 hn1 hrunS with hfail | hgood
      · exact Or.inl hfail
      · exact Or.inr hgood

/-- If an `AlgRun` reaches a state marked done with a stable-IF witness on `p`, the
algorithm (lifted) eventually fails. -/
theorem algRun_catches_witness [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    {p0 : Set State1 × State2} {c : AlgState State1 State2}
    (hrun : AlgRun (NormTr lts1) lts2 (AlgState.initial p0) c)
    {p : Set State1 × State2} (hpdone : p ∈ c.done)
    (hpwit : IsStableIFWitness lts1 lts2 p.1 p.2) :
    OptFoundFailure lts1 lts2 p0 := by
  induction hrun with
  | refl => simp [AlgState.initial] at hpdone
  | @tail s s' hprev hstep ih =>
    obtain ⟨q, hq, _, _, hd⟩ := hstep
    rw [hd] at hpdone
    rcases Set.mem_insert_iff.mp hpdone with heq | hpdone
    · rw [← heq] at hq
      rcases optState_lift lts1 lts2 hprev with hfail | ⟨st, hrunS, hcore, hs1, hn1⟩
      · exact hfail
      · exact ⟨st, hrunS, p, (by simpa [hcore] using hq), isStableIFWitness_optFailsAt lts1 lts2 hs1 hn1 hpwit⟩
    · exact ih hpdone

/-- The algorithm finds a failure iff a stable-IF witness is reachable in the product. -/
theorem optFoundFailure_iff_exists_stableIFWitness [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (p0 : Set State1 × State2) :
    OptFoundFailure lts1 lts2 p0 ↔
      ∃ U s, (product (NormTr lts1) lts2).CanReach p0 (U, s) ∧ IsStableIFWitness lts1 lts2 U s := by
  constructor
  · rintro ⟨c, hrun, p, hpw, hfail⟩
    have hreach : (product (NormTr lts1) lts2).CanReach p0 p :=
      OptAlgRun.working_canReach lts1 lts2 hrun p hpw
    have hs := OptAlgRun.sound lts1 lts2 hrun
    rcases hfail with hA | hB
    · obtain ⟨q, ⟨a, hTr⟩, hq1⟩ := hA
      refine ⟨q.1, q.2,
        canReach_trans hreach ⟨[a], Cslib.LTS.MTr.single (product (NormTr lts1) lts2) hTr⟩, Or.inl hq1⟩
    · obtain ⟨hstab, ts, henum, pos', neg', hloop⟩ := hB
      have hv := checkLoop_verdict lts1 lts2 p.2 ts c.pos c.neg true pos' neg' hloop hs.1 hs.2
      refine ⟨p.1, p.2, hreach, Or.inr ⟨hstab, fun t (ht : t ∈ p.1) =>
        hv.1.mp rfl t ((henum.2 t).mpr ht)⟩⟩
  · rintro ⟨U, s, hreach, hwit⟩
    have hfw : FoundWitness (NormTr lts1) lts2 (IsStableIFWitness lts1 lts2) p0 :=
      (foundWitness_iff_exists_witness_finite (normTr_isMonotone lts1)
        (fun hle hw => IsStableIFWitness.antitone lts1 lts2 hle hw) p0).2 ⟨(U, s), hreach, hwit⟩
    rcases hfw with ⟨c, hrun, p, hpdone, hpwit⟩
    exact algRun_catches_witness lts1 lts2 hrun hpdone hpwit

/-- **Theorem 3.** Algorithm 6 is correct for finite LTSs with a convergent implementation. -/
theorem optImpossibleFutures_correct [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hconv : Convergent lts2) :
    OptImpossibleFuturesCorrectSpec lts1 s1 lts2 s2 hconv := by
  show (s1 ⊑if[lts1,lts2] s2) ↔ ¬ OptFoundFailure lts1 lts2 (NormInit lts1 s1, s2)
  rw [impossibleFuturesRefines_iff_not_reachable_ifWitness lts1 s1 lts2 s2,
    reachable_ifWitness_iff_reachable_stableIFWitness lts1 lts2 hconv (NormInit lts1 s1, s2),
    ← optFoundFailure_iff_exists_stableIFWitness lts1 lts2 (NormInit lts1 s1, s2)]

end Refinement

end AlgorithmOptProofs
