module

public import Mathlib.Data.Set.Card
public import Refinement.Semantics
public import Refinement.Product
public import Refinement.Antichain
public import Refinement.Algorithm
public import Refinement.Proofs.Antichain_Proofs
public import Refinement.Proofs.Product_Proofs

open Cslib (LTS HasTau)

@[expose] public section AlgorithmProofs

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

This file proves the algorithm's structural invariants, termination for finite `State1`/`State2`
(`AlgRun.terminates`, Theorem 5.6), and correctness: `foundWitness_iff_exists_witness` is
conditional on termination (useful on its own, since the correctness argument doesn't actually
need finiteness - only Proposition 5.8/Lemma 5.9, i.e. `IsMonotoneNormalForm` and witness
antitonicity); `foundWitness_iff_exists_witness_finite` discharges that premise via `AlgRun.terminates`
to give the unconditional statement (Theorem 5.2/5.14 in full) for finite `State1`/`State2`. -/

/-- A single step only ever adds to the antichain. -/
theorem AlgStep.antichain_subset [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {s s' : AlgState State1 State2}
    (h : AlgStep L1 lts2 s s') : s.antichain ⊆ s'.antichain := by
  obtain ⟨p, _, _, hac, _⟩ := h
  rw [hac]
  exact Set.subset_union_left

/-- Across a run, the antichain only grows. -/
theorem AlgRun.antichain_subset [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {s s' : AlgState State1 State2}
    (h : AlgRun L1 lts2 s s') : s.antichain ⊆ s'.antichain := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact ih.trans (AlgStep.antichain_subset hstep)

/-- **Invariant, part 1.** Everything in `working` or `done` is in the antichain. -/
theorem AlgRun.working_union_done_subset_antichain [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {p0 : Set State1 × State2}
    {c : AlgState State1 State2} (h : AlgRun L1 lts2 (AlgState.initial p0) c) :
    c.working ∪ c.done ⊆ c.antichain := by
  induction h with
  | refl => rintro x (hx | hx) <;> simp_all [AlgState.initial]
  | @tail s s' _ hstep ih =>
    have hmono_step := AlgStep.antichain_subset hstep
    obtain ⟨p, hp, hw, ha, hd⟩ := hstep
    rintro x (hx | hx)
    · rw [hw] at hx
      rcases hx with hx | hx
      · exact hmono_step (ih (Or.inl hx.1))
      · rw [ha]; exact Or.inr hx
    · rw [hd] at hx
      rcases hx with rfl | hx
      · exact hmono_step (ih (Or.inl hp))
      · exact hmono_step (ih (Or.inr hx))

/-- **Invariant, part 2** (converse of part 1). Everything in the antichain is in `working` or
    `done`: combined with part 1, `antichain = working ∪ done` always. -/
theorem AlgRun.antichain_subset_working_union_done [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {p0 : Set State1 × State2}
    {c : AlgState State1 State2} (h : AlgRun L1 lts2 (AlgState.initial p0) c) :
    c.antichain ⊆ c.working ∪ c.done := by
  induction h with
  | refl => simp [AlgState.initial]
  | @tail s s' _ hstep ih =>
    obtain ⟨p, hp, hw, ha, hd⟩ := hstep
    rw [ha, hw, hd]
    rintro x (hx | hx)
    · rcases ih hx with hx | hx
      · by_cases hxp : x = p
        · exact Or.inr (Or.inl hxp)
        · exact Or.inl (Or.inl ⟨hx, hxp⟩)
      · exact Or.inr (Or.inr hx)
    · exact Or.inl (Or.inr hx)

/-- **Invariant, part 3.** `working` and `done` are disjoint. -/
theorem AlgRun.disjoint_working_done [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {p0 : Set State1 × State2}
    {c : AlgState State1 State2} (h : AlgRun L1 lts2 (AlgState.initial p0) c) :
    Disjoint c.working c.done := by
  induction h with
  | refl => simp [AlgState.initial]
  | @tail s s' hprev hstep ih =>
    have hinv := AlgRun.working_union_done_subset_antichain hprev
    obtain ⟨p, hp, hw, ha, hd⟩ := hstep
    rw [Set.disjoint_left]
    rintro x hx hxd
    rw [hw] at hx
    rw [hd] at hxd
    rcases hx with ⟨hxw, hxp⟩ | hxnew
    · rcases hxd with rfl | hxd
      · exact hxp rfl
      · exact (Set.disjoint_left.mp ih) hxw hxd
    · obtain ⟨⟨a, hTr⟩, hncov⟩ := hxnew
      apply hncov
      rcases hxd with rfl | hxd
      · exact AntichainMem.self (hinv (Or.inl hp))
      · exact AntichainMem.self (hinv (Or.inr hxd))

/-- Every discovered state is reachable from `p0` in the product. -/
theorem AlgRun.antichain_subset_canReach [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {p0 : Set State1 × State2}
    {c : AlgState State1 State2} (h : AlgRun L1 lts2 (AlgState.initial p0) c) :
    c.antichain ⊆ { q | (product L1 lts2).CanReach p0 q } := by
  induction h with
  | refl => simp [AlgState.initial, Cslib.LTS.CanReach.refl]
  | @tail s s' hprev hstep ih =>
    have hinv := AlgRun.working_union_done_subset_antichain hprev
    obtain ⟨p, hp, _, ha, _⟩ := hstep
    rw [ha]
    rintro x (hx | ⟨⟨a, hTr⟩, _⟩)
    · exact ih hx
    · have hpr : (product L1 lts2).CanReach p0 p := ih (hinv (Or.inl hp))
      obtain ⟨σ, hσ⟩ := hpr
      exact ⟨σ ++ [a], Cslib.LTS.MTr.stepR (product L1 lts2) hσ hTr⟩

/-- **Key saturation ingredient.** Once a state has been popped into `done`, its successors are
    (eventually, hence - since the antichain only grows - forever after) covered by the
    antichain. -/
theorem AlgRun.done_successors_covered [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {p0 : Set State1 × State2}
    {c : AlgState State1 State2} (h : AlgRun L1 lts2 (AlgState.initial p0) c) :
    ∀ p ∈ c.done, ∀ a q, (product L1 lts2).Tr p a q → AntichainMem c.antichain q := by
  induction h with
  | refl => simp [AlgState.initial]
  | @tail s s' _ hstep ih =>
    have hmono_step := AlgStep.antichain_subset hstep
    obtain ⟨p, hp, hw, ha, hd⟩ := hstep
    intro p' hp' a q hTr
    rw [hd] at hp'
    rcases hp' with rfl | hp'
    · by_cases hcov : AntichainMem s.antichain q
      · exact AntichainMem.mono hmono_step hcov
      · have hnew : q ∈ newSuccessors L1 lts2 s.antichain p' := ⟨⟨a, hTr⟩, hcov⟩
        rw [ha]
        exact AntichainMem.self (Or.inr hnew)
    · exact AntichainMem.mono hmono_step (ih p' hp' a q hTr)

/-- At a terminal state, `antichain = done` exactly: nothing is left in `working` to account for
    the difference with the general `antichain = working ∪ done` invariant. -/
theorem AlgRun.terminal_antichain_eq_done [HasTau Label]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {p0 : Set State1 × State2}
    {c : AlgState State1 State2} (h : AlgRun L1 lts2 (AlgState.initial p0) c)
    (hterm : c.Terminal) : c.antichain = c.done := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases AlgRun.antichain_subset_working_union_done h hx with hx | hx
    · rw [hterm] at hx; exact hx.elim
    · exact hx
  · intro x hx
    exact AlgRun.working_union_done_subset_antichain h (Or.inr hx)

/-- **Saturation.** Once the algorithm has terminated, every state reachable from `p0` in
    `L1 ⋉ L2` is covered by the final antichain - the antichain-pruned exploration never misses a
    reachable state, it only ever avoids processing a *larger* representative of one already
    covered by a smaller one. -/
theorem AlgRun.saturated [HasTau Label]
    {L1 : LTS (Set State1) Label} (hmono : IsMonotoneNormalForm L1) {lts2 : LTS State2 Label}
    {p0 : Set State1 × State2} {c : AlgState State1 State2}
    (h : AlgRun L1 lts2 (AlgState.initial p0) c) (hterm : c.Terminal) :
    ∀ q, (product L1 lts2).CanReach p0 q → AntichainMem c.antichain q := by
  have hdone_eq := AlgRun.terminal_antichain_eq_done h hterm
  rintro q ⟨σ, hσ⟩
  induction σ using List.reverseRecOn generalizing q with
  | nil =>
    obtain rfl := Cslib.LTS.MTr.nil_eq (product L1 lts2) hσ
    exact AntichainMem.self (AlgRun.antichain_subset h (by simp [AlgState.initial]))
  | append_singleton σ' a ih =>
    obtain ⟨q', hq'1, hq'2⟩ := (Cslib.LTS.MTr.append_iff _).mp hσ
    obtain ⟨z, hzA, hzq'⟩ := ih q' hq'1
    have hTr : (product L1 lts2).Tr q' a q :=
      (Cslib.LTS.MTr.singleton_iff _ _ _ _).mp hq'2
    obtain ⟨z', hz'step, hz'le⟩ :=
      hmono.simulate lts2 hzq' (Cslib.LTS.MTr.single (product L1 lts2) hTr)
    have hzTr : (product L1 lts2).Tr z a z' := (Cslib.LTS.MTr.singleton_iff _ _ _ _).mp hz'step
    have hzdone : z ∈ c.done := hdone_eq ▸ hzA
    obtain ⟨w, hwA, hwz'⟩ := AlgRun.done_successors_covered h z hzdone a z' hzTr
    exact ⟨w, hwA, hwz'.trans hz'le⟩

/-- The termination measure (Theorem 5.6): the number of not-yet-discovered states. Needs
    `Set (Set State1 × State2)` to be a finite type - i.e. `Finite State1` and `Finite State2`,
    the paper's "finite state" hypothesis (`Set State1` is finite exactly when `State1` is, via
    `Set State1 ≃ (State1 → Prop)` and `Finite Prop`). -/
noncomputable def AlgState.measure [Finite State1] [Finite State2]
    (s : AlgState State1 State2) : ℕ := Set.ncard (Set.univ \ s.done)

/-- `done` strictly grows on every step - not just when new states are discovered, since the
    popped state itself always moves from `working` to `done`. This is what drives termination:
    unlike `antichain` (which may not grow when the step rediscovers nothing new), `done` always
    does. -/
theorem AlgStep.measure_lt [HasTau Label] [Finite State1] [Finite State2]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {s s' : AlgState State1 State2}
    (h : AlgStep L1 lts2 s s') (hdisj : Disjoint s.working s.done) :
    s'.measure < s.measure := by
  obtain ⟨p, hp, _, _, hd⟩ := h
  have hpd : p ∉ s.done := Set.disjoint_left.mp hdisj hp
  have hsub : (Set.univ \ s'.done) ⊆ (Set.univ \ s.done) := by
    rw [hd]; exact Set.sdiff_subset_sdiff_right (Set.subset_insert p s.done)
  have hpmem : p ∈ (Set.univ \ s.done) := ⟨Set.mem_univ p, hpd⟩
  have hpnotmem : p ∉ (Set.univ \ s'.done) := by rw [hd]; simp
  have hssub : (Set.univ \ s'.done) ⊂ (Set.univ \ s.done) :=
    lt_of_le_of_ne hsub (fun heq => hpnotmem (heq ▸ hpmem))
  exact Set.ncard_lt_ncard hssub

/-- **Theorem 5.6.** The algorithm terminates: for finite `State1`, `State2`, every run reaches a
    terminal state. -/
theorem AlgRun.terminates [HasTau Label] [Finite State1] [Finite State2]
    {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label} {p0 : Set State1 × State2}
    {c : AlgState State1 State2} (h : AlgRun L1 lts2 (AlgState.initial p0) c) :
    ∃ c', AlgRun L1 lts2 c c' ∧ c'.Terminal := by
  have key : ∀ n c, c.measure = n → AlgRun L1 lts2 (AlgState.initial p0) c →
      ∃ c', AlgRun L1 lts2 c c' ∧ c'.Terminal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hcn h
      by_cases hw : c.working = ∅
      · exact ⟨c, .refl, hw⟩
      · obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hw
        set c2 : AlgState State1 State2 :=
          { working := (c.working \ {p}) ∪ newSuccessors L1 lts2 c.antichain p
            antichain := c.antichain ∪ newSuccessors L1 lts2 c.antichain p
            done := insert p c.done } with hc2
        have hstep : AlgStep L1 lts2 c c2 := ⟨p, hp, rfl, rfl, rfl⟩
        have hlt : c2.measure < c.measure :=
          AlgStep.measure_lt hstep (AlgRun.disjoint_working_done h)
        obtain ⟨c', hc'run, hc'term⟩ :=
          ih c2.measure (hcn ▸ hlt) c2 rfl (Relation.ReflTransGen.tail h hstep)
        exact ⟨c', Relation.ReflTransGen.head hstep hc'run, hc'term⟩
  exact key c.measure c rfl h

/-- **Theorem 5.2/5.14, conditional on termination.** The algorithm finds a witness iff one is
    reachable, given that it does terminate (some run reaches a terminal state - see the
    file-level status note for why that premise isn't discharged here). Generic over `IsWitness`
    and the antitonicity it needs under `ProductLE`, so it specializes to TR/SF/FD-witnesses via
    `IsTRWitness.antitone`/`IsSFWitness.antitone`/`IsFDWitness.antitone` and, combined with
    Theorems 3.11/3.14/3.24, to trace/stable-failures/failures-divergences refinement. -/
theorem foundWitness_iff_exists_witness [HasTau Label]
    {L1 : LTS (Set State1) Label} (hmono : IsMonotoneNormalForm L1) {lts2 : LTS State2 Label}
    {IsWitness : Set State1 → State2 → Prop}
    (hantitone : ∀ {U V : Set State1} {s t : State2}, ProductLE (U, s) (V, t) →
      IsWitness V t → IsWitness U s)
    {p0 : Set State1 × State2}
    (hterminates : ∃ c, AlgRun L1 lts2 (AlgState.initial p0) c ∧ c.Terminal) :
    FoundWitness L1 lts2 IsWitness p0 ↔
      ∃ q, (product L1 lts2).CanReach p0 q ∧ IsWitness q.1 q.2 := by
  constructor
  · rintro ⟨c, hrun, p, hpdone, hpwit⟩
    exact ⟨p, AlgRun.antichain_subset_canReach hrun
      (AlgRun.working_union_done_subset_antichain hrun (Or.inr hpdone)), hpwit⟩
  · rintro ⟨q, hreach, hqwit⟩
    obtain ⟨c, hrun, hterm⟩ := hterminates
    obtain ⟨z, hzA, hzle⟩ := AlgRun.saturated hmono hrun hterm q hreach
    have hzdone : z ∈ c.done := AlgRun.terminal_antichain_eq_done hrun hterm ▸ hzA
    obtain ⟨z1, z2⟩ := z
    obtain ⟨q1, q2⟩ := q
    exact ⟨c, hrun, (z1, z2), hzdone, hantitone hzle hqwit⟩

/-- **Theorem 5.2/5.14, unconditional.** Combines `foundWitness_iff_exists_witness` with
    termination (`AlgRun.terminates`, Theorem 5.6) to drop the "assume termination" hypothesis:
    for finite `State1`/`State2`, the algorithm finds a witness iff one is reachable. -/
theorem foundWitness_iff_exists_witness_finite [HasTau Label] [Finite State1] [Finite State2]
    {L1 : LTS (Set State1) Label} (hmono : IsMonotoneNormalForm L1) {lts2 : LTS State2 Label}
    {IsWitness : Set State1 → State2 → Prop}
    (hantitone : ∀ {U V : Set State1} {s t : State2}, ProductLE (U, s) (V, t) →
      IsWitness V t → IsWitness U s)
    (p0 : Set State1 × State2) :
    FoundWitness L1 lts2 IsWitness p0 ↔
      ∃ q, (product L1 lts2).CanReach p0 q ∧ IsWitness q.1 q.2 :=
  foundWitness_iff_exists_witness hmono hantitone (AlgRun.terminates (L1 := L1) .refl)

/-- **Algorithm 4, correctness.** Trace refinement holds iff the algorithm - started from
    `(NormInit lts1 s1, s2)`, exploring `norm(L1) ⋉ L2` - never finds a TR-witness. -/
theorem traceRefines_iff_not_foundWitness [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑tr[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 IsTRWitness (NormInit lts1 s1, s2) := by
  rw [traceRefines_iff_not_reachable_trWitness,
    foundWitness_iff_exists_witness_finite (normTr_isMonotone lts1)
      (fun hle hwit => IsTRWitness.antitone hle hwit), Prod.exists]

/-- **Algorithm 5, correctness.** Stable failures refinement holds iff the algorithm - started
    from `(NormInit lts1 s1, s2)`, exploring `norm(L1) ⋉ L2` - never finds an SF-witness. -/
theorem stableFailuresRefines_iff_not_foundWitness [HasTau Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑sfr[lts1,lts2] s2) ↔
      ¬ FoundWitness (NormTr lts1) lts2 (IsSFWitness lts1 lts2) (NormInit lts1 s1, s2) := by
  rw [stableFailuresRefines_iff_not_reachable_sfWitness,
    foundWitness_iff_exists_witness_finite (normTr_isMonotone lts1)
      (fun hle hwit => IsSFWitness.antitone lts1 lts2 hle hwit), Prod.exists]

/-- **Algorithm 6, correctness.** Failures-divergences refinement holds iff the algorithm -
    started from `(NormInit lts1 s1, s2)`, exploring `normfdr(L1) ⋉ L2` - never finds an
    FD-witness. -/
theorem failuresDivergencesRefines_iff_not_foundWitness [HasTau Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (s1 ⊑fdr[lts1,lts2] s2) ↔
      ¬ FoundWitness (FdrNormTr lts1) lts2 (IsFDWitness lts1 lts2) (NormInit lts1 s1, s2) := by
  rw [failuresDivergencesRefines_iff_not_reachable_fdWitness,
    foundWitness_iff_exists_witness_finite (fdrNormTr_isMonotone lts1)
      (fun hle hwit => IsFDWitness.antitone lts1 lts2 hle hwit), Prod.exists]

end AlgorithmProofs
