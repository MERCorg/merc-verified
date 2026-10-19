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
/-- Lines 10-19 of Algorithm 5 as a recursive function: the `for` loop over the outgoing
    transitions of `impl` (a state of `lts1`), extending `working` and `antichain`. Returns `none`
    if line 16 fires. `forIn_outgoingOpt` relates it to the `for` loop of `weakTraceOpt`. -/
noncomputable def forSuccessorsOpt [HasTau Label] (lts2 : LTS State2 Label)
    (pos neg : Antichain (Set State2 × State1)) (spec : Set State2) :
    List (Label × State1) → List (Set State2 × State1) → Antichain (Set State2 × State1) →
      Option (List (Set State2 × State1) × Antichain (Set State2 × State1))
  | [], working, antichain => some (working, antichain)
  | (a, impl') :: rest, working, antichain =>
    let spec' := if a = HasTau.τ then spec else { s' | ∃ s ∈ spec, WeakTr lts2 s [a] s' }
    if (spec', impl') ⊑ neg ∨ spec' = ∅ then none
    else if ¬ (spec', impl') ⊑ antichain ∧ ¬ (spec', impl') ⊑ pos then
      forSuccessorsOpt lts2 pos neg spec rest ((spec', impl') :: working)
        (insert (spec', impl') antichain)
    else forSuccessorsOpt lts2 pos neg spec rest working antichain

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

/-! ### The loops of `weakTraceOpt` -/

/-- The state of the loops of `weakTraceOpt`: the value of a pending early `return`, `working`
    and `antichain`. -/
abbrev LoopState5 (State1 State2 : Type*) :=
  Option (Bool × Antichain (Set State2 × State1)) × List (Set State2 × State1) ×
    Antichain (Set State2 × State1)

open scoped Classical in
/-- One iteration of the `for` loop (lines 11-19) on the transition `impl -a-> t`. -/
noncomputable def succStepOpt [HasTau Label] (lts2 : LTS State2 Label)
    (init : Set State2 × State1) (pos neg : Antichain (Set State2 × State1)) (spec : Set State2)
    (a : Label) (t : State1) (w : List (Set State2 × State1))
    (A : Antichain (Set State2 × State1)) : ForInStep (LoopState5 State1 State2) :=
  if (succSpec lts2 spec a, t) ⊑ neg ∨ succSpec lts2 spec a = ∅ then
    .done (some (false, insert init neg), w, A)
  else if ¬ (succSpec lts2 spec a, t) ⊑ A ∧ ¬ (succSpec lts2 spec a, t) ⊑ pos then
    .yield (none, (succSpec lts2 spec a, t) :: w, insert (succSpec lts2 spec a, t) A)
  else .yield (none, w, A)

/-- The `for` loop (lines 10-19) computes `forSuccessorsOpt`. -/
theorem forIn_outgoingOpt [HasTau Label] {lts2 : LTS State2 Label} {init : Set State2 × State1}
    {pos neg : Antichain (Set State2 × State1)} {spec : Set State2}
    (g : Label × State1 → LoopState5 State1 State2 → Id (ForInStep (LoopState5 State1 State2)))
    (hg : ∀ a t w A, (g (a, t) (none, w, A)).run = succStepOpt lts2 init pos neg spec a t w A) :
    ∀ (l : List (Label × State1)) w A,
      match forSuccessorsOpt lts2 pos neg spec l w A with
      | none => (forIn l (none, w, A) g).run.1 = some (false, insert init neg)
      | some (w', A') => (forIn l (none, w, A) g).run = (none, w', A')
  | [], w, A => rfl
  | (a, t) :: rest, w, A => by
    rw [forSuccessorsOpt_cons]
    simp only [List.forIn_cons, Id.run_bind, hg, succStepOpt]
    by_cases h1 : (succSpec lts2 spec a, t) ⊑ neg ∨ succSpec lts2 spec a = ∅
    · simp only [eq_true h1, ↓reduceIte]
      rfl
    by_cases h2 : ¬ (succSpec lts2 spec a, t) ⊑ A ∧ ¬ (succSpec lts2 spec a, t) ⊑ pos
    · simp only [eq_false h1, eq_true h2, ↓reduceIte]
      exact forIn_outgoingOpt g hg rest _ _
    · simp only [eq_false h1, eq_false h2, ↓reduceIte]
      exact forIn_outgoingOpt g hg rest w A

theorem forIn_outgoingOpt_none [HasTau Label] {lts2 : LTS State2 Label}
    {init : Set State2 × State1} {pos neg : Antichain (Set State2 × State1)} {spec : Set State2}
    (g : Label × State1 → LoopState5 State1 State2 → Id (ForInStep (LoopState5 State1 State2)))
    (hg : ∀ a t w A, (g (a, t) (none, w, A)).run = succStepOpt lts2 init pos neg spec a t w A)
    {l : List (Label × State1)} {w A} (h : forSuccessorsOpt lts2 pos neg spec l w A = none) :
    (forIn l (none, w, A) g).run.1 = some (false, insert init neg) := by
  have := forIn_outgoingOpt g hg l w A
  rw [h] at this
  exact this

theorem forIn_outgoingOpt_some [HasTau Label] {lts2 : LTS State2 Label}
    {init : Set State2 × State1} {pos neg : Antichain (Set State2 × State1)} {spec : Set State2}
    (g : Label × State1 → LoopState5 State1 State2 → Id (ForInStep (LoopState5 State1 State2)))
    (hg : ∀ a t w A, (g (a, t) (none, w, A)).run = succStepOpt lts2 init pos neg spec a t w A)
    {l : List (Label × State1)} {w A w' A'}
    (h : forSuccessorsOpt lts2 pos neg spec l w A = some (w', A')) :
    (forIn l (none, w, A) g).run = (none, w', A') := by
  have := forIn_outgoingOpt g hg l w A
  rw [h] at this
  exact this

/-- The `for` loop does not increase `|pending antichain| + |working|`. -/
theorem forSuccessorsOpt_measure [HasTau Label] [Finite State1] [Finite State2]
    {lts2 : LTS State2 Label} {pos neg : Antichain (Set State2 × State1)} {spec : Set State2} :
    ∀ {l : List (Label × State1)} {w w' : List (Set State2 × State1)}
      {A A' : Antichain (Set State2 × State1)}, A.le = ProductLE →
      forSuccessorsOpt lts2 pos neg spec l w A = some (w', A') →
      (pending A').ncard + w'.length ≤ (pending A).ncard + w.length
  | [], w, w', A, A', _, h => by
    simp only [forSuccessorsOpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact le_rfl
  | (a, t) :: rest, w, w', A, A', hle, h => by
    rw [forSuccessorsOpt_cons] at h
    split_ifs at h with h1 h2
    · have ih := forSuccessorsOpt_measure (by rw [Antichain.le_insert]; exact hle) h
      have hlt : (pending (insert (succSpec lts2 spec a, t) A)).ncard < (pending A).ncard := by
        refine Set.ncard_lt_ncard ⟨fun x hx hxA => hx ?_, fun hsub => ?_⟩ (Set.toFinite _)
        · exact Antichain.mem_insert_of_mem (Antichain.le_trans_of_eq hle) hxA h2.1
        · exact hsub h2.1 (Antichain.mem_insert_self hle _)
      simp only [List.length_cons] at ih
      omega
    · exact forSuccessorsOpt_measure hle h

/-- The postcondition of the `while` loop of Algorithm 5 started from `init`. -/
def LoopPost5 [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (init : Set State2 × State1) (pos : Antichain (Set State2 × State1))
    (s : LoopState5 State1 State2) : Prop :=
  (∀ r, s.1 = some r → InnerOk lts1 lts2 init r) ∧
    (s.1 = none → InnerOk lts1 lts2 init (true, ⟨pos.le, pos.set ∪ s.2.2.set⟩))

/-- **Proposition 3**, for the whole of Algorithm 5 (including the cached answers of lines 2-5). -/
theorem weakTraceOpt_ok [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (pos neg : Antichain (Set State2 × State1))
    (hpos : PosSound lts1 lts2 pos) (hneg : NegSound lts1 lts2 neg) (t : State1)
    (impl : State2) :
    InnerOk lts1 lts2 (NormInit lts2 impl, t) (weakTraceOpt lts1 lts2 t impl pos neg) := by
  unfold weakTraceOpt
  dsimp only [Id.run_bind]
  by_cases h1 : (NormInit lts2 impl, t) ⊑ pos
  · -- line 3
    simp only [eq_true h1, ↓reduceIte]
    exact ⟨⟨fun _ => hpos.2 _ h1, fun _ => rfl⟩, by simpa using hpos⟩
  by_cases h2 : (NormInit lts2 impl, t) ⊑ neg
  · -- line 5
    simp only [eq_false h1, eq_true h2, ↓reduceIte]
    have hTR : TRReach lts1 lts2 (NormInit lts2 impl, t) := hneg.2 _ h2
    exact ⟨⟨fun hf => absurd hf Bool.false_ne_true, fun hn => absurd hTR hn⟩, by simpa using hneg⟩
  simp only [eq_false h1, eq_false h2, ↓reduceIte, Id.run_bind]
  generalize hres : (forIn (m := Id) Lean.Loop.mk _ _).run = res
  have key : LoopPost5 lts1 lts2 (NormInit lts2 impl, t) pos res := by
    rw [← hres]
    refine MercLib.Control.whileInduction _
      (InvImage.wf (fun s : LoopState5 State1 State2 => (pending s.2.2).ncard + s.2.1.length)
        Nat.lt_wfRel.wf)
      (fun s => s.1 = none ∧ ∃ done, ExploreInv (NormTr lts2) lts1 IsTRWitness (fun _ => False)
        (· ⊑ pos) (NormInit lts2 impl, t) done s.2.1 s.2.2)
      _ ?_ _ ⟨rfl, ∅, ExploreInv.initial ⟨impl, WeakTr.refl impl⟩⟩
    rintro ⟨r, w, A⟩ ⟨rfl, done, h⟩
    clear hres
    rcases w with _ | ⟨⟨spec, t'⟩, w⟩
    · -- line 20
      refine ⟨fun r hr => absurd hr nofun, fun _ => ?_⟩
      have hdone : ∀ y ∈ A.set, y ∈ done := fun y hy =>
        (h.set_sub y hy).resolve_left List.not_mem_nil
      have key : ∀ x, (∃ z ∈ done, ProductLE z x) → ¬ TRReach lts1 lts2 x := by
        rintro x hz ⟨q, ⟨σ, hq⟩, hw⟩
        exact h.safe (normTr_isMonotone lts2) (fun hle hw => IsTRWitness.antitone hle hw)
          (fun _ hp => hp) (fun _ hp => hp.elim) (fun x hx => hpos.2 x hx) hq hz id hw
      refine ⟨?_, ?_⟩
      · obtain ⟨y, hyA, hy⟩ := h.init
        rw [h.le_eq] at hy
        exact ⟨fun _ => key _ ⟨y, hdone y hyA, hy⟩, fun _ => rfl⟩
      · refine ⟨hpos.1, ?_⟩
        rintro x ⟨y, hy | hy, hyx⟩
        · exact hpos.2 x ⟨y, hy, hyx⟩
        · change pos.le y x at hyx
          rw [hpos.1] at hyx
          exact key x ⟨y, hdone y hy, hyx⟩
    rw [dite_eq_left (List.cons_ne_nil _ _)]
    dsimp +instances only [List.head_cons, List.tail_cons, Id.run_bind]
    rcases hfs : forSuccessorsOpt lts2 pos neg spec (outgoing lts1 t') w A with _ | ⟨w', A'⟩
    · -- line 16
      rw [forIn_outgoingOpt_none _ ?hg hfs]
      case hg => intro _ _ _ _; rfl
      refine ⟨fun r hr => ?_, fun hr => absurd hr nofun⟩
      cases hr
      obtain ⟨⟨a, t''⟩, hp, hbad⟩ := forSuccessorsOpt_none hfs
      have hreach := h.reach_succ (stepsBy_normTr lts2 spec) (mem_outgoing.mp hp)
      have hTR : TRReach lts1 lts2 (NormInit lts2 impl, t) := by
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
    · rw [forIn_outgoingOpt_some _ ?hg hfs]
      case hg => intro _ _ _ _; rfl
      refine ⟨⟨rfl, _, h.step (stepsBy_normTr lts2 spec) (fun _ => mem_outgoing)
        (fun he => (h.nonempty _ List.mem_cons_self).ne_empty he)
        (forSuccessorsOpt_some h.le_eq hfs)⟩, ?_⟩
      have := forSuccessorsOpt_measure h.le_eq hfs
      show _ + _ < _ + _
      simp only [List.length_cons] at this ⊢
      omega
  obtain ⟨k1, k2⟩ := key
  rcases hr : res.1 with _ | r
  · exact k2 hr
  · exact k1 r hr

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

open scoped Classical in
/-- Lines 8-14 of Algorithm 6 as a recursive function: pop the states `t` of `spec'` and call
    Algorithm 5 against `impl`. Returns the final `(b, antichain⁺, antichain⁻)`. `forIn_toList`
    relates it to the inner `for` loop of `weakImpossibleFuturesOpt`. -/
noncomputable def checkLoop (impl : State2) :
    List State1 → Bool → Antichain (Set State2 × State1) → Antichain (Set State2 × State1) →
      Bool × Antichain (Set State2 × State1) × Antichain (Set State2 × State1)
  | [], b, pos, neg => (b, pos, neg)
  | t :: spec', b, pos, neg =>
    if Stable lts2 impl ∧ b = true then
      match weakTraceOpt lts1 lts2 t impl pos neg with
      | (true, antichain') => checkLoop impl spec' false antichain' neg
      | (false, antichain') => checkLoop impl spec' b pos antichain'
    else (b, pos, neg)

/-- The state `(antichain⁻, antichain⁺, b)` of the inner `for` loop of Algorithm 6. -/
abbrev CheckState (State1 State2 : Type*) :=
  Antichain (Set State2 × State1) × Antichain (Set State2 × State1) × Bool

open scoped Classical in
/-- One iteration of the inner `for` loop (lines 8-14) on the state `t`. -/
noncomputable def checkStep (impl : State2) (t : State1) (s : CheckState State1 State2) :
    ForInStep (CheckState State1 State2) :=
  if ¬ (Stable lts2 impl ∧ s.2.2 = true) then .done s
  else
    match weakTraceOpt lts1 lts2 t impl s.2.1 s.1 with
    | (b', antichain') =>
      if b' = true then .yield (s.1, antichain', false) else .yield (antichain', s.2.1, s.2.2)

/-- The inner `for` loop (lines 8-14) computes `checkLoop`. -/
theorem forIn_toList (impl : State2)
    (g : State1 → CheckState State1 State2 → Id (ForInStep (CheckState State1 State2)))
    (hg : ∀ t s, (g t s).run = checkStep lts1 lts2 impl t s) :
    ∀ (ts : List State1) (neg pos : Antichain (Set State2 × State1)) (b : Bool),
      (forIn ts (neg, pos, b) g).run =
        ((checkLoop lts1 lts2 impl ts b pos neg).2.2, (checkLoop lts1 lts2 impl ts b pos neg).2.1,
          (checkLoop lts1 lts2 impl ts b pos neg).1)
  | [], _, _, _ => rfl
  | t :: ts, neg, pos, b => by
    simp only [List.forIn_cons, Id.run_bind, hg, checkStep]
    by_cases hc : Stable lts2 impl ∧ b = true
    · rcases hw : weakTraceOpt lts1 lts2 t impl pos neg with ⟨b', ac'⟩
      cases b'
      · simp only [eq_true hc, not_true_eq_false, ↓reduceIte, hw, Bool.false_eq_true, checkLoop]
        exact forIn_toList impl g hg ts ac' pos b
      · simp only [eq_true hc, not_true_eq_false, ↓reduceIte, hw, checkLoop]
        exact forIn_toList impl g hg ts neg ac' false
    · simp only [eq_false hc, not_false_eq_true, ↓reduceIte, checkLoop]
      rfl

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

/-- No stable IF-witness is reachable from `p0` (the right-hand side of Theorem 3). -/
def NoIFWitness [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (p0 : Set State1 × State2) : Prop :=
  ¬ ∃ q, (product (NormTr lts1) lts2).CanReach p0 q ∧ IsStableIFWitness lts1 lts2 q.1 q.2

/-- The state of the outer loop of Algorithm 6: the value of a pending early `return`, `working`,
    `antichain`, `antichain⁻` and `antichain⁺`. -/
abbrev LoopState6 (State1 : Type u) (State2 : Type v) :=
  Option (ULift.{max u v} Bool) × List (Set State1 × State2) × Antichain (Set State1 × State2) ×
    Antichain (Set State2 × State1) × Antichain (Set State2 × State1)

/-- The postcondition of the outer loop of Algorithm 6. -/
def LoopPost6 [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)
    (p0 : Set State1 × State2) (s : LoopState6 State1 State2) : Prop :=
  (s.1 = none ∧ NoIFWitness lts1 lts2 p0) ∨
    ∃ b, s.1 = some (.up b) ∧ (b = true ↔ NoIFWitness lts1 lts2 p0)

/-- **Theorem 3**, for the whole algorithm: Algorithm 6 returns `true` iff no stable IF-witness is
    reachable from the initial pair. -/
theorem weakImpossibleFuturesOpt_iff [HasTau Label] [Finite Label] [Finite State1]
    [Finite State2] (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label)
    (s2 : State2) :
    weakImpossibleFuturesOpt lts1 s1 lts2 s2 = true ↔ NoIFWitness lts1 lts2 (NormInit lts1 s1, s2) := by
  unfold weakImpossibleFuturesOpt
  dsimp only [Id.run_bind]
  generalize hres : (forIn (m := Id) Lean.Loop.mk _ _).run = res
  have key : LoopPost6 lts1 lts2 (NormInit lts1 s1, s2) res := by
    rw [← hres]
    refine MercLib.Control.whileInduction _
      (InvImage.wf (fun s : LoopState6 State1 State2 => (pending s.2.2.1).ncard + s.2.1.length)
        Nat.lt_wfRel.wf)
      (fun s => s.1 = none ∧ (∃ done, ExploreInv (NormTr lts1) lts2 (IsStableIFWitness lts1 lts2)
        (fun _ => False) (fun _ => False) (NormInit lts1 s1, s2) done s.2.1 s.2.2.1) ∧
        PosSound lts1 lts2 s.2.2.2.2 ∧ NegSound lts1 lts2 s.2.2.2.1)
      _ ?_ _ ?_
    on_goal 2 =>
      exact ⟨rfl, ⟨∅, ExploreInv.initial ⟨s1, WeakTr.refl s1⟩⟩, posSound_empty, negSound_empty⟩
    rintro ⟨r, w, A, neg, pos⟩ ⟨rfl, ⟨done, h⟩, hpos, hneg⟩
    clear hres
    have found : ∀ q, (product (NormTr lts1) lts2).CanReach (NormInit lts1 s1, s2) q →
        IsStableIFWitness lts1 lts2 q.1 q.2 →
          (false = true ↔ NoIFWitness lts1 lts2 (NormInit lts1 s1, s2)) := fun q hq hw => by
      simp only [Bool.false_eq_true, false_iff, NoIFWitness, not_not]
      exact ⟨q, hq, hw⟩
    rcases w with _ | ⟨⟨spec, impl⟩, w⟩
    · -- line 27
      refine Or.inl ⟨rfl, ?_⟩
      exact h.no_witness (normTr_isMonotone lts1)
        (fun hle hw => IsStableIFWitness.antitone lts1 lts2 hle hw) (fun _ hp => hp)
        (fun _ hp => hp.elim) (fun _ hp => hp) (fun _ hx => hx.elim)
    rw [dite_eq_left (List.cons_ne_nil _ _)]
    dsimp +instances only [List.head_cons, List.tail_cons, Id.run_bind]
    rw [forIn_toList lts1 lts2 impl _ ?hg]
    case hg => intro _ _; rfl
    obtain ⟨hpos', hneg'⟩ := checkLoop_sound lts1 lts2 impl (toList spec) hpos hneg
    have hiff := stableIFWitness_iff_checkLoop lts1 lts2 (h.nonempty _ List.mem_cons_self) hpos
      hneg (Prod.ext rfl (Prod.ext rfl rfl) : checkLoop lts1 lts2 impl (toList spec) true pos neg = _)
    generalize checkLoop lts1 lts2 impl (toList spec) true pos neg = cl at hpos' hneg' hiff
    obtain ⟨b, pos', neg'⟩ := cl
    dsimp only at hpos' hneg' hiff ⊢
    by_cases hbst : b = true ∧ Stable lts2 impl
    · -- line 16
      simp only [eq_true hbst, ↓reduceIte]
      exact Or.inr ⟨false, rfl, found _ h.reach_head (hiff.mpr hbst)⟩
    simp only [eq_false hbst, ↓reduceIte, Id.run_bind]
    have hW : ¬ IsStableIFWitness lts1 lts2 spec impl := fun hw => hbst (hiff.mp hw)
    rcases hfs : forSuccessors lts1 spec (outgoing lts2 impl) w A with _ | ⟨w', A'⟩
    · -- line 23
      rw [forIn_outgoing_none _ ?hg hfs]
      case hg => intro _ _ _ _; rfl
      obtain ⟨⟨a, t⟩, hp, he⟩ := forSuccessors_none hfs
      exact Or.inr ⟨false, rfl, found (succSpec lts1 spec a, t)
        (h.reach_succ (stepsBy_normTr lts1 spec) (mem_outgoing.mp hp)) (Or.inl he)⟩
    · rw [forIn_outgoing_some _ ?hg hfs]
      case hg => intro _ _ _ _; rfl
      refine ⟨⟨rfl, ⟨_, h.step (stepsBy_normTr lts1 spec) (fun _ => mem_outgoing) hW
        (forSuccessors_some h.le_eq hfs)⟩, hpos', hneg'⟩, ?_⟩
      have := forSuccessors_measure h.le_eq hfs
      show _ + _ < _ + _
      simp only [List.length_cons] at this ⊢
      omega
  rcases key with ⟨h1, h2⟩ | ⟨b, h1, h2⟩
  · rw [h1]; exact iff_of_true rfl h2
  · rw [h1]; exact h2

/-- **Theorem 3.** For finite LTSs with a convergent implementation, Algorithm 6 returns `true`
    iff weak impossible futures refinement holds. -/
theorem weakImpossibleFuturesOptCorrect {State1 State2 Label : Type*} [HasTau Label]
    [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2)
    (hconv : Convergent lts2) :
    weakImpossibleFuturesOpt lts1 s1 lts2 s2 = true ↔ s1 ⊑if[lts1,lts2] s2 := by
  rw [weakImpossibleFuturesOpt_iff, NoIFWitness, impossibleFuturesRefines_iff_not_reachable_ifWitness,
    reachable_ifWitness_iff_reachable_stableIFWitness lts1 lts2 hconv, Prod.exists]

end MercLib.Refinement
