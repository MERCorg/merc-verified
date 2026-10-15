module

public import Mathlib.Data.Set.Card
public import MercLib.Refinement.Semantics
public import MercLib.Refinement.Product
public import MercLib.Refinement.Antichain
public import MercLib.Refinement.Algorithm
public import MercLib.Refinement.Proofs.Semantics_Proofs
public import MercLib.Refinement.Proofs.Antichain_Proofs
public import MercLib.Refinement.Proofs.Product_Proofs

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.Refinement

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline
theorem `refinesNewCorrect` is stated in `Challenges/Refinement.lean`.

Correctness of Algorithm 2 (Theorem 2). The proof follows Lemma 2 of the paper: a loop invariant
`ExploreInv` relating `done`, `working` and `antichain` (everything in `working` is reachable and
non-empty, the antichain is covered by `working ∪ done`, nothing in `done` is a witness, and every
successor of a fully explored pair of `done` is covered by the antichain). When `working` runs
empty, every reachable pair is dominated by a pair of `done` (`ExploreInv.no_witness`), so by
antitonicity of witnesses (Lemma 3) no witness is reachable. The invariant is stated over an
arbitrary monotone normal form, witness predicate and pruning predicate, so that the outer loop of
Algorithm 6 (`AlgorithmImpossibleFutures_Proofs.lean`) reuses it. -/

/-! ## The successor computation (lines 13-22) -/

open scoped Classical in
/-- The specification set `spec'` reached from `spec` by the action `a` (lines 14-17). -/
noncomputable def succSpec [HasTau Label] (lts1 : LTS State1 Label) (spec : Set State1)
    (a : Label) : Set State1 :=
  if a = HasTau.τ then spec else { s' | ∃ s ∈ spec, WeakTr lts1 s [a] s' }

theorem mem_outgoing [Finite Label] [Finite State2] {lts2 : LTS State2 Label} {s : State2}
    {p : Label × State2} : p ∈ outgoing lts2 s ↔ lts2.Tr s p.1 p.2 := by
  simp [outgoing]

/-- `L1` makes the visible steps of the subset construction of `lts1` from `spec`. -/
def StepsBy [HasTau Label] (lts1 : LTS State1 Label) (L1 : LTS (Set State1) Label)
    (spec : Set State1) : Prop :=
  ∀ a V, IsVisible a → (L1.Tr spec a V ↔ V = succSpec lts1 spec a)

theorem stepsBy_normTr [HasTau Label] (lts1 : LTS State1 Label) (spec : Set State1) :
    StepsBy lts1 (NormTr lts1) spec := by
  intro a V ha
  simp [NormTr, succSpec, ha, show ¬ a = HasTau.τ from ha]

theorem stepsBy_fdrNormTr [HasTau Label] (lts1 : LTS State1 Label) {spec : Set State1}
    (h : ¬ SetDivergent lts1 spec) : StepsBy lts1 (FdrNormTr lts1) spec := by
  intro a V ha
  simp [FdrNormTr, succSpec, ha, h, show ¬ a = HasTau.τ from ha]

/-- The product steps out of `(spec, impl)` are `impl`'s steps, with `succSpec` on the left. -/
theorem product_tr_iff [HasTau Label] {lts1 : LTS State1 Label} {L1 : LTS (Set State1) Label}
    {lts2 : LTS State2 Label} {spec : Set State1} {impl : State2} {μ : Label}
    {q : Set State1 × State2} (h : StepsBy lts1 L1 spec) :
    (product L1 lts2).Tr (spec, impl) μ q ↔ lts2.Tr impl μ q.2 ∧ q.1 = succSpec lts1 spec μ := by
  obtain ⟨q1, q2⟩ := q
  by_cases hμ : μ = HasTau.τ
  · subst hμ
    simp only [product, succSpec, ite_true, IsVisible, ne_eq, not_true_eq_false, false_and,
      or_false, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  · simp only [product, hμ, false_and, false_or]
    rw [h μ q1 hμ]
    exact ⟨fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨hμ, h2, h1⟩⟩

theorem Antichain.le_trans_of_eq {A : Antichain (Set State1 × State2)} (h : A.le = ProductLE) :
    ∀ {x y z}, A.le x y → A.le y z → A.le x z := by
  intro x y z h1 h2
  rw [h] at h1 h2 ⊢
  exact h1.trans h2

theorem Antichain.mem_insert_self {A : Antichain (Set State1 × State2)} (h : A.le = ProductLE)
    (x : Set State1 × State2) : x ⊑ insert x A :=
  ⟨x, Or.inl rfl, by change A.le x x; rw [h]⟩

/-- What a successful run of a `for` loop over the transitions `l` (lines 13-22) guarantees:
    `w'`/`A'` extend `w`/`A` with non-empty successors only, and every successor is covered by
    `A'` or satisfies `extra` (for Algorithm 5: is covered by `antichain⁺`). -/
structure SuccFacts [HasTau Label] (lts1 : LTS State1 Label) (spec : Set State1)
    (extra : Set State1 × State2 → Prop) (l : List (Label × State2))
    (w : List (Set State1 × State2)) (A : Antichain (Set State1 × State2))
    (w' : List (Set State1 × State2)) (A' : Antichain (Set State1 × State2)) : Prop where
  le_eq : A'.le = ProductLE
  working : ∀ x ∈ w', x ∈ w ∨ ∃ p ∈ l, x = (succSpec lts1 spec p.1, p.2) ∧ x.1.Nonempty
  set : ∀ x ∈ A'.set, x ∈ A.set ∨ x ∈ w'
  mono : ∀ x, x ⊑ A → x ⊑ A'
  keep : ∀ x ∈ w, x ∈ w'
  covered : ∀ p ∈ l, (succSpec lts1 spec p.1, p.2) ⊑ A' ∨ extra (succSpec lts1 spec p.1, p.2)

theorem SuccFacts.nil [HasTau Label] {lts1 : LTS State1 Label} {spec : Set State1}
    {extra : Set State1 × State2 → Prop} {w : List (Set State1 × State2)}
    {A : Antichain (Set State1 × State2)} (hle : A.le = ProductLE) :
    SuccFacts lts1 spec extra [] w A w A :=
  ⟨hle, fun _ hx => Or.inl hx, fun _ hx => Or.inl hx, fun _ hx => hx, fun _ hx => hx,
    fun _ hp => absurd hp List.not_mem_nil⟩

/-- A pushed successor `x0 = (succSpec spec a, t)`: the facts for the rest of the loop give the
    facts for the whole loop. -/
theorem SuccFacts.push [HasTau Label] {lts1 : LTS State1 Label} {spec : Set State1}
    {extra : Set State1 × State2 → Prop} {a : Label} {t : State2} {rest : List (Label × State2)}
    {w w' : List (Set State1 × State2)} {A A' : Antichain (Set State1 × State2)}
    (hle : A.le = ProductLE) (hne : succSpec lts1 spec a ≠ ∅)
    (hnot : ¬ (succSpec lts1 spec a, t) ⊑ A)
    (r : SuccFacts lts1 spec extra rest ((succSpec lts1 spec a, t) :: w)
      (insert (succSpec lts1 spec a, t) A) w' A') :
    SuccFacts lts1 spec extra ((a, t) :: rest) w A w' A' where
  le_eq := r.le_eq
  working x hx := by
    rcases r.working x hx with hx | ⟨p, hp, hxp, hxne⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr ⟨(a, t), List.mem_cons_self, rfl, Set.nonempty_iff_ne_empty.mpr hne⟩
      · exact Or.inl hx
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hxp, hxne⟩
  set x hx := by
    rcases r.set x hx with hx | hx
    · rcases Antichain.mem_set_insert.mp hx with rfl | ⟨hx, _⟩
      · exact Or.inr (r.keep _ List.mem_cons_self)
      · exact Or.inl hx
    · exact Or.inr hx
  mono x hx := r.mono x (Antichain.mem_insert_of_mem (Antichain.le_trans_of_eq hle) hx hnot)
  keep x hx := r.keep x (List.mem_cons_of_mem _ hx)
  covered p hp := by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl (r.mono _ (Antichain.mem_insert_self hle _))
    · exact r.covered p hp

/-- A skipped successor that is already covered by `A` or satisfies `extra`. -/
theorem SuccFacts.skip [HasTau Label] {lts1 : LTS State1 Label} {spec : Set State1}
    {extra : Set State1 × State2 → Prop} {a : Label} {t : State2} {rest : List (Label × State2)}
    {w w' : List (Set State1 × State2)} {A A' : Antichain (Set State1 × State2)}
    (hcov : (succSpec lts1 spec a, t) ⊑ A ∨ extra (succSpec lts1 spec a, t))
    (r : SuccFacts lts1 spec extra rest w A w' A') :
    SuccFacts lts1 spec extra ((a, t) :: rest) w A w' A' where
  le_eq := r.le_eq
  working x hx := by
    rcases r.working x hx with hx | ⟨p, hp, hxp, hxne⟩
    · exact Or.inl hx
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hxp, hxne⟩
  set := r.set
  mono := r.mono
  keep := r.keep
  covered p hp := by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hcov.imp_left (r.mono _)
    · exact r.covered p hp

open scoped Classical in
theorem forSuccessors_cons [HasTau Label] (lts1 : LTS State1 Label) (spec : Set State1)
    (a : Label) (t : State2) (rest : List (Label × State2)) (w : List (Set State1 × State2))
    (A : Antichain (Set State1 × State2)) :
    forSuccessors lts1 spec ((a, t) :: rest) w A =
      if succSpec lts1 spec a = ∅ then none
      else if ¬ (succSpec lts1 spec a, t) ⊑ A then
        forSuccessors lts1 spec rest ((succSpec lts1 spec a, t) :: w)
          (insert (succSpec lts1 spec a, t) A)
      else forSuccessors lts1 spec rest w A := by
  rw [forSuccessors]; rfl

theorem forSuccessors_none [HasTau Label] {lts1 : LTS State1 Label} {spec : Set State1} :
    ∀ {l : List (Label × State2)} {w : List (Set State1 × State2)}
      {A : Antichain (Set State1 × State2)},
      forSuccessors lts1 spec l w A = none → ∃ p ∈ l, succSpec lts1 spec p.1 = ∅
  | [], w, A, h => by simp [forSuccessors] at h
  | (a, t) :: rest, w, A, h => by
    rw [forSuccessors_cons] at h
    split_ifs at h with h1 h2
    · exact ⟨(a, t), List.mem_cons_self, h1⟩
    · obtain ⟨p, hp, he⟩ := forSuccessors_none h
      exact ⟨p, List.mem_cons_of_mem _ hp, he⟩
    · obtain ⟨p, hp, he⟩ := forSuccessors_none h
      exact ⟨p, List.mem_cons_of_mem _ hp, he⟩

theorem forSuccessors_some [HasTau Label] {lts1 : LTS State1 Label} {spec : Set State1} :
    ∀ {l : List (Label × State2)} {w w' : List (Set State1 × State2)}
      {A A' : Antichain (Set State1 × State2)}, A.le = ProductLE →
      forSuccessors lts1 spec l w A = some (w', A') →
      SuccFacts lts1 spec (fun _ => False) l w A w' A'
  | [], w, w', A, A', hle, h => by
    simp only [forSuccessors, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact SuccFacts.nil hle
  | (a, t) :: rest, w, w', A, A', hle, h => by
    rw [forSuccessors_cons] at h
    split_ifs at h with h1 h2
    · exact SuccFacts.skip (Or.inl h2) (forSuccessors_some hle h)
    · exact SuccFacts.push hle h1 h2 (forSuccessors_some hle h)

/-! ## The exploration invariant (Lemma 2) -/

/-- The invariant of the `while` loop, for the exploration of `L1 ⋉ lts2` from `p0` looking for
    pairs satisfying `W`, where pairs whose specification set satisfies `Pr` are not expanded and
    successors satisfying `Ex` need not be covered by the antichain (for Algorithm 5: those covered
    by `antichain⁺`). -/
structure ExploreInv [HasTau Label] (L1 : LTS (Set State1) Label) (lts2 : LTS State2 Label)
    (W : Set State1 → State2 → Prop) (Pr : Set State1 → Prop)
    (Ex : Set State1 × State2 → Prop) (p0 : Set State1 × State2)
    (done : Set (Set State1 × State2)) (working : List (Set State1 × State2))
    (A : Antichain (Set State1 × State2)) : Prop where
  le_eq : A.le = ProductLE
  reach : ∀ x ∈ working, (product L1 lts2).CanReach p0 x
  nonempty : ∀ x ∈ working, x.1.Nonempty
  set_sub : ∀ x ∈ A.set, x ∈ working ∨ x ∈ done
  done_ok : ∀ z ∈ done, ¬ W z.1 z.2
  closed : ∀ z ∈ done, ¬ Pr z.1 → ∀ μ z', (product L1 lts2).Tr z μ z' → z' ⊑ A ∨ Ex z'
  init : p0 ⊑ A

namespace ExploreInv

variable [HasTau Label] {L1 : LTS (Set State1) Label} {lts2 : LTS State2 Label}
  {W : Set State1 → State2 → Prop} {Pr : Set State1 → Prop} {Ex : Set State1 × State2 → Prop}
  {p0 : Set State1 × State2}
  {done : Set (Set State1 × State2)} {w : List (Set State1 × State2)}
  {A : Antichain (Set State1 × State2)}

/-- Lines 2-3: the invariant holds initially. -/
theorem initial (hp0 : p0.1.Nonempty) :
    ExploreInv L1 lts2 W Pr Ex p0 ∅ [p0] (insert p0 (Antichain.empty ProductLE)) where
  le_eq := rfl
  reach x hx := by rw [List.mem_singleton.mp hx]; exact Cslib.LTS.CanReach.refl _ _
  nonempty x hx := by rw [List.mem_singleton.mp hx]; exact hp0
  set_sub x hx := by
    rcases Antichain.mem_set_insert.mp hx with rfl | ⟨hx, _⟩
    · exact Or.inl List.mem_cons_self
    · exact absurd hx (Set.notMem_empty x)
  done_ok _ hz := absurd hz (Set.notMem_empty _)
  closed _ hz := absurd hz (Set.notMem_empty _)
  init := Antichain.mem_insert_self rfl p0

/-- The `else` branch of the `done` guard (never taken): the invariant is kept. -/
theorem skip {p : Set State1 × State2} (h : ExploreInv L1 lts2 W Pr Ex p0 done (p :: w) A)
    (hp : p ∈ done) : ExploreInv L1 lts2 W Pr Ex p0 done w A where
  le_eq := h.le_eq
  reach x hx := h.reach x (List.mem_cons_of_mem _ hx)
  nonempty x hx := h.nonempty x (List.mem_cons_of_mem _ hx)
  set_sub x hx := by
    rcases h.set_sub x hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr hp
      · exact Or.inl hx
    · exact Or.inr hx
  done_ok := h.done_ok
  closed := h.closed
  init := h.init

/-- A pruned pair (not a witness) is moved to `done` without exploring its successors. -/
theorem prune {p : Set State1 × State2} (h : ExploreInv L1 lts2 W Pr Ex p0 done (p :: w) A)
    (hpr : Pr p.1) (hW : ¬ W p.1 p.2) : ExploreInv L1 lts2 W Pr Ex p0 (insert p done) w A where
  le_eq := h.le_eq
  reach x hx := h.reach x (List.mem_cons_of_mem _ hx)
  nonempty x hx := h.nonempty x (List.mem_cons_of_mem _ hx)
  set_sub x hx := by
    rcases h.set_sub x hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (Set.mem_insert _ _)
      · exact Or.inl hx
    · exact Or.inr (Set.mem_insert_of_mem _ hx)
  done_ok z hz := by
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hW
    · exact h.done_ok z hz
  closed z hz hzp := by
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact absurd hpr hzp
    · exact h.closed z hz hzp
  init := h.init

/-- A pair that is not a witness, whose successors are pushed by a successful `for` loop
    (lines 13-22), is moved to `done`. -/
theorem step {lts1 : LTS State1 Label} {spec : Set State1} {impl : State2}
    {l : List (Label × State2)}
    {w' : List (Set State1 × State2)} {A' : Antichain (Set State1 × State2)}
    (h : ExploreInv L1 lts2 W Pr Ex p0 done ((spec, impl) :: w) A)
    (hsteps : StepsBy lts1 L1 spec) (hl : ∀ p, p ∈ l ↔ lts2.Tr impl p.1 p.2)
    (hW : ¬ W spec impl) (r : SuccFacts lts1 spec Ex l w A w' A') :
    ExploreInv L1 lts2 W Pr Ex p0 (insert (spec, impl) done) w' A' where
  le_eq := r.le_eq
  reach x hx := by
    rcases r.working x hx with hx | ⟨⟨a, t⟩, hp, rfl, _⟩
    · exact h.reach x (List.mem_cons_of_mem _ hx)
    · exact canReach_trans (h.reach _ List.mem_cons_self)
        ⟨[a], Cslib.LTS.MTr.single _ ((product_tr_iff hsteps).mpr ⟨(hl _).mp hp, rfl⟩)⟩
  nonempty x hx := by
    rcases r.working x hx with hx | ⟨_, _, rfl, hne⟩
    · exact h.nonempty x (List.mem_cons_of_mem _ hx)
    · exact hne
  set_sub x hx := by
    rcases r.set x hx with hx | hx
    · rcases h.set_sub x hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Set.mem_insert _ _)
        · exact Or.inl (r.keep x hx)
      · exact Or.inr (Set.mem_insert_of_mem _ hx)
    · exact Or.inl hx
  done_ok z hz := by
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hW
    · exact h.done_ok z hz
  closed z hz hzp μ z' hz' := by
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · obtain ⟨htr, h1⟩ := (product_tr_iff hsteps).mp hz'
      have hz'eq : z' = (succSpec lts1 spec μ, z'.2) := Prod.ext h1 rfl
      rw [hz'eq]
      exact r.covered (μ, z'.2) ((hl _).mpr htr)
    · exact (h.closed z hz hzp μ z' hz').imp_left (r.mono _)
  init := r.mono _ h.init

/-- A popped pair is reachable. -/
theorem reach_head {p : Set State1 × State2} (h : ExploreInv L1 lts2 W Pr Ex p0 done (p :: w) A) :
    (product L1 lts2).CanReach p0 p :=
  h.reach p List.mem_cons_self

/-- A successor of a popped pair is reachable. -/
theorem reach_succ {lts1 : LTS State1 Label} {spec : Set State1} {impl : State2} {a : Label}
    {t : State2} (h : ExploreInv L1 lts2 W Pr Ex p0 done ((spec, impl) :: w) A)
    (hsteps : StepsBy lts1 L1 spec) (htr : lts2.Tr impl a t) :
    (product L1 lts2).CanReach p0 (succSpec lts1 spec a, t) :=
  canReach_trans h.reach_head
    ⟨[a], Cslib.LTS.MTr.single _ ((product_tr_iff hsteps).mpr ⟨htr, rfl⟩)⟩

/-- When `working` is empty, no pair reachable from a pair dominating one of `done` is a witness,
    unless it is pruned: every such pair is dominated by a pair of `done` (Proposition 2,
    saturation) or reachable from an `Ex` pair, and witnesses are antitone (Lemma 3). -/
theorem safe (hmono : IsMonotoneNormalForm L1)
    (hW_anti : ∀ {U V : Set State1} {s t : State2}, ProductLE (U, s) (V, t) → W V t → W U s)
    (hPr_mono : ∀ {U V : Set State1}, U ⊆ V → Pr U → Pr V)
    (hPr_path : ∀ {x q : Set State1 × State2} {σ : List Label},
      (product L1 lts2).MTr x σ q → Pr x.1 → q.1 = x.1)
    (hEx : ∀ x, Ex x → ¬ ∃ q, (product L1 lts2).CanReach x q ∧ W q.1 q.2)
    (h : ExploreInv L1 lts2 W Pr Ex p0 done [] A) :
    ∀ {x q : Set State1 × State2} {σ : List Label}, (product L1 lts2).MTr x σ q →
      (∃ z ∈ done, ProductLE z x) → ¬ Pr q.1 → ¬ W q.1 q.2 := by
  have hdone : ∀ y ∈ A.set, y ∈ done := fun y hy =>
    (h.set_sub y hy).resolve_left List.not_mem_nil
  intro x q σ hx
  induction hx with
  | refl => exact fun ⟨z, hz, hzx⟩ _ hw => h.done_ok z hz (hW_anti hzx hw)
  | @stepL x μ mid μs q hstep hrest ih =>
    rintro ⟨z, hz, hzx⟩ hq hw
    have hxp : ¬ Pr x.1 := fun hp =>
      hq (by rw [hPr_path (Cslib.LTS.MTr.stepL hstep hrest) hp]; exact hp)
    have hzp : ¬ Pr z.1 := fun hp => hxp (hPr_mono hzx.2 hp)
    obtain ⟨z', hz'tr, hz'le⟩ := hmono.simulate lts2 hzx (Cslib.LTS.MTr.single _ hstep)
    rcases h.closed z hz hzp μ z' ((Cslib.LTS.MTr.singleton_iff _ _ _ _).mp hz'tr) with
      ⟨y, hyA, hyz'⟩ | hex
    · rw [h.le_eq] at hyz'
      exact ih ⟨y, hdone y hyA, hyz'.trans hz'le⟩ hq hw
    · obtain ⟨q', hq', hq'le⟩ := productLE_canReach hmono lts2 hz'le ⟨μs, hrest⟩
      exact hEx z' hex ⟨q', hq', hW_anti hq'le hw⟩

/-- Line 23: when `working` is empty, no witness is reachable from `p0`. -/
theorem no_witness (hmono : IsMonotoneNormalForm L1)
    (hW_anti : ∀ {U V : Set State1} {s t : State2}, ProductLE (U, s) (V, t) → W V t → W U s)
    (hPr_mono : ∀ {U V : Set State1}, U ⊆ V → Pr U → Pr V)
    (hPr_path : ∀ {x q : Set State1 × State2} {σ : List Label},
      (product L1 lts2).MTr x σ q → Pr x.1 → q.1 = x.1)
    (hW_Pr : ∀ {U : Set State1} {s : State2}, W U s → ¬ Pr U)
    (hEx : ∀ x, Ex x → ¬ ∃ q, (product L1 lts2).CanReach x q ∧ W q.1 q.2)
    (h : ExploreInv L1 lts2 W Pr Ex p0 done [] A) :
    ¬ ∃ q, (product L1 lts2).CanReach p0 q ∧ W q.1 q.2 := by
  rintro ⟨q, ⟨σ, hq⟩, hw⟩
  obtain ⟨y, hyA, hy⟩ := h.init
  rw [h.le_eq] at hy
  exact h.safe hmono hW_anti hPr_mono hPr_path hEx hq
    ⟨y, (h.set_sub y hyA).resolve_left List.not_mem_nil, hy⟩ (hW_Pr hw) hw

end ExploreInv

/-! ## Algorithm 2 -/

/-- The normal form explored by Algorithm 2: `norm` for stable failures, `normfdr` for
    failures-divergences refinement. -/
def ModeNorm [HasTau Label] (lts1 : LTS State1 Label) : Bool → LTS (Set State1) Label
  | false => NormTr lts1
  | true => FdrNormTr lts1

/-- The witnesses Algorithm 2 looks for: SF-witnesses or FD-witnesses. -/
def ModeWitness [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
    Bool → Set State1 → State2 → Prop
  | false => IsSFWitness lts1 lts2
  | true => IsFDWitness lts1 lts2

/-- The pairs Algorithm 2 does not expand (line 6): divergent specification sets, when checking
    for divergences. -/
def Pruned [HasTau Label] (lts1 : LTS State1 Label) (checkDiv : Bool) (U : Set State1) : Prop :=
  checkDiv = true ∧ SetDivergent lts1 U

section Mode

variable [HasTau Label] (lts1 : LTS State1 Label) (lts2 : LTS State2 Label)

theorem modeNorm_isMonotone (c : Bool) : IsMonotoneNormalForm (ModeNorm lts1 c) := by
  cases c
  · exact normTr_isMonotone lts1
  · exact fdrNormTr_isMonotone lts1

theorem modeWitness_antitone (c : Bool) {U V : Set State1} {s t : State2}
    (hle : ProductLE (U, s) (V, t)) (hw : ModeWitness lts1 lts2 c V t) :
    ModeWitness lts1 lts2 c U s := by
  cases c
  · exact IsSFWitness.antitone lts1 lts2 hle hw
  · exact IsFDWitness.antitone lts1 lts2 hle hw

theorem pruned_mono {c : Bool} {U V : Set State1} (hUV : U ⊆ V) :
    Pruned lts1 c U → Pruned lts1 c V
  | ⟨hc, s, hs, hd⟩ => ⟨hc, s, hUV hs, hd⟩

theorem pruned_path {c : Bool} {x q : Set State1 × State2} {σ : List Label}
    (h : (product (ModeNorm lts1 c) lts2).MTr x σ q) (hp : Pruned lts1 c x.1) : q.1 = x.1 := by
  induction h with
  | refl => rfl
  | @stepL x μ mid μs q hstep _ ih =>
    obtain ⟨rfl, hd⟩ := hp
    rcases hstep with ⟨_, hmid, _⟩ | ⟨_, ⟨_, hnd, _⟩, _⟩
    · rw [ih ⟨rfl, hmid ▸ hd⟩, hmid]
    · exact absurd hd hnd

theorem not_pruned_of_witness {c : Bool} {U : Set State1} {s : State2}
    (hw : ModeWitness lts1 lts2 c U s) : ¬ Pruned lts1 c U := by
  rintro ⟨rfl, hd⟩
  exact hw.1 hd

theorem modeWitness_empty (c : Bool) (s : State2) : ModeWitness lts1 lts2 c ∅ s := by
  cases c
  · exact Or.inl rfl
  · exact ⟨fun ⟨_, h, _⟩ => h, Or.inl rfl⟩

theorem stepsBy_modeNorm {c : Bool} {spec : Set State1} (h : ¬ Pruned lts1 c spec) :
    StepsBy lts1 (ModeNorm lts1 c) spec := by
  cases c
  · exact stepsBy_normTr lts1 spec
  · exact stepsBy_fdrNormTr lts1 fun hd => h ⟨rfl, hd⟩

/-- Lines 7-12 decide whether a popped, non-pruned, non-empty pair is a witness. -/
theorem modeWitness_iff {c : Bool} {spec : Set State1} {impl : State2} (hne : spec.Nonempty)
    (hp : ¬ Pruned lts1 c spec) :
    ModeWitness lts1 lts2 c spec impl ↔
      (c = true ∧ lts2.Divergent impl) ∨
        (Stable lts2 impl ∧ ¬ refusalsOf lts2 impl ⊆ refusals lts1 spec) := by
  cases c
  · simp [ModeWitness, IsSFWitness, hne.ne_empty]
  · have hnd : ¬ SetDivergent lts1 spec := fun hd => hp ⟨rfl, hd⟩
    simp only [ModeWitness, IsFDWitness, hnd, not_false_eq_true, hne.ne_empty, false_or,
      true_and]
    exact or_comm

end Mode

/-- **Theorem 2**, for the `while` loop: from the invariant, the loop returns `true` iff no witness
    is reachable. -/
theorem refinesLoop_spec [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) (c : Bool) (p0 : Set State1 × State2)
    (done : Set (Set State1 × State2)) (working : List (Set State1 × State2))
    (A : Antichain (Set State1 × State2))
    (h : ExploreInv (ModeNorm lts1 c) lts2 (ModeWitness lts1 lts2 c) (Pruned lts1 c)
      (fun _ => False) p0 done working A) :
    refinesLoop lts1 lts2 c done working A = true ↔
      ¬ ∃ q, (product (ModeNorm lts1 c) lts2).CanReach p0 q ∧ ModeWitness lts1 lts2 c q.1 q.2 := by
  have hnp : ∀ {spec : Set State1}, (¬ SetDivergent lts1 spec ∨ c = false) →
      ¬ Pruned lts1 c spec := by
    rintro spec hor ⟨rfl, hd⟩
    rcases hor with hor | hor
    · exact hor hd
    · cases hor
  have found : ∀ q, (product (ModeNorm lts1 c) lts2).CanReach p0 q →
      ModeWitness lts1 lts2 c q.1 q.2 → (false = true ↔
        ¬ ∃ q, (product (ModeNorm lts1 c) lts2).CanReach p0 q ∧
          ModeWitness lts1 lts2 c q.1 q.2) := fun q hq hw => by
    simp only [Bool.false_eq_true, false_iff, not_not]
    exact ⟨q, hq, hw⟩
  fun_induction refinesLoop lts1 lts2 c done working A
  case case1 =>
    simp only [true_iff]
    exact h.no_witness (modeNorm_isMonotone lts1 c)
      (fun hle hw => modeWitness_antitone lts1 lts2 c hle hw)
      (fun hUV => pruned_mono lts1 hUV) (fun hx hp => pruned_path lts1 lts2 hx hp)
      (fun hw => not_pruned_of_witness lts1 lts2 hw) (fun _ hx => hx.elim)
  case case2 _ _ spec impl _ _ hor hdiv =>
    exact found _ h.reach_head ((modeWitness_iff lts1 lts2
      (h.nonempty _ List.mem_cons_self) (hnp hor)).mpr (Or.inl hdiv))
  case case3 _ _ spec impl _ _ hor _ hst =>
    exact found _ h.reach_head ((modeWitness_iff lts1 lts2
      (h.nonempty _ List.mem_cons_self) (hnp hor)).mpr (Or.inr hst))
  case case4 _ _ spec impl _ _ hor _ _ hnone =>
    obtain ⟨⟨a, t⟩, hp, he⟩ := forSuccessors_none hnone
    refine found (succSpec lts1 spec a, t)
      (h.reach_succ (stepsBy_modeNorm lts1 (hnp hor)) (mem_outgoing.mp hp)) ?_
    change ModeWitness lts1 lts2 c (succSpec lts1 spec a) t
    rw [he]
    exact modeWitness_empty lts1 lts2 c t
  case case5 _ _ spec impl _ _ hor hndiv hnst _ _ hsome ih =>
    have hW : ¬ ModeWitness lts1 lts2 c spec impl := by
      rw [modeWitness_iff lts1 lts2 (h.nonempty _ List.mem_cons_self) (hnp hor)]
      exact not_or.mpr ⟨hndiv, hnst⟩
    exact ih (h.step (stepsBy_modeNorm lts1 (hnp hor)) (fun _ => mem_outgoing) hW
      (forSuccessors_some h.le_eq hsome))
  case case6 _ _ spec impl _ _ hor ih =>
    have hpr : Pruned lts1 c spec := by
      rw [not_or, not_not, Bool.not_eq_false] at hor
      exact ⟨hor.2, hor.1⟩
    exact ih (h.prune hpr fun hw => not_pruned_of_witness lts1 lts2 hw hpr)
  case case7 _ _ _ _ _ hd ih =>
    exact ih (h.skip (not_not.mp hd))

/-- **Theorem 2**, for the whole algorithm: `refinesNew` returns `true` iff no witness is reachable
    from the initial pair. -/
theorem refinesNew_iff [HasTau Label] [Finite Label] [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) (c : Bool) :
    refinesNew lts1 s1 lts2 s2 c = true ↔
      ¬ ∃ q, (product (ModeNorm lts1 c) lts2).CanReach (NormInit lts1 s1, s2) q ∧
        ModeWitness lts1 lts2 c q.1 q.2 :=
  refinesLoop_spec lts1 lts2 c _ _ _ _ (ExploreInv.initial ⟨s1, WeakTr.refl s1⟩)

/-- **Theorem 2.** `refines_new` decides stable failures refinement (`CheckDiv = false`) and
    failures-divergences refinement (`CheckDiv = true`). -/
theorem refinesNewCorrect {State1 State2 Label : Type*} [HasTau Label] [Finite Label]
    [Finite State1] [Finite State2]
    (lts1 : LTS State1 Label) (s1 : State1) (lts2 : LTS State2 Label) (s2 : State2) :
    (refinesNew lts1 s1 lts2 s2 false = true ↔ s1 ⊑sfr[lts1, lts2] s2) ∧
      (refinesNew lts1 s1 lts2 s2 true = true ↔ s1 ⊑fdr[lts1, lts2] s2) := by
  refine ⟨?_, ?_⟩
  · rw [refinesNew_iff, stableFailuresRefines_iff_not_reachable_sfWitness]
    simp only [ModeNorm, ModeWitness, Prod.exists]
  · rw [refinesNew_iff, failuresDivergencesRefines_iff_not_reachable_fdWitness]
    simp only [ModeNorm, ModeWitness, Prod.exists]

end MercLib.Refinement
