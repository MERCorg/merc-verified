module

public import MercLib.Algorithms.LDD.Reachability
import all MercLib.Theory.LDD.Proofs.Ldd_Proofs
import all MercLib.Algorithms.LDD.Proofs.SetOperations_Proofs
import all MercLib.Algorithms.LDD.Proofs.Relational_Proofs
import all MercLib.Util.Proofs.While_Proofs
import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Proofs: symbolic reachability on list decision diagrams

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/LDD.lean` (human-vetted).

Every algorithm keeps a set between the start set and its reachable vectors, and stops only when a
round of firing adds nothing; then the set is closed under the events, so it contains every
reachable vector. For saturation and REACH, the set after saturating the children is moreover
closed under the events below the position, because those events copy the value at the position.
Every round that does not stop adds a reachable vector, so the number of reachable vectors that
are still missing decreases, which ends the loops when the reachable set is finite.
-/

namespace MercLib.LDD

variable {α : Type*}

/-! ## Reachable sets -/

/-- `S` is closed under the events of `E` whose `top` is at least `p`. -/
private def Closed (E : List (Event α)) (p : ℕ) (S : Set (List α)) : Prop :=
  ∀ e ∈ E, p ≤ e.top → ∀ x ∈ S, ∀ y, e.Fires p x y → y ∈ S

private theorem subset_sat {E : List (Event α)} {p : ℕ} {X : Set (List α)} : X ⊆ Sat E p X :=
  fun _ hx => Reach.base hx

private theorem sat_closed {E : List (Event α)} {p : ℕ} {X : Set (List α)} :
    Closed E p (Sat E p X) :=
  fun e he hp _ hx _ hf => Reach.step e he hp hx hf

private theorem sat_min {E : List (Event α)} {p : ℕ} {X S : Set (List α)} (hX : X ⊆ S)
    (hS : Closed E p S) : Sat E p X ⊆ S := by
  intro y hy
  induction hy with
  | base hx => exact hX hx
  | step e he hp _ hf ih => exact hS e he hp _ ih _ hf

private theorem sat_mono {E : List (Event α)} {p : ℕ} {X Y : Set (List α)} (h : X ⊆ Y) :
    Sat E p X ⊆ Sat E p Y :=
  sat_min (h.trans subset_sat) sat_closed

/-- A set between `X` and its reachable vectors has the same reachable vectors. -/
private theorem sat_eq_of_between {E : List (Event α)} {p : ℕ} {X Y : Set (List α)} (h1 : X ⊆ Y)
    (h2 : Y ⊆ Sat E p X) : Sat E p Y = Sat E p X :=
  Set.Subset.antisymm (sat_min h2 sat_closed) (sat_mono h1)

/-- A closed set between `X` and its reachable vectors is the set of reachable vectors. -/
private theorem eq_sat_of_closed {E : List (Event α)} {p : ℕ} {X Y : Set (List α)} (h1 : X ⊆ Y)
    (h2 : Y ⊆ Sat E p X) (hc : Closed E p Y) : Y = Sat E p X :=
  Set.Subset.antisymm h2 (sat_min h1 hc)

/-! ## Firing one event -/

private theorem relWidth_metaAt (e : Event α) (p : ℕ) : relWidth (e.metaAt p) = relWidth e.access := by
  simp [Event.metaAt, relWidth, Access.width]

private theorem length_metaAt (e : Event α) (p : ℕ) :
    (e.metaAt p).length = e.top - p + e.access.length := by
  simp [Event.metaAt]

/-- The successors of `X` under `e`. -/
private def post (e : Event α) (p : ℕ) (X : Set (List α)) : Set (List α) :=
  {y | ∃ x ∈ X, e.Fires p x y}

namespace Ldd

variable [LinearOrder α]

/-- The successors of a well-formed set under a well-formed event at position `p`. -/
private theorem successors_event {e : Event α} {p k : ℕ} {X : Ldd α} (hX : X.WellFormed k)
    (hm : e.top - p + e.access.length ≤ k) (hR : e.rel.WellFormed (relWidth e.access)) :
    (successors (e.metaAt p) X e.rel).WellFormed k ∧
      (successors (e.metaAt p) X e.rel).denote = post e p X.denote := by
  have hR' : e.rel.WellFormed (relWidth (e.metaAt p)) := by rwa [relWidth_metaAt]
  obtain ⟨hw, hd⟩ := successorsCorrect (e.metaAt p) X e.rel k (by rw [length_metaAt]; exact hm) hX hR'
  refine ⟨hw, ?_⟩
  rw [hd]
  ext y
  simp only [post, Event.Fires, Set.mem_ofPred_eq]

private theorem fire_correct {e : Event α} {p k : ℕ} {X : Ldd α} (hX : X.WellFormed k)
    (hm : e.top - p + e.access.length ≤ k) (hR : e.rel.WellFormed (relWidth e.access)) :
    (fire p X e).WellFormed k ∧ (fire p X e).denote = X.denote ∪ post e p X.denote := by
  obtain ⟨hw, hd⟩ := successors_event hX hm hR
  obtain ⟨hw', hd'⟩ := unionCorrect X _ k hX hw
  exact ⟨hw', by rw [fire, hd', hd]⟩

/-! ## Breadth-first search and chaining -/

/-- The events of `L` are well-formed at position `p` for sets of height `k`. -/
private def EventsFit (L : List (Event α)) (p k : ℕ) : Prop :=
  ∀ e ∈ L, e.top - p + e.access.length ≤ k ∧ e.rel.WellFormed (relWidth e.access)

private theorem bfs_fold (X : Ldd α) {k : ℕ} (hX : X.WellFormed k) :
    ∀ (L : List (Event α)) (S : Ldd α), EventsFit L 0 k → S.WellFormed k →
      (L.foldl (fun S e => union S (successors (e.metaAt 0) X e.rel)) S).WellFormed k ∧
      (L.foldl (fun S e => union S (successors (e.metaAt 0) X e.rel)) S).denote =
        S.denote ∪ {y | ∃ e ∈ L, y ∈ post e 0 X.denote}
  | [], S, _, hS => ⟨hS, by simp⟩
  | e :: L, S, hL, hS => by
    obtain ⟨hw, hd⟩ := successors_event hX (hL e (List.mem_cons_self ..)).1 (hL e (List.mem_cons_self ..)).2
    obtain ⟨hw', hd'⟩ := unionCorrect S _ k hS hw
    obtain ⟨ih1, ih2⟩ := bfs_fold X hX L _ (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) hw'
    refine ⟨ih1, ?_⟩
    simp only [List.foldl_cons]
    rw [ih2, hd', hd]
    ext y
    simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨e', he', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e, Or.inl rfl, h⟩
      · exact Or.inr ⟨e', Or.inr he', h⟩
    · rintro (h | ⟨e', he' | he', h⟩)
      · exact Or.inl (Or.inl h)
      · subst he'; exact Or.inl (Or.inr h)
      · exact Or.inr ⟨e', he', h⟩

private theorem eventsFit_zero {E : List (Event α)} {n : ℕ} (hE : ∀ e ∈ E, e.WellFormed n) :
    EventsFit E 0 n :=
  fun e he => ⟨by have := (hE e he).1; omega, (hE e he).2⟩

/-- Firing the events of `L` one after the other only adds successors, and when it adds nothing,
    the set is closed under every event of `L`. -/
private theorem chain_fold {p k : ℕ} :
    ∀ (L : List (Event α)) (S : Ldd α), EventsFit L p k → S.WellFormed k →
      (L.foldl (fire p) S).WellFormed k ∧ S.denote ⊆ (L.foldl (fire p) S).denote ∧
      (∀ T : Set (List α), S.denote ⊆ T → (∀ e ∈ L, post e p T ⊆ T) →
        (L.foldl (fire p) S).denote ⊆ T) ∧
      ((L.foldl (fire p) S).denote = S.denote → ∀ e ∈ L, post e p S.denote ⊆ S.denote)
  | [], S, _, hS => ⟨hS, subset_rfl, fun _ h _ => h, fun _ e he => by simp at he⟩
  | e :: L, S, hL, hS => by
    obtain ⟨hw, hd⟩ := fire_correct (e := e) (p := p) hS (hL e (List.mem_cons_self ..)).1
      (hL e (List.mem_cons_self ..)).2
    obtain ⟨ih1, ih2, ih3, ih4⟩ := chain_fold L (fire p S e)
      (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) hw
    simp only [List.foldl_cons]
    have hsub : S.denote ⊆ (fire p S e).denote := by rw [hd]; exact Set.subset_union_left
    refine ⟨ih1, hsub.trans ih2, ?_, ?_⟩
    · intro T hST hT
      refine ih3 T ?_ (fun e' he' => hT e' (List.mem_cons_of_mem _ he'))
      rw [hd]
      rintro y (hy | ⟨x, hx, hf⟩)
      · exact hST hy
      · exact hT e (List.mem_cons_self ..) ⟨x, hST hx, hf⟩
    · intro heq
      have hfe : (fire p S e).denote = S.denote :=
        Set.Subset.antisymm (heq ▸ ih2) hsub
      intro e' he'
      rcases List.mem_cons.mp he' with he'' | he'
      · intro y hy
        rw [he''] at hy
        have : y ∈ (fire p S e).denote := by rw [hd]; exact Or.inr hy
        rwa [hfe] at this
      · have := ih4 (by rw [heq, hfe]) e' he'
        rwa [hfe] at this

/-! ## Saturation -/

/-- `S` is closed under the events of `E` below position `p` (whose `top` is greater than `p`). -/
private def ClosedBelow (E : List (Event α)) (p : ℕ) (S : Set (List α)) : Prop :=
  ∀ e ∈ E, p < e.top → ∀ x ∈ S, ∀ y, e.Fires p x y → y ∈ S

omit [LinearOrder α] in
private theorem metaAt_succ {e : Event α} {p : ℕ} (h : p < e.top) :
    e.metaAt p = .skip :: e.metaAt (p + 1) := by
  simp only [Event.metaAt]
  rw [show e.top - p = (e.top - (p + 1)) + 1 by omega, List.replicate_succ, List.cons_append]

omit [LinearOrder α] in
/-- An event below position `p` keeps the value at `p`. -/
private theorem fires_below {e : Event α} {p : ℕ} (h : p < e.top) {x y : List α} :
    e.Fires p x y ↔ ∃ a x' y', x = a :: x' ∧ y = a :: y' ∧ e.Fires (p + 1) x' y' := by
  simp only [Event.Fires, metaAt_succ h, apply_skip]
  constructor
  · rintro ⟨t, ht, a, x', y', rfl, rfl, ha⟩; exact ⟨a, x', y', rfl, rfl, t, ht, ha⟩
  · rintro ⟨a, x', y', rfl, rfl, t, ht, ha⟩; exact ⟨t, ht, a, x', y', rfl, rfl, ha⟩

omit [LinearOrder α] in
/-- What is reachable below a value is reachable from the vectors starting with that value. -/
private theorem reach_cons {E : List (Event α)} {p : ℕ} {D : Set (List α)} (v : α) {y : List α}
    (h : Reach E (p + 1) D y) : Reach E p (List.cons v '' D) (v :: y) := by
  induction h with
  | base hx => exact Reach.base ⟨_, hx, rfl⟩
  | step e he hp _ hf ih =>
    exact Reach.step e he (by omega) ih ((fires_below (by omega)).2 ⟨v, _, _, rfl, rfl, hf⟩)

omit [LinearOrder α] in
private theorem sat_empty {E : List (Event α)} {p : ℕ} : Sat E p (∅ : Set (List α)) = ∅ :=
  Set.eq_empty_of_subset_empty (sat_min subset_rfl (fun _ _ _ _ hx => by simp at hx))

private theorem sat_one {E : List (Event α)} {n p : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    (h : n - p = 0) : Sat E p ({[]} : Set (List α)) = {[]} := by
  refine Set.Subset.antisymm (sat_min subset_rfl ?_) subset_sat
  intro e he hle x hx y hf
  have hlen := (hE e he).1
  have hacc : e.access = [] := List.eq_nil_of_length_eq_zero (by omega)
  have htop : e.top - p = 0 := by omega
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  simp only [Event.Fires, Event.metaAt, htop, hacc, List.replicate_zero, List.nil_append,
    apply_nil] at hf
  obtain ⟨t, -, -, rfl⟩ := hf
  rfl

omit [LinearOrder α] in
private theorem mk_of_ne_zero {v : α} {d r : Ldd α} (h : d ≠ zero) : mk v d r = node v d r := by
  cases d <;> simp_all [mk]

/-! ## REACH -/

omit [LinearOrder α] in
private theorem lookup_mem [DecidableEq α] {v : α} :
    ∀ {R : Ldd α} {t : List α}, t ∈ (R.lookup v).denote → v :: t ∈ R.denote
  | node w d r, t, h => by
    simp only [lookup] at h
    split_ifs at h with hw
    · subst hw; exact Or.inl ⟨t, h, rfl⟩
    · exact Or.inr (lookup_mem h)
  | zero, _, h => by simp [lookup, denote] at h
  | one, _, h => by simp [lookup, denote] at h

private theorem lookup_wf {v : α} : ∀ {R : Ldd α} {k : ℕ}, R.WellFormed (k + 1) →
    (R.lookup v).WellFormed k
  | node w d r, k, h => by
    obtain ⟨-, hd, hr, -⟩ := h
    simp only [lookup]
    split_ifs
    · exact hd
    · exact lookup_wf hr
  | zero, _, _ => by simp [lookup, WellFormed]
  | one, _, h => by simp [WellFormed] at h

private theorem diag_wf {e : Event α} {n : ℕ} (v : α) (he : e.WellFormed n) (htop : e.top < n) :
    (e.diag v).WellFormed n := by
  obtain ⟨top, acc, rel⟩ := e
  obtain ⟨hlen, hrel⟩ := he
  simp only at hlen hrel htop
  cases acc with
  | nil => exact ⟨by simp [Event.diag]; omega, by simpa [Event.diag] using hrel⟩
  | cons a m =>
    simp only [List.length_cons] at hlen
    rw [relWidth_cons] at hrel
    cases a with
    | skip => exact ⟨by simp [Event.diag]; omega, by simpa [Event.diag, Access.width] using hrel⟩
    | read => exact ⟨by simp [Event.diag]; omega, by simpa [Event.diag] using lookup_wf hrel⟩
    | write => exact ⟨by simp [Event.diag]; omega, by simpa [Event.diag] using lookup_wf hrel⟩
    | readWrite =>
      exact ⟨by simp [Event.diag]; omega, by simpa [Event.diag] using lookup_wf (lookup_wf hrel)⟩

omit [LinearOrder α] in
/-- A transition of a diagonal is a transition of the event that keeps the value at its `top`. -/
private theorem diag_fires [DecidableEq α] {e : Event α} {p : ℕ} (htop : e.top = p) {v : α}
    {x y : List α} (h : (e.diag v).Fires (p + 1) x y) : e.Fires p (v :: x) (v :: y) := by
  obtain ⟨top, acc, rel⟩ := e
  simp only at htop
  subst htop
  cases acc with
  | nil =>
    obtain ⟨t, ht, ha⟩ := h
    simp only [Event.diag, Event.metaAt, Nat.sub_self, List.replicate_zero, List.nil_append,
      apply_nil] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact ⟨[], ht, by simp [Event.metaAt, Apply]⟩
  | cons a m =>
    cases a with
    | skip =>
      obtain ⟨t, ht, ha⟩ := h
      simp only [Event.diag, Event.metaAt, Nat.sub_self, List.replicate_zero, List.nil_append] at ha
      exact ⟨t, ht, by simpa [Event.metaAt, Apply] using ha⟩
    | read =>
      obtain ⟨t, ht, ha⟩ := h
      simp only [Event.diag, Event.metaAt, Nat.sub_self, List.replicate_zero, List.nil_append] at ha ht
      exact ⟨v :: t, lookup_mem ht, by simpa [Event.metaAt, Apply] using ha⟩
    | write =>
      obtain ⟨t, ht, ha⟩ := h
      simp only [Event.diag, Event.metaAt, Nat.sub_self, List.replicate_zero, List.nil_append] at ha ht
      exact ⟨v :: t, lookup_mem ht, by simpa [Event.metaAt, Apply] using ha⟩
    | readWrite =>
      obtain ⟨t, ht, ha⟩ := h
      simp only [Event.diag, Event.metaAt, Nat.sub_self, List.replicate_zero, List.nil_append] at ha ht
      exact ⟨v :: v :: t, lookup_mem (lookup_mem ht), by simpa [Event.metaAt, Apply] using ha⟩

private theorem mem_reachEvents_below {E : List (Event α)} {p : ℕ} {v : α}
    {e : Event α} (he : e ∈ E) (hlt : p < e.top) : e ∈ reachEvents E p v :=
  List.mem_append_left _ (List.mem_filter.mpr ⟨he, by simpa using hlt⟩)

private theorem reachEvents_wf {E : List (Event α)} {n p : ℕ} (v : α)
    (hE : ∀ e ∈ E, e.WellFormed n) (hp : p < n) : ∀ e ∈ reachEvents E p v, e.WellFormed n := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hE e (List.mem_filter.mp he).1
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    obtain ⟨he0, htop⟩ := List.mem_filter.mp he0
    have htop : e0.top = p := by simpa using htop
    exact diag_wf v (hE e0 he0) (by omega)

/-- What REACH finds below a value is reachable from the vectors starting with that value. -/
private theorem reach_cons_events {E : List (Event α)} {p : ℕ} {D : Set (List α)}
    (v : α) {y : List α} (h : Reach (reachEvents E p v) (p + 1) D y) :
    Reach E p (List.cons v '' D) (v :: y) := by
  induction h with
  | base hx => exact Reach.base ⟨_, hx, rfl⟩
  | step e he hp _ hf ih =>
    rcases List.mem_append.mp he with he | he
    · obtain ⟨he, hlt⟩ := List.mem_filter.mp he
      have hlt : p < e.top := by simpa using hlt
      exact Reach.step e he hlt.le ih ((fires_below hlt).2 ⟨v, _, _, rfl, rfl, hf⟩)
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      obtain ⟨he0, htop⟩ := List.mem_filter.mp he0
      have htop : e0.top = p := by simpa using htop
      exact Reach.step e0 he0 htop.ge ih (diag_fires htop hf)


/-! ## The loop -/

/-- **The loop.** If every round from an `Inv`-set that changes it ends in an `Inv`-set with a
    smaller measure, then the loop ends in an `Inv`-set that the round no longer changes. -/
private theorem fixLoop_spec (g h : Ldd α → Ldd α) (Inv : Ldd α → Prop) (μ : Ldd α → ℕ)
    (hstep : ∀ S, Inv S → g S ≠ S → Inv (h (g S)) ∧ μ (h (g S)) < μ S) :
    ∀ S, Inv S → Inv (fixLoop g h S) ∧ g (fixLoop g h S) = fixLoop g h S := by
  intro S hS
  unfold fixLoop
  simp only [Id.run_bind]
  refine MercLib.Util.whileInduction _ (measure (fun s : Ldd α × Ldd α => μ s.1)).wf
    (fun s => Inv s.1 ∧ s.2 = g s.1) (fun s => Inv s.1 ∧ g s.1 = s.1) ?_ (S, g S) ⟨hS, rfl⟩
  rintro ⟨S, T⟩ ⟨hS, hT⟩
  simp only at hS hT
  subst hT
  by_cases hc : g S ≠ S
  · rw [ite_eq_left hc]
    obtain ⟨h1, h2⟩ := hstep S hS hc
    exact ⟨⟨h1, rfl⟩, h2⟩
  · rw [ite_eq_right hc]
    exact ⟨hS, Classical.not_not.mp hc⟩

/-- Two well-formed LDDs of the same height, the first a subset of the second, that differ: the
    first is a strict subset. -/
private theorem ssubset_of_ne {S T : Ldd α} {k : ℕ} (hS : S.WellFormed k) (hT : T.WellFormed k)
    (hsub : S.denote ⊆ T.denote) (hne : T ≠ S) : S.denote ⊂ T.denote :=
  ⟨hsub, fun h => hne (canonical α k T S hT hS (Set.Subset.antisymm h hsub))⟩

omit [LinearOrder α] in
/-- Growing a set within a finite set `T` decreases the number of missing elements of `T`. -/
private theorem missing_lt {T S S' : Set (List α)} (hfin : T.Finite) (h1 : S ⊂ S') (h2 : S' ⊆ T) :
    (T \ S').ncard < (T \ S).ncard := by
  obtain ⟨x, hx', hx⟩ := Set.exists_of_ssubset h1
  exact Set.ncard_lt_ncard ⟨Set.sdiff_subset_sdiff_right h1.1, fun h => (h ⟨h2 hx', hx⟩).2 hx'⟩
    (hfin.sdiff)

/-! ## Firing the events at a position -/

private theorem fireTop_facts {E : List (Event α)} {n p : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    {S : Ldd α} (hS : S.WellFormed (n - p)) :
    (fireTop E p S).WellFormed (n - p) ∧ S.denote ⊆ (fireTop E p S).denote ∧
      (∀ T : Set (List α), S.denote ⊆ T → Closed E p T → (fireTop E p S).denote ⊆ T) ∧
      ((fireTop E p S).denote = S.denote → ∀ e ∈ E, e.top = p → post e p S.denote ⊆ S.denote) := by
  have hL : EventsFit (E.filter (fun e => e.top == p)) p (n - p) := by
    intro e he
    obtain ⟨he, htop⟩ := List.mem_filter.mp he
    have htop : e.top = p := by simpa using htop
    exact ⟨by have := (hE e he).1; omega, (hE e he).2⟩
  obtain ⟨hw, hsub, hbound, hfix⟩ := chain_fold _ S hL hS
  refine ⟨hw, hsub, fun T hST hT => hbound T hST fun e he y ⟨x, hx, hf⟩ => ?_, fun heq e he htop =>
    hfix heq e (List.mem_filter.mpr ⟨he, by simp [htop]⟩)⟩
  obtain ⟨he, htop⟩ := List.mem_filter.mp he
  exact hT e he (by simp at htop; omega) x hx y hf

/-- A set closed below `p` that firing the events at `p` does not change is closed. -/
private theorem closed_of_fixed {E : List (Event α)} {n p : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    {S : Ldd α} (hS : S.WellFormed (n - p)) (hcb : ClosedBelow E p S.denote)
    (hfix : (fireTop E p S).denote = S.denote) : Closed E p S.denote := by
  intro e he hle x hx y hf
  rcases Nat.lt_or_eq_of_le hle with hlt | htop
  · exact hcb e he hlt x hx y hf
  · exact (fireTop_facts hE hS).2.2.2 hfix e he htop.symm ⟨x, hx, hf⟩

/-! ## The children of a node -/

/-- The vectors `v :: y` with `(v, d)` on the spine of `X` and `y` reachable from `d` at the next
    position with the events `F v`: the set after saturating (or reaching) the children of `X`. -/
private def ChildrenOf (F : α → List (Event α)) (p : ℕ) (X : Ldd α) (z : List α) : Prop :=
  ∃ v y d, z = v :: y ∧ (v, d) ∈ X.spine ∧ y ∈ Sat (F v) (p + 1) d.denote

omit [LinearOrder α] in
private theorem mapSpine_eq [LinearOrder α] (f : Ldd α → Ldd α) :
    ∀ X : Ldd α, mapSpine f X = mapSpineWith (fun _ d => f d) X
  | node v d r => by simp [mapSpine, mapSpineWith, mapSpine_eq f r]
  | zero => rfl
  | one => rfl

private theorem mapSpineWith_correct (F : α → List (Event α)) (p k : ℕ) (f : α → Ldd α → Ldd α) :
    ∀ X : Ldd α, X.WellFormed (k + 1) →
      (∀ v d, (v, d) ∈ X.spine →
        (f v d).WellFormed k ∧ (f v d).denote = Sat (F v) (p + 1) d.denote) →
      (mapSpineWith f X).WellFormed (k + 1) ∧
        (∀ w, HeadAbove w X → HeadAbove w (mapSpineWith f X)) ∧
        ∀ z, z ∈ (mapSpineWith f X).denote ↔ ChildrenOf F p X z
  | zero, _, _ => ⟨trivial, fun _ h => h, fun z => by simp [mapSpineWith, ChildrenOf, spine, denote]⟩
  | one, h, _ => absurd h (by simp [WellFormed])
  | node v d r, hX, hf => by
    obtain ⟨hd0, hdw, hrw, hha⟩ := hX
    have hsp : (node v d r).spine = (v, d) :: r.spine := rfl
    obtain ⟨hfw, hfd⟩ := hf v d (by rw [hsp]; exact List.mem_cons_self ..)
    obtain ⟨ihw, ihh, ihd⟩ := mapSpineWith_correct F p k f r hrw
      (fun v' d' hm => hf v' d' (by rw [hsp]; exact List.mem_cons_of_mem _ hm))
    obtain ⟨x, hx⟩ := nonempty_of_ne_zero d k hdw hd0
    have hne : f v d ≠ zero := ne_zero_of_mem (x := x) (by rw [hfd]; exact subset_sat hx)
    simp only [mapSpineWith]
    rw [mk_of_ne_zero hne]
    refine ⟨⟨hne, hfw, ihw, ihh v hha⟩, fun _ h => h, fun z => ?_⟩
    simp only [ChildrenOf, hsp, List.mem_cons]
    rw [show (node v (f v d) (mapSpineWith f r)).denote =
      (List.cons v '' (f v d).denote) ∪ (mapSpineWith f r).denote from rfl, hfd]
    constructor
    · rintro (⟨y, hy, rfl⟩ | hz)
      · exact ⟨v, y, d, rfl, Or.inl rfl, hy⟩
      · obtain ⟨b, y, d2, rfl, hm, hy⟩ := (ihd z).1 hz
        exact ⟨b, y, d2, rfl, Or.inr hm, hy⟩
    · rintro ⟨b, y, d2, rfl, hm | hm, hy⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
        exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ((ihd _).2 ⟨b, y, d2, rfl, hm, hy⟩)

/-- The events `F v` below a value `v` only reach what the events `E` reach from `v`. -/
private def Lifts (E : List (Event α)) (F : α → List (Event α)) (p : ℕ) : Prop :=
  ∀ v (D : Set (List α)) y, Reach (F v) (p + 1) D y → Reach E p (List.cons v '' D) (v :: y)

private theorem children_superset {F : α → List (Event α)} {p k : ℕ} {X Y : Ldd α}
    (hX : X.WellFormed (k + 1)) (hY : ∀ z, z ∈ Y.denote ↔ ChildrenOf F p X z) :
    X.denote ⊆ Y.denote := by
  intro z hz
  obtain ⟨b, y, d, rfl, hm, hy⟩ := (mem_denote_iff hX z).1 hz
  exact (hY _).2 ⟨b, y, d, rfl, hm, subset_sat hy⟩

private theorem children_sound {E : List (Event α)} {F : α → List (Event α)} {p k : ℕ}
    {X Y : Ldd α} (hX : X.WellFormed (k + 1)) (hlift : Lifts E F p)
    (hY : ∀ z, z ∈ Y.denote ↔ ChildrenOf F p X z) : Y.denote ⊆ Sat E p X.denote := by
  intro z hz
  obtain ⟨b, y, d, rfl, hm, hy⟩ := (hY z).1 hz
  refine sat_mono ?_ (hlift b _ y hy)
  rintro _ ⟨y', hy', rfl⟩
  exact (mem_denote_iff hX _).2 ⟨b, y', d, rfl, hm, hy'⟩

omit [LinearOrder α] in
private theorem children_closed {E : List (Event α)} {F : α → List (Event α)} {p : ℕ}
    {X Y : Ldd α} (hbelow : ∀ v, ∀ e ∈ E, p < e.top → e ∈ F v)
    (hY : ∀ z, z ∈ Y.denote ↔ ChildrenOf F p X z) : ClosedBelow E p Y.denote := by
  intro e he hlt x hx y hf
  obtain ⟨a, x', y', rfl, rfl, hf'⟩ := (fires_below hlt).1 hf
  obtain ⟨b, x'', d, heq, hm, hx''⟩ := (hY _).1 hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  exact (hY _).2 ⟨a, y', d, rfl, hm, Reach.step e (hbelow a e he hlt) (by omega) hx'' hf'⟩

/-- Below a value of `X`, only finitely many vectors are reachable when only finitely many are
    reachable from `X`. -/
private theorem child_finite {E : List (Event α)} {F : α → List (Event α)} {p k : ℕ} {X : Ldd α}
    (hX : X.WellFormed (k + 1)) (hlift : Lifts E F p) (hfin : (Sat E p X.denote).Finite)
    {v : α} {d : Ldd α} (hm : (v, d) ∈ X.spine) : (Sat (F v) (p + 1) d.denote).Finite := by
  have hsub : List.cons v '' Sat (F v) (p + 1) d.denote ⊆ Sat E p X.denote := by
    rintro _ ⟨y, hy, rfl⟩
    refine sat_mono ?_ (hlift v _ y hy)
    rintro _ ⟨y', hy', rfl⟩
    exact (mem_denote_iff hX _).2 ⟨v, y', d, rfl, hm, hy'⟩
  exact (hfin.subset hsub).of_finite_image (fun _ _ _ _ h => List.cons_injective h)

/-- Positions at the end of the vectors: the set itself is closed. -/
private theorem sat_end {E : List (Event α)} {n p : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    (h : n - p = 0) {X : Ldd α} (hX : X.WellFormed (n - p)) : Sat E p X.denote = X.denote := by
  rw [h] at hX
  cases X with
  | zero => exact sat_empty
  | one => exact sat_one hE h
  | node v d r => exact absurd hX (by simp [WellFormed])

/-! ## Breadth-first search and chaining -/

private theorem bfs_round {E : List (Event α)} {n : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    {X S : Ldd α} (hS : S.WellFormed n) (h2 : S.denote ⊆ Sat E 0 X.denote) :
    (bfsStep E S).WellFormed n ∧ S.denote ⊆ (bfsStep E S).denote ∧
      (bfsStep E S).denote ⊆ Sat E 0 X.denote ∧
      ((bfsStep E S).denote = S.denote → Closed E 0 S.denote) := by
  unfold bfsStep
  obtain ⟨hw, hd⟩ := bfs_fold S hS E S (eventsFit_zero hE) hS
  refine ⟨hw, by rw [hd]; exact Set.subset_union_left, ?_, fun heq e he _ x hx y hf => ?_⟩
  · rw [hd]
    rintro y (hy | ⟨e, he, x, hx, hf⟩)
    · exact h2 hy
    · exact sat_closed e he (Nat.zero_le _) x (h2 hx) y hf
  · have : y ∈ (E.foldl (fun T e => union T (successors (e.metaAt 0) S e.rel)) S).denote := by
      rw [hd]; exact Or.inr ⟨e, he, x, hx, hf⟩
    rwa [heq] at this

private theorem bfs_terminates (E : List (Event α)) (X : Ldd α) (n : ℕ) : BfsTerminates E X n := by
  intro hE _ S hS h1 h2 hne
  obtain ⟨hw, hsub, hsat, -⟩ := bfs_round hE hS h2
  exact ⟨ssubset_of_ne hS hw hsub hne, hsat⟩

private theorem bfs_correct (E : List (Event α)) (X : Ldd α) (n : ℕ) : BfsCorrect E X n := by
  intro hE hX hfin
  obtain ⟨⟨hw, h1, h2⟩, hfix⟩ := fixLoop_spec (bfsStep E) id
    (fun S => S.WellFormed n ∧ X.denote ⊆ S.denote ∧ S.denote ⊆ Sat E 0 X.denote)
    (fun S => (Sat E 0 X.denote \ S.denote).ncard)
    (fun S ⟨hS, h1, h2⟩ hne => by
      obtain ⟨hw, hsub, hsat, -⟩ := bfs_round hE hS h2
      exact ⟨⟨hw, h1.trans hsub, hsat⟩,
        missing_lt hfin (ssubset_of_ne hS hw hsub hne) hsat⟩)
    X ⟨hX, subset_rfl, subset_sat⟩
  refine ⟨hw, eq_sat_of_closed h1 h2 ?_⟩
  exact (bfs_round hE hw h2).2.2.2 (by rw [hfix])

private theorem chain_round {E : List (Event α)} {n : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    {X S : Ldd α} (hS : S.WellFormed n) (h2 : S.denote ⊆ Sat E 0 X.denote) :
    (chainStep E S).WellFormed n ∧ S.denote ⊆ (chainStep E S).denote ∧
      (chainStep E S).denote ⊆ Sat E 0 X.denote ∧
      ((chainStep E S).denote = S.denote → Closed E 0 S.denote) := by
  obtain ⟨hw, hsub, hbound, hfix⟩ := chain_fold E S (eventsFit_zero hE) hS
  exact ⟨hw, hsub, hbound _ h2 fun e he y ⟨x, hx, hf⟩ => sat_closed e he (Nat.zero_le _) x hx y hf,
    fun heq e he _ x hx y hf => hfix heq e he ⟨x, hx, hf⟩⟩

private theorem chaining_terminates (E : List (Event α)) (X : Ldd α) (n : ℕ) :
    ChainingTerminates E X n := by
  intro hE _ S hS h1 h2 hne
  obtain ⟨hw, hsub, hsat, -⟩ := chain_round hE hS h2
  exact ⟨ssubset_of_ne hS hw hsub hne, hsat⟩

private theorem chaining_correct (E : List (Event α)) (X : Ldd α) (n : ℕ) :
    ChainingCorrect E X n := by
  intro hE hX hfin
  obtain ⟨⟨hw, h1, h2⟩, hfix⟩ := fixLoop_spec (chainStep E) id
    (fun S => S.WellFormed n ∧ X.denote ⊆ S.denote ∧ S.denote ⊆ Sat E 0 X.denote)
    (fun S => (Sat E 0 X.denote \ S.denote).ncard)
    (fun S ⟨hS, h1, h2⟩ hne => by
      obtain ⟨hw, hsub, hsat, -⟩ := chain_round hE hS h2
      exact ⟨⟨hw, h1.trans hsub, hsat⟩,
        missing_lt hfin (ssubset_of_ne hS hw hsub hne) hsat⟩)
    X ⟨hX, subset_rfl, subset_sat⟩
  exact ⟨hw, eq_sat_of_closed h1 h2 ((chain_round hE hw h2).2.2.2 (by rw [hfix]))⟩

/-! ## Recursive saturation -/

/-- What saturating the children of a node with `B` gives. -/
private def SaturatesChildren (E : List (Event α)) (p k : ℕ) (B : Ldd α → Ldd α) : Prop :=
  ∀ Y : Ldd α, Y.WellFormed (k + 1) → (Sat E p Y.denote).Finite →
    (B Y).WellFormed (k + 1) ∧ ∀ z, z ∈ (B Y).denote ↔ ChildrenOf (fun _ => E) p Y z

omit [LinearOrder α] in
private theorem lifts_self [LinearOrder α] {E : List (Event α)} {p : ℕ} : Lifts E (fun _ => E) p :=
  fun v _ _ h => reach_cons v h

omit [LinearOrder α] in
private theorem below_self {E : List (Event α)} {p : ℕ} :
    ∀ (v : α), ∀ e ∈ E, p < e.top → e ∈ (fun _ => E) v :=
  fun _ _ he _ => he

/-- A round of the loop of recursive saturation from a set between `X` and its reachable vectors
    that changes it ends in a strictly larger set between them, closed below `p`. -/
private theorem saturate_round {E : List (Event α)} {n p k : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    (hk : n - p = k + 1) {B : Ldd α → Ldd α} (hB : SaturatesChildren E p k B) {X S : Ldd α}
    (hfin : (Sat E p X.denote).Finite) (hS : S.WellFormed (n - p)) (h2 : S.denote ⊆ Sat E p X.denote)
    (hne : fireTop E p S ≠ S) :
    (B (fireTop E p S)).WellFormed (n - p) ∧ S.denote ⊂ (B (fireTop E p S)).denote ∧
      (B (fireTop E p S)).denote ⊆ Sat E p X.denote ∧
      ClosedBelow E p (B (fireTop E p S)).denote := by
  obtain ⟨hT, hST, hbound, -⟩ := fireTop_facts hE hS
  have hTX : (fireTop E p S).denote ⊆ Sat E p X.denote := hbound _ h2 sat_closed
  have hTfin : (Sat E p (fireTop E p S).denote).Finite := hfin.subset (sat_min hTX sat_closed)
  have hTk : (fireTop E p S).WellFormed (k + 1) := hk ▸ hT
  obtain ⟨hBw, hBd⟩ := hB _ hTk hTfin
  refine ⟨hk ▸ hBw, ?_, (children_sound hTk lifts_self hBd).trans (sat_min hTX sat_closed),
    children_closed below_self hBd⟩
  exact (ssubset_of_ne hS hT hST hne).trans_subset (children_superset hTk hBd)

private theorem saturate_correct (E : List (Event α)) {n : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    (p : ℕ) (hp : p ≤ n) (X : Ldd α) (hX : X.WellFormed (n - p))
    (hfin : (Sat E p X.denote).Finite) :
    (saturate E n p X).WellFormed (n - p) ∧ (saturate E n p X).denote = Sat E p X.denote := by
  rw [saturate]
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, n - p = k + 1 := ⟨n - p - 1, by omega⟩
    have hB : SaturatesChildren E p k (mapSpine fun d => saturate E n (p + 1) d) := by
      intro Y hY hYfin
      rw [mapSpine_eq]
      obtain ⟨w, -, d⟩ := mapSpineWith_correct (fun _ => E) p k _ Y hY fun v d hm => by
        have hdk : n - (p + 1) = k := by omega
        have := saturate_correct E hE (p + 1) (by omega) d (hdk ▸ (spine_wf hY hm).1)
          (child_finite hY lifts_self hYfin hm)
        rwa [hdk] at this
      exact ⟨w, d⟩
    have hXk : X.WellFormed (k + 1) := hk ▸ hX
    obtain ⟨hB0w, hB0⟩ := hB X hXk hfin
    obtain ⟨⟨hw, h1, h2, hcb⟩, hfix⟩ := fixLoop_spec (fireTop E p) _
      (fun S => S.WellFormed (n - p) ∧ X.denote ⊆ S.denote ∧ S.denote ⊆ Sat E p X.denote ∧
        ClosedBelow E p S.denote)
      (fun S => (Sat E p X.denote \ S.denote).ncard)
      (fun S ⟨hS, h1, h2, _⟩ hne => by
        obtain ⟨hw, hlt, hsat, hcb⟩ := saturate_round hE hk hB hfin hS h2 hne
        exact ⟨⟨hw, h1.trans hlt.1, hsat, hcb⟩, missing_lt hfin hlt hsat⟩)
      _ ⟨hk ▸ hB0w, children_superset hXk hB0, children_sound hXk lifts_self hB0,
        children_closed below_self hB0⟩
    exact ⟨hw, eq_sat_of_closed h1 h2 (closed_of_fixed hE hw hcb (by rw [hfix]))⟩
  · exact ⟨hX, (sat_end hE (by omega) hX).symm⟩
termination_by n - p
decreasing_by omega

private theorem saturate_terminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateTerminates E n p X := by
  intro hE hp _ hfin S hS _ h2 hne
  obtain ⟨k, hk⟩ : ∃ k, n - p = k + 1 := ⟨n - p - 1, by omega⟩
  have hB : SaturatesChildren E p k (mapSpine fun d => saturate E n (p + 1) d) := by
    intro Y hY hYfin
    rw [mapSpine_eq]
    obtain ⟨w, -, d⟩ := mapSpineWith_correct (fun _ => E) p k _ Y hY fun v d hm => by
      have hdk : n - (p + 1) = k := by omega
      have := saturate_correct E hE (p + 1) (by omega) d (hdk ▸ (spine_wf hY hm).1)
        (child_finite hY lifts_self hYfin hm)
      rwa [hdk] at this
    exact ⟨w, d⟩
  obtain ⟨-, hlt, hsat, -⟩ := saturate_round hE hk hB hfin hS h2 hne
  exact ⟨hlt, hsat⟩

/-! ## REACH -/

private theorem lifts_reachEvents {E : List (Event α)} {p : ℕ} : Lifts E (reachEvents E p) p :=
  fun v _ _ h => reach_cons_events v h

/-- What REACH of the children of a node with `B` gives. -/
private def ReachesChildren (E : List (Event α)) (p k : ℕ) (B : Ldd α → Ldd α) : Prop :=
  ∀ Y : Ldd α, Y.WellFormed (k + 1) → (Sat E p Y.denote).Finite →
    (B Y).WellFormed (k + 1) ∧ ∀ z, z ∈ (B Y).denote ↔ ChildrenOf (reachEvents E p) p Y z

/-- A round of REACH from a set between `X` and its reachable vectors: reaching the children and
    firing the events at `p` stays between them, and when it changes nothing the set is closed. -/
private theorem reach_round {E : List (Event α)} {n p k : ℕ} (hE : ∀ e ∈ E, e.WellFormed n)
    (hk : n - p = k + 1) {B : Ldd α → Ldd α} (hB : ReachesChildren E p k B) {X S : Ldd α}
    (hfin : (Sat E p X.denote).Finite) (hS : S.WellFormed (n - p)) (h2 : S.denote ⊆ Sat E p X.denote) :
    (fireTop E p (B S)).WellFormed (n - p) ∧ S.denote ⊆ (fireTop E p (B S)).denote ∧
      (fireTop E p (B S)).denote ⊆ Sat E p X.denote ∧
      (fireTop E p (B S) = S → Closed E p S.denote) := by
  have hSk : S.WellFormed (k + 1) := hk ▸ hS
  obtain ⟨hBw, hBd⟩ := hB S hSk (hfin.subset (sat_min h2 sat_closed))
  have hBw' : (B S).WellFormed (n - p) := hk ▸ hBw
  have hSB := children_superset hSk hBd
  have hBX : (B S).denote ⊆ Sat E p X.denote :=
    (children_sound hSk lifts_reachEvents hBd).trans (sat_min h2 sat_closed)
  obtain ⟨hT, hBT, hbound, -⟩ := fireTop_facts hE hBw'
  refine ⟨hT, hSB.trans hBT, hbound _ hBX sat_closed, fun heq => ?_⟩
  have hBS : (B S).denote = S.denote :=
    Set.Subset.antisymm (by have := hBT; rwa [heq] at this) hSB
  have hcl := closed_of_fixed hE hBw'
    (children_closed (fun v e he hlt => mem_reachEvents_below he hlt) hBd)
    (Set.Subset.antisymm (by rw [heq, hBS]) hBT)
  rwa [hBS] at hcl

private theorem reachesChildren {E : List (Event α)} {n p k : ℕ} (hk : n - p = k + 1)
    (ih : ∀ v (d : Ldd α), d.WellFormed (n - (p + 1)) →
      (Sat (reachEvents E p v) (p + 1) d.denote).Finite →
      (reach (reachEvents E p v) n (p + 1) d).WellFormed (n - (p + 1)) ∧
        (reach (reachEvents E p v) n (p + 1) d).denote = Sat (reachEvents E p v) (p + 1) d.denote) :
    ReachesChildren E p k (mapSpineWith fun v d => reach (reachEvents E p v) n (p + 1) d) := by
  intro Y hY hYfin
  obtain ⟨w, -, d⟩ := mapSpineWith_correct (reachEvents E p) p k _ Y hY fun v d hm => by
    have hdk : n - (p + 1) = k := by omega
    have := ih v d (hdk ▸ (spine_wf hY hm).1) (child_finite hY lifts_reachEvents hYfin hm)
    rwa [hdk] at this
  exact ⟨w, d⟩

private theorem reach_correct {n : ℕ} (p : ℕ) (E : List (Event α))
    (hE : ∀ e ∈ E, e.WellFormed n) (hp : p ≤ n) (X : Ldd α) (hX : X.WellFormed (n - p))
    (hfin : (Sat E p X.denote).Finite) :
    (reach E n p X).WellFormed (n - p) ∧ (reach E n p X).denote = Sat E p X.denote := by
  rw [reach]
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, n - p = k + 1 := ⟨n - p - 1, by omega⟩
    have hB := reachesChildren hk fun v d hd hdfin =>
      reach_correct (p + 1) (reachEvents E p v) (reachEvents_wf v hE h) (by omega) d hd hdfin
    obtain ⟨⟨hw, h1, h2⟩, hfix⟩ := fixLoop_spec _ id
      (fun S => S.WellFormed (n - p) ∧ X.denote ⊆ S.denote ∧ S.denote ⊆ Sat E p X.denote)
      (fun S => (Sat E p X.denote \ S.denote).ncard)
      (fun S ⟨hS, h1, h2⟩ hne => by
        obtain ⟨hw, hsub, hsat, -⟩ := reach_round hE hk hB hfin hS h2
        exact ⟨⟨hw, h1.trans hsub, hsat⟩, missing_lt hfin (ssubset_of_ne hS hw hsub hne) hsat⟩)
      X ⟨hX, subset_rfl, subset_sat⟩
    exact ⟨hw, eq_sat_of_closed h1 h2 ((reach_round hE hk hB hfin hw h2).2.2.2 hfix)⟩
  · exact ⟨hX, (sat_end hE (by omega) hX).symm⟩
termination_by n - p
decreasing_by omega

private theorem reach_terminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    ReachTerminates E n p X := by
  intro hE hp _ hfin S hS _ h2 S' hne
  obtain ⟨k, hk⟩ : ∃ k, n - p = k + 1 := ⟨n - p - 1, by omega⟩
  have hB := reachesChildren hk fun v d hd hdfin =>
    reach_correct (p + 1) (reachEvents E p v) (reachEvents_wf v hE hp) (by omega) d hd hdfin
  obtain ⟨hw, hsub, hsat, -⟩ := reach_round hE hk hB hfin hS h2
  exact ⟨ssubset_of_ne hS hw hsub hne, hsat⟩

/-! ## Node-wise saturation -/

omit [LinearOrder α] in
private theorem entries_eq_spine : ∀ X : Ldd α, X.entries = X.spine
  | node v d r => by simp [entries, spine, entries_eq_spine r]
  | zero => rfl
  | one => rfl

/-- The continuation of `j` in a well-formed `S`: the vectors `y` with `j :: y` in `S`. -/
private theorem lookup_denote : ∀ {S : Ldd α} {k : ℕ}, S.WellFormed (k + 1) → ∀ j : α,
    (S.lookup j).denote = {y | j :: y ∈ S.denote}
  | zero, _, _, j => by simp [lookup, denote]
  | one, _, h, _ => absurd h (by simp [WellFormed])
  | node w d r, k, h, j => by
    obtain ⟨-, -, hr, hha⟩ := h
    ext y
    simp only [lookup, Set.mem_ofPred_eq]
    rw [show (node w d r).denote = (List.cons w '' d.denote) ∪ r.denote from rfl]
    split_ifs with hw
    · subst hw
      constructor
      · intro hy; exact Or.inl ⟨y, hy, rfl⟩
      · rintro (⟨y', hy', heq⟩ | hy)
        · obtain ⟨-, rfl⟩ := List.cons.inj heq; exact hy'
        · exact absurd hy (not_mem_of_headAbove hr hha y)
    · rw [lookup_denote hr j]
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
      constructor
      · exact Or.inr
      · rintro (⟨y', -, heq⟩ | hy)
        · exact absurd (List.cons.inj heq).1 hw
        · exact hy

private theorem mem_lookup {S : Ldd α} {k : ℕ} (hS : S.WellFormed (k + 1)) {x : List α}
    (hx : x ∈ S.denote) : ∃ i y, x = i :: y ∧ y ∈ (S.lookup i).denote := by
  obtain ⟨b, y, d, rfl, -, -⟩ := (mem_denote_iff hS x).1 hx
  exact ⟨b, y, rfl, by rw [lookup_denote hS]; exact hx⟩

private theorem lookup_mono {S T : Ldd α} {k : ℕ} (hS : S.WellFormed (k + 1))
    (hT : T.WellFormed (k + 1)) (h : S.denote ⊆ T.denote) (j : α) :
    (S.lookup j).denote ⊆ (T.lookup j).denote := by
  rw [lookup_denote hS, lookup_denote hT]
  exact fun y hy => h hy

private theorem cons_lookup_subset {S : Ldd α} {k : ℕ} (hS : S.WellFormed (k + 1)) (i : α) :
    List.cons i '' (S.lookup i).denote ⊆ S.denote := by
  rintro _ ⟨y, hy, rfl⟩
  rw [lookup_denote hS] at hy
  exact hy

omit [LinearOrder α] in
private theorem lookup_eq_zero [LinearOrder α] {i : α} :
    ∀ {S : Ldd α}, i ∉ S.entries.map Prod.fst → S.lookup i = zero
  | node w d r, h => by
    simp only [entries, List.map_cons, List.mem_cons, not_or] at h
    simp only [lookup, ite_eq_right (Ne.symm h.1)]
    exact lookup_eq_zero h.2
  | zero, _ => rfl
  | one, _ => rfl

private theorem rows_wf {e : Event α} {n : ℕ} (he : e.WellFormed n) (i : α) :
    ∀ row ∈ e.rows i, row.2.WellFormed (relWidth e.access.tail) := by
  obtain ⟨top, acc, rel⟩ := e
  obtain ⟨-, hrel⟩ := he
  simp only at hrel
  intro row hrow
  cases acc with
  | nil => simp [Event.rows] at hrow
  | cons a m =>
    rw [relWidth_cons] at hrel
    cases a with
    | skip =>
      simp only [Event.rows, List.mem_singleton] at hrow
      subst hrow
      simpa [Access.width] using hrel
    | read =>
      simp only [Event.rows, List.mem_singleton] at hrow
      subst hrow
      exact lookup_wf hrel
    | write =>
      simp only [Event.rows] at hrow
      rw [entries_eq_spine] at hrow
      exact (spine_wf hrel hrow).1
    | readWrite =>
      simp only [Event.rows] at hrow
      rw [entries_eq_spine] at hrow
      exact (spine_wf (lookup_wf (k := relWidth m + 1) hrel) hrow).1

/-- The successors of `A` under a row, at the next position. -/
private theorem rows_successors {e : Event α} {n p k : ℕ} (he : e.WellFormed n) (htop : e.top = p)
    (hk : n - p = k + 1) {A : Ldd α} (hA : A.WellFormed k) {i : α} {row : α × Ldd α}
    (hrow : row ∈ e.rows i) :
    (successors e.access.tail A row.2).WellFormed k ∧
      (successors e.access.tail A row.2).denote =
        {y | ∃ x ∈ A.denote, ∃ t ∈ row.2.denote, Apply e.access.tail t x y} :=
  successorsCorrect _ A row.2 k (by have := he.1; simp; omega) hA (rows_wf he i row hrow)

/-- The rows of an event from `i` give exactly the successors of the vectors `i :: x` that are not
    `i :: x` itself, or more. -/
private theorem rows_sound {e : Event α} {n p k : ℕ} (he : e.WellFormed n) (htop : e.top = p)
    (hk : n - p = k + 1) {A : Ldd α} (hA : A.WellFormed k) {i : α} {row : α × Ldd α}
    (hrow : row ∈ e.rows i) :
    List.cons row.1 '' (successors e.access.tail A row.2).denote ⊆
      post e p (List.cons i '' A.denote) := by
  rw [(rows_successors he htop hk hA hrow).2]
  rintro _ ⟨y, ⟨x, hx, t, ht, ha⟩, rfl⟩
  obtain ⟨top, acc, rel⟩ := e
  simp only at htop
  subst htop
  have hrel := he.2
  simp only at hrel
  refine ⟨i :: x, ⟨x, hx, rfl⟩, ?_⟩
  simp only [Event.Fires, Event.metaAt, Nat.sub_self, List.replicate_zero, List.nil_append]
  cases acc with
  | nil => simp [Event.rows] at hrow
  | cons a m =>
    rw [relWidth_cons] at hrel
    simp only [List.tail_cons] at ha
    cases a with
    | skip =>
      simp only [Event.rows, List.mem_singleton] at hrow
      subst hrow
      exact ⟨t, ht, by simpa [Apply] using ha⟩
    | read =>
      simp only [Event.rows, List.mem_singleton] at hrow
      subst hrow
      exact ⟨i :: t, lookup_mem ht, by simpa [Apply] using ha⟩
    | write =>
      simp only [Event.rows] at hrow
      rw [entries_eq_spine] at hrow
      exact ⟨row.1 :: t, (mem_denote_iff hrel _).2 ⟨row.1, t, row.2, rfl, hrow, ht⟩,
        by simpa [Apply] using ha⟩
    | readWrite =>
      simp only [Event.rows] at hrow
      rw [entries_eq_spine] at hrow
      have hl : rel.lookup i |>.WellFormed (relWidth m + 1) := lookup_wf (k := relWidth m + 1) hrel
      exact ⟨i :: row.1 :: t, lookup_mem ((mem_denote_iff hl _).2 ⟨row.1, t, row.2, rfl, hrow, ht⟩),
        by simpa [Apply] using ha⟩

private theorem rows_complete {e : Event α} {n p k : ℕ} (he : e.WellFormed n) (htop : e.top = p)
    (hk : n - p = k + 1) {A : Ldd α} (hA : A.WellFormed k) (i : α) :
    post e p (List.cons i '' A.denote) ⊆ List.cons i '' A.denote ∪
      {z | ∃ row ∈ e.rows i, z ∈ List.cons row.1 '' (successors e.access.tail A row.2).denote} := by
  rintro y ⟨_, ⟨x, hx, rfl⟩, t, ht, ha⟩
  have hsucc := fun {row} (hrow : row ∈ e.rows i) => (rows_successors he htop hk hA hrow).2
  obtain ⟨top, acc, rel⟩ := e
  simp only at htop
  subst htop
  have hrel := he.2
  simp only at hrel
  simp only [Event.metaAt, Nat.sub_self, List.replicate_zero, List.nil_append] at ha
  cases acc with
  | nil =>
    obtain ⟨-, rfl⟩ := apply_nil.1 ha
    exact Or.inl ⟨x, hx, rfl⟩
  | cons a m =>
    rw [relWidth_cons] at hrel
    right
    cases a with
    | skip =>
      obtain ⟨b, x', y', hxx, rfl, ha⟩ := apply_skip.1 ha
      obtain ⟨rfl, rfl⟩ := List.cons.inj hxx
      refine ⟨(i, rel), by simp [Event.rows], y', ?_, rfl⟩
      rw [hsucc (by simp [Event.rows])]
      exact ⟨x, hx, t, ht, ha⟩
    | read =>
      obtain ⟨b, t', x', y', rfl, hxx, rfl, ha⟩ := apply_read.1 ha
      obtain ⟨rfl, rfl⟩ := List.cons.inj hxx
      refine ⟨(i, rel.lookup i), by simp [Event.rows], y', ?_, rfl⟩
      rw [hsucc (by simp [Event.rows])]
      exact ⟨x, hx, t', by rw [lookup_denote hrel]; exact ht, ha⟩
    | write =>
      obtain ⟨c, t', b, x', y', rfl, hxx, rfl, ha⟩ := apply_write.1 ha
      obtain ⟨rfl, rfl⟩ := List.cons.inj hxx
      obtain ⟨c', t'', d, hct, hm, ht'⟩ := (mem_denote_iff hrel _).1 ht
      obtain ⟨rfl, rfl⟩ := List.cons.inj hct
      have hrow : (c, d) ∈ Event.rows ⟨top, .write :: m, rel⟩ i := by
        simp only [Event.rows]; rw [entries_eq_spine]; exact hm
      exact ⟨(c, d), hrow, y', by rw [hsucc hrow]; exact ⟨x, hx, t', ht', ha⟩, rfl⟩
    | readWrite =>
      obtain ⟨b, c, t', x', y', rfl, hxx, rfl, ha⟩ := apply_readWrite.1 ha
      obtain ⟨rfl, rfl⟩ := List.cons.inj hxx
      have hl : (rel.lookup i).WellFormed (relWidth m + 1) := lookup_wf (k := relWidth m + 1) hrel
      have hct : c :: t' ∈ (rel.lookup i).denote := by rw [lookup_denote hrel]; exact ht
      obtain ⟨c', t'', d, hct', hm, ht'⟩ := (mem_denote_iff hl _).1 hct
      obtain ⟨rfl, rfl⟩ := List.cons.inj hct'
      have hrow : (c, d) ∈ Event.rows ⟨top, .readWrite :: m, rel⟩ i := by
        simp only [Event.rows]; rw [entries_eq_spine]; exact hm
      exact ⟨(c, d), hrow, y', by rw [hsucc hrow]; exact ⟨x, hx, t', ht', ha⟩, rfl⟩

/-- The rows of the events at `p` from the value `i`, one event after the other. -/
private def fireEvent (sat : Ldd α → Ldd α) (i : α) (s : Ldd α × List α) (e : Event α) :
    Ldd α × List α :=
  (e.rows i).foldl (addRow sat e (s.1.lookup i)) s

private theorem fireValue_eq (sat : Ldd α → Ldd α) (E : List (Event α)) (p : ℕ) (i : α)
    (S : Ldd α) (F : List α) :
    fireValue sat E p i S F = (E.filter (fun e => e.top == p)).foldl (fireEvent sat i) (S, F) := by
  unfold fireValue
  simp [List.forIn_pure_yield_eq_foldl]
  rfl

/-- What the node-wise saturation needs of the saturation `sat` of a continuation. -/
private def SatNext (E : List (Event α)) (p k : ℕ) (sat : Ldd α → Ldd α) : Prop :=
  ∀ d : Ldd α, d.WellFormed k → (Sat E (p + 1) d.denote).Finite →
    (sat d).WellFormed k ∧ (sat d).denote = Sat E (p + 1) d.denote

/-- The effect of a row. -/
private theorem addRow_facts {E : List (Event α)} {n p k : ℕ} {X : Ldd α}
    {sat : Ldd α → Ldd α} (hk : n - p = k + 1) (hfin : (Sat E p X.denote).Finite)
    (hsat : SatNext E p k sat) {e : Event α} (heE : e ∈ E) (he : e.WellFormed n)
    (htop : e.top = p) {i : α} {row : α × Ldd α} (hrow : row ∈ e.rows i) {A : Ldd α}
    (hA : A.WellFormed k) (hAX : List.cons i '' A.denote ⊆ Sat E p X.denote)
    {s : Ldd α × List α} (hs : s.1.WellFormed (k + 1)) (hsX : s.1.denote ⊆ Sat E p X.denote) :
    (addRow sat e A s row).1.WellFormed (k + 1) ∧ s.1.denote ⊆ (addRow sat e A s row).1.denote ∧
      (addRow sat e A s row).1.denote ⊆ Sat E p X.denote ∧
      List.cons row.1 '' (successors e.access.tail A row.2).denote ⊆
        (addRow sat e A s row).1.denote ∧
      (ClosedBelow E p s.1.denote → ClosedBelow E p (addRow sat e A s row).1.denote) ∧
      ((addRow sat e A s row).1 = s.1 → (addRow sat e A s row).2 = s.2) ∧
      (∀ j ∈ s.2, j ∈ (addRow sat e A s row).2) ∧
      (∀ j, ((addRow sat e A s row).1.lookup j).denote ≠ (s.1.lookup j).denote →
        j ∈ (addRow sat e A s row).2) := by
  obtain ⟨hsw, -⟩ := rows_successors he htop hk hA hrow
  have hsuccX : List.cons row.1 '' (successors e.access.tail A row.2).denote ⊆ Sat E p X.denote :=
    (rows_sound he htop hk hA hrow).trans fun y ⟨x, hx, hf⟩ =>
      sat_closed e heE htop.ge x (hAX hx) y hf
  -- What is reachable below `row.1` from the successors is reachable from `X`.
  have hreach : List.cons row.1 '' Sat E (p + 1) (successors e.access.tail A row.2).denote ⊆
      Sat E p X.denote := by
    rintro _ ⟨y, hy, rfl⟩
    exact sat_min hsuccX sat_closed (reach_cons row.1 hy)
  have hfinsucc : (Sat E (p + 1) (successors e.access.tail A row.2).denote).Finite :=
    (hfin.subset hreach).of_finite_image (fun _ _ _ _ h => List.cons_injective h)
  obtain ⟨hfw, hfd⟩ := hsat _ hsw hfinsucc
  unfold addRow
  generalize sat (successors e.access.tail A row.2) = f at hfw hfd ⊢
  have hMw : (mk row.1 f zero).WellFormed (k + 1) := wellFormed_mk hfw trivial trivial
  have hMd : (mk row.1 f zero).denote = List.cons row.1 '' f.denote := by
    rw [denote_mk]; simp [denote]
  obtain ⟨hUw, hUd⟩ := unionCorrect s.1 _ (k + 1) hs hMw
  have hU1 : s.1.denote ⊆ (union s.1 (mk row.1 f zero)).denote := by
    rw [hUd]; exact Set.subset_union_left
  have hUX : (union s.1 (mk row.1 f zero)).denote ⊆ Sat E p X.denote := by
    rw [hUd, hMd, hfd]; exact Set.union_subset hsX hreach
  have hUsucc : List.cons row.1 '' (successors e.access.tail A row.2).denote ⊆
      (union s.1 (mk row.1 f zero)).denote := by
    rw [hUd, hMd, hfd]; exact (Set.image_mono subset_sat).trans Set.subset_union_right
  have hUcb : ClosedBelow E p s.1.denote →
      ClosedBelow E p (union s.1 (mk row.1 f zero)).denote := by
    intro hcb e' he' hlt x hx y hf'
    rw [hUd, hMd] at hx ⊢
    rcases hx with hx | ⟨y0, hy0, rfl⟩
    · exact Or.inl (hcb e' he' hlt x hx y hf')
    · obtain ⟨a, x', y', hxx, rfl, hf''⟩ := (fires_below hlt).1 hf'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hxx
      rw [hfd] at hy0 ⊢
      exact Or.inr ⟨y', Reach.step e' he' (by omega) hy0 hf'', rfl⟩
  have hUlook : ∀ j, j ≠ row.1 →
      ((union s.1 (mk row.1 f zero)).lookup j).denote = (s.1.lookup j).denote := by
    intro j hj
    rw [lookup_denote hUw, lookup_denote hs, hUd, hMd]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro (h | ⟨y', -, heq⟩)
      · exact h
      · exact absurd (List.cons.inj heq).1.symm hj
    · exact Or.inl
  dsimp only
  split_ifs with hne hj
  · refine ⟨hUw, hU1, hUX, hUsucc, hUcb, fun h => absurd h hne, fun j hj' => hj', fun j hj' => ?_⟩
    by_cases hjr : j = row.1
    · subst hjr; exact hj
    · exact absurd (hUlook j hjr) hj'
  · refine ⟨hUw, hU1, hUX, hUsucc, hUcb, fun h => absurd h hne,
      fun j hj' => List.mem_append_left _ hj', fun j hj' => ?_⟩
    by_cases hjr : j = row.1
    · subst hjr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact absurd (hUlook j hjr) hj'
  · have heq : union s.1 (mk row.1 f zero) = s.1 := Classical.not_not.mp hne
    exact ⟨hs, subset_rfl, hsX, heq ▸ hUsucc, id, fun _ => rfl, fun _ h => h,
      fun _ h => absurd rfl h⟩

/-- The effect of the rows of one event, from the continuation `A`. -/
private theorem rows_fold {E : List (Event α)} {n p k : ℕ} {X : Ldd α} {sat : Ldd α → Ldd α}
    (hk : n - p = k + 1) (hfin : (Sat E p X.denote).Finite) (hsat : SatNext E p k sat)
    {e : Event α} (heE : e ∈ E) (he : e.WellFormed n) (htop : e.top = p) {i : α} {A : Ldd α}
    (hA : A.WellFormed k) (hAX : List.cons i '' A.denote ⊆ Sat E p X.denote) :
    ∀ (rs : List (α × Ldd α)), (∀ row ∈ rs, row ∈ e.rows i) → ∀ s : Ldd α × List α,
      s.1.WellFormed (k + 1) → s.1.denote ⊆ Sat E p X.denote →
      (rs.foldl (addRow sat e A) s).1.WellFormed (k + 1) ∧
      s.1.denote ⊆ (rs.foldl (addRow sat e A) s).1.denote ∧
      (rs.foldl (addRow sat e A) s).1.denote ⊆ Sat E p X.denote ∧
      (∀ row ∈ rs, List.cons row.1 '' (successors e.access.tail A row.2).denote ⊆
        (rs.foldl (addRow sat e A) s).1.denote) ∧
      (ClosedBelow E p s.1.denote → ClosedBelow E p (rs.foldl (addRow sat e A) s).1.denote) ∧
      ((rs.foldl (addRow sat e A) s).1 = s.1 → (rs.foldl (addRow sat e A) s).2 = s.2) ∧
      (∀ j ∈ s.2, j ∈ (rs.foldl (addRow sat e A) s).2) ∧
      (∀ j, ((rs.foldl (addRow sat e A) s).1.lookup j).denote ≠ (s.1.lookup j).denote →
        j ∈ (rs.foldl (addRow sat e A) s).2)
  | [], _, s, hs, hsX => ⟨hs, subset_rfl, hsX, fun _ h => by simp at h, id, fun _ => rfl,
      fun _ h => h, fun _ h => absurd rfl h⟩
  | row :: rs, hrs, s, hs, hsX => by
    obtain ⟨h1w, h1sub, h1X, h1succ, h1cb, h1eq, h1F, h1look⟩ :=
      addRow_facts hk hfin hsat heE he htop (hrs row (List.mem_cons_self ..)) hA hAX hs hsX
    obtain ⟨h2w, h2sub, h2X, h2succ, h2cb, h2eq, h2F, h2look⟩ :=
      rows_fold hk hfin hsat heE he htop hA hAX rs (fun r hr => hrs r (List.mem_cons_of_mem _ hr))
        _ h1w h1X
    simp only [List.foldl_cons]
    refine ⟨h2w, h1sub.trans h2sub, h2X, ?_, fun h => h2cb (h1cb h), ?_,
      fun j hj => h2F j (h1F j hj), ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with hr | hr
      · subst hr; exact h1succ.trans h2sub
      · exact h2succ r hr
    · intro heq
      have hs1 : (addRow sat e A s row).1 = s.1 :=
        canonical α (k + 1) _ _ h1w hs (Set.Subset.antisymm (by rw [← heq]; exact h2sub) h1sub)
      rw [← h1eq hs1]
      exact h2eq (heq.trans hs1.symm)
    · intro j hj
      by_cases hj1 : ((addRow sat e A s row).1.lookup j).denote = (s.1.lookup j).denote
      · exact h2look j (by rw [hj1]; exact hj)
      · exact h2F j (h1look j hj1)

/-- The effect of firing the events `es` (at `p`) out of the value `i`. -/
private theorem events_fold {E : List (Event α)} {n p k : ℕ} {X : Ldd α} {sat : Ldd α → Ldd α}
    (hE : ∀ e ∈ E, e.WellFormed n) (hk : n - p = k + 1) (hfin : (Sat E p X.denote).Finite)
    (hsat : SatNext E p k sat) (i : α) :
    ∀ (es : List (Event α)), (∀ e ∈ es, e ∈ E ∧ e.top = p) → ∀ s : Ldd α × List α,
      s.1.WellFormed (k + 1) → s.1.denote ⊆ Sat E p X.denote →
      (es.foldl (fireEvent sat i) s).1.WellFormed (k + 1) ∧
      s.1.denote ⊆ (es.foldl (fireEvent sat i) s).1.denote ∧
      (es.foldl (fireEvent sat i) s).1.denote ⊆ Sat E p X.denote ∧
      (ClosedBelow E p s.1.denote → ClosedBelow E p (es.foldl (fireEvent sat i) s).1.denote) ∧
      ((es.foldl (fireEvent sat i) s).1 = s.1 → (es.foldl (fireEvent sat i) s).2 = s.2) ∧
      (∀ j ∈ s.2, j ∈ (es.foldl (fireEvent sat i) s).2) ∧
      (∀ j, ((es.foldl (fireEvent sat i) s).1.lookup j).denote ≠ (s.1.lookup j).denote →
        j ∈ (es.foldl (fireEvent sat i) s).2) ∧
      (((es.foldl (fireEvent sat i) s).1.lookup i).denote = (s.1.lookup i).denote →
        ∀ e ∈ es, post e p (List.cons i '' (s.1.lookup i).denote) ⊆
          (es.foldl (fireEvent sat i) s).1.denote)
  | [], _, s, hs, hsX => ⟨hs, subset_rfl, hsX, id, fun _ => rfl, fun _ h => h,
      fun _ h => absurd rfl h, fun _ _ h => by simp at h⟩
  | e :: es, hes, s, hs, hsX => by
    obtain ⟨heE, htop⟩ := hes e (List.mem_cons_self ..)
    have he := hE e heE
    have hA : (s.1.lookup i).WellFormed k := lookup_wf hs
    have hAs := cons_lookup_subset hs i
    obtain ⟨h1w, h1sub, h1X, h1succ, h1cb, h1eq, h1F, h1look⟩ :=
      rows_fold hk hfin hsat heE he htop hA (hAs.trans hsX) (e.rows i) (fun _ h => h) s hs hsX
    obtain ⟨h2w, h2sub, h2X, h2cb, h2eq, h2F, h2look, h2post⟩ :=
      events_fold hE hk hfin hsat i es (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
        _ h1w h1X
    rw [List.foldl_cons, show fireEvent sat i s e =
      (e.rows i).foldl (addRow sat e (s.1.lookup i)) s from rfl]
    have hpost1 : post e p (List.cons i '' (s.1.lookup i).denote) ⊆
        ((e.rows i).foldl (addRow sat e (s.1.lookup i)) s).1.denote := by
      refine (rows_complete he htop hk hA i).trans (Set.union_subset (hAs.trans h1sub) ?_)
      rintro z ⟨row, hrow, hz⟩
      exact h1succ row hrow hz
    refine ⟨h2w, h1sub.trans h2sub, h2X, fun h => h2cb (h1cb h), ?_,
      fun j hj => h2F j (h1F j hj), ?_, ?_⟩
    · intro heq
      have hs1 : ((e.rows i).foldl (addRow sat e (s.1.lookup i)) s).1 = s.1 :=
        canonical α (k + 1) _ _ h1w hs (Set.Subset.antisymm
          (fun x hx => by have := h2sub hx; rwa [heq] at this) h1sub)
      rw [← h1eq hs1]
      exact h2eq (heq.trans hs1.symm)
    · intro j hj
      by_cases hj1 : (((e.rows i).foldl (addRow sat e (s.1.lookup i)) s).1.lookup j).denote = (s.1.lookup j).denote
      · exact h2look j (by rw [hj1]; exact hj)
      · exact h2F j (h1look j hj1)
    · intro hlook e' he'
      have hl1 : (((e.rows i).foldl (addRow sat e (s.1.lookup i)) s).1.lookup i).denote = (s.1.lookup i).denote :=
        Set.Subset.antisymm
          (fun y hy => by have := lookup_mono h1w h2w h2sub i hy; rwa [hlook] at this)
          (lookup_mono hs h1w h1sub i)
      rcases List.mem_cons.mp he' with he' | he'
      · subst he'; exact hpost1.trans h2sub
      · have := h2post (hlook.trans hl1.symm) e' he'
        rwa [hl1] at this

/-- One round of the loop of the node-wise saturation: firing out of the first value `i` of the
    frontier `F`. -/
private theorem nodewise_round {E : List (Event α)} {n p k : ℕ} {X : Ldd α}
    {sat : Ldd α → Ldd α} (hE : ∀ e ∈ E, e.WellFormed n) (hk : n - p = k + 1)
    (hfin : (Sat E p X.denote).Finite) (hsat : SatNext E p k sat) (i : α) (S : Ldd α)
    (F : List α) (hS : S.WellFormed (k + 1)) (hSX : S.denote ⊆ Sat E p X.denote) :
    (fireValue sat E p i S F).1.WellFormed (k + 1) ∧ S.denote ⊆ (fireValue sat E p i S F).1.denote ∧
      (fireValue sat E p i S F).1.denote ⊆ Sat E p X.denote ∧
      (ClosedBelow E p S.denote → ClosedBelow E p (fireValue sat E p i S F).1.denote) ∧
      ((fireValue sat E p i S F).1 = S → (fireValue sat E p i S F).2 = F) ∧
      (∀ j ∈ F, j ∈ (fireValue sat E p i S F).2) ∧
      (∀ j, ((fireValue sat E p i S F).1.lookup j).denote ≠ (S.lookup j).denote →
        j ∈ (fireValue sat E p i S F).2) ∧
      (((fireValue sat E p i S F).1.lookup i).denote = (S.lookup i).denote →
        ∀ e ∈ E, e.top = p → post e p (List.cons i '' (S.lookup i).denote) ⊆
          (fireValue sat E p i S F).1.denote) := by
  rw [fireValue_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    events_fold hE hk hfin hsat i (E.filter (fun e => e.top == p)) (fun e he => by
      obtain ⟨he, htop⟩ := List.mem_filter.mp he
      exact ⟨he, by simpa using htop⟩) (S, F) hS hSX
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun hl e he htop =>
    h8 hl e (List.mem_filter.mpr ⟨he, by simp [htop]⟩)⟩

private theorem saturateNodewise_correct (E : List (Event α)) {n : ℕ}
    (hE : ∀ e ∈ E, e.WellFormed n) (p : ℕ) (hp : p ≤ n) (X : Ldd α) (hX : X.WellFormed (n - p))
    (hfin : (Sat E p X.denote).Finite) :
    (saturateNodewise E n p X).WellFormed (n - p) ∧
      (saturateNodewise E n p X).denote = Sat E p X.denote := by
  rw [saturateNodewise]
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, n - p = k + 1 := ⟨n - p - 1, by omega⟩
    have hsat : SatNext E p k (fun d => saturateNodewise E n (p + 1) d) := fun d hd hdfin => by
      have hdk : n - (p + 1) = k := by omega
      have := saturateNodewise_correct E hE (p + 1) (by omega) d (hdk ▸ hd) hdfin
      rwa [hdk] at this
    simp only [Id.run_bind, Id.run_pure]
    have hXk : X.WellFormed (k + 1) := hk ▸ hX
    obtain ⟨hS0w, -, hS0⟩ := mapSpineWith_correct (fun _ => E) p k (fun _ d => saturateNodewise E n (p + 1) d)
      X hXk fun v d hm => hsat d (spine_wf hXk hm).1 (child_finite hXk lifts_self hfin hm)
    rw [← mapSpine_eq] at hS0w hS0
    refine MercLib.Util.whileInduction _
      (invImage (fun s : Ldd α × List α => ((Sat E p X.denote \ s.1.denote).ncard, s.2.length))
        (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf
      (fun s => s.1.WellFormed (k + 1) ∧ X.denote ⊆ s.1.denote ∧ s.1.denote ⊆ Sat E p X.denote ∧
        ClosedBelow E p s.1.denote ∧ ∀ i, i ∉ s.2 → ∀ e ∈ E, e.top = p →
          post e p (List.cons i '' (s.1.lookup i).denote) ⊆ s.1.denote)
      (fun s => s.1.WellFormed (n - p) ∧ s.1.denote = Sat E p X.denote) ?_ _
      ⟨hS0w, children_superset hXk hS0, children_sound hXk lifts_self hS0,
        children_closed below_self hS0, fun i hi e _ _ => ?_⟩
    · rintro ⟨S, F⟩ ⟨hS, h1, h2, hcb, hdone⟩
      simp only at hS h1 h2 hcb hdone
      by_cases hF : F = []
      · subst hF
        simp only [ne_eq, not_true_eq_false, ↓reduceDIte]
        refine ⟨hk ▸ hS, eq_sat_of_closed h1 h2 ?_⟩
        intro e he hle x hx y hf
        rcases Nat.lt_or_eq_of_le hle with hlt | htop
        · exact hcb e he hlt x hx y hf
        · obtain ⟨i, y0, rfl, hy0⟩ := mem_lookup hS hx
          exact hdone i (List.not_mem_nil) e he htop.symm ⟨_, ⟨y0, hy0, rfl⟩, hf⟩
      · rw [dite_eq_left hF]
        obtain ⟨r1w, r1sub, r1X, r1cb, r1eq, r1F, r1look, r1post⟩ :=
          nodewise_round hE hk hfin hsat (F.head hF) S F.tail hS h2
        refine ⟨⟨r1w, h1.trans r1sub, r1X, r1cb hcb, fun j hj e he htop => ?_⟩, ?_⟩
        · by_cases hji : j = F.head hF
          · subst hji
            have hl : ((fireValue (fun d => saturateNodewise E n (p + 1) d) E p (F.head hF) S F.tail).1.lookup (F.head hF)).denote =
                (S.lookup (F.head hF)).denote := by
              by_contra hne; exact hj (r1look _ hne)
            rw [hl]
            exact r1post hl e he htop
          · have hjF : j ∉ F := by
              rw [← List.cons_head_tail hF]
              simp only [List.mem_cons, not_or]
              exact ⟨hji, fun h => hj (r1F j h)⟩
            have hl : ((fireValue (fun d => saturateNodewise E n (p + 1) d) E p (F.head hF) S F.tail).1.lookup j).denote =
                (S.lookup j).denote := by
              by_contra hne; exact hj (r1look _ hne)
            rw [hl]
            exact (hdone j hjF e he htop).trans r1sub
        · show Prod.Lex _ _ _ _
          by_cases hr : (fireValue (fun d => saturateNodewise E n (p + 1) d) E p (F.head hF) S F.tail).1 = S
          · rw [hr, r1eq hr]
            exact Prod.Lex.right _ (show F.tail.length < F.length by
              have := List.length_pos_iff.mpr hF; simp only [List.length_tail]; omega)
          · exact Prod.Lex.left _ _ (missing_lt hfin (ssubset_of_ne hS r1w r1sub hr) r1X)
    · rw [lookup_eq_zero hi]
      intro y ⟨x, hx, _⟩
      obtain ⟨_, hx', rfl⟩ := hx
      simp [denote] at hx'
  · exact ⟨hX, (sat_end hE (by omega) hX).symm⟩
termination_by n - p
decreasing_by omega

private theorem saturateNodewise_terminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateNodewiseTerminates E n p X := by
  intro hE hp _ hfin S F hF hS _ h2
  obtain ⟨k, hk⟩ : ∃ k, n - p = k + 1 := ⟨n - p - 1, by omega⟩
  have hsat : SatNext E p k (fun d => saturateNodewise E n (p + 1) d) := fun d hd hdfin => by
    have hdk : n - (p + 1) = k := by omega
    have := saturateNodewise_correct E hE (p + 1) (by omega) d (hdk ▸ hd) hdfin
    rwa [hdk] at this
  have hSk : S.WellFormed (k + 1) := hk ▸ hS
  obtain ⟨r1w, r1sub, r1X, -, r1eq, -, -, -⟩ :=
    nodewise_round hE hk hfin hsat (F.head hF) S F.tail hSk h2
  intro r
  by_cases hr : r.1 = S
  · exact Or.inl ⟨hr, r1eq hr⟩
  · exact Or.inr ⟨ssubset_of_ne hSk r1w r1sub hr, r1X⟩

end Ldd

open Ldd

variable [LinearOrder α]

/-- **Breadth-first search is correct.** -/
theorem bfsCorrect (E : List (Event α)) (X : Ldd α) (n : ℕ) : BfsCorrect E X n :=
  bfs_correct E X n

/-- **Breadth-first search terminates.** -/
theorem bfsTerminates (E : List (Event α)) (X : Ldd α) (n : ℕ) : BfsTerminates E X n :=
  bfs_terminates E X n

/-- **Chaining is correct.** -/
theorem chainingCorrect (E : List (Event α)) (X : Ldd α) (n : ℕ) : ChainingCorrect E X n :=
  chaining_correct E X n

/-- **Chaining terminates.** -/
theorem chainingTerminates (E : List (Event α)) (X : Ldd α) (n : ℕ) : ChainingTerminates E X n :=
  chaining_terminates E X n

/-- **Recursive saturation is correct.** -/
theorem saturateCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) : SaturateCorrect E n p X :=
  fun hE hp hX hfin => saturate_correct E hE p hp X hX hfin

/-- **Recursive saturation terminates.** -/
theorem saturateTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateTerminates E n p X :=
  saturate_terminates E n p X

/-- **Node-wise saturation is correct.** -/
theorem saturateNodewiseCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateNodewiseCorrect E n p X :=
  fun hE hp hX hfin => saturateNodewise_correct E hE p hp X hX hfin

/-- **Node-wise saturation terminates.** -/
theorem saturateNodewiseTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) :
    SaturateNodewiseTerminates E n p X :=
  saturateNodewise_terminates E n p X

/-- **REACH is correct.** -/
theorem reachCorrect (E : List (Event α)) (n p : ℕ) (X : Ldd α) : ReachCorrect E n p X :=
  fun hE hp hX hfin => reach_correct p E hE hp X hX hfin

/-- **REACH terminates.** -/
theorem reachTerminates (E : List (Event α)) (n p : ℕ) (X : Ldd α) : ReachTerminates E n p X :=
  reach_terminates E n p X

end MercLib.LDD
