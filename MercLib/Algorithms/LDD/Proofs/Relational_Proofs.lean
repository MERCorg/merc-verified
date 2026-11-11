module

public import MercLib.Algorithms.LDD.Relational
import all MercLib.Theory.LDD.Proofs.Ldd_Proofs
import all MercLib.Algorithms.LDD.Proofs.SetOperations_Proofs

@[expose] public section

/-!
# Proofs: projection and relational successors on list decision diagrams

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/LDD.lean` (human-vetted).

The spine combinators are characterised through the list `spine X` of the pairs `(v, d)` on the
right spine of `X`: a vector `b :: y` is in a node-level LDD iff `(b, d)` is on its spine with `y`
in `d`.
-/

namespace MercLib.LDD

namespace Ldd

variable {α : Type*} [LinearOrder α]

/-- The pairs `(value, down child)` on the right spine. -/
private def spine : Ldd α → List (α × Ldd α)
  | node v d r => (v, d) :: spine r
  | _ => []

/-! ## The spine -/

private theorem mem_denote_iff : ∀ {X : Ldd α} {k : ℕ}, X.WellFormed (k + 1) → ∀ x : List α,
    x ∈ X.denote ↔ ∃ b y d, x = b :: y ∧ (b, d) ∈ X.spine ∧ y ∈ d.denote
  | zero, _, _, x => by simp [denote, spine]
  | one, _, h, _ => by simp [WellFormed] at h
  | node v e s, k, h, x => by
    have ih := mem_denote_iff h.2.2.1
    constructor
    · rintro (⟨y, hy, rfl⟩ | hx)
      · exact ⟨v, y, e, rfl, List.mem_cons_self .., hy⟩
      · obtain ⟨b, y, d, rfl, hm, hy⟩ := (ih x).1 hx
        exact ⟨b, y, d, rfl, List.mem_cons_of_mem _ hm, hy⟩
    · rintro ⟨b, y, d, rfl, hm, hy⟩
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm; exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ((ih _).2 ⟨b, y, d, rfl, hm, hy⟩)

private theorem ne_one_of_wf {X : Ldd α} {k : ℕ} (h : X.WellFormed (k + 1)) : X ≠ one := by
  rintro rfl; simp [WellFormed] at h

private theorem spine_wf : ∀ {X : Ldd α} {k : ℕ}, X.WellFormed (k + 1) →
    ∀ {b : α} {d : Ldd α}, (b, d) ∈ X.spine → d.WellFormed k ∧ d ≠ zero
  | zero, _, _, _, _, hm => by simp [spine] at hm
  | one, _, h, _, _, _ => by simp [WellFormed] at h
  | node v e s, k, h, b, d, hm => by
    obtain ⟨he0, he, hs, -⟩ := h
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact ⟨he, he0⟩
    · exact spine_wf hs hm

private theorem spine_lt : ∀ {X : Ldd α} {k : ℕ}, X.WellFormed (k + 1) →
    ∀ {v b : α} {d : Ldd α}, HeadAbove v X → (b, d) ∈ X.spine → v < b
  | zero, _, _, _, _, _, _, hm => by simp [spine] at hm
  | one, _, h, _, _, _, _, _ => by simp [WellFormed] at h
  | node w e s, k, h, v, b, d, hv, hm => by
    obtain ⟨-, -, hs, hws⟩ := h
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact hv
    · exact lt_trans hv (spine_lt hs hws hm)

private theorem spine_le {w : α} {e s : Ldd α} {k : ℕ} (h : (node w e s).WellFormed (k + 1))
    {b : α} {d : Ldd α} (hm : (b, d) ∈ (node w e s).spine) : w ≤ b := by
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm; exact le_rfl
  · exact le_of_lt (spine_lt h.2.2.1 h.2.2.2 hm)

omit [LinearOrder α] in
private theorem spine_tail {v : α} {d r : Ldd α} {b : α} {d' : Ldd α} (hm : (b, d') ∈ r.spine) :
    (b, d') ∈ (node v d r).spine := List.mem_cons_of_mem _ hm

omit [LinearOrder α] in
private theorem spine_head (v : α) (d r : Ldd α) : (v, d) ∈ (node v d r).spine :=
  List.mem_cons_self ..

omit [LinearOrder α] in
private theorem spine_cases {v : α} {d r : Ldd α} {b : α} {d' : Ldd α}
    (hm : (b, d') ∈ (node v d r).spine) : (b = v ∧ d' = d) ∨ (b, d') ∈ r.spine := by
  rcases List.mem_cons.mp hm with hm | hm
  · exact Or.inl (Prod.mk.inj hm)
  · exact Or.inr hm

/-! ## Spine combinators -/

private theorem mapSpine_correct (f : Ldd α → Ldd α) {k k' : ℕ} :
    ∀ {X : Ldd α}, X.WellFormed (k + 1) → (∀ b d, (b, d) ∈ X.spine → (f d).WellFormed k') →
    (mapSpine f X).WellFormed (k' + 1) ∧ ∀ x, x ∈ (mapSpine f X).denote ↔
      ∃ b y d, x = b :: y ∧ (b, d) ∈ X.spine ∧ y ∈ (f d).denote
  | zero, _, _ => ⟨trivial, by simp [mapSpine, denote, spine]⟩
  | one, h, _ => by simp [WellFormed] at h
  | node v d r, h, hf => by
    have hr := h.2.2.1
    obtain ⟨ih1, ih2⟩ := mapSpine_correct f hr (fun b d' hm => hf b d' (spine_tail hm))
    have hfd := hf v d (spine_head ..)
    simp only [mapSpine]
    refine ⟨wellFormed_mk hfd ih1 (headAbove_of_lt ih1 fun b y hx => ?_), fun x => ?_⟩
    · obtain ⟨b', y', d', heq, hm, -⟩ := (ih2 _).1 hx
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact spine_lt hr h.2.2.2 hm
    · rw [denote_mk]
      constructor
      · rintro (⟨y, hy, rfl⟩ | hx)
        · exact ⟨v, y, d, rfl, spine_head .., hy⟩
        · obtain ⟨b, y, d', rfl, hm, hy⟩ := (ih2 x).1 hx
          exact ⟨b, y, d', rfl, spine_tail hm, hy⟩
      · rintro ⟨b, y, d', rfl, hm, hy⟩
        rcases spine_cases hm with ⟨rfl, rfl⟩ | hm
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr ((ih2 _).2 ⟨b, y, d', rfl, hm, hy⟩)

private theorem unionSpine_correct (f : Ldd α → Ldd α) {k' : ℕ} :
    ∀ {X : Ldd α}, (∀ b d, (b, d) ∈ X.spine → (f d).WellFormed k') →
    (unionSpine f X).WellFormed k' ∧ ∀ x, x ∈ (unionSpine f X).denote ↔
      ∃ b d, (b, d) ∈ X.spine ∧ x ∈ (f d).denote
  | zero, _ => ⟨trivial, by simp [unionSpine, denote, spine]⟩
  | one, _ => ⟨trivial, by simp [unionSpine, denote, spine]⟩
  | node v d r, hf => by
    obtain ⟨ih1, ih2⟩ := unionSpine_correct f (fun b d' hm => hf b d' (spine_tail hm))
    obtain ⟨u1, u2⟩ := union_correct _ _ k' ih1 (hf v d (spine_head ..))
    simp only [unionSpine]
    refine ⟨u1, fun x => ?_⟩
    rw [u2, Set.mem_union, ih2]
    constructor
    · rintro (⟨b, d', hm, hx⟩ | hx)
      · exact ⟨b, d', spine_tail hm, hx⟩
      · exact ⟨v, d, spine_head .., hx⟩
    · rintro ⟨b, d', hm, hx⟩
      rcases spine_cases hm with ⟨rfl, rfl⟩ | hm
      · exact Or.inr hx
      · exact Or.inl ⟨b, d', hm, hx⟩

private theorem matchSpine_zero (f : Ldd α → Ldd α → Ldd α) (X R : Ldd α)
    (h : ∀ v d r w e s, X = node v d r → R = node w e s → False) : matchSpine f X R = zero := by
  cases X <;> cases R <;> first | exact (h _ _ _ _ _ _ rfl rfl).elim | simp [matchSpine]

private theorem joinSpine_zero (f : Ldd α → Ldd α → Ldd α) (X R : Ldd α)
    (h : ∀ v d r w e s, X = node v d r → R = node w e s → False) : joinSpine f X R = zero := by
  cases X <;> cases R <;> first | exact (h _ _ _ _ _ _ rfl rfl).elim | simp [joinSpine]

omit [LinearOrder α] in
private theorem spine_nil_of_not_node {X R : Ldd α}
    (h : ∀ v d r w e s, X = node v d r → R = node w e s → False) {b : α} {d e : Ldd α}
    (hd : (b, d) ∈ X.spine) (he : (b, e) ∈ R.spine) : False := by
  cases X <;> cases R <;> first | exact (h _ _ _ _ _ _ rfl rfl).elim | simp_all [spine]

/-- A private copy of the functional induction principle of `matchSpine` and `joinSpine`, so that
    this module does not export the generated `.induct` theorems. -/
private theorem spine_induct (motive : Ldd α → Ldd α → Prop)
    (case1 : ∀ v d r w e s, v < w → motive r (node w e s) → motive (node v d r) (node w e s))
    (case2 : ∀ v d r w e s, ¬v < w → w < v → motive (node v d r) s →
      motive (node v d r) (node w e s))
    (case3 : ∀ v d r w e s, ¬v < w → ¬w < v → motive r s → motive (node v d r) (node w e s))
    (case4 : ∀ X R, (∀ v d r w e s, X = node v d r → R = node w e s → False) → motive X R) :
    ∀ a b, motive a b := by
  intro a b
  induction h : sizeOf a + sizeOf b using Nat.strong_induction_on generalizing a b with
  | _ k ih =>
    subst h
    match a, b with
    | node v d r, node w e s =>
      if h1 : v < w then exact case1 v d r w e s h1 (ih _ size_lt_left _ _ rfl)
      else if h2 : w < v then exact case2 v d r w e s h1 h2 (ih _ size_lt_right _ _ rfl)
      else exact case3 v d r w e s h1 h2 (ih _ size_lt_both _ _ rfl)
    | zero, _ => exact case4 _ _ (by simp)
    | one, _ => exact case4 _ _ (by simp)
    | node .., zero => exact case4 _ _ (by simp)
    | node .., one => exact case4 _ _ (by simp)

private theorem matchSpine_correct (f : Ldd α → Ldd α → Ldd α) {k j k' : ℕ} (X R : Ldd α) :
    X.WellFormed (k + 1) → R.WellFormed (j + 1) →
    (∀ b d e, (b, d) ∈ X.spine → (b, e) ∈ R.spine → (f d e).WellFormed k') →
    (matchSpine f X R).WellFormed (k' + 1) ∧ ∀ x, x ∈ (matchSpine f X R).denote ↔
      ∃ b y d e, x = b :: y ∧ (b, d) ∈ X.spine ∧ (b, e) ∈ R.spine ∧ y ∈ (f d e).denote := by
  induction X, R using spine_induct with
  | case1 v d r w e s hvw ih =>
    intro hX hR hf
    obtain ⟨ih1, ih2⟩ := ih hX.2.2.1 hR (fun b d' e' hd he => hf b d' e' (spine_tail hd) he)
    simp only [matchSpine, hvw, ↓reduceIte]
    refine ⟨ih1, fun x => (ih2 x).trans ⟨?_, ?_⟩⟩
    · rintro ⟨b, y, d', e', h1, h2, h3, h4⟩; exact ⟨b, y, d', e', h1, spine_tail h2, h3, h4⟩
    · rintro ⟨b, y, d', e', h1, h2, h3, h4⟩
      rcases spine_cases h2 with ⟨rfl, rfl⟩ | h2
      · exact absurd (spine_le hR h3) (not_le.mpr hvw)
      · exact ⟨b, y, d', e', h1, h2, h3, h4⟩
  | case2 v d r w e s h1 hwv ih =>
    intro hX hR hf
    obtain ⟨ih1, ih2⟩ := ih hX hR.2.2.1 (fun b d' e' hd he => hf b d' e' hd (spine_tail he))
    simp only [matchSpine, h1, hwv, ↓reduceIte]
    refine ⟨ih1, fun x => (ih2 x).trans ⟨?_, ?_⟩⟩
    · rintro ⟨b, y, d', e', h1, h2, h3, h4⟩; exact ⟨b, y, d', e', h1, h2, spine_tail h3, h4⟩
    · rintro ⟨b, y, d', e', h1, h2, h3, h4⟩
      rcases spine_cases h3 with ⟨rfl, rfl⟩ | h3
      · exact absurd (spine_le hX h2) (not_le.mpr hwv)
      · exact ⟨b, y, d', e', h1, h2, h3, h4⟩
  | case3 v d r w e s h1 h2 ih =>
    obtain rfl := eq_of_not_lt h1 h2
    intro hX hR hf
    obtain ⟨ih1, ih2⟩ := ih hX.2.2.1 hR.2.2.1
      (fun b d' e' hd he => hf b d' e' (spine_tail hd) (spine_tail he))
    simp only [matchSpine, h1, ↓reduceIte]
    refine ⟨wellFormed_mk (hf v d e (spine_head ..) (spine_head ..)) ih1
      (headAbove_of_lt ih1 fun b y hx => ?_), fun x => ?_⟩
    · obtain ⟨b', y', d', e', heq, hm, -, -⟩ := (ih2 _).1 hx
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact spine_lt hX.2.2.1 hX.2.2.2 hm
    · rw [denote_mk, Set.mem_union, ih2]
      constructor
      · rintro (⟨y, hy, rfl⟩ | ⟨b, y, d', e', rfl, hd, he, hy⟩)
        · exact ⟨v, y, d, e, rfl, spine_head .., spine_head .., hy⟩
        · exact ⟨b, y, d', e', rfl, spine_tail hd, spine_tail he, hy⟩
      · rintro ⟨b, y, d', e', rfl, hd, he, hy⟩
        rcases spine_cases hd with ⟨rfl, rfl⟩ | hd
        · rcases spine_cases he with ⟨-, rfl⟩ | he
          · exact Or.inl ⟨y, hy, rfl⟩
          · exact absurd (spine_lt hR.2.2.1 hR.2.2.2 he) (lt_irrefl _)
        · rcases spine_cases he with ⟨hb, -⟩ | he
          · exact absurd (spine_lt hX.2.2.1 hX.2.2.2 (hb ▸ hd)) (lt_irrefl _)
          · exact Or.inr ⟨b, y, d', e', rfl, hd, he, hy⟩
  | case4 X R h =>
    intro _ _ _
    rw [matchSpine_zero f X R h]
    refine ⟨trivial, fun x => ⟨fun hx => by simp [denote] at hx, ?_⟩⟩
    rintro ⟨b, y, d, e, -, hd, he, -⟩
    exact (spine_nil_of_not_node h hd he).elim

private theorem joinSpine_correct (f : Ldd α → Ldd α → Ldd α) {k j k' : ℕ} (X R : Ldd α) :
    X.WellFormed (k + 1) → R.WellFormed (j + 1) →
    (∀ b d e, (b, d) ∈ X.spine → (b, e) ∈ R.spine → (f d e).WellFormed k') →
    (joinSpine f X R).WellFormed k' ∧ ∀ x, x ∈ (joinSpine f X R).denote ↔
      ∃ b d e, (b, d) ∈ X.spine ∧ (b, e) ∈ R.spine ∧ x ∈ (f d e).denote := by
  induction X, R using spine_induct with
  | case1 v d r w e s hvw ih =>
    intro hX hR hf
    obtain ⟨ih1, ih2⟩ := ih hX.2.2.1 hR (fun b d' e' hd he => hf b d' e' (spine_tail hd) he)
    simp only [joinSpine, hvw, ↓reduceIte]
    refine ⟨ih1, fun x => (ih2 x).trans ⟨?_, ?_⟩⟩
    · rintro ⟨b, d', e', h2, h3, h4⟩; exact ⟨b, d', e', spine_tail h2, h3, h4⟩
    · rintro ⟨b, d', e', h2, h3, h4⟩
      rcases spine_cases h2 with ⟨rfl, rfl⟩ | h2
      · exact absurd (spine_le hR h3) (not_le.mpr hvw)
      · exact ⟨b, d', e', h2, h3, h4⟩
  | case2 v d r w e s h1 hwv ih =>
    intro hX hR hf
    obtain ⟨ih1, ih2⟩ := ih hX hR.2.2.1 (fun b d' e' hd he => hf b d' e' hd (spine_tail he))
    simp only [joinSpine, h1, hwv, ↓reduceIte]
    refine ⟨ih1, fun x => (ih2 x).trans ⟨?_, ?_⟩⟩
    · rintro ⟨b, d', e', h2, h3, h4⟩; exact ⟨b, d', e', h2, spine_tail h3, h4⟩
    · rintro ⟨b, d', e', h2, h3, h4⟩
      rcases spine_cases h3 with ⟨rfl, rfl⟩ | h3
      · exact absurd (spine_le hX h2) (not_le.mpr hwv)
      · exact ⟨b, d', e', h2, h3, h4⟩
  | case3 v d r w e s h1 h2 ih =>
    obtain rfl := eq_of_not_lt h1 h2
    intro hX hR hf
    obtain ⟨ih1, ih2⟩ := ih hX.2.2.1 hR.2.2.1
      (fun b d' e' hd he => hf b d' e' (spine_tail hd) (spine_tail he))
    obtain ⟨u1, u2⟩ := union_correct _ _ k' (hf v d e (spine_head ..) (spine_head ..)) ih1
    simp only [joinSpine, h1, ↓reduceIte]
    refine ⟨u1, fun x => ?_⟩
    rw [u2, Set.mem_union, ih2]
    constructor
    · rintro (hx | ⟨b, d', e', hd, he, hx⟩)
      · exact ⟨v, d, e, spine_head .., spine_head .., hx⟩
      · exact ⟨b, d', e', spine_tail hd, spine_tail he, hx⟩
    · rintro ⟨b, d', e', hd, he, hx⟩
      rcases spine_cases hd with ⟨rfl, rfl⟩ | hd
      · rcases spine_cases he with ⟨-, rfl⟩ | he
        · exact Or.inl hx
        · exact absurd (spine_lt hR.2.2.1 hR.2.2.2 he) (lt_irrefl _)
      · rcases spine_cases he with ⟨hb, -⟩ | he
        · exact absurd (spine_lt hX.2.2.1 hX.2.2.2 (hb ▸ hd)) (lt_irrefl _)
        · exact Or.inr ⟨b, d', e', hd, he, hx⟩
  | case4 X R h =>
    intro _ _ _
    rw [joinSpine_zero f X R h]
    refine ⟨trivial, fun x => ⟨fun hx => by simp [denote] at hx, ?_⟩⟩
    rintro ⟨b, d, e, hd, he, -⟩
    exact (spine_nil_of_not_node h hd he).elim

/-! ## One vector -/

omit [LinearOrder α] in
private theorem select_nil (x : List α) : select [] x = [] := by cases x <;> rfl

omit [LinearOrder α] in
private theorem apply_nil {t x y : List α} : Apply [] t x y ↔ t = [] ∧ y = x := by
  cases t <;> simp [Apply]

omit [LinearOrder α] in
private theorem apply_skip {m : List Access} {t x' y' : List α} :
    Apply (.skip :: m) t x' y' ↔ ∃ a x y, x' = a :: x ∧ y' = a :: y ∧ Apply m t x y := by
  cases x' <;> cases y' <;> simp [Apply]

omit [LinearOrder α] in
private theorem apply_read {m : List Access} {t' x' y' : List α} :
    Apply (.read :: m) t' x' y' ↔
      ∃ a t x y, t' = a :: t ∧ x' = a :: x ∧ y' = a :: y ∧ Apply m t x y := by
  cases t' <;> cases x' <;> cases y' <;> simp [Apply]
  aesop

omit [LinearOrder α] in
private theorem apply_write {m : List Access} {t' x' y' : List α} :
    Apply (.write :: m) t' x' y' ↔
      ∃ c t a x y, t' = c :: t ∧ x' = a :: x ∧ y' = c :: y ∧ Apply m t x y := by
  cases t' <;> cases x' <;> cases y' <;> simp [Apply]

omit [LinearOrder α] in
private theorem apply_readWrite {m : List Access} {t' x' y' : List α} :
    Apply (.readWrite :: m) t' x' y' ↔
      ∃ a c t x y, t' = a :: c :: t ∧ x' = a :: x ∧ y' = c :: y ∧ Apply m t x y := by
  match t', x', y' with
  | a :: c :: t, a' :: x, c' :: y =>
    simp only [Apply, List.cons.injEq]
    constructor
    · rintro ⟨rfl, rfl, h⟩; exact ⟨_, _, _, _, _, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, _, _, _, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, h⟩; exact ⟨rfl, rfl, h⟩
  | [], _, _ => simp [Apply]
  | [_], _, _ => simp [Apply]
  | _ :: _ :: _, [], _ => simp [Apply]
  | _ :: _ :: _, _ :: _, [] => simp [Apply]

/-! ## Projection -/

private theorem project_correct : ∀ (m : List Bool) {X : Ldd α} {n : ℕ}, m.length ≤ n →
    X.WellFormed n →
    (project m X).WellFormed (m.count true) ∧ (project m X).denote = select m '' X.denote
  | [], X, n, _, hX => by
    cases X with
    | zero => exact ⟨trivial, by simp [project, denote]⟩
    | one =>
      refine ⟨by simp [project, WellFormed], ?_⟩
      ext x; simp [project, denote, select_nil]
    | node v d r =>
      refine ⟨by simp [project, WellFormed], ?_⟩
      obtain ⟨y, hy⟩ := nonempty_of_ne_zero _ n hX (by simp)
      ext x
      simp only [project, denote, Set.mem_singleton_iff, Set.mem_image, select_nil]
      constructor
      · rintro rfl; exact ⟨y, hy, rfl⟩
      · rintro ⟨_, _, rfl⟩; rfl
  | b :: m, X, n, hm, hX => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hm; omega⟩
    have hm' : m.length ≤ k := by simpa using hm
    have ih : ∀ c d, (c, d) ∈ X.spine →
        (project m d).WellFormed (m.count true) ∧ (project m d).denote = select m '' d.denote :=
      fun c d hd => project_correct m hm' (spine_wf hX hd).1
    cases b with
    | true =>
      obtain ⟨h1, h2⟩ := mapSpine_correct (project m) hX fun c d hd => (ih c d hd).1
      simp only [project]
      refine ⟨by simpa [List.count_cons] using h1, ?_⟩
      ext x
      rw [h2, Set.mem_image]
      constructor
      · rintro ⟨c, y, d, rfl, hd, hy⟩
        rw [(ih c d hd).2] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact ⟨c :: z, (mem_denote_iff hX _).2 ⟨c, z, d, rfl, hd, hz⟩, rfl⟩
      · rintro ⟨x', hx', rfl⟩
        obtain ⟨c, z, d, rfl, hd, hz⟩ := (mem_denote_iff hX _).1 hx'
        exact ⟨c, select m z, d, rfl, hd, by rw [(ih c d hd).2]; exact ⟨z, hz, rfl⟩⟩
    | false =>
      obtain ⟨h1, h2⟩ := unionSpine_correct (project m) fun c d hd => (ih c d hd).1
      simp only [project]
      refine ⟨by simpa [List.count_cons] using h1, ?_⟩
      ext x
      rw [h2, Set.mem_image]
      constructor
      · rintro ⟨c, d, hd, hx⟩
        rw [(ih c d hd).2] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        exact ⟨c :: z, (mem_denote_iff hX _).2 ⟨c, z, d, rfl, hd, hz⟩, rfl⟩
      · rintro ⟨x', hx', rfl⟩
        obtain ⟨c, z, d, rfl, hd, hz⟩ := (mem_denote_iff hX _).1 hx'
        exact ⟨c, d, hd, by rw [(ih c d hd).2]; exact ⟨z, hz, rfl⟩⟩

/-! ## Relational successors -/

private theorem relWidth_cons (a : Access) (m : List Access) :
    relWidth (a :: m) = relWidth m + a.width := by
  simp [relWidth, Nat.add_comm]

private theorem successors_correct : ∀ (m : List Access) {X R : Ldd α} {n : ℕ}, m.length ≤ n →
    X.WellFormed n → R.WellFormed (relWidth m) →
    (successors m X R).WellFormed n ∧ ∀ y, y ∈ (successors m X R).denote ↔
      ∃ x ∈ X.denote, ∃ t ∈ R.denote, Apply m t x y
  | [], X, R, n, _, hX, hR => by
    cases R with
    | zero => exact ⟨trivial, fun y => by simp [successors, denote]⟩
    | one =>
      refine ⟨by simpa [successors] using hX, fun y => ?_⟩
      simp only [successors, denote, Set.mem_singleton_iff, apply_nil]
      constructor
      · intro hy; exact ⟨y, hy, [], rfl, rfl, rfl⟩
      · rintro ⟨x, hx, _, -, -, rfl⟩; exact hx
    | node v d r => simp [relWidth, WellFormed] at hR
  | a :: m, X, R, n, hm, hX, hR => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hm; omega⟩
    have hm' : m.length ≤ k := by simpa using hm
    have ih : ∀ {d e : Ldd α}, d.WellFormed k → e.WellFormed (relWidth m) →
        (successors m d e).WellFormed k ∧ ∀ y, y ∈ (successors m d e).denote ↔
          ∃ x ∈ d.denote, ∃ t ∈ e.denote, Apply m t x y :=
      fun hd he => successors_correct m hm' hd he
    rw [relWidth_cons] at hR
    cases a with
    | skip =>
      simp only [Access.width, Nat.add_zero] at hR
      obtain ⟨h1, h2⟩ := mapSpine_correct (fun d => successors m d R) hX
        fun c d hd => (ih (spine_wf hX hd).1 hR).1
      simp only [successors]
      refine ⟨h1, fun y => (h2 y).trans ?_⟩
      simp only [apply_skip]
      constructor
      · rintro ⟨c, y, d, rfl, hd, hy⟩
        obtain ⟨x, hx, t, ht, hA⟩ := ((ih (spine_wf hX hd).1 hR).2 y).1 hy
        exact ⟨c :: x, (mem_denote_iff hX _).2 ⟨c, x, d, rfl, hd, hx⟩, t, ht, c, x, y, rfl, rfl, hA⟩
      · rintro ⟨x', hx', t, ht, c, x, y, rfl, rfl, hA⟩
        obtain ⟨c', x0, d, heq, hd, hx⟩ := (mem_denote_iff hX _).1 hx'
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        exact ⟨c, y, d, rfl, hd, ((ih (spine_wf hX hd).1 hR).2 y).2 ⟨x, hx, t, ht, hA⟩⟩
    | read =>
      simp only [Access.width] at hR
      obtain ⟨h1, h2⟩ := matchSpine_correct (fun d e => successors m d e) X R hX hR
        fun c d e hd he => (ih (spine_wf hX hd).1 (spine_wf hR he).1).1
      simp only [successors]
      refine ⟨h1, fun y => (h2 y).trans ?_⟩
      simp only [apply_read]
      constructor
      · rintro ⟨c, y, d, e, rfl, hd, he, hy⟩
        obtain ⟨x, hx, t, ht, hA⟩ := ((ih (spine_wf hX hd).1 (spine_wf hR he).1).2 y).1 hy
        exact ⟨c :: x, (mem_denote_iff hX _).2 ⟨c, x, d, rfl, hd, hx⟩,
          c :: t, (mem_denote_iff hR _).2 ⟨c, t, e, rfl, he, ht⟩, c, t, x, y, rfl, rfl, rfl, hA⟩
      · rintro ⟨x', hx', t', ht', c, t, x, y, rfl, rfl, rfl, hA⟩
        obtain ⟨c', x0, d, heq, hd, hx⟩ := (mem_denote_iff hX _).1 hx'
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        obtain ⟨c'', t0, e, heq', he, ht⟩ := (mem_denote_iff hR _).1 ht'
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq'
        exact ⟨c, y, d, e, rfl, hd, he,
          ((ih (spine_wf hX hd).1 (spine_wf hR he).1).2 y).2 ⟨x, hx, t, ht, hA⟩⟩
    | write =>
      simp only [Access.width] at hR
      obtain ⟨u1, u2⟩ := unionSpine_correct (k' := k) id fun c d hd => (spine_wf hX hd).1
      obtain ⟨h1, h2⟩ := mapSpine_correct (fun e => successors m (unionSpine id X) e) hR
        fun c e he => (ih u1 (spine_wf hR he).1).1
      simp only [successors]
      refine ⟨h1, fun y => (h2 y).trans ?_⟩
      simp only [apply_write]
      constructor
      · rintro ⟨c, y, e, rfl, he, hy⟩
        obtain ⟨x, hx, t, ht, hA⟩ := ((ih u1 (spine_wf hR he).1).2 y).1 hy
        obtain ⟨a, d, hd, hx⟩ := (u2 x).1 hx
        exact ⟨a :: x, (mem_denote_iff hX _).2 ⟨a, x, d, rfl, hd, hx⟩,
          c :: t, (mem_denote_iff hR _).2 ⟨c, t, e, rfl, he, ht⟩, c, t, a, x, y, rfl, rfl, rfl, hA⟩
      · rintro ⟨x', hx', t', ht', c, t, a, x, y, rfl, rfl, rfl, hA⟩
        obtain ⟨a', x0, d, heq, hd, hx⟩ := (mem_denote_iff hX _).1 hx'
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        obtain ⟨c', t0, e, heq', he, ht⟩ := (mem_denote_iff hR _).1 ht'
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq'
        exact ⟨c, y, e, rfl, he,
          ((ih u1 (spine_wf hR he).1).2 y).2 ⟨x, (u2 x).2 ⟨a, d, hd, hx⟩, t, ht, hA⟩⟩
    | readWrite =>
      simp only [Access.width] at hR
      have hg : ∀ c d e, (c, d) ∈ X.spine → (c, e) ∈ R.spine →
          (mapSpine (fun e' => successors m d e') e).WellFormed (k + 1) ∧
          ∀ y, y ∈ (mapSpine (fun e' => successors m d e') e).denote ↔
            ∃ b y' e', y = b :: y' ∧ (b, e') ∈ e.spine ∧ y' ∈ (successors m d e').denote :=
        fun c d e hd he => mapSpine_correct _ (spine_wf hR he).1
          fun b e' he' => (ih (spine_wf hX hd).1 (spine_wf (spine_wf hR he).1 he').1).1
      obtain ⟨h1, h2⟩ := joinSpine_correct
        (fun d e => mapSpine (fun e' => successors m d e') e) X R hX hR
        fun c d e hd he => (hg c d e hd he).1
      simp only [successors]
      refine ⟨h1, fun y => (h2 y).trans ?_⟩
      simp only [apply_readWrite]
      constructor
      · rintro ⟨a, d, e, hd, he, hy⟩
        obtain ⟨c, y, e', rfl, he', hy⟩ := ((hg a d e hd he).2 _).1 hy
        have heW := (spine_wf hR he).1
        obtain ⟨x, hx, t, ht, hA⟩ :=
          ((ih (spine_wf hX hd).1 (spine_wf heW he').1).2 y).1 hy
        exact ⟨a :: x, (mem_denote_iff hX _).2 ⟨a, x, d, rfl, hd, hx⟩, a :: c :: t,
          (mem_denote_iff hR _).2 ⟨a, c :: t, e, rfl, he,
            (mem_denote_iff heW _).2 ⟨c, t, e', rfl, he', ht⟩⟩,
          a, c, t, x, y, rfl, rfl, rfl, hA⟩
      · rintro ⟨x', hx', t', ht', a, c, t, x, y, rfl, rfl, rfl, hA⟩
        obtain ⟨a', x0, d, heq, hd, hx⟩ := (mem_denote_iff hX _).1 hx'
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        obtain ⟨a'', ct, e, heq', he, hct⟩ := (mem_denote_iff hR _).1 ht'
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq'
        have heW := (spine_wf hR he).1
        obtain ⟨c', t0, e', heq'', he', ht⟩ := (mem_denote_iff heW _).1 hct
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq''
        exact ⟨a, d, e, hd, he, ((hg a d e hd he).2 _).2 ⟨c, y, e', rfl, he',
          ((ih (spine_wf hX hd).1 (spine_wf heW he').1).2 y).2 ⟨x, hx, t, ht, hA⟩⟩⟩

end Ldd

open Ldd

variable {α : Type*} [LinearOrder α]

/-- **Projection is correct.** -/
theorem projectCorrect (m : List Bool) (X : Ldd α) (n : ℕ) : ProjectCorrect m X n :=
  fun hm hX => project_correct m hm hX

/-- **Relational successors are correct.** -/
theorem successorsCorrect (m : List Access) (X R : Ldd α) (n : ℕ) : SuccessorsCorrect m X R n :=
  fun hm hX hR =>
    ⟨(successors_correct m hm hX hR).1, Set.ext (successors_correct m hm hX hR).2⟩

end MercLib.LDD
