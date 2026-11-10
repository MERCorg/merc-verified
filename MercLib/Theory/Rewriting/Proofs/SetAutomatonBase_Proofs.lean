module

public import MercLib.Theory.Rewriting.SetAutomatonPartition

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Basic facts about positions (`lcp`, `gcp`) and patterns (`at`, `dom`), and the dependency classes
of match goals. -/

namespace MercLib.SetAutomaton

open Position

private theorem lcp_prefix_left : ∀ p q : Position, lcp p q <+: p
  | a :: p, b :: q => by
    simp only [lcp]; split
    · exact (List.cons_prefix_cons.2 ⟨rfl, lcp_prefix_left p q⟩)
    · exact List.nil_prefix
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

private theorem lcp_prefix_right : ∀ p q : Position, lcp p q <+: q
  | a :: p, b :: q => by
    simp only [lcp]; split
    · rename_i h; subst h; exact (List.cons_prefix_cons.2 ⟨rfl, lcp_prefix_right p q⟩)
    · exact List.nil_prefix
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

private theorem prefix_lcp : ∀ {c p q : Position}, c <+: p → c <+: q → c <+: lcp p q
  | [], _, _, _, _ => List.nil_prefix
  | a :: c, [], _, h, _ => by simp at h
  | a :: c, _ :: _, [], _, h => by simp at h
  | a :: c, x :: p, y :: q, h1, h2 => by
    obtain ⟨e1, h1'⟩ := List.cons_prefix_cons.1 h1
    obtain ⟨e2, h2'⟩ := List.cons_prefix_cons.1 h2
    subst e1; subst e2
    simp only [lcp, ite_true]
    exact List.cons_prefix_cons.2 ⟨rfl, prefix_lcp h1' h2'⟩

private theorem foldl_lcp_prefix : ∀ (l : List Position) (p : Position),
    l.foldl lcp p <+: p ∧ ∀ q ∈ l, l.foldl lcp p <+: q
  | [], p => by simp
  | a :: l, p => by
    obtain ⟨h1, h2⟩ := foldl_lcp_prefix l (lcp p a)
    refine ⟨by simpa using h1.trans (lcp_prefix_left p a), fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact by simpa using h1.trans (lcp_prefix_right p q)
    · exact by simpa using h2 q hq

private theorem prefix_foldl_lcp : ∀ (l : List Position) (p c : Position),
    c <+: p → (∀ q ∈ l, c <+: q) → c <+: l.foldl lcp p
  | [], _, _, h, _ => by simpa using h
  | a :: l, p, c, h, hl => by
    simpa using prefix_foldl_lcp l (lcp p a) c
      (prefix_lcp h (hl a (List.mem_cons_self))) fun q hq => hl q (List.mem_cons_of_mem _ hq)

/-- If `c` belongs to `P` and is a prefix of every position of `P`, it is `gcp P`. -/
private theorem gcp_eq {P : Finset Position} {c : Position} (hc : c ∈ P)
    (hall : ∀ q ∈ P, c <+: q) : gcp P = c := by
  unfold gcp
  split
  next hl =>
    have : c ∈ ([] : List Position) := by rw [← hl, Finset.mem_sort]; exact hc
    simp at this
  next p ps hl =>
    have hps : ∀ q, q ∈ p :: ps ↔ q ∈ P := fun q => by rw [← hl, Finset.mem_sort]
    obtain ⟨h1, h2⟩ := foldl_lcp_prefix ps p
    have upper : c <+: ps.foldl lcp p := prefix_foldl_lcp ps p c
      (hall p ((hps p).1 List.mem_cons_self))
      fun q hq => hall q ((hps q).1 (List.mem_cons_of_mem _ hq))
    have lower : ps.foldl lcp p <+: c := by
      rcases List.mem_cons.1 ((hps c).2 hc) with rfl | h
      · exact h1
      · exact h2 c h
    exact List.IsPrefix.eq_of_length_le lower upper.length_le

variable {F : Type} [DecidableEq F]

namespace Pat

mutual

private theorem at_append : ∀ (t : Pat F) (r r' : Position),
    t.at (r ++ r') = (t.at r).bind (·.at r')
  | _, [], _ => by simp [Pat.at]
  | .omega, _ :: _, _ => by simp [Pat.at]
  | .app _ args, i :: r, r' => by
    simpa [Pat.at] using atArgs_append args i r r'

private theorem atArgs_append : ∀ (ts : List (Pat F)) (i : ℕ) (r r' : Position),
    atArgs ts i (r ++ r') = (atArgs ts i r).bind (·.at r')
  | [], _, _, _ => by simp [atArgs]
  | _ :: _, 0, _, _ => by simp [atArgs]
  | t :: _, 1, r, r' => by simpa [atArgs] using at_append t r r'
  | _ :: ts, i + 2, r, r' => by simpa [atArgs] using atArgs_append ts (i + 1) r r'

end

mutual

private theorem mem_domList_iff : ∀ (t : Pat F) (r : Position), r ∈ domList t ↔ (t.at r).isSome
  | .omega, [] => by simp [domList, Pat.at]
  | .omega, _ :: _ => by simp [domList, Pat.at]
  | .app _ _, [] => by simp [domList, Pat.at]
  | .app _ args, i :: r => by
    have h := mem_domArgs_iff args 0 i r
    simp only [domList, List.mem_cons, reduceCtorEq, false_or, Pat.at]
    refine h.trans ⟨fun x => by simpa using x.2, fun x => ⟨?_, by simpa using x⟩⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · cases args <;> simp [atArgs] at x
    · exact hi

private theorem mem_domArgs_iff : ∀ (ts : List (Pat F)) (k i : ℕ) (r : Position),
    (i :: r) ∈ domArgs ts (k + 1) ↔ k < i ∧ (atArgs ts (i - k) r).isSome
  | [], _, _, _ => by simp [domArgs, atArgs]
  | t :: ts, k, i, r => by
    have ih := mem_domArgs_iff ts (k + 1) i r
    have ht := mem_domList_iff t r
    by_cases hki : k < i
    · obtain ⟨m, rfl⟩ : ∃ m, i = k + 1 + m := ⟨i - (k + 1), by omega⟩
      cases m with
      | zero =>
        have e : k + 1 + 0 - k = 1 := by omega
        simp only [domArgs, List.mem_append, List.mem_map, List.cons.injEq, e, atArgs]
        constructor
        · rintro (⟨a, ha, -, rfl⟩ | h)
          · exact ⟨hki, ht.1 ha⟩
          · exact absurd (ih.1 h).1 (by omega)
        · rintro ⟨-, h⟩
          exact Or.inl ⟨r, ht.2 h, by simp, rfl⟩
      | succ m =>
        have e : k + 1 + (m + 1) - k = m + 2 := by omega
        have e' : k + 1 + (m + 1) - (k + 1) = m + 1 := by omega
        rw [e'] at ih
        simp only [domArgs, List.mem_append, List.mem_map, List.cons.injEq, e, atArgs]
        constructor
        · rintro (⟨a, ha, h, -⟩ | h)
          · omega
          · exact ⟨hki, (ih.1 h).2⟩
        · rintro ⟨-, h⟩
          exact Or.inr (ih.2 ⟨by omega, h⟩)
    · simp only [domArgs, List.mem_append, List.mem_map, List.cons.injEq, hki, false_and, iff_false]
      rintro (⟨a, _, h, -⟩ | h)
      · omega
      · exact hki (by have := (ih.1 h).1; omega)

end

/-- `r ∈ D(t)` iff `t[r]` is defined. -/
private theorem mem_dom_iff (t : Pat F) (r : Position) : r ∈ t.dom ↔ (t.at r).isSome := by
  simp only [dom, List.mem_toFinset, mem_domList_iff]

end Pat

/-! ### Classes of a relation -/

private theorem depends_symm {g h : Goal F} (d : Depends g h) : Depends h g := by
  unfold Depends at *; rwa [Finset.inter_comm]

section Classes

variable {Q : Goal F → Goal F → Prop} [DecidableRel Q]

/-- The goals reachable from `a` by `Q`-steps inside `X`. -/
private def Rch (Q : Goal F → Goal F → Prop) (X : State F) (a h : Goal F) : Prop :=
  Relation.ReflTransGen (fun u v => Q u v ∧ v ∈ X) a h

private def clStep (Q : Goal F → Goal F → Prop) [DecidableRel Q] (X K : State F) : State F :=
  K ∪ X.filter fun h => ∃ k ∈ K, Q k h

private def clIt (Q : Goal F → Goal F → Prop) [DecidableRel Q] (X : State F) (g : Goal F) :
    ℕ → State F
  | 0 => {g}
  | n + 1 => clStep Q X (clIt Q X g n)

private theorem foldl_eq_clIt (X : State F) (g : Goal F) (n : ℕ) :
    (List.range n).foldl (fun K _ => K ∪ X.filter fun h => ∃ k ∈ K, Q k h) {g} = clIt Q X g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil, ih]; rfl

private theorem clIt_subset {X : State F} {g : Goal F} (hg : g ∈ X) : ∀ n, clIt Q X g n ⊆ X
  | 0 => by simpa [clIt] using hg
  | n + 1 => fun h hh => by
    rcases Finset.mem_union.1 hh with h1 | h1
    · exact clIt_subset hg n h1
    · exact (Finset.mem_filter.1 h1).1

private theorem clIt_le (X : State F) (g : Goal F) (n : ℕ) : clIt Q X g n ⊆ clIt Q X g (n + 1) :=
  Finset.subset_union_left

private theorem clIt_card (X : State F) (g : Goal F) :
    ∀ n, clIt Q X g n = clIt Q X g (n + 1) ∨ n + 1 ≤ (clIt Q X g n).card
  | 0 => Or.inr (by simp [clIt])
  | n + 1 => by
    by_cases he : clIt Q X g (n + 1) = clIt Q X g (n + 1 + 1)
    · exact Or.inl he
    · refine Or.inr ?_
      rcases clIt_card X g n with h | h
      · exact absurd (by show clIt Q X g (n + 1) = clStep Q X (clIt Q X g (n + 1)); rw [← h]; exact h) he
      · have hne : clIt Q X g n ≠ clIt Q X g (n + 1) := by
          intro h'
          exact he (by show clIt Q X g (n + 1) = clStep Q X (clIt Q X g (n + 1)); rw [← h']; exact h')
        have := Finset.card_lt_card ((clIt_le X g n).ssubset_of_ne hne)
        omega

private theorem classOf_eq_it (X : State F) (g : Goal F) : classOfBy Q X g = clIt Q X g X.card :=
  foldl_eq_clIt X g _

private theorem self_mem_classOf (X : State F) (g : Goal F) : g ∈ classOfBy Q X g := by
  rw [classOf_eq_it]
  have : ∀ n, g ∈ clIt Q X g n := fun n => by
    induction n with
    | zero => simp [clIt]
    | succ n ih => exact clIt_le X g n ih
  exact this _

private theorem classOf_subset {X : State F} {g : Goal F} (hg : g ∈ X) : classOfBy Q X g ⊆ X := by
  rw [classOf_eq_it]; exact clIt_subset hg _

/-- A class is closed under `Q` in `X`. -/
private theorem classOf_closed {X : State F} {g k h : Goal F} (hg : g ∈ X) (hk : k ∈ classOfBy Q X g)
    (hh : h ∈ X) (d : Q k h) : h ∈ classOfBy Q X g := by
  rw [classOf_eq_it] at hk ⊢
  have hfix : clIt Q X g X.card = clIt Q X g (X.card + 1) := by
    rcases clIt_card (Q := Q) X g X.card with h' | h'
    · exact h'
    · exact absurd (Finset.card_le_card (clIt_subset (Q := Q) hg X.card)) (by omega)
  rw [hfix]
  exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hh, k, hk, d⟩)

private theorem rch_of_mem_it {X : State F} {g : Goal F} : ∀ n h, h ∈ clIt Q X g n → Rch Q X g h
  | 0, h, hh => by rw [Finset.mem_singleton.1 hh]; exact .refl
  | n + 1, h, hh => by
    rcases Finset.mem_union.1 hh with h1 | h1
    · exact rch_of_mem_it n h h1
    · obtain ⟨hX, k, hk, d⟩ := Finset.mem_filter.1 h1
      exact (rch_of_mem_it n k hk).tail ⟨d, hX⟩

private theorem rch_of_mem {X : State F} {g h : Goal F} (hh : h ∈ classOfBy Q X g) : Rch Q X g h := by
  rw [classOf_eq_it] at hh; exact rch_of_mem_it _ h hh

private theorem mem_of_rch {X : State F} {g h : Goal F} (hg : g ∈ X) (r : Rch Q X g h) :
    h ∈ classOfBy Q X g := by
  induction r with
  | refl => exact self_mem_classOf X g
  | tail _ hs ih => exact classOf_closed hg ih hs.2 hs.1

private theorem rch_mem_X {X : State F} {g h : Goal F} (hg : g ∈ X) (r : Rch Q X g h) : h ∈ X :=
  classOf_subset hg (mem_of_rch hg r)

private theorem rch_symm (hQ : ∀ g h, Q g h → Q h g) {X : State F} {g h : Goal F} (hg : g ∈ X)
    (r : Rch Q X g h) : Rch Q X h g := by
  induction r with
  | refl => exact .refl
  | @tail b c hbc hs ih =>
    exact Relation.ReflTransGen.head ⟨hQ _ _ hs.1, rch_mem_X hg hbc⟩ ih

/-- A member of a class generates the same class. -/
private theorem classOf_eq_of_mem (hQ : ∀ g h, Q g h → Q h g) {X : State F} {g h : Goal F}
    (hg : g ∈ X) (hh : h ∈ classOfBy Q X g) : classOfBy Q X h = classOfBy Q X g := by
  have r := rch_of_mem hh
  have hX := rch_mem_X hg r
  ext k
  constructor
  · intro hk; exact mem_of_rch hg (r.trans (rch_of_mem hk))
  · intro hk; exact mem_of_rch hX ((rch_symm hQ hg r).trans (rch_of_mem hk))

/-- **Lemma 1, for a class whose goals have their obligations below their announcements.** The
`gcp` of a class is the announcement position of one of its goals, and a prefix of them all. This
needs only that related goals depend or announce at comparable positions. -/
private theorem gcpOf_spec (hQ : ∀ g h, Q g h → Q h g)
    (hcmp : ∀ g h, Q g h → Depends g h ∨ Comparable g.2.2 h.2.2) {X : State F} {g : Goal F}
    (hg : g ∈ X) (hbelow : ∀ h ∈ X, ∀ a ∈ h.1, h.2.2 <+: a.2) :
    (∃ h ∈ classOfBy Q X g, h.2.2 = gcpOf (classOfBy Q X g)) ∧
      ∀ h ∈ classOfBy Q X g, gcpOf (classOfBy Q X g) <+: h.2.2 := by
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (classOfBy Q X g) (fun h => h.2.2.length)
    ⟨g, self_mem_classOf X g⟩
  have hK : classOfBy Q X m = classOfBy Q X g := classOf_eq_of_mem hQ hg hm
  have hmX : m ∈ X := classOf_subset hg hm
  have hall : ∀ h ∈ classOfBy Q X g, m.2.2 <+: h.2.2 := by
    intro h hh
    have r : Rch Q X m h := by rw [← hK] at hh; exact rch_of_mem hh
    induction r with
    | refl => exact List.prefix_refl _
    | @tail b c hbc hs ih =>
      have hbK : b ∈ classOfBy Q X g := by rw [← hK]; exact mem_of_rch hmX hbc
      have ihb := ih hbK
      have hbX : b ∈ X := classOf_subset hg hbK
      rcases hcmp b c hs.1 with ⟨x, hx⟩ | hc
      · obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
        obtain ⟨a1, ha1, rfl⟩ := Finset.mem_image.1 hx1
        obtain ⟨a2, ha2, e⟩ := Finset.mem_image.1 hx2
        have p1 : m.2.2 <+: a1.2 := ihb.trans (hbelow b hbX a1 ha1)
        have p2 : c.2.2 <+: a1.2 := e ▸ hbelow c hs.2 a2 ha2
        exact List.prefix_of_prefix_length_le p1 p2 (hmin c hh)
      · rcases hc with hbc' | hcb
        · exact ihb.trans hbc'
        · exact List.prefix_of_prefix_length_le ihb hcb (hmin c hh)
  have hgcp : gcpOf (classOfBy Q X g) = m.2.2 :=
    gcp_eq (Finset.mem_image.2 ⟨m, hm, rfl⟩) fun q hq => by
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hq
      exact hall h hh
  exact ⟨⟨m, hm, hgcp.symm⟩, fun h hh => hgcp ▸ hall h hh⟩

end Classes

end MercLib.SetAutomaton
