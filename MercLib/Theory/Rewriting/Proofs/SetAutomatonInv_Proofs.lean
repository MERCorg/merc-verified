module

public import MercLib.Theory.Rewriting.SetAutomatonPartition
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonBase_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The invariant of the reachable states of the set automaton (Propositions 2 and 3, Corollary 1 of
the paper), preserved by `deriv` and `lift`. -/

namespace MercLib.SetAutomaton

variable {F : Type} [DecidableEq F] {ar : F → ℕ} {Ls : Finset (Pat F)}

private theorem mem_idx {n i : ℕ} : i ∈ (Finset.range n).image (· + 1) ↔ 1 ≤ i ∧ i ≤ n := by
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨i - 1, by omega, by omega⟩

private theorem mem_reduce {mo : Finset (At F)} {f : F} {l : Position} {a : At F} :
    a ∈ reduce ar mo f l ↔ (a ∈ mo ∧ a.2 ≠ l) ∨
      ∃ b ∈ mo, b.2 = l ∧ ∃ i, 1 ≤ i ∧ i ≤ ar f ∧ ∃ u, argAt b.1 i = some u ∧ u ≠ .omega ∧
        a = (u, l ++ [i]) := by
  simp only [reduce, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, mem_idx]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨b, ⟨hb, hl⟩, i, ⟨h1, h2⟩, hm⟩
    split at hm
    · rename_i u hu
      split at hm
      · simp at hm
      · rename_i hne
        exact ⟨b, hb, hl, i, h1, h2, u, hu, hne, Finset.mem_singleton.1 hm⟩
    · simp at hm
  · rintro ⟨b, hb, hl, i, h1, h2, u, hu, hne, rfl⟩
    exact ⟨b, ⟨hb, hl⟩, i, ⟨h1, h2⟩, by simp [hu, hne]⟩

private theorem mem_deriv {s : State F} {l : Position} {f : F} {g : Goal F} :
    g ∈ deriv ar Ls s l f ↔ (g ∈ s ∧ l ∉ pos g.1) ∨
      (∃ g₀ ∈ s, (∃ a ∈ g₀.1, a.2 = l ∧ a.1.hd = some f) ∧ g = (reduce ar g₀.1 f l, g₀.2) ∧
        g.1 ≠ ∅) ∨
      ∃ p ∈ Ls, ∃ i, 1 ≤ i ∧ i ≤ ar f ∧ g = ({(p, l ++ [i])}, (p, l ++ [i])) := by
  simp only [deriv, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_biUnion,
    or_assoc]
  refine or_congr Iff.rfl (or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩)
  · rintro ⟨⟨g₀, ⟨hg, ha⟩, rfl⟩, hne⟩; exact ⟨g₀, hg, ha, rfl, hne⟩
  · rintro ⟨g₀, hg, ha, rfl, hne⟩; exact ⟨⟨g₀, ⟨hg, ha⟩, rfl⟩, hne⟩
  · rintro ⟨p, hp, i, hi, rfl⟩
    have h := mem_idx.1 (Finset.mem_image.2 hi)
    exact ⟨p, hp, i, h.1, h.2, rfl⟩
  · rintro ⟨p, hp, i, h1, h2, rfl⟩
    exact ⟨p, hp, i, Finset.mem_image.1 (mem_idx.2 ⟨h1, h2⟩), rfl⟩

omit [DecidableEq F] in
private theorem mem_pos {mo : Finset (At F)} {p : Position} : p ∈ pos mo ↔ ∃ a ∈ mo, a.2 = p := by
  simp [pos]

/-- The state invariant without the root goal. -/
private structure GInv (Ls : Finset (Pat F)) (s : State F) : Prop where
  goals : ∀ g ∈ s, g.1.Nonempty ∧ g.2.1 ∈ Ls ∧
    ∀ a ∈ g.1, ∃ r, a.2 = g.2.2 ++ r ∧ g.2.1.at r = some a.1 ∧ a.1 ≠ .omega
  incomp : ∀ g ∈ s, ∀ g' ∈ s, ∀ a ∈ g.1, ∀ b ∈ g'.1, (a.2 <+: b.2 ∨ b.2 <+: a.2) → a.2 = b.2
  fresh : ∀ g ∈ s, ∀ a ∈ g.1, ∀ p ∈ Ls, (({(p, a.2)}, (p, a.2)) : Goal F) ∈ s

omit [DecidableEq F] in
private theorem GInv.below {X : State F} (I : GInv Ls X) : ∀ h ∈ X, ∀ a ∈ h.1, h.2.2 <+: a.2 := by
  intro h hh a ha
  obtain ⟨r, e, _⟩ := (I.goals h hh).2.2 a ha
  exact e ▸ List.prefix_append _ _

private theorem ginv_initial (hLs : ∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) : GInv Ls (initial Ls) := by
  have hmem : ∀ g, g ∈ initial Ls ↔ ∃ p ∈ Ls, g = ({(p, [])}, (p, [])) := fun g => by
    simp [initial, eq_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := (hmem g).1 hg
    refine ⟨by simp, hp, ?_⟩
    intro a ha
    rw [Finset.mem_singleton.1 ha]
    exact ⟨[], rfl, by simp [Pat.at], (hLs p hp).1⟩
  · intro g hg g' hg' a ha b hb _
    obtain ⟨p, hp, rfl⟩ := (hmem g).1 hg
    obtain ⟨p', hp', rfl⟩ := (hmem g').1 hg'
    rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb]
  · intro g hg a ha p hp
    obtain ⟨q, _, rfl⟩ := (hmem g).1 hg
    rw [Finset.mem_singleton.1 ha]
    exact (hmem _).2 ⟨p, hp, rfl⟩

/-- Every obligation position of `deriv` is old (and not the label), or a child of the label. -/
private theorem pos_deriv {s : State F} {l : Position} {f : F} {g : Goal F} {a : At F}
    (hg : g ∈ deriv ar Ls s l f) (ha : a ∈ g.1) :
    (∃ g₀ ∈ s, a ∈ g₀.1 ∧ a.2 ≠ l) ∨ ∃ i, 1 ≤ i ∧ i ≤ ar f ∧ a.2 = l ++ [i] := by
  rcases mem_deriv.1 hg with ⟨hs, hl⟩ | ⟨g₀, hs, -, rfl, -⟩ | ⟨p, -, i, h1, h2, rfl⟩
  · exact Or.inl ⟨g, hs, ha, fun e => hl (mem_pos.2 ⟨a, ha, e⟩)⟩
  · rcases mem_reduce.1 ha with ⟨h, hne⟩ | ⟨b, -, -, i, h1, h2, u, -, -, rfl⟩
    · exact Or.inl ⟨g₀, hs, h, hne⟩
    · exact Or.inr ⟨i, h1, h2, rfl⟩
  · rw [Finset.mem_singleton.1 ha]; exact Or.inr ⟨i, h1, h2, rfl⟩

omit [DecidableEq F] in
private theorem not_comparable_child {s : State F} {l : Position} (I : GInv Ls s)
    {g₀ g₁ : Goal F} (hg₀ : g₀ ∈ s) (hg₁ : g₁ ∈ s) {a d : At F} (ha : a ∈ g₀.1) (hd : d ∈ g₁.1)
    (hdl : d.2 = l) (hne : a.2 ≠ l) (i : ℕ) (hc : a.2 <+: l ++ [i] ∨ l ++ [i] <+: a.2) : False := by
  have key : a.2 <+: l ∨ l <+: a.2 := by
    rcases hc with h | h
    · rcases List.prefix_concat_iff.1 h with e | h'
      · exact Or.inr (e ▸ List.prefix_append _ _)
      · exact Or.inl h'
    · exact Or.inr ((List.prefix_append _ _).trans h)
  exact hne ((I.incomp g₀ hg₀ g₁ hg₁ a ha d hd (by rw [hdl]; exact key)).trans hdl)

private theorem ginv_deriv {s : State F} {l : Position} {f : F}
    (hLs : ∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) (I : GInv Ls s)
    (hl : ∃ g ∈ s, ∃ a ∈ g.1, a.2 = l) : GInv Ls (deriv ar Ls s l f) := by
  obtain ⟨g₁, hg₁, d, hd, hdl⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases mem_deriv.1 hg with ⟨hs, -⟩ | ⟨g₀, hs, -, rfl, hne⟩ | ⟨p, hp, i, -, -, rfl⟩
    · exact I.goals g hs
    · obtain ⟨-, hLm, hgoals⟩ := I.goals g₀ hs
      refine ⟨Finset.nonempty_iff_ne_empty.2 hne, hLm, ?_⟩
      intro a ha
      rcases mem_reduce.1 ha with ⟨h, -⟩ | ⟨b, hb, hbl, i, -, -, u, hu, hne', rfl⟩
      · exact hgoals a h
      · obtain ⟨r, e, hat, -⟩ := hgoals b hb
        refine ⟨r ++ [i], ?_, ?_, hne'⟩
        · show l ++ [i] = g₀.2.2 ++ (r ++ [i])
          rw [← List.append_assoc, ← e, hbl]
        · rw [Pat.at_append, hat]; exact hu
    · refine ⟨by simp, hp, ?_⟩
      intro a ha
      rw [Finset.mem_singleton.1 ha]
      exact ⟨[], by simp, by simp [Pat.at], (hLs p hp).1⟩
  · intro g hg g' hg' a ha b hb hc
    rcases pos_deriv hg ha with ⟨g₀, hs, ha', hne⟩ | ⟨i, -, -, ei⟩ <;>
      rcases pos_deriv hg' hb with ⟨g₀', hs', hb', hne'⟩ | ⟨j, -, -, ej⟩
    · exact I.incomp g₀ hs g₀' hs' a ha' b hb' hc
    · exact (not_comparable_child I hs hg₁ ha' hd hdl hne j (by rwa [ej] at hc)).elim
    · exact (not_comparable_child I hs' hg₁ hb' hd hdl hne' i
        (by rw [ei] at hc; exact hc.symm)).elim
    · rw [ei, ej] at hc ⊢
      have hlen : (l ++ [i]).length = (l ++ [j]).length := by simp
      rcases hc with h | h
      · exact h.eq_of_length hlen
      · exact (h.eq_of_length hlen.symm).symm
  · intro g hg a ha p hp
    rcases pos_deriv hg ha with ⟨g₀, hs, ha', hne⟩ | ⟨i, h1, h2, ei⟩
    · refine mem_deriv.2 (Or.inl ⟨I.fresh g₀ hs a ha' p hp, fun h => hne ?_⟩)
      obtain ⟨b, hb, e⟩ := mem_pos.1 h
      rw [Finset.mem_singleton.1 hb] at e
      exact e.symm ▸ rfl
    · rw [ei]
      exact mem_deriv.2 (Or.inr (Or.inr ⟨p, hp, i, h1, h2, rfl⟩))

/-! ### Lifting -/

private theorem shorten_app {c q : Position} (h : c <+: q) : c ++ shorten c q = q := by
  obtain ⟨t, rfl⟩ := h; simp [shorten]

private theorem shorten_append {c q : Position} (h : c <+: q) (r : Position) :
    shorten c (q ++ r) = shorten c q ++ r := by
  obtain ⟨t, rfl⟩ := h; simp [shorten]

private theorem shorten_self (c : Position) : shorten c c = [] := by simp [shorten]

private theorem shorten_prefix {c x y : Position} (hx : c <+: x) (hy : c <+: y) :
    shorten c x <+: shorten c y ↔ x <+: y := by
  obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy; simp [shorten]

private theorem mem_lift {K : State F} {g : Goal F} :
    g ∈ lift K ↔ ∃ h ∈ K, g = (h.1.image fun a => (a.1, shorten (gcpOf K) a.2),
      (h.2.1, shorten (gcpOf K) h.2.2)) := by
  simp [lift, eq_comm]

/-- The conditions on a relation that partitions a derivative. -/
private structure QOk (Q : Goal F → Goal F → Prop) : Prop where
  symm : ∀ g h, Q g h → Q h g
  dep : ∀ g h, Depends g h → Q g h
  cmp : ∀ g h, Q g h → Depends g h ∨ Comparable g.2.2 h.2.2

omit [DecidableEq F] in
private theorem PartitionAdmissible.ok {R : Position → F → Goal F → Goal F → Prop}
    (hR : PartitionAdmissible R) (l : Position) (f : F) : QOk (R l f) :=
  ⟨fun g h => (hR l f g h).1, fun g h => (hR l f g h).2.1, fun g h => (hR l f g h).2.2⟩

section Lift

variable {Q : Goal F → Goal F → Prop} [DecidableRel Q]

private theorem QOk.gcp (hQ : QOk Q) {X : State F} (I : GInv Ls X) {g : Goal F} (hg : g ∈ X) :
    (∃ h ∈ classOfBy Q X g, h.2.2 = gcpOf (classOfBy Q X g)) ∧
      ∀ h ∈ classOfBy Q X g, gcpOf (classOfBy Q X g) <+: h.2.2 :=
  gcpOf_spec hQ.symm hQ.cmp hg I.below

/-- What is known of a class of `X`. -/
private theorem class_prefix (hQ : QOk Q) {X : State F} (I : GInv Ls X) {g h : Goal F} (hg : g ∈ X)
    (hh : h ∈ classOfBy Q X g) {a : At F} (ha : a ∈ h.1) : gcpOf (classOfBy Q X g) <+: a.2 :=
  ((hQ.gcp I hg).2 h hh).trans (I.below h (classOf_subset hg hh) a ha)

private theorem ginv_lift (hQ : QOk Q) {X : State F} (I : GInv Ls X) {g : Goal F} (hg : g ∈ X) :
    GInv Ls (lift (classOfBy Q X g)) ∧ ∃ h ∈ lift (classOfBy Q X g), h.2.2 = [] := by
  set K := classOfBy Q X g with hK
  have hsub : K ⊆ X := classOf_subset hg
  have hma : ∀ h ∈ K, gcpOf K <+: h.2.2 := (hQ.gcp I hg).2
  have hpre : ∀ h ∈ K, ∀ a ∈ h.1, gcpOf K <+: a.2 := fun h hh a ha => class_prefix hQ I hg hh ha
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g' hg'
    obtain ⟨h, hh, rfl⟩ := mem_lift.1 hg'
    obtain ⟨hne, hLm, hgoals⟩ := I.goals h (hsub hh)
    refine ⟨hne.image _, hLm, ?_⟩
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
    obtain ⟨r, e, hat, hom⟩ := hgoals a ha
    refine ⟨r, ?_, hat, hom⟩
    show shorten (gcpOf K) a.2 = shorten (gcpOf K) h.2.2 ++ r
    rw [e, shorten_append (hma h hh)]
  · intro g₁ hg₁ g₂ hg₂ a' ha' b' hb' hc
    obtain ⟨h₁, hh₁, rfl⟩ := mem_lift.1 hg₁
    obtain ⟨h₂, hh₂, rfl⟩ := mem_lift.1 hg₂
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    have hc' : a.2 <+: b.2 ∨ b.2 <+: a.2 := by
      simpa only [shorten_prefix (hpre h₁ hh₁ a ha) (hpre h₂ hh₂ b hb),
        shorten_prefix (hpre h₂ hh₂ b hb) (hpre h₁ hh₁ a ha)] using hc
    show shorten _ a.2 = shorten _ b.2
    rw [I.incomp h₁ (hsub hh₁) h₂ (hsub hh₂) a ha b hb hc']
  · intro g' hg' a' ha' p hp
    obtain ⟨h, hh, rfl⟩ := mem_lift.1 hg'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
    have hG := I.fresh h (hsub hh) a ha p hp
    have hd : Depends h (({(p, a.2)}, (p, a.2)) : Goal F) :=
      ⟨a.2, Finset.mem_inter.2 ⟨mem_pos.2 ⟨a, ha, rfl⟩, mem_pos.2 ⟨_, Finset.mem_singleton_self _, rfl⟩⟩⟩
    have hGK : (({(p, a.2)}, (p, a.2)) : Goal F) ∈ K := classOf_closed hg hh hG (hQ.dep _ _ hd)
    refine mem_lift.2 ⟨_, hGK, ?_⟩
    simp
  · obtain ⟨h, hh, e⟩ := (hQ.gcp I hg).1
    refine ⟨_, mem_lift.2 ⟨h, hh, rfl⟩, ?_⟩
    show shorten (gcpOf K) h.2.2 = []
    rw [e, shorten_self]

end Lift

variable {R : Position → F → Goal F → Goal F → Prop} [∀ l f, DecidableRel (R l f)]

/-- The state invariant. -/
private structure Inv (Ls : Finset (Pat F)) (s : State F) : Prop extends GInv Ls s where
  root : ∃ g ∈ s, g.2.2 = []

omit [DecidableEq F] in
/-- The label of a reachable state is an obligation position. -/
private theorem label_mem {L : State F → Position} (hL : Admissible L) {s : State F}
    (I : Inv Ls s) : ∃ g ∈ s, ∃ a ∈ g.1, a.2 = L s := by
  obtain ⟨g, hg, -, hp⟩ := hL s I.root
  obtain ⟨a, ha, e⟩ := mem_pos.1 hp
  exact ⟨g, hg, a, ha, e⟩

private theorem mem_delta {s s' : State F} {l p' : Position} {f : F} :
    (s', p') ∈ deltaBy R ar Ls s l f ↔ ∃ g ∈ deriv ar Ls s l f,
      s' = lift (classOfBy (R l f) (deriv ar Ls s l f) g) ∧
        p' = gcpOf (classOfBy (R l f) (deriv ar Ls s l f) g) := by
  simp only [deltaBy, classesBy, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨K, ⟨g, hg, rfl⟩, rfl, rfl⟩; exact ⟨g, hg, rfl, rfl⟩
  · rintro ⟨g, hg, rfl, rfl⟩; exact ⟨_, ⟨g, hg, rfl⟩, rfl, rfl⟩

private theorem inv_reachable (hR : PartitionAdmissible R) {L : State F → Position}
    (hL : Admissible L) (hne : Ls.Nonempty)
    (hLs : ∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) {s : State F} (h : ReachableBy R ar Ls L s) :
    Inv Ls s := by
  induction h with
  | init =>
    obtain ⟨p, hp⟩ := hne
    exact ⟨ginv_initial hLs, ⟨_, Finset.mem_image.2 ⟨p, hp, rfl⟩, rfl⟩⟩
  | step _ hd ih =>
    obtain ⟨g, hg, rfl, -⟩ := mem_delta.1 hd
    obtain ⟨h1, h2⟩ := ginv_lift (hR.ok _ _) (ginv_deriv hLs ih.toGInv (label_mem hL ih)) hg
    exact ⟨h1, h2⟩

end MercLib.SetAutomaton
