module

public import MercLib.Algorithms.Rewriting.SetAutomaton
public import MercLib.Theory.Rewriting.Proofs.SetAutomaton_Proofs
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonEval_Proofs
import Mathlib.Data.Finset.Card
import Std.Tactic.Do

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Correctness of `construct` and `findMatches`. `SetAutomatonRun_Proofs` imports this module privately,
so that the lemmas `mvcgen` and `simp` generate are not exported.

No configuration is processed twice because the work sets `W` of the proof of Lemma 3 of the paper
are pairwise disjoint on the configurations waiting in the work set, and the positions already
inspected lie outside all of them. -/

namespace MercLib.SetAutomaton

variable {F : Type} [DecidableEq F] {ar : F → ℕ} {Ls : Finset (Pat F)} {L : State F → Position}

/-! ### The construction -/

section Construct

variable [Fintype F]

private theorem mem_edges {s s₀ s' : State F} {f : F} {p' : Position} :
    (s₀, f, s', p') ∈ edges ar Ls L s ↔ s₀ = s ∧ (s', p') ∈ delta ar Ls s (L s) f := by
  simp only [edges, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨g, ⟨a, b⟩, h, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨f, _, h, rfl, rfl, rfl, rfl⟩

private theorem mem_outputs {s s₀ : State F} {f : F} {a : At F} :
    (s₀, f, a) ∈ outputs ar L s ↔ s₀ = s ∧ a ∈ eta ar s (L s) f := by
  simp only [outputs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨g, b, h, rfl, rfl, rfl⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨f, _, h, rfl, rfl, rfl⟩

/-- The invariant of `construct`. -/
private structure CInv (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position)
    (S Q : Finset (State F)) (δ : Finset (State F × F × State F × Position))
    (η : Finset (State F × F × At F)) : Prop where
  reach : ∀ s ∈ S, Reachable ar Ls L s
  qs : Q ⊆ S
  init : initial Ls ∈ S
  hdelta : ∀ s f s' p', (s, f, s', p') ∈ δ ↔ (s ∈ S ∧ s ∉ Q) ∧ (s', p') ∈ delta ar Ls s (L s) f
  heta : ∀ s f a, (s, f, a) ∈ η ↔ (s ∈ S ∧ s ∉ Q) ∧ a ∈ eta ar s (L s) f
  closed : ∀ s ∈ S, s ∉ Q → ∀ f n, n ∈ delta ar Ls s (L s) f → n.1 ∈ S

private theorem cinv_init : CInv ar Ls L {initial Ls} {initial Ls} ∅ ∅ := by
  refine ⟨?_, subset_rfl, Finset.mem_singleton_self _, ?_, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_singleton.1 hs]
    exact .init
  · simp
  · simp
  · intro s hs hq
    exact absurd hs hq

/-- The target states of the states in `Q`. -/
private abbrev targets (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position)
    (Q : Finset (State F)) : Finset (State F) :=
  (Q.biUnion (edges ar Ls L)).image fun e => e.2.2.1

private theorem mem_targets {Q : Finset (State F)} {s' : State F} :
    s' ∈ targets ar Ls L Q ↔ ∃ s ∈ Q, ∃ f p', (s', p') ∈ delta ar Ls s (L s) f := by
  simp only [targets, Finset.mem_image, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨s₀, f, s'', p'⟩, ⟨s, hs, he⟩, rfl⟩
    obtain ⟨rfl, hd⟩ := mem_edges.1 he
    exact ⟨_, hs, f, p', hd⟩
  · rintro ⟨s, hs, f, p', hd⟩
    exact ⟨(s, f, s', p'), ⟨s, hs, mem_edges.2 ⟨rfl, hd⟩⟩, rfl⟩

private theorem cinv_step {S Q : Finset (State F)} {δ : Finset (State F × F × State F × Position)}
    {η : Finset (State F × F × At F)} (I : CInv ar Ls L S Q δ η) :
    CInv ar Ls L (S ∪ targets ar Ls L Q) (targets ar Ls L Q \ S)
      (δ ∪ Q.biUnion (edges ar Ls L)) (η ∪ Q.biUnion (outputs ar L)) := by
  have hold : ∀ {s}, s ∈ S ∪ targets ar Ls L Q → s ∉ targets ar Ls L Q \ S → s ∈ S := by
    intro s h₁ h₂
    by_contra hs
    rcases Finset.mem_union.1 h₁ with h | h
    · exact hs h
    · exact h₂ (Finset.mem_sdiff.2 ⟨h, hs⟩)
  have hnew : ∀ {s}, s ∈ S → s ∉ targets ar Ls L Q \ S := fun hs h =>
    (Finset.mem_sdiff.1 h).2 hs
  refine ⟨?_, ?_, Finset.mem_union_left _ I.init, ?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_union.1 hs with h | h
    · exact I.reach s h
    · obtain ⟨s₀, h₀, f, p', hd⟩ := mem_targets.1 h
      exact .step (I.reach s₀ (I.qs h₀)) hd
  · intro s hs
    exact Finset.mem_union_right _ (Finset.mem_sdiff.1 hs).1
  · intro s f s' p'
    simp only [Finset.mem_union, I.hdelta, Finset.mem_biUnion, mem_edges]
    constructor
    · rintro (⟨⟨hs, -⟩, hd⟩ | ⟨s₀, h₀, rfl, hd⟩)
      · exact ⟨⟨Or.inl hs, hnew hs⟩, hd⟩
      · exact ⟨⟨Or.inl (I.qs h₀), hnew (I.qs h₀)⟩, hd⟩
    · rintro ⟨⟨h₁, h₂⟩, hd⟩
      have hs := hold (Finset.mem_union.2 h₁) h₂
      by_cases hq : s ∈ Q
      · exact Or.inr ⟨s, hq, rfl, hd⟩
      · exact Or.inl ⟨⟨hs, hq⟩, hd⟩
  · intro s f a
    simp only [Finset.mem_union, I.heta, Finset.mem_biUnion, mem_outputs]
    constructor
    · rintro (⟨⟨hs, -⟩, hd⟩ | ⟨s₀, h₀, rfl, hd⟩)
      · exact ⟨⟨Or.inl hs, hnew hs⟩, hd⟩
      · exact ⟨⟨Or.inl (I.qs h₀), hnew (I.qs h₀)⟩, hd⟩
    · rintro ⟨⟨h₁, h₂⟩, hd⟩
      have hs := hold (Finset.mem_union.2 h₁) h₂
      by_cases hq : s ∈ Q
      · exact Or.inr ⟨s, hq, rfl, hd⟩
      · exact Or.inl ⟨⟨hs, hq⟩, hd⟩
  · intro s h₁ h₂ f n hn
    have hs := hold h₁ h₂
    by_cases hq : s ∈ Q
    · exact Finset.mem_union_right _ (mem_targets.2 ⟨s, hq, f, n.2, hn⟩)
    · exact Finset.mem_union_left _ (I.closed s hs hq f n hn)

private theorem cinv_measure {R S Q : Finset (State F)} {δ : Finset (State F × F × State F × Position)}
    {η : Finset (State F × F × At F)} (I : CInv ar Ls L S Q δ η)
    (hR : ∀ s, s ∈ R ↔ Reachable ar Ls L s) (hQ : Q ≠ ∅) :
    (R \ (S ∪ targets ar Ls L Q)).card + (targets ar Ls L Q \ S).card < (R \ S).card + Q.card := by
  have hsub : targets ar Ls L Q \ S ⊆ R \ S := by
    intro s hs
    obtain ⟨h₁, h₂⟩ := Finset.mem_sdiff.1 hs
    refine Finset.mem_sdiff.2 ⟨(hR s).2 ?_, h₂⟩
    obtain ⟨s₀, h₀, f, p', hd⟩ := mem_targets.1 h₁
    exact .step (I.reach s₀ (I.qs h₀)) hd
  have he : R \ (S ∪ targets ar Ls L Q) = (R \ S) \ (targets ar Ls L Q \ S) := by
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hc := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hQ)
  have hs := Finset.card_sdiff_add_card_eq_card hsub
  rw [he]
  omega

private theorem cinv_final {S : Finset (State F)} {δ : Finset (State F × F × State F × Position)}
    {η : Finset (State F × F × At F)} (I : CInv ar Ls L S ∅ δ η) (s : State F) :
    s ∈ S ↔ Reachable ar Ls L s := by
  refine ⟨I.reach s, fun h => ?_⟩
  induction h with
  | init => exact I.init
  | step _ hd ih => exact I.closed _ ih (Finset.notMem_empty _) _ _ hd

end Construct

/-! ### Matching -/

section Match

variable {t : Pat F}

/-- The tables `M` are those of the automaton on the reachable states. -/
private structure Tab [Fintype F] (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position)
    (M : Automaton F) : Prop where
  init : M.init = initial Ls
  hdelta : ∀ s f s' p', (s, f, s', p') ∈ M.delta ↔
    Reachable ar Ls L s ∧ (s', p') ∈ delta ar Ls s (L s) f
  heta : ∀ s f a, (s, f, a) ∈ M.eta ↔ Reachable ar Ls L s ∧ a ∈ eta ar s (L s) f

private theorem node_reachable {n : Config F} (h : NodeBy depR ar Ls L t n) :
    Reachable ar Ls L n.1 := by
  induction h with
  | root => exact .init
  | step _ _ hd ih => exact .step ih hd

private theorem w_sub (H : Hyp depR ar Ls L t) {n c : Config F} (hn : NodeBy depR ar Ls L t n)
    (hc : Child depR ar Ls L t n c) : W t c ⊆ W t n := by
  obtain ⟨f, A⟩ := exists_head H hn
  exact W_child_subset A hc

private theorem w_self (H : Hyp depR ar Ls L t) {n : Config F} (hn : NodeBy depR ar Ls L t n) :
    n.2 ++ L n.1 ∈ W t n := by
  obtain ⟨f, A⟩ := exists_head H hn
  exact phi_mem_W A

private theorem w_not (H : Hyp depR ar Ls L t) {n c : Config F} (hn : NodeBy depR ar Ls L t n)
    (hc : Child depR ar Ls L t n c) : n.2 ++ L n.1 ∉ W t c := by
  obtain ⟨f, A⟩ := exists_head H hn
  exact phi_not_mem_child A hc

private theorem w_disj (H : Hyp depR ar Ls L t) {n c₁ c₂ : Config F} (hn : NodeBy depR ar Ls L t n)
    (h₁ : Child depR ar Ls L t n c₁) (h₂ : Child depR ar Ls L t n c₂) (hne : c₁ ≠ c₂) {x : Position}
    (hx₁ : x ∈ W t c₁) (hx₂ : x ∈ W t c₂) : False := by
  obtain ⟨f, A⟩ := exists_head H hn
  exact children_disjoint A h₁ h₂ hne hx₁ hx₂

variable [Fintype F] {M : Automaton F}

private theorem mem_successors (T : Tab ar Ls L M) {n c : Config F} (hn : NodeBy depR ar Ls L t n) :
    c ∈ M.successors L t n ↔ Child depR ar Ls L t n c := by
  have hr := node_reachable hn
  unfold Automaton.successors Child
  cases hh : headAt t (n.2 ++ L n.1) with
  | none => simp
  | some f =>
    simp only [Finset.mem_image, Finset.mem_filter, Option.some.injEq]
    constructor
    · rintro ⟨⟨s, g, s', p'⟩, ⟨he, rfl, rfl⟩, rfl⟩
      exact ⟨g, s', p', rfl, ((T.hdelta _ _ _ _).1 he).2, rfl⟩
    · rintro ⟨g, s', p', rfl, hd, rfl⟩
      exact ⟨(n.1, f, s', p'), ⟨(T.hdelta _ _ _ _).2 ⟨hr, hd⟩, rfl, rfl⟩, rfl⟩

private theorem mem_announced (T : Tab ar Ls L M) {n : Config F} {a : At F}
    (hn : NodeBy depR ar Ls L t n) :
    a ∈ M.announced L t n ↔ ∃ f q, headAt t (n.2 ++ L n.1) = some f ∧
      (a.1, q) ∈ eta ar n.1 (L n.1) f ∧ a.2 = n.2 ++ q := by
  have hr := node_reachable hn
  unfold Automaton.announced
  cases hh : headAt t (n.2 ++ L n.1) with
  | none => simp
  | some f =>
    simp only [Finset.mem_image, Finset.mem_filter, Option.some.injEq]
    constructor
    · rintro ⟨⟨s, g, b⟩, ⟨he, rfl, rfl⟩, rfl⟩
      exact ⟨g, b.2, rfl, ((T.heta _ _ _).1 he).2, rfl⟩
    · rintro ⟨g, q, rfl, hd, ha⟩
      exact ⟨(n.1, f, a.1, q), ⟨(T.heta _ _ _).2 ⟨hr, hd⟩, rfl, rfl⟩, Prod.ext rfl ha.symm⟩

/-- The position inspected in a configuration. -/
private abbrev phi (L : State F → Position) (c : Config F) : Position := c.2 ++ L c.1

/-- The invariant of `findMatches`; `S` is the set of configurations processed so far. -/
private structure MInv (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position) (M : Automaton F)
    (t : Pat F) (S Wk : Finset (Config F)) (A : Finset (At F)) (log : Multiset Position) : Prop where
  nodeS : ∀ n ∈ S, NodeBy depR ar Ls L t n
  nodeW : ∀ n ∈ Wk, NodeBy depR ar Ls L t n
  root : (initial Ls, []) ∈ S ∨ (initial Ls, []) ∈ Wk
  pair : ∀ n ∈ Wk, ∀ m ∈ Wk, n ≠ m → ∀ x, x ∈ W t n → x ∈ W t m → False
  sep : ∀ m ∈ S, ∀ n ∈ Wk, phi L m ∉ W t n
  log : log = S.val.map (phi L)
  ann : ∀ a, a ∈ A ↔ ∃ n ∈ S, a ∈ M.announced L t n
  closed : ∀ n ∈ S, ∀ c, Child depR ar Ls L t n c → c ∈ S ∨ c ∈ Wk

private theorem minv_init : MInv ar Ls L M t ∅ {(initial Ls, [])} ∅ 0 := by
  refine ⟨by simp, ?_, by simp, ?_, by simp, by simp, by simp, by simp⟩
  · intro n hn
    rw [Finset.mem_singleton.1 hn]
    exact .root
  · intro n hn m hm hne
    exact absurd ((Finset.mem_singleton.1 hn).trans (Finset.mem_singleton.1 hm).symm) hne

private theorem minv_disjoint (H : Hyp depR ar Ls L t) {S Wk B : Finset (Config F)} {A : Finset (At F)}
    {log : Multiset Position} (I : MInv ar Ls L M t S Wk A log) (hB : B ⊆ Wk) : Disjoint S B :=
  Finset.disjoint_left.2 fun m hS hb =>
    I.sep m hS m (hB hb) (w_self H (I.nodeW m (hB hb)))

private theorem minv_step (T : Tab ar Ls L M) (H : Hyp depR ar Ls L t) {S Wk B : Finset (Config F)}
    {A : Finset (At F)} {log : Multiset Position} (I : MInv ar Ls L M t S Wk A log) (hB : B ⊆ Wk) :
    MInv ar Ls L M t (S ∪ B) ((Wk \ B) ∪ B.biUnion (M.successors L t))
      (A ∪ B.biUnion (M.announced L t)) (log + B.val.map (phi L)) := by
  have hchild : ∀ {c}, c ∈ B.biUnion (M.successors L t) → ∃ b ∈ B, Child depR ar Ls L t b c := by
    intro c hc
    obtain ⟨b, hb, hs⟩ := Finset.mem_biUnion.1 hc
    exact ⟨b, hb, (mem_successors T (I.nodeW b (hB hb))).1 hs⟩
  have hsub : ∀ {b c}, b ∈ B → Child depR ar Ls L t b c → W t c ⊆ W t b := fun hb hc =>
    w_sub H (I.nodeW _ (hB hb)) hc
  have mixed : ∀ {n c b : Config F}, n ∈ Wk → n ∉ B → b ∈ B → Child depR ar Ls L t b c →
      ∀ x, x ∈ W t n → x ∈ W t c → False := by
    intro n c b hn hnB hb hc x hx₁ hx₂
    exact I.pair n hn b (hB hb) (fun e => hnB (e ▸ hb)) x hx₁ (hsub hb hc hx₂)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_union.1 hn with h | h
    · exact I.nodeS n h
    · exact I.nodeW n (hB h)
  · intro n hn
    rcases Finset.mem_union.1 hn with h | h
    · exact I.nodeW n (Finset.mem_sdiff.1 h).1
    · obtain ⟨b, hb, hc⟩ := hchild h
      exact node_child (I.nodeW b (hB hb)) hc
  · by_cases hr : ((initial Ls, []) : Config F) ∈ B
    · exact Or.inl (Finset.mem_union_right _ hr)
    · rcases I.root with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h, hr⟩))
  · intro n hn m hm hne x hx₁ hx₂
    rcases Finset.mem_union.1 hn with hn' | hn' <;> rcases Finset.mem_union.1 hm with hm' | hm'
    · exact I.pair n (Finset.mem_sdiff.1 hn').1 m (Finset.mem_sdiff.1 hm').1 hne x hx₁ hx₂
    · obtain ⟨hn₁, hn₂⟩ := Finset.mem_sdiff.1 hn'
      obtain ⟨b, hb, hc⟩ := hchild hm'
      exact mixed hn₁ hn₂ hb hc x hx₁ hx₂
    · obtain ⟨hm₁, hm₂⟩ := Finset.mem_sdiff.1 hm'
      obtain ⟨b, hb, hc⟩ := hchild hn'
      exact mixed hm₁ hm₂ hb hc x hx₂ hx₁
    · obtain ⟨b₁, hb₁, hc₁⟩ := hchild hn'
      obtain ⟨b₂, hb₂, hc₂⟩ := hchild hm'
      by_cases e : b₁ = b₂
      · subst e
        exact w_disj H (I.nodeW _ (hB hb₁)) hc₁ hc₂ hne hx₁ hx₂
      · exact I.pair b₁ (hB hb₁) b₂ (hB hb₂) e x (hsub hb₁ hc₁ hx₁) (hsub hb₂ hc₂ hx₂)
  · intro m hm n hn hx
    rcases Finset.mem_union.1 hm with hm' | hm' <;> rcases Finset.mem_union.1 hn with hn' | hn'
    · exact I.sep m hm' n (Finset.mem_sdiff.1 hn').1 hx
    · obtain ⟨b, hb, hc⟩ := hchild hn'
      exact I.sep m hm' b (hB hb) (hsub hb hc hx)
    · obtain ⟨hn₁, hn₂⟩ := Finset.mem_sdiff.1 hn'
      exact I.pair m (hB hm') n hn₁ (fun e => hn₂ (e ▸ hm')) _ (w_self H (I.nodeW m (hB hm'))) hx
    · obtain ⟨b, hb, hc⟩ := hchild hn'
      by_cases e : b = m
      · subst e
        exact w_not H (I.nodeW _ (hB hb)) hc hx
      · exact I.pair m (hB hm') b (hB hb) (Ne.symm e) _ (w_self H (I.nodeW m (hB hm')))
          (hsub hb hc hx)
  · rw [I.log, ← Finset.disjUnion_eq_union S B (minv_disjoint H I hB)]
    simp [Finset.disjUnion, Multiset.map_add]
  · intro a
    simp only [Finset.mem_union, I.ann, Finset.mem_biUnion]
    constructor
    · rintro (⟨n, hn, ha⟩ | ⟨n, hn, ha⟩)
      · exact ⟨n, Or.inl hn, ha⟩
      · exact ⟨n, Or.inr hn, ha⟩
    · rintro ⟨n, hn | hn, ha⟩
      · exact Or.inl ⟨n, hn, ha⟩
      · exact Or.inr ⟨n, hn, ha⟩
  · intro n hn c hc
    rcases Finset.mem_union.1 hn with h | h
    · rcases I.closed n h c hc with h' | h'
      · exact Or.inl (Finset.mem_union_left _ h')
      · by_cases hb : c ∈ B
        · exact Or.inl (Finset.mem_union_right _ hb)
        · exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h', hb⟩))
    · refine Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨n, h, ?_⟩))
      exact (mem_successors T (I.nodeW n (hB h))).2 hc

/-- The inspected positions stay within the domain, so the variant goes down. -/
private theorem minv_measure (H : Hyp depR ar Ls L t) {S Wk B : Finset (Config F)}
    {A : Finset (At F)} {log : Multiset Position} (I : MInv ar Ls L M t S Wk A log) (hB : B ⊆ Wk)
    (hne : B.Nonempty) :
    t.dom.card - (log + B.val.map (phi L)).card < t.dom.card - log.card := by
  have hbij := inspects_once H
  have hnode : ∀ n ∈ S ∪ B, NodeBy depR ar Ls L t n := by
    intro n hn
    rcases Finset.mem_union.1 hn with h | h
    · exact I.nodeS n h
    · exact I.nodeW n (hB h)
  have hle : (S ∪ B).card ≤ t.dom.card :=
    Finset.card_le_card_of_injOn (phi L) (fun n hn => hbij.mapsTo (hnode n hn))
      (fun _ h₁ _ h₂ e => hbij.injOn (hnode _ h₁) (hnode _ h₂) e)
  have hc : (S ∪ B).card = S.card + B.card := Finset.card_union_of_disjoint (minv_disjoint H I hB)
  have hpos := hne.card_pos
  have hlog : log.card = S.card := by rw [I.log, Multiset.card_map]; rfl
  have hadd : (log + B.val.map (phi L)).card = S.card + B.card := by
    rw [Multiset.card_add, hlog, Multiset.card_map]; rfl
  omega

private theorem minv_final (T : Tab ar Ls L M) (H : Hyp depR ar Ls L t) {S : Finset (Config F)}
    {A : Finset (At F)} {log : Multiset Position} (I : MInv ar Ls L M t S ∅ A log) :
    (A : Set (At F)) = {a | a.1 ∈ Ls ∧ a.2 ∈ t.dom ∧ a.1.Matches t a.2} ∧ log = t.dom.val := by
  have hall : ∀ n, NodeBy depR ar Ls L t n ↔ n ∈ S := by
    intro n
    refine ⟨fun hn => ?_, I.nodeS n⟩
    have hroot : ((initial Ls, []) : Config F) ∈ S := by simpa using I.root
    induction path_of_node hn with
    | refl => exact hroot
    | tail hp hc ih =>
      have hm := ih (path_node NodeBy.root hp)
      simpa using I.closed _ hm _ hc
  have hbij := inspects_once H
  constructor
  · rw [← correct_aux depR_admissible H.hL H.hne H.hLs t H.hc H.hw]
    ext a
    simp only [Finset.mem_coe, I.ann, outputBy, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, ha⟩
      have hnode := I.nodeS n hn
      obtain ⟨f, q, hf, he, ea⟩ := (mem_announced T hnode).1 ha
      exact ⟨n.1, n.2, f, q, hnode, hf, he, ea⟩
    · rintro ⟨s, p, f, q, hnode, hf, he, ea⟩
      exact ⟨(s, p), (hall _).1 hnode, (mem_announced T hnode).2 ⟨f, q, hf, he, ea⟩⟩
  · have himg : t.dom = S.image (phi L) := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · intro hx
        obtain ⟨n, hn, e⟩ := hbij.surjOn hx
        exact ⟨n, (hall n).1 hn, e⟩
      · rintro ⟨n, hn, rfl⟩
        exact hbij.mapsTo ((hall n).2 hn)
    rw [I.log, himg, Finset.image_val_of_injOn]
    exact fun _ h₁ _ h₂ e => hbij.injOn ((hall _).2 h₁) ((hall _).2 h₂) e

end Match

open Std.Do

private theorem eval_iff {σ : Type} (f : σ → ℕ) (s : σ) (m : ℕ) :
    (WhileVariant.eval (ps := PostShape.pure) (fun s : σ => (⟨f s⟩ : ULift ℕ)) s m).down ↔
      f s = m := by
  simp [WhileVariant.eval, SVal.evalsTo, eq_comm]

section Run

variable [Fintype F]

set_option linter.deprecated.syntax false in
private theorem construct_spec (hL : Admissible L) (hLs : ∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) :
    ∃ S δ η, construct ar Ls L = ⟨initial Ls, S, δ, η⟩ ∧ CInv ar Ls L S ∅ δ η := by
  have hfin := setAutomatonFinite ar Ls L hL hLs
  generalize h : construct ar Ls L = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => fun s => ⟨(hfin.toFinset \ s.1).card + s.2.1.card⟩
  | inv2 => ⇓ x => match x with
      | .inl s => ⌜CInv ar Ls L s.1 s.2.1 s.2.2.1 s.2.2.2⌝
      | .inr s => ⌜CInv ar Ls L s.1 s.2.1 s.2.2.1 s.2.2.2 ∧ s.2.1 = ∅⌝
  case vc1.step.isTrue b mb _ _ _ _ _ _ hne _ _ _ _ _ _ hi =>
    obtain ⟨hev, I⟩ := hi
    have hm := cinv_measure (R := hfin.toFinset) I (by simp) hne
    refine ⟨_, (eval_iff _ _ _).2 rfl, ?_, cinv_step I⟩
    rw [← (eval_iff _ b mb).1 hev]
    exact hm
  case vc2.step.isFalse hne hi => exact ⟨hi.2, not_not.1 hne⟩
  case vc3.pre => exact cinv_init
  case vc4.post.success r _ _ _ hi =>
    obtain ⟨I, he⟩ := hi
    exact ⟨r.1, r.2.2.1, r.2.2.2, rfl, he ▸ I⟩

set_option linter.deprecated.syntax false in
private theorem findMatches_spec {M : Automaton F} {t : Pat F}
    {pick : Finset (Config F) → Finset (Config F)} (T : Tab ar Ls L M) (H : Hyp depR ar Ls L t)
    (hp : ∀ W, W.Nonempty → (pick W).Nonempty ∧ pick W ⊆ W) :
    (((findMatches M L pick t).1 : Finset (At F)) : Set (At F)) =
        {a | a.1 ∈ Ls ∧ a.2 ∈ t.dom ∧ a.1.Matches t a.2} ∧
      (findMatches M L pick t).2 = t.dom.val := by
  generalize h : findMatches M L pick t = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => fun s => ⟨t.dom.card - s.2.2.card⟩
  | inv2 => ⇓ x => match x with
      | .inl s => ⌜∃ S, MInv ar Ls L M t S s.1 s.2.1 s.2.2⌝
      | .inr s => ⌜(∃ S, MInv ar Ls L M t S s.1 s.2.1 s.2.2) ∧ s.1 = ∅⌝
  case vc1.step.isTrue b mb _ _ _ _ hne _ _ _ _ hi =>
    obtain ⟨hev, S, I⟩ := hi
    have hn := hp _ (Finset.nonempty_iff_ne_empty.2 hne)
    refine ⟨_, (eval_iff _ _ _).2 rfl, ?_, _, minv_step T H I hn.2⟩
    rw [← (eval_iff _ b mb).1 hev]
    exact minv_measure H I hn.2 hn.1
  case vc2.step.isFalse hne hi => exact ⟨hi.2, not_not.1 hne⟩
  case vc3.pre => exact ⟨∅, by rw [T.init]; exact minv_init⟩
  case vc4.post.success hi =>
    obtain ⟨⟨S, I⟩, he⟩ := hi
    exact minv_final T H (he ▸ I)

private theorem constructCorrect_aux : ConstructCorrect ar Ls L := by
  intro hL hLs M
  obtain ⟨S, δ, η, h, I⟩ := construct_spec hL hLs
  have hM : M = ⟨initial Ls, S, δ, η⟩ := h
  clear_value M
  subst hM
  refine ⟨rfl, cinv_final I, fun s f s' p' => ?_, fun s f a => ?_⟩
  · change (s, f, s', p') ∈ δ ↔ _
    rw [I.hdelta, cinv_final I]
    simp
  · change (s, f, a) ∈ η ↔ _
    rw [I.heta, cinv_final I]
    simp

private theorem findMatchesCorrect_aux {pick : Finset (Config F) → Finset (Config F)} :
    FindMatchesCorrect ar Ls L pick := by
  intro hL hne hLs hp t hc hw
  have hC := constructCorrect_aux hL hLs
  exact findMatches_spec ⟨hC.1, hC.2.2.1, hC.2.2.2⟩ ⟨depR_admissible, hL, hne, hLs, hc, hw⟩ hp

end Run

end MercLib.SetAutomaton
