module

public import MercLib.Theory.Rewriting.SetAutomatonPartition
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonBase_Proofs
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonInv_Proofs
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonNode_Proofs
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The evaluation tree of a term: the work sets `W` and Lemma 3 of the paper, Corollary 4 (every
position is inspected exactly once) and Theorem 1 (correctness). -/

namespace MercLib.SetAutomaton

variable {F : Type} [DecidableEq F] {ar : F → ℕ} {Ls : Finset (Pat F)} {L : State F → Position}
  {t : Pat F}
  {R : Position → F → Goal F → Goal F → Prop} [∀ l f, DecidableRel (R l f)]

/-- The assumptions of the theorems. -/
private structure Hyp (R : Position → F → Goal F → Goal F → Prop) (ar : F → ℕ)
    (Ls : Finset (Pat F)) (L : State F → Position) (t : Pat F) : Prop where
  hR : PartitionAdmissible R
  hL : Admissible L
  hne : Ls.Nonempty
  hLs : ∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar
  hc : t.Closed
  hw : t.WF ar

private theorem node_inv (H : Hyp R ar Ls L t) : ∀ n, NodeBy R ar Ls L t n →
    ReachableBy R ar Ls L n.1 ∧ NInv t n.1 n.2 := by
  intro n h
  induction h with
  | root => exact ⟨.init, ninv_initial t⟩
  | step _ hf hd ih =>
    have I := inv_reachable H.hR H.hL H.hne H.hLs ih.1
    obtain ⟨g, hg, rfl, rfl⟩ := mem_delta.1 hd
    exact ⟨.step ih.1 (mem_delta.2 ⟨g, hg, rfl, rfl⟩),
      ninv_lift (H.hR.ok _ _) (ginv_deriv H.hLs I.toGInv (label_mem H.hL I))
        (ninv_deriv H.hLs H.hw I.toGInv ih.2 hf) hg⟩

/-- The positions that remain to be inspected below a node (Definition 3). -/
private def W (t : Pat F) (n : State F × Position) : Set Position :=
  {x | x ∈ t.dom ∧ ∃ g ∈ n.1, ∃ a ∈ g.1, ∃ y, x = n.2 ++ a.2 ++ y}

/-- A child in the evaluation tree. -/
private def Child (R : Position → F → Goal F → Goal F → Prop) [∀ l f, DecidableRel (R l f)]
    (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position) (t : Pat F)
    (n c : State F × Position) : Prop :=
  ∃ f s' p', headAt t (n.2 ++ L n.1) = some f ∧ (s', p') ∈ deltaBy R ar Ls n.1 (L n.1) f ∧
    c = (s', n.2 ++ p')

private theorem node_child {n c : State F × Position} (hn : NodeBy R ar Ls L t n)
    (hc : Child R ar Ls L t n c) : NodeBy R ar Ls L t c := by
  obtain ⟨f, s', p', hf, hd, rfl⟩ := hc
  exact NodeBy.step (s := n.1) (p := n.2) hn hf hd

/-- The facts available at a node. -/
private structure At' (R : Position → F → Goal F → Goal F → Prop) (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position) (t : Pat F)
    (n : State F × Position) (f : F) : Prop where
  I : Inv Ls n.1
  N : NInv t n.1 n.2
  lab : ∃ g ∈ n.1, ∃ a ∈ g.1, a.2 = L n.1
  hf : headAt t (n.2 ++ L n.1) = some f
  GX : GInv Ls (deriv ar Ls n.1 (L n.1) f)
  hQ : QOk (R (L n.1) f)

private theorem exists_head (H : Hyp R ar Ls L t) {n : State F × Position}
    (hn : NodeBy R ar Ls L t n) : ∃ f, At' R ar Ls L t n f := by
  obtain ⟨hr, N⟩ := node_inv H n hn
  have I := inv_reachable H.hR H.hL H.hne H.hLs hr
  have lab := label_mem H.hL I
  obtain ⟨g, hg, a, ha, e⟩ := lab
  have hin := N.inside g hg a ha
  rw [e] at hin
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hin
  have hcl := Pat.at_closed _ _ _ H.hc hu
  cases u with
  | omega => exact absurd hcl (by simp [Pat.Closed])
  | app f args =>
    have hf : headAt t (n.2 ++ L n.1) = some f := by simp [headAt, hu, Pat.hd]
    exact ⟨f, I, N, ⟨g, hg, a, ha, e⟩, hf, ginv_deriv H.hLs I.toGInv ⟨g, hg, a, ha, e⟩, H.hR.ok _ _⟩

private theorem child_spec {n c : State F × Position} {f : F} (A : At' R ar Ls L t n f)
    (hc : Child R ar Ls L t n c) : ∃ g ∈ deriv ar Ls n.1 (L n.1) f,
      c = (lift (classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) g),
        n.2 ++ gcpOf (classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) g)) := by
  obtain ⟨f', s', p', hf', hd, rfl⟩ := hc
  have : f' = f := Option.some.inj (hf'.symm.trans A.hf)
  subst this
  obtain ⟨g, hg, rfl, rfl⟩ := mem_delta.1 hd
  exact ⟨g, hg, rfl⟩

private theorem child_of_goal {n : State F × Position} {f : F} (A : At' R ar Ls L t n f)
    {G : Goal F} (hG : G ∈ deriv ar Ls n.1 (L n.1) f) :
    Child R ar Ls L t n (lift (classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) G),
      n.2 ++ gcpOf (classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) G)) :=
  ⟨f, _, _, A.hf, mem_delta.2 ⟨G, hG, rfl, rfl⟩, rfl⟩

private theorem lift_obl {K : State F} {g' : Goal F} {a' : At F} (hg : g' ∈ lift K)
    (ha : a' ∈ g'.1) : ∃ h ∈ K, ∃ a ∈ h.1, a' = (a.1, shorten (gcpOf K) a.2) := by
  obtain ⟨h, hh, rfl⟩ := mem_lift.1 hg
  obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
  exact ⟨h, hh, a, ha', rfl⟩

private theorem phi_mem_W {n : State F × Position} {f : F} (A : At' R ar Ls L t n f) :
    n.2 ++ L n.1 ∈ W t n := by
  obtain ⟨g, hg, a, ha, e⟩ := A.lab
  refine ⟨?_, g, hg, a, ha, [], by simp [e]⟩
  have := A.N.inside g hg a ha
  rw [e] at this
  exact (Pat.mem_dom_iff _ _).2 this

/-- Positions of a class, relative to a child. -/
private theorem class_pos {Q : Goal F → Goal F → Prop} [DecidableRel Q] (hQ : QOk Q) {X : State F}
    (GX : GInv Ls X) {g h : Goal F} (hg : g ∈ X)
    (hh : h ∈ classOfBy Q X g) {a : At F} (ha : a ∈ h.1) (p y : Position) :
    (p ++ gcpOf (classOfBy Q X g)) ++ shorten (gcpOf (classOfBy Q X g)) a.2 ++ y = p ++ a.2 ++ y := by
  rw [List.append_assoc p, shorten_app (class_prefix hQ GX hg hh ha)]

/-- **Lemma 3.1.** The inspected position is not left to a child. -/
private theorem phi_not_mem_child {n c : State F × Position} {f : F} (A : At' R ar Ls L t n f)
    (hc : Child R ar Ls L t n c) : n.2 ++ L n.1 ∉ W t c := by
  obtain ⟨g, hg, rfl⟩ := child_spec A hc
  rintro ⟨-, g', hg', a', ha', y, e⟩
  obtain ⟨h, hh, a, ha, rfl⟩ := lift_obl hg' ha'
  obtain ⟨g₁, hg₁, d, hd, hdl⟩ := A.lab
  have hsub := classOf_subset hg hh
  dsimp only at e
  rw [class_pos A.hQ A.GX hg hh ha, List.append_assoc] at e
  have e' : L n.1 = a.2 ++ y := List.append_cancel_left e
  rcases pos_deriv hsub ha with ⟨g₀, hs, ha₀, hne⟩ | ⟨i, -, -, ei⟩
  · apply hne
    refine (A.I.incomp g₀ hs g₁ hg₁ a ha₀ d hd ?_).trans hdl
    rw [hdl]; exact Or.inl ⟨y, e'.symm⟩
  · have := congrArg List.length e'
    simp [ei] at this

/-- **Lemma 3.2.** Distinct children have disjoint work sets. -/
private theorem children_disjoint {n c₁ c₂ : State F × Position} {f : F} (A : At' R ar Ls L t n f)
    (h₁ : Child R ar Ls L t n c₁) (h₂ : Child R ar Ls L t n c₂) (hne : c₁ ≠ c₂) {x : Position}
    (hx₁ : x ∈ W t c₁) (hx₂ : x ∈ W t c₂) : False := by
  obtain ⟨g₁, hg₁, rfl⟩ := child_spec A h₁
  obtain ⟨g₂, hg₂, rfl⟩ := child_spec A h₂
  obtain ⟨-, g₁', hg₁', a₁', ha₁', y₁, e₁⟩ := hx₁
  obtain ⟨-, g₂', hg₂', a₂', ha₂', y₂, e₂⟩ := hx₂
  obtain ⟨h₁', hh₁, a₁, ha₁, rfl⟩ := lift_obl hg₁' ha₁'
  obtain ⟨h₂', hh₂, a₂, ha₂, rfl⟩ := lift_obl hg₂' ha₂'
  dsimp only at e₁ e₂
  rw [class_pos A.hQ A.GX hg₁ hh₁ ha₁] at e₁
  rw [class_pos A.hQ A.GX hg₂ hh₂ ha₂] at e₂
  rw [List.append_assoc] at e₁ e₂
  have e : a₁.2 ++ y₁ = a₂.2 ++ y₂ := List.append_cancel_left (e₁.symm.trans e₂)
  have hX₁ := classOf_subset hg₁ hh₁
  have hX₂ := classOf_subset hg₂ hh₂
  have hcmp : a₁.2 <+: a₂.2 ∨ a₂.2 <+: a₁.2 := by
    have p₁ : a₁.2 <+: a₂.2 ++ y₂ := ⟨y₁, e⟩
    have p₂ : a₂.2 <+: a₂.2 ++ y₂ := List.prefix_append _ _
    rcases le_total a₁.2.length a₂.2.length with hl | hl
    · exact Or.inl (List.prefix_of_prefix_length_le p₁ p₂ hl)
    · exact Or.inr (List.prefix_of_prefix_length_le p₂ p₁ hl)
  have hpos := A.GX.incomp _ hX₁ _ hX₂ a₁ ha₁ a₂ ha₂ hcmp
  have hd : Depends h₁' h₂' :=
    ⟨a₁.2, Finset.mem_inter.2 ⟨mem_pos.2 ⟨a₁, ha₁, rfl⟩, mem_pos.2 ⟨a₂, ha₂, hpos.symm⟩⟩⟩
  have hin : h₂' ∈ classOfBy _ _ g₁ := classOf_closed hg₁ hh₁ hX₂ (A.hQ.dep _ _ hd)
  have ek : classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) g₁ = classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) g₂ := by
    rw [← classOf_eq_of_mem A.hQ.symm hg₁ hin, classOf_eq_of_mem A.hQ.symm hg₂ hh₂]
  exact hne (by rw [ek])

/-- **Lemma 3.3, inclusion.** A child's work is work of its parent. -/
private theorem W_child_subset {n c : State F × Position} {f : F} (A : At' R ar Ls L t n f)
    (hc : Child R ar Ls L t n c) : W t c ⊆ W t n := by
  obtain ⟨g, hg, rfl⟩ := child_spec A hc
  rintro x ⟨hx, g', hg', a', ha', y, rfl⟩
  obtain ⟨h, hh, a, ha, rfl⟩ := lift_obl hg' ha'
  dsimp only at hx ⊢
  rw [class_pos A.hQ A.GX hg hh ha] at hx ⊢
  refine ⟨hx, ?_⟩
  rcases pos_deriv (classOf_subset hg hh) ha with ⟨g₀, hs, ha₀, -⟩ | ⟨i, -, -, ei⟩
  · exact ⟨g₀, hs, a, ha₀, y, rfl⟩
  · obtain ⟨g₁, hg₁, d, hd, hdl⟩ := A.lab
    exact ⟨g₁, hg₁, d, hd, [i] ++ y, by simp [ei, hdl]⟩

/-- **Lemma 3.3, the rest.** Any other position of the work set is left to a child. -/
private theorem W_exists_child (H : Hyp R ar Ls L t) {n : State F × Position} {f : F}
    (A : At' R ar Ls L t n f) {x : Position} (hx : x ∈ W t n) (hne : x ≠ n.2 ++ L n.1) :
    ∃ c, Child R ar Ls L t n c ∧ x ∈ W t c := by
  obtain ⟨hd, g, hg, e, he, y, rfl⟩ := hx
  obtain ⟨p₀, hp₀⟩ := H.hne
  have hmem : ∀ {G : Goal F} (hG : G ∈ deriv ar Ls n.1 (L n.1) f) {a : At F}, a ∈ G.1 → ∀ z,
      n.2 ++ e.2 ++ y = n.2 ++ a.2 ++ z →
      ∃ c, Child R ar Ls L t n c ∧ n.2 ++ e.2 ++ y ∈ W t c := by
    intro G hG a ha z ez
    refine ⟨_, child_of_goal A hG, hd, _, mem_lift.2 ⟨G, self_mem_classOf _ _, rfl⟩, _,
      Finset.mem_image.2 ⟨a, ha, rfl⟩, z, ?_⟩
    dsimp only
    rw [class_pos A.hQ A.GX hG (self_mem_classOf _ _) ha]
    exact ez
  by_cases hel : e.2 = L n.1
  · cases y with
    | nil => exact absurd (by simp [hel]) hne
    | cons i y =>
      obtain ⟨args, hat, hlen⟩ := head_shape H.hw A.hf
      have hs := (Pat.mem_dom_iff _ _).1 (hel ▸ hd)
      rw [Pat.at_append, hat] at hs
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hs
      have hb : Pat.atArgs args i y = some u := by simpa [Pat.at] using hu
      obtain ⟨h1, h2⟩ := Pat.atArgs_bounds _ _ _ _ hb
      have hG : (({(p₀, L n.1 ++ [i])}, (p₀, L n.1 ++ [i])) : Goal F) ∈ deriv ar Ls n.1 (L n.1) f :=
        mem_deriv.2 (Or.inr (Or.inr ⟨p₀, hp₀, i, h1, by omega, rfl⟩))
      exact hmem hG (Finset.mem_singleton_self _) y (by simp [hel])
  · have hG : (({(p₀, e.2)}, (p₀, e.2)) : Goal F) ∈ deriv ar Ls n.1 (L n.1) f := by
      refine mem_deriv.2 (Or.inl ⟨A.I.fresh g hg e he p₀ hp₀, fun h => hel ?_⟩)
      obtain ⟨b, hb, eb⟩ := mem_pos.1 h
      rw [Finset.mem_singleton.1 hb] at eb
      exact eb
    exact hmem hG (Finset.mem_singleton_self _) y rfl

private theorem W_finite (n : State F × Position) : (W t n).Finite :=
  t.dom.finite_toSet.subset fun _ hx => hx.1

private theorem ncard_child_lt {n c : State F × Position} {f : F} (A : At' R ar Ls L t n f)
    (hc : Child R ar Ls L t n c) : (W t c).ncard < (W t n).ncard :=
  Set.ncard_lt_ncard
    ⟨W_child_subset A hc, fun h => phi_not_mem_child A hc (h (phi_mem_W A))⟩ (W_finite n)

private abbrev Path (R : Position → F → Goal F → Goal F → Prop) [∀ l f, DecidableRel (R l f)]
    (ar : F → ℕ) (Ls : Finset (Pat F)) (L : State F → Position) (t : Pat F) :=
  Relation.ReflTransGen (Child R ar Ls L t)

private theorem path_node {n m : State F × Position} (hn : NodeBy R ar Ls L t n)
    (p : Path R ar Ls L t n m) : NodeBy R ar Ls L t m := by
  induction p with
  | refl => exact hn
  | tail _ hc ih => exact node_child ih hc

private theorem path_W (H : Hyp R ar Ls L t) {n m : State F × Position} (hn : NodeBy R ar Ls L t n)
    (p : Path R ar Ls L t n m) : W t m ⊆ W t n := by
  induction p with
  | refl => exact subset_rfl
  | tail hp hc ih =>
    obtain ⟨f, A⟩ := exists_head H (path_node hn hp)
    exact (W_child_subset A hc).trans ih

private theorem phi_in_W (H : Hyp R ar Ls L t) {n m : State F × Position} (hn : NodeBy R ar Ls L t n)
    (p : Path R ar Ls L t n m) : m.2 ++ L m.1 ∈ W t n := by
  obtain ⟨f, A⟩ := exists_head H (path_node hn p)
  exact path_W H hn p (phi_mem_W A)

/-- Below a node, `φ` is injective. -/
private theorem phi_injective (H : Hyp R ar Ls L t) : ∀ (k : ℕ) (n : State F × Position),
    (W t n).ncard ≤ k → NodeBy R ar Ls L t n → ∀ m₁ m₂, Path R ar Ls L t n m₁ → Path R ar Ls L t n m₂ →
      m₁.2 ++ L m₁.1 = m₂.2 ++ L m₂.1 → m₁ = m₂ := by
  intro k
  induction k with
  | zero =>
    intro n hk hn
    obtain ⟨f, A⟩ := exists_head H hn
    have := Set.ncard_pos (W_finite n) |>.2 ⟨_, phi_mem_W A⟩
    omega
  | succ k ih =>
    intro n hk hn m₁ m₂ p₁ p₂ e
    obtain ⟨f, A⟩ := exists_head H hn
    rcases Relation.ReflTransGen.cases_head p₁ with rfl | ⟨c₁, hc₁, p₁'⟩ <;>
      rcases Relation.ReflTransGen.cases_head p₂ with rfl | ⟨c₂, hc₂, p₂'⟩
    · rfl
    · have hc₂n := node_child hn hc₂
      exact absurd (e ▸ phi_in_W H hc₂n p₂') (phi_not_mem_child A hc₂)
    · have hc₁n := node_child hn hc₁
      exact absurd (e ▸ phi_in_W H hc₁n p₁') (phi_not_mem_child A hc₁)
    · have hc₁n := node_child hn hc₁
      have hc₂n := node_child hn hc₂
      by_cases hcc : c₁ = c₂
      · subst hcc
        exact ih c₁ (by have := ncard_child_lt A hc₁; omega) hc₁n _ _ p₁' p₂' e
      · exact (children_disjoint A hc₁ hc₂ hcc (phi_in_W H hc₁n p₁')
          (e ▸ phi_in_W H hc₂n p₂' : _ ∈ W t c₂)).elim

/-- Every position of the work set is inspected somewhere below the node. -/
private theorem phi_surjective (H : Hyp R ar Ls L t) : ∀ (k : ℕ) (n : State F × Position),
    (W t n).ncard ≤ k → NodeBy R ar Ls L t n → ∀ x ∈ W t n,
      ∃ m, Path R ar Ls L t n m ∧ m.2 ++ L m.1 = x := by
  intro k
  induction k with
  | zero =>
    intro n hk hn
    obtain ⟨f, A⟩ := exists_head H hn
    have := Set.ncard_pos (W_finite n) |>.2 ⟨_, phi_mem_W A⟩
    omega
  | succ k ih =>
    intro n hk hn x hx
    obtain ⟨f, A⟩ := exists_head H hn
    by_cases he : x = n.2 ++ L n.1
    · exact ⟨n, .refl, he.symm⟩
    · obtain ⟨c, hc, hxc⟩ := W_exists_child H A hx he
      obtain ⟨m, p, em⟩ := ih c (by have := ncard_child_lt A hc; omega) (node_child hn hc) x hxc
      exact ⟨m, Relation.ReflTransGen.head hc p, em⟩

private theorem path_of_node {m : State F × Position} (h : NodeBy R ar Ls L t m) :
    Path R ar Ls L t (initial Ls, []) m := by
  induction h with
  | root => exact .refl
  | step _ hf hd ih => exact ih.tail ⟨_, _, _, hf, hd, rfl⟩

private theorem mem_W_root (H : Hyp R ar Ls L t) {x : Position} (hx : x ∈ t.dom) :
    x ∈ W t (initial Ls, []) := by
  obtain ⟨p, hp⟩ := H.hne
  exact ⟨hx, _, Finset.mem_image.2 ⟨p, hp, rfl⟩, _, Finset.mem_singleton_self _, x, by simp⟩

private theorem inspects_once (H : Hyp R ar Ls L t) :
    Set.BijOn (fun n : State F × Position => n.2 ++ L n.1)
      {n | NodeBy R ar Ls L t n} {p | p ∈ t.dom} := by
  refine ⟨fun n hn => ?_, fun m₁ h₁ m₂ h₂ e => ?_, fun x hx => ?_⟩
  · obtain ⟨f, A⟩ := exists_head H hn
    exact (phi_mem_W A).1
  · exact phi_injective H _ _ le_rfl NodeBy.root _ _ (path_of_node h₁) (path_of_node h₂) e
  · obtain ⟨m, p, e⟩ := phi_surjective H _ _ le_rfl NodeBy.root x (mem_W_root H hx)
    exact ⟨m, path_node NodeBy.root p, e⟩

/-! ### Correctness -/

private theorem mem_eta {s : State F} {l : Position} {f : F} {b : At F} :
    b ∈ eta ar s l f ↔ ∃ g ∈ s, g.1 = {(shallow ar f, l)} ∧ g.2 = b := by
  simp [eta]

private theorem output_sound (H : Hyp R ar Ls L t) {a : At F} (ha : a ∈ outputBy R ar Ls L t) :
    a.1 ∈ Ls ∧ a.2 ∈ t.dom ∧ a.1.Matches t a.2 := by
  obtain ⟨s, p, f, q, hn, hf, he, hq⟩ := ha
  obtain ⟨g, hg, e1, e2⟩ := mem_eta.1 he
  obtain ⟨hr, N⟩ := node_inv H _ hn
  have I := inv_reachable H.hR H.hL H.hne H.hLs hr
  obtain ⟨-, hLm, goalsa⟩ := I.goals g hg
  have e21 : g.2.1 = a.1 := by rw [e2]
  have e22 : g.2.2 = q := by rw [e2]
  have ha0 : ((shallow ar f, L s) : At F) ∈ g.1 := by rw [e1]; exact Finset.mem_singleton_self _
  obtain ⟨rL, eL, hatL, -⟩ := goalsa _ ha0
  simp only [e22] at eL
  refine ⟨e21 ▸ hLm, ?_, ?_⟩
  · have hin := N.inside g hg _ ha0
    simp only at hin
    rw [eL, ← List.append_assoc, Pat.at_append] at hin
    apply (Pat.mem_dom_iff _ _).2
    rw [hq]
    cases hx : t.at (p ++ q) with
    | none => simp [hx] at hin
    | some _ => simp
  · intro p' _ l' hat hne
    have hat' : g.2.1.at p' = some l' := e21 ▸ hat
    rcases N.sound g hg p' l' hat' hne with ⟨a1, ha1, hpre⟩ | hchk
    · rw [e1, Finset.mem_singleton] at ha1
      subst ha1
      rw [e22] at hpre
      dsimp only at hpre
      rw [eL] at hpre
      obtain ⟨x, rfl⟩ := (List.prefix_append_right_inj _).1 hpre
      rw [Pat.at_append, hatL] at hat'
      replace hat' : (shallow ar f).at x = some l' := hat'
      cases x with
      | nil =>
        simp only [Pat.at, Option.some.injEq] at hat'
        rw [hq, List.append_nil, List.append_assoc, ← eL, ← hat']
        exact hf.trans (by simp [shallow, Pat.hd])
      | cons i x =>
        exact absurd (Pat.atArgs_replicate _ _ _ _ (by simpa [shallow, Pat.at] using hat')) hne
    · rw [e22] at hchk
      rw [hq, List.append_assoc]
      exact hchk

/-- Lemma 5, iterated: a goal whose pattern matches is eventually announced. -/
private theorem announced (H : Hyp R ar Ls L t) : ∀ (k : ℕ) (n : State F × Position) (g : Goal F),
    (W t n).ncard ≤ k → NodeBy R ar Ls L t n → g ∈ n.1 → g.2.1.Matches t (n.2 ++ g.2.2) →
      ((g.2.1, n.2 ++ g.2.2) : At F) ∈ outputBy R ar Ls L t := by
  intro k
  induction k with
  | zero =>
    intro n g hk hn
    obtain ⟨f, A⟩ := exists_head H hn
    have := Set.ncard_pos (W_finite n) |>.2 ⟨_, phi_mem_W A⟩
    omega
  | succ k ih =>
    intro n g hk hn hg hm
    obtain ⟨f, A⟩ := exists_head H hn
    -- descend through a goal of the derivative that keeps the announcement of `g`
    have descend : ∀ h ∈ deriv ar Ls n.1 (L n.1) f, h.2 = g.2 →
        ((g.2.1, n.2 ++ g.2.2) : At F) ∈ outputBy R ar Ls L t := by
      intro h hh e
      have hc := child_of_goal A hh
      have hcm := node_child hn hc
      have hma : gcpOf (classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) h) <+: h.2.2 :=
        (A.hQ.gcp A.GX hh).2 h (self_mem_classOf _ _)
      have hlt := ncard_child_lt A hc
      have hpos : ((n.2 ++ gcpOf (classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) h)) ++
          shorten (gcpOf (classOfBy (R (L n.1) f) (deriv ar Ls n.1 (L n.1) f) h)) h.2.2) = n.2 ++ g.2.2 := by
        rw [List.append_assoc, shorten_app hma, e]
      have := ih _ (h.1.image fun a => (a.1, shorten (gcpOf (classOfBy _ _ h)) a.2),
          (h.2.1, shorten (gcpOf (classOfBy _ _ h)) h.2.2)) (by omega) hcm
        (mem_lift.2 ⟨h, self_mem_classOf _ _, rfl⟩)
        (by dsimp only; rw [hpos, e]; exact hm)
      dsimp only at this
      rw [hpos, e] at this
      exact this
    by_cases hl : L n.1 ∈ pos g.1
    swap
    · exact descend g (mem_deriv.2 (Or.inl ⟨hg, hl⟩)) rfl
    obtain ⟨b, hb, hbl⟩ := mem_pos.1 hl
    obtain ⟨-, hLm, hgoals⟩ := A.I.goals g hg
    obtain ⟨rb, eb, hatb, hbne⟩ := hgoals b hb
    have hhd : b.1.hd = some f := by
      have := hm rb ((Pat.mem_dom_iff _ _).2 (by simp [hatb])) b.1 hatb hbne
      rw [List.append_assoc, ← eb, hbl] at this
      exact this.symm.trans A.hf
    have hbw : b.1.WF ar := Pat.at_wf _ _ _ (H.hLs _ hLm).2 hatb
    by_cases hemp : reduce ar g.1 f (L n.1) = ∅
    · -- the last obligation: `g` is announced here
      have hall : ∀ a ∈ g.1, a = b := by
        intro a ha
        have hal : a.2 = L n.1 := by
          by_contra hne
          have : a ∈ reduce ar g.1 f (L n.1) := mem_reduce.2 (Or.inl ⟨ha, hne⟩)
          rw [hemp] at this; simp at this
        obtain ⟨ra, ea, hata, -⟩ := hgoals a ha
        have hrr : ra = rb := List.append_cancel_left (by rw [← ea, ← eb, hal, hbl])
        subst hrr
        have h1 : a.1 = b.1 := by rw [hata] at hatb; exact Option.some.inj hatb
        exact Prod.ext h1 (hal.trans hbl.symm)
      obtain ⟨args, hba, hlen⟩ := Pat.shape hbw hhd
      have hargs : args = List.replicate (ar f) .omega := by
        refine List.eq_replicate_iff.2 ⟨hlen, fun x hx => ?_⟩
        by_contra hxne
        obtain ⟨i, h1, h2, e⟩ := Pat.mem_atArgs args x hx
        have : ((x, L n.1 ++ [i]) : At F) ∈ reduce ar g.1 f (L n.1) :=
          mem_reduce.2 (Or.inr ⟨b, hb, hbl, i, h1, by omega, x, by
            rw [argAt, hba]; simpa [Pat.at] using e, hxne, rfl⟩)
        rw [hemp] at this; simp at this
      have hbs : b = (shallow ar f, L n.1) := Prod.ext (by rw [hba, hargs]; rfl) hbl
      have hg1 : g.1 = {(shallow ar f, L n.1)} := by
        ext a
        simp only [Finset.mem_singleton]
        exact ⟨fun ha => (hall a ha).trans hbs, fun e => by rw [e, ← hbs]; exact hb⟩
      exact ⟨n.1, n.2, f, g.2.2, hn, A.hf, mem_eta.2 ⟨g, hg, hg1, rfl⟩, rfl⟩
    · exact descend (reduce ar g.1 f (L n.1), g.2)
        (mem_deriv.2 (Or.inr (Or.inl ⟨g, hg, ⟨b, hb, hbl, hhd⟩, rfl, hemp⟩))) rfl

private theorem output_complete (H : Hyp R ar Ls L t) {a : At F} (hl : a.1 ∈ Ls) (hx : a.2 ∈ t.dom)
    (hm : a.1.Matches t a.2) : a ∈ outputBy R ar Ls L t := by
  obtain ⟨m, p, e⟩ := phi_surjective H _ _ le_rfl NodeBy.root a.2 (mem_W_root H hx)
  have hn := path_node NodeBy.root p
  obtain ⟨f, A⟩ := exists_head H hn
  obtain ⟨g, hg, d, hd, hdl⟩ := A.lab
  have hG := A.I.fresh g hg d hd a.1 hl
  have := announced H _ m _ le_rfl hn hG (by dsimp only; rw [hdl, e]; exact hm)
  dsimp only at this
  rw [hdl, e] at this
  exact this

private theorem correct_aux (hR : PartitionAdmissible R) {L : State F → Position} :
    CorrectBy R ar Ls L := by
  intro hL hne hLs t hc hw
  have H : Hyp R ar Ls L t := ⟨hR, hL, hne, hLs, hc, hw⟩
  ext a
  exact ⟨output_sound H, fun ⟨h1, h2, h3⟩ => output_complete H h1 h2 h3⟩

private theorem inspectsOnce_aux (hR : PartitionAdmissible R) {L : State F → Position} :
    InspectsOnceBy R ar Ls L := by
  intro hL hne hLs t hc hw
  exact inspects_once ⟨hR, hL, hne, hLs, hc, hw⟩

/-! ### Finitely many states -/

private theorem finite_aux [Finite F] (hR : PartitionAdmissible R) {L : State F → Position} :
    FinitelyManyStatesBy R ar Ls L := by
  classical
  intro hL hLs
  by_cases hne : Ls.Nonempty
  swap
  · have hemp : Ls = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    refine (Set.finite_singleton (initial Ls)).subset fun s hs => ?_
    induction hs with
    | init => rfl
    | step _ hd ih =>
      obtain ⟨g, hg, -, -⟩ := mem_delta.1 hd
      subst hemp
      rw [Set.mem_singleton_iff] at ih
      subst ih
      rcases mem_deriv.1 hg with ⟨h, -⟩ | ⟨g₀, h, -⟩ | ⟨p, h, -⟩
      · simp [initial] at h
      · simp [initial] at h
      · simp at h
  obtain ⟨N, hN⟩ := (Set.finite_range ar).bddAbove
  have hN' : ∀ f, ar f ≤ N := fun f => hN ⟨f, rfl⟩
  let D : Finset Position := Ls.biUnion Pat.dom
  let U₀ : Finset Position := D ∪ D.biUnion fun q => (Finset.range N).image fun i => q ++ [i + 1]
  let Rs : Set Position := {x | ∃ u ∈ U₀, x <:+: u}
  have hRfin : Rs.Finite := by
    refine (U₀.biUnion fun u => u.sublists.toFinset).finite_toSet.subset ?_
    rintro x ⟨u, hu, hx⟩
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨u, hu, List.mem_toFinset.2
      (List.mem_sublists.2 hx.sublist)⟩)
  let Subs : Set (Pat F) := {u | ∃ l ∈ Ls, ∃ r, l.at r = some u}
  have hSfin : Subs.Finite := by
    have h0 : ((Ls.biUnion fun l => l.dom.image fun r => l.at r : Finset (Option (Pat F))) :
        Set (Option (Pat F))).Finite := Finset.finite_toSet _
    refine (h0.preimage (f := some) (Option.some_injective _).injOn).subset ?_
    rintro u ⟨l, hl, r, hr⟩
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_image.2
      ⟨r, (Pat.mem_dom_iff _ _).2 (by simp [hr]), hr⟩⟩)
  have hInv : ∀ s, ReachableBy R ar Ls L s → ∀ g ∈ s, ∀ a ∈ g.1, a.2 ∈ Rs := by
    intro s hs
    induction hs with
    | init =>
      intro g hg a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
      rw [Finset.mem_singleton.1 ha]
      refine ⟨[], Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨p, hp, ?_⟩), List.infix_refl _⟩
      exact (Pat.mem_dom_iff _ _).2 (by simp [Pat.at])
    | @step s s' f p' hr hd ih =>
      intro g hg a ha
      have I := inv_reachable hR hL hne hLs hr
      obtain ⟨g₀, hg₀, rfl, -⟩ := mem_delta.1 hd
      obtain ⟨h, hh, b, hb, rfl⟩ := lift_obl hg ha
      have hbR : b.2 ∈ Rs := by
        rcases pos_deriv (classOf_subset hg₀ hh) hb with ⟨g₁, hs, hb', -⟩ | ⟨i, h1, h2, ei⟩
        · exact ih g₁ hs b hb'
        · obtain ⟨gr, hgr, hroot, hp⟩ := hL s I.root
          obtain ⟨c, hc, ec⟩ := mem_pos.1 hp
          obtain ⟨-, hLm, hgoals⟩ := I.goals gr hgr
          obtain ⟨r, er, hat, -⟩ := hgoals c hc
          have hrD : L s ∈ D := by
            refine Finset.mem_biUnion.2 ⟨gr.2.1, hLm, ?_⟩
            have : L s = r := by rw [← ec, er, hroot]; rfl
            rw [this]
            exact (Pat.mem_dom_iff _ _).2 (by simp [hat])
          have hmem : L s ++ [i] ∈ U₀ := by
            refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hrD, Finset.mem_image.2
              ⟨i - 1, Finset.mem_range.2 ?_, ?_⟩⟩)
            · have := hN' f; omega
            · have : i - 1 + 1 = i := by omega
              rw [this]
          exact ⟨_, hmem, ei ▸ List.infix_refl _⟩
      obtain ⟨u, hu, hi⟩ := hbR
      exact ⟨u, hu, (List.drop_suffix _ _).isInfix.trans hi⟩
  let A : Finset (At F) := hSfin.toFinset ×ˢ hRfin.toFinset
  let B : Finset (At F) := Ls ×ˢ hRfin.toFinset
  let U : Finset (Goal F) := A.powerset ×ˢ B
  refine (Finset.finite_toSet U.powerset).subset fun s hs => ?_
  have I := inv_reachable hR hL hne hLs hs
  refine Finset.mem_coe.2 (Finset.mem_powerset.2 fun g hg => ?_)
  obtain ⟨hgne, hLm, hgoals⟩ := I.goals g hg
  refine Finset.mem_product.2 ⟨Finset.mem_powerset.2 fun a ha => ?_, Finset.mem_product.2
    ⟨hLm, ?_⟩⟩
  · obtain ⟨r, -, hat, -⟩ := hgoals a ha
    exact Finset.mem_product.2 ⟨hSfin.mem_toFinset.2 ⟨_, hLm, r, hat⟩,
      hRfin.mem_toFinset.2 (hInv s hs g hg a ha)⟩
  · obtain ⟨a, ha⟩ := hgne
    obtain ⟨r, e, -, -⟩ := hgoals a ha
    obtain ⟨u, hu, hi⟩ := hInv s hs g hg a ha
    refine hRfin.mem_toFinset.2 ⟨u, hu, (List.IsPrefix.isInfix ?_).trans hi⟩
    exact e ▸ List.prefix_append _ _

/-! ### The partition of the paper and merc's partition -/

/-- The relation of the paper: dependency (Definition 7). -/
private abbrev depR : Position → F → Goal F → Goal F → Prop := fun _ _ => Depends

private theorem depR_admissible : PartitionAdmissible (depR (F := F)) :=
  fun _ _ _ _ => ⟨depends_symm, id, Or.inl⟩

private theorem delta_eq : delta ar Ls = deltaBy depR ar Ls := rfl

private theorem reachable_iff {s : State F} : Reachable ar Ls L s ↔ ReachableBy depR ar Ls L s := by
  constructor
  · intro h
    induction h with
    | init => exact .init
    | step _ hd ih => exact .step ih hd
  · intro h
    induction h with
    | init => exact .init
    | step _ hd ih => exact .step ih hd

private theorem node_iff {n : State F × Position} : Node ar Ls L t n ↔ NodeBy depR ar Ls L t n := by
  constructor
  · intro h
    induction h with
    | root => exact .root
    | step _ hf hd ih => exact .step ih hf hd
  · intro h
    induction h with
    | root => exact .root
    | step _ hf hd ih => exact .step ih hf hd

private theorem output_eq : output ar Ls L t = outputBy depR ar Ls L t := by
  ext a
  simp only [output, outputBy, Set.mem_ofPred_eq, node_iff]

private theorem comparable_symm {p q : Position} (h : Comparable p q) : Comparable q p := h.symm

private theorem merc_admissible : PartitionAdmissible (MercDepends ar Ls) := by
  intro l f g h
  refine ⟨?_, Or.inl, ?_⟩
  · rintro (d | ⟨hg, hh, hc⟩)
    · exact Or.inl (depends_symm d)
    · exact Or.inr ⟨hh, hg, comparable_symm hc⟩
  · rintro (d | ⟨-, -, hc⟩)
    · exact Or.inl d
    · exact Or.inr hc

end MercLib.SetAutomaton
