module

public import MercLib.Theory.ParityGame.Incomplete

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Lemmas 3 and 4 of [Laveaux2022]: inside the safe vertices, the safe control predecessor and the
safe attractor are the ordinary ones of the safe subgame. -/

namespace MercLib.ParityGame

variable {V : Type*}

private theorem opp_opp' (i : Player) : i.opp.opp = i := by cases i <;> rfl

private theorem opp_ne' (i : Player) : i.opp ≠ i := by cases i <;> simp [Player.opp]

namespace IncompleteGame

variable (G : IncompleteGame V)

/-- A vertex of `β` with a successor in the attractor of `β` is in it. -/
private theorem mem_attr_of_edge {β : Player} {T : Set V} {v w : V} (hv : v ∈ G.vs)
    (ho : G.owner v = β) (he : G.edge v w) (hw : w ∈ G.attr β T) : v ∈ G.attr β T := by
  obtain ⟨k, hk⟩ := hw
  exact ⟨k + 1, Or.inr (Or.inl ⟨⟨hv, ho⟩, hv, w, hk, he⟩)⟩

/-- The target is in the attractor. -/
private theorem subset_attr {β : Player} {T : Set V} : T ⊆ G.attr β T :=
  fun _ hv => ⟨1, Or.inl hv⟩

/-- A vertex of the opponent of `β` with a successor outside the attractor is not in it. -/
private theorem not_mem_attr_of_edge {β : Player} {T : Set V} {v w : V} (hT : v ∉ T)
    (ho : G.owner v ≠ β) (he : G.edge v w) (hw : w ∉ G.attr β T) : v ∉ G.attr β T := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => exact hk
  | succ k =>
    rcases hk with hk | ⟨⟨-, ho'⟩, -⟩ | ⟨-, hk⟩
    · exact hT hk
    · exact ho ho'
    · exact hk (Or.inl ⟨(G.edge_mem v w he).1, w,
        ⟨(G.edge_mem v w he).2, fun hwk => hw ⟨k, hwk⟩⟩, he⟩)

/-- A vertex of `β` outside the target whose successors avoid the attractor is not in it. -/
private theorem not_mem_attr_of_own {β : Player} {T : Set V} {v : V} (hT : v ∉ T)
    (ho : G.owner v = β) (hs : ∀ w, G.edge v w → w ∉ G.attr β T) : v ∉ G.attr β T := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => exact hk
  | succ k =>
    rcases hk with hk | ⟨-, -, w, hw, he⟩ | ⟨⟨-, ho'⟩, -⟩
    · exact hT hk
    · exact hs w he ⟨k, hw⟩
    · exact opp_ne' β (ho'.symm.trans ho)

variable (a : IncompleteGame V)

private theorem safeCpreEq_aux (α : Player) (X : Set V) (hX : X ⊆ a.safe α) :
    (a.restrict (a.safe α)).cpre α X = a.spre α X := by
  set T := a.attr α.opp (a.own α.opp ∩ a.I) with hT
  have hsafe : ∀ {v}, v ∈ a.safe α ↔ v ∈ a.vs ∧ v ∉ T := Iff.rfl
  ext v
  constructor
  · rintro (⟨⟨⟨hv, hvs⟩, ho⟩, -, w, hwX, he, -, -⟩ | ⟨⟨⟨hv, hvs⟩, ho⟩, hn⟩)
    · exact Or.inl ⟨⟨hv, ho⟩, hv, w, hwX, he⟩
    · refine Or.inr ⟨⟨hv, ho⟩, ?_⟩
      rintro ((⟨-, w, ⟨hw, hwX⟩, he⟩ | ⟨-, hsink⟩) | hI)
      · by_cases hws : w ∈ a.safe α
        · exact hn (Or.inl ⟨⟨hv, hvs⟩, w, ⟨⟨hw, hws⟩, hwX⟩, he, hvs, hws⟩)
        · have hwT : w ∈ T := by
            by_contra h; exact hws ⟨hw, h⟩
          exact (hsafe.1 hvs).2 (a.mem_attr_of_edge hv ho he hwT)
      · refine hn (Or.inr ⟨⟨hv, hvs⟩, fun w hw => ?_⟩)
        exact hsink w hw.1
      · exact (hsafe.1 hvs).2 (a.subset_attr ⟨⟨hv, ho⟩, hI⟩)
  · rintro (⟨⟨hv, ho⟩, -, w, hwX, he⟩ | ⟨⟨hv, ho⟩, hn⟩)
    · -- a vertex of `α` with a successor in `X ⊆ safe` is safe
      have hvs : v ∈ a.safe α := by
        refine ⟨hv, a.not_mem_attr_of_edge (fun h => ?_) ?_ he (hX hwX).2⟩
        · exact opp_ne' α (h.1.2.symm.trans ho)
        · intro h; exact opp_ne' α (h.symm.trans ho)
      exact Or.inl ⟨⟨⟨hv, hvs⟩, ho⟩, ⟨hv, hvs⟩, w, hwX, he, hvs, hX hwX⟩
    · have hsucc : ∀ w, a.edge v w → w ∈ X := by
        intro w he
        by_contra hw
        exact hn (Or.inl (Or.inl ⟨hv, w, ⟨(a.edge_mem v w he).2, hw⟩, he⟩))
      have hvs : v ∈ a.safe α := by
        refine ⟨hv, a.not_mem_attr_of_own (fun h => hn (Or.inr h.2)) ho fun w he => ?_⟩
        exact (hX (hsucc w he)).2
      refine Or.inr ⟨⟨⟨hv, hvs⟩, ho⟩, ?_⟩
      rintro (⟨-, w, ⟨-, hwX⟩, he, -⟩ | ⟨-, hsink⟩)
      · exact hwX (hsucc w he)
      · refine hn (Or.inl (Or.inr ⟨hv, fun w he => ?_⟩))
        exact hsink w ⟨he, hvs, hX (hsucc w he)⟩

private theorem safeAttrEq_aux (α : Player) (X : Set V) (hX : X ⊆ a.safe α) :
    (a.restrict (a.safe α)).attr α X = a.sattr α X := by
  have hstage : ∀ k, (a.restrict (a.safe α)).attrStage α X k = a.sattrStage α X k ∧
      a.sattrStage α X k ⊆ a.safe α := by
    intro k
    induction k with
    | zero => exact ⟨rfl, Set.empty_subset _⟩
    | succ k ih =>
      have e : (a.restrict (a.safe α)).attrStage α X (k + 1) = a.sattrStage α X (k + 1) := by
        show X ∪ _ = X ∪ _
        rw [ih.1, safeCpreEq_aux a α _ ih.2]
      refine ⟨e, ?_⟩
      rw [← e]
      rintro v (hv | (⟨⟨⟨-, hvs⟩, -⟩, -⟩ | ⟨⟨⟨-, hvs⟩, -⟩, -⟩))
      · exact hX hv
      · exact hvs
      · exact hvs
  ext v
  exact exists_congr fun k => by rw [(hstage k).1]

end IncompleteGame

/-- **Lemma 3 of [Laveaux2022].** -/
public theorem IncompleteGame.safeCpreEq (a : IncompleteGame V) : a.SafeCpreEq :=
  fun α X hX => a.safeCpreEq_aux α X hX

/-- **Lemma 4 of [Laveaux2022].** -/
public theorem IncompleteGame.safeAttrEq (a : IncompleteGame V) : a.SafeAttrEq :=
  fun α X hX => a.safeAttrEq_aux α X hX

end MercLib.ParityGame
