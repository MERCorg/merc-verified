module

public import MercLib.Theory.Rewriting.SetAutomatonPartition
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonBase_Proofs
import all MercLib.Theory.Rewriting.Proofs.SetAutomatonInv_Proofs

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

The invariant of a node of the evaluation tree: the obligations lie inside the term, and every
position of a pattern is either still pending in the obligations or has been checked against the
term (the paper's "history respects `t`", Definition 5 and Lemma 4). -/

namespace MercLib.SetAutomaton

variable {F : Type} [DecidableEq F] {ar : F → ℕ} {Ls : Finset (Pat F)}

namespace Pat

section
omit [DecidableEq F]
mutual

private theorem at_wf : ∀ (t : Pat F) (r : Position) (u : Pat F), t.WF ar → t.at r = some u → u.WF ar
  | _, [], u, h, e => by simp only [Pat.at, Option.some.injEq] at e; exact e ▸ h
  | .omega, _ :: _, _, _, e => by simp [Pat.at] at e
  | .app _ args, i :: r, u, h, e => atArgs_wf args i r u h.2 (by simpa [Pat.at] using e)

private theorem atArgs_wf : ∀ (ts : List (Pat F)) (i : ℕ) (r : Position) (u : Pat F), WFArgs ar ts →
    atArgs ts i r = some u → u.WF ar
  | [], _, _, _, _, e => by simp [atArgs] at e
  | _ :: _, 0, _, _, _, e => by simp [atArgs] at e
  | t :: _, 1, r, u, h, e => at_wf t r u h.1 (by simpa [atArgs] using e)
  | _ :: ts, i + 2, r, u, h, e => atArgs_wf ts (i + 1) r u h.2 (by simpa [atArgs] using e)

end
end

section
omit [DecidableEq F]
mutual

private theorem at_closed : ∀ (t : Pat F) (r : Position) (u : Pat F), t.Closed → t.at r = some u →
    u.Closed
  | _, [], u, h, e => by simp only [Pat.at, Option.some.injEq] at e; exact e ▸ h
  | .omega, _ :: _, _, _, e => by simp [Pat.at] at e
  | .app _ args, i :: r, u, h, e => atArgs_closed args i r u h (by simpa [Pat.at] using e)

private theorem atArgs_closed : ∀ (ts : List (Pat F)) (i : ℕ) (r : Position) (u : Pat F),
    ClosedArgs ts → atArgs ts i r = some u → u.Closed
  | [], _, _, _, _, e => by simp [atArgs] at e
  | _ :: _, 0, _, _, _, e => by simp [atArgs] at e
  | t :: _, 1, r, u, h, e => at_closed t r u h.1 (by simpa [atArgs] using e)
  | _ :: ts, i + 2, r, u, h, e => atArgs_closed ts (i + 1) r u h.2 (by simpa [atArgs] using e)

end
end

omit [DecidableEq F] in
private theorem atArgs_bounds : ∀ (ts : List (Pat F)) (i : ℕ) (r : Position) (u : Pat F),
    atArgs ts i r = some u → 1 ≤ i ∧ i ≤ ts.length
  | [], _, _, _, e => by simp [atArgs] at e
  | _ :: _, 0, _, _, e => by simp [atArgs] at e
  | _ :: _, 1, _, _, _ => by simp
  | _ :: ts, i + 2, r, u, e => by
    have := atArgs_bounds ts (i + 1) r u (by simpa [atArgs] using e)
    simp only [List.length_cons]; omega

omit [DecidableEq F] in
private theorem atArgs_isSome : ∀ (ts : List (Pat F)) (i : ℕ), 1 ≤ i → i ≤ ts.length →
    (atArgs ts i []).isSome
  | [], _, _, h => by simp at h; omega
  | _ :: _, 0, h, _ => by omega
  | _ :: _, 1, _, _ => by simp [atArgs, Pat.at]
  | _ :: ts, i + 2, _, h => by
    simpa [atArgs] using atArgs_isSome ts (i + 1) (by omega) (by simpa using h)

omit [DecidableEq F] in
private theorem mem_atArgs : ∀ (ts : List (Pat F)) (x : Pat F), x ∈ ts →
    ∃ i, 1 ≤ i ∧ i ≤ ts.length ∧ atArgs ts i [] = some x
  | t :: ts, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨1, by omega, by simp, by simp [atArgs, Pat.at]⟩
    · obtain ⟨i, h1, h2, e⟩ := mem_atArgs ts x h
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact ⟨j + 2, by omega, by simp at *; omega, by simpa [atArgs] using e⟩

omit [DecidableEq F] in
private theorem atArgs_replicate : ∀ (n i : ℕ) (x : Position) (l : Pat F),
    atArgs (List.replicate n (Pat.omega : Pat F)) i x = some l → l = .omega
  | 0, _, _, _, e => by simp [atArgs] at e
  | _ + 1, 0, _, _, e => by simp [List.replicate_succ, atArgs] at e
  | _ + 1, 1, x, l, e => by
    simp only [List.replicate_succ, atArgs] at e
    cases x with
    | nil => simp only [Pat.at, Option.some.injEq] at e; exact e.symm
    | cons _ _ => simp [Pat.at] at e
  | n + 1, i + 2, x, l, e => by
    simp only [List.replicate_succ, atArgs] at e
    exact atArgs_replicate n (i + 1) x l e

omit [DecidableEq F] in
/-- The shape of a well-formed pattern with head `f`. -/
private theorem shape {u : Pat F} {f : F} (hu : u.WF ar) (hd : u.hd = some f) :
    ∃ args, u = .app f args ∧ args.length = ar f := by
  cases u with
  | omega => simp [Pat.hd] at hd
  | app g args =>
    simp only [Pat.hd, Option.some.injEq] at hd
    subst hd
    exact ⟨args, rfl, hu.1⟩

end Pat

/-- The invariant of a node `(s, p)`. -/
private structure NInv (t : Pat F) (s : State F) (p : Position) : Prop where
  inside : ∀ g ∈ s, ∀ a ∈ g.1, (t.at (p ++ a.2)).isSome
  sound : ∀ g ∈ s, ∀ r l', g.2.1.at r = some l' → l' ≠ .omega →
    (∃ a ∈ g.1, a.2 <+: g.2.2 ++ r) ∨ headAt t (p ++ (g.2.2 ++ r)) = l'.hd

omit [DecidableEq F] in
/-- The term below a position with head `f`. -/
private theorem head_shape {t : Pat F} (hw : t.WF ar) {x : Position} {f : F}
    (hf : headAt t x = some f) : ∃ args, t.at x = some (.app f args) ∧ args.length = ar f := by
  unfold headAt at hf
  obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨args, rfl, hl⟩ := Pat.shape (Pat.at_wf t x u hw hu) hd
  exact ⟨args, hu, hl⟩

omit [DecidableEq F] in
private theorem child_inside {t : Pat F} (hw : t.WF ar) {x : Position} {f : F}
    (hf : headAt t x = some f) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ ar f) : (t.at (x ++ [i])).isSome := by
  obtain ⟨args, hu, hl⟩ := head_shape hw hf
  rw [Pat.at_append, hu]
  simpa [Pat.at] using Pat.atArgs_isSome args i h1 (by omega)

private theorem ninv_initial (t : Pat F) : NInv t (initial Ls) [] := by
  have hmem : ∀ g, g ∈ initial Ls → ∃ p ∈ Ls, g = ({(p, [])}, (p, [])) := fun g hg => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg; exact ⟨p, hp, rfl⟩
  refine ⟨?_, ?_⟩
  · intro g hg a ha
    obtain ⟨p, -, rfl⟩ := hmem g hg
    rw [Finset.mem_singleton.1 ha]
    simp [Pat.at]
  · intro g hg r l' _ _
    obtain ⟨p, -, rfl⟩ := hmem g hg
    exact Or.inl ⟨_, Finset.mem_singleton_self _, by simp⟩

private theorem ninv_deriv {t : Pat F} {s : State F} {p l : Position} {f : F}
    (hLs : ∀ l ∈ Ls, l ≠ .omega ∧ l.WF ar) (hw : t.WF ar) (I : GInv Ls s) (N : NInv t s p)
    (hf : headAt t (p ++ l) = some f) : NInv t (deriv ar Ls s l f) p := by
  have hchild : ∀ i, 1 ≤ i → i ≤ ar f → (t.at (p ++ (l ++ [i]))).isSome := fun i h1 h2 => by
    rw [← List.append_assoc]; exact child_inside hw hf h1 h2
  refine ⟨?_, ?_⟩
  · intro g hg a ha
    rcases pos_deriv hg ha with ⟨g₀, hs, ha', -⟩ | ⟨i, h1, h2, e⟩
    · exact N.inside g₀ hs a ha'
    · rw [e]; exact hchild i h1 h2
  · intro g hg r l' hat hne
    rcases mem_deriv.1 hg with ⟨hs, -⟩ | ⟨g₀, hs, ⟨b, hb, hbl, hbf⟩, rfl, -⟩ | ⟨q, -, i, -, -, rfl⟩
    · exact N.sound g hs r l' hat hne
    · rcases N.sound g₀ hs r l' hat hne with ⟨a, ha, hp⟩ | hchk
      swap
      · exact Or.inr hchk
      by_cases hal : a.2 = l
      swap
      · exact Or.inl ⟨a, mem_reduce.2 (Or.inl ⟨ha, hal⟩), hp⟩
      obtain ⟨-, hLm, hgoals⟩ := I.goals g₀ hs
      obtain ⟨ra, ea, hata, -⟩ := hgoals a ha
      obtain ⟨rb, eb, hatb, -⟩ := hgoals b hb
      have hrr : ra = rb := by
        have : g₀.2.2 ++ ra = g₀.2.2 ++ rb := by rw [← ea, ← eb, hal, hbl]
        exact List.append_cancel_left this
      subst hrr
      have hab : a.1 = b.1 := by
        rw [hata] at hatb; exact Option.some.inj hatb
      rw [ea] at hp
      obtain ⟨x, rfl⟩ := (List.prefix_append_right_inj _).1 hp
      rw [Pat.at_append, hata] at hat
      replace hat : a.1.at x = some l' := hat
      have hel : g₀.2.2 ++ ra = l := by rw [← ea, hal]
      cases x with
      | nil =>
        refine Or.inr ?_
        simp only [Pat.at, Option.some.injEq] at hat
        rw [List.append_nil, hel, hf, ← hat, hab, hbf]
      | cons i x =>
        refine Or.inl ?_
        rw [hab, show i :: x = [i] ++ x from rfl, Pat.at_append] at hat
        obtain ⟨u, hu, hux⟩ := Option.bind_eq_some_iff.1 hat
        have hbw : b.1.WF ar := Pat.at_wf _ _ _ (hLs _ hLm).2 hatb
        obtain ⟨args, hba, hlen⟩ := Pat.shape hbw hbf
        have hb' : Pat.atArgs args i [] = some u := by
          rw [hba] at hu; simpa [Pat.at] using hu
        obtain ⟨h1, h2⟩ := Pat.atArgs_bounds _ _ _ _ hb'
        have hune : u ≠ .omega := by
          rintro rfl
          cases x with
          | nil => simp only [Pat.at, Option.some.injEq] at hux; exact hne hux.symm
          | cons _ _ => simp [Pat.at] at hux
        refine ⟨(u, l ++ [i]), mem_reduce.2 (Or.inr ⟨b, hb, hbl, i, h1, by omega, u, hu, hune, rfl⟩), ?_⟩
        refine ⟨x, ?_⟩
        show l ++ [i] ++ x = g₀.2.2 ++ (ra ++ i :: x)
        rw [← hel]; simp
    · exact Or.inl ⟨_, Finset.mem_singleton_self _, by simp⟩

private theorem ninv_lift {Q : Goal F → Goal F → Prop} [DecidableRel Q] (hQ : QOk Q) {t : Pat F}
    {X : State F} {p : Position} (I : GInv Ls X) (N : NInv t X p)
    {g : Goal F} (hg : g ∈ X) : NInv t (lift (classOfBy Q X g)) (p ++ gcpOf (classOfBy Q X g)) := by
  set K := classOfBy Q X g with hK
  have hsub : K ⊆ X := classOf_subset hg
  have hma : ∀ h ∈ K, gcpOf K <+: h.2.2 := (hQ.gcp I hg).2
  have hpre : ∀ h ∈ K, ∀ a ∈ h.1, gcpOf K <+: a.2 := fun h hh a ha => class_prefix hQ I hg hh ha
  refine ⟨?_, ?_⟩
  · intro g' hg' a' ha'
    obtain ⟨h, hh, rfl⟩ := mem_lift.1 hg'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
    show (t.at ((p ++ gcpOf K) ++ shorten (gcpOf K) a.2)).isSome
    rw [List.append_assoc, shorten_app (hpre h hh a ha)]
    exact N.inside h (hsub hh) a ha
  · intro g' hg' r l' hat hne
    obtain ⟨h, hh, rfl⟩ := mem_lift.1 hg'
    rcases N.sound h (hsub hh) r l' hat hne with ⟨a, ha, hp⟩ | hchk
    · refine Or.inl ⟨_, Finset.mem_image.2 ⟨a, ha, rfl⟩, ?_⟩
      show shorten (gcpOf K) a.2 <+: shorten (gcpOf K) h.2.2 ++ r
      rw [← shorten_append (hma h hh)]
      exact (shorten_prefix (hpre h hh a ha) ((hma h hh).trans (List.prefix_append _ _))).2 hp
    · refine Or.inr ?_
      show headAt t ((p ++ gcpOf K) ++ (shorten (gcpOf K) h.2.2 ++ r)) = l'.hd
      rw [List.append_assoc, ← List.append_assoc (gcpOf K), shorten_app (hma h hh)]
      exact hchk

end MercLib.SetAutomaton
