import Sigref.Proofs.TarjanMain_Proofs

/-!
# Proofs: size bounds of the Tarjan model

The number of blocks, the SCC stack and the work stack never exceed the number of states; these
bound the arithmetic and the vector pushes of the Rust implementation.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

namespace Sigref.Tarjan

variable {n : ℕ} {g : Graph n} {c : Ctx n}

theorem initNode_eq (g : Graph n) (s : Fin n) (c : Ctx n) : (initNode g s c).eq = c.eq := by
  unfold initNode; split_ifs <;> rfl

theorem scan_work_eq (g : Graph n) (s : Fin n) :
    ∀ (ts : List (Bool × Fin n)) (idx : ℕ) (c : Ctx n),
      (scan g s ts idx c).2.2.work = c.work ∧ (scan g s ts idx c).2.2.eq = c.eq ∧
        (scan g s ts idx c).2.2.ri = c.ri := by
  intro ts
  induction ts with
  | nil => intro idx c; simp [scan]
  | cons e ts ih =>
    obtain ⟨h, v⟩ := e
    intro idx c
    cases h with
    | false => simp only [scan, Bool.false_eq_true, if_false]; exact ih _ _
    | true =>
      by_cases hd : c.disc v = g.unv
      · simp [scan, hd]
      · by_cases hc : (c.onSt v && decide (c.disc v < c.low s)) = true
        · simp only [scan, if_true, hd, if_false, hc]
          exact ih _ { c with low := Function.update c.low s (c.disc v) }
        · simp only [scan, if_true, hd, if_false, hc, Bool.false_eq_true]
          exact ih _ c

theorem finish_ri {s : Fin n} {c c' : Ctx n} (h : finish s c = some c') : c'.ri = c.ri := by
  unfold finish at h
  by_cases hd : c.disc s = c.low s
  · rw [if_pos hd] at h
    cases hp : popComp s c.eq c.stk c.onSt c.blk with
    | none => rw [hp] at h; simp at h
    | some r =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]
      split <;> (try split_ifs) <;> rfl
  · rw [if_neg hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]
    split <;> (try split_ifs) <;> rfl

theorem step_ri_cons {g : Graph n} {c c' : Ctx n} {s : Fin n} {off : ℕ} {W : List (Fin n × ℕ)}
    (hw : c.work = (s, off) :: W) (h : step g c = Out.next c') : c'.ri = c.ri := by
  have hri1 : (initNode g s { c with work := W }).ri = c.ri := by
    rw [initNode_ri]
  unfold step at h
  rw [hw] at h
  simp only at h
  have hsc := (scan_work_eq g s ((g.adj s).drop off) off (initNode g s { c with work := W })).2.2
  rcases hs : scan g s ((g.adj s).drop off) off (initNode g s { c with work := W }) with ⟨chm, offm, c2⟩
  rw [hs] at h hsc
  simp only at hsc
  cases chm with
  | some ch =>
    simp only [Out.next.injEq] at h
    rw [← h]; simp [hsc, hri1]
  | none =>
    simp only at h
    cases hf : finish s c2 with
    | none => rw [hf] at h; simp at h
    | some c3 =>
      rw [hf] at h
      simp only [Out.next.injEq] at h
      subst h
      rw [finish_ri hf, hsc, hri1]

namespace Inv

theorem eq_le (h : Inv g c) : c.eq ≤ n := by
  have h4 : ∀ b : Fin c.eq, ∃ v, c.blk v = b.val := fun b => by
    obtain ⟨v, _, hv⟩ := h.E4 b.val b.2
    exact ⟨v, hv⟩
  choose f hf using h4
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    rw [← hf a, ← hf b, hab]
  simpa using Fintype.card_le_of_injective f hinj

theorem stk_len_le (h : Inv g c) : c.stk.length ≤ n := by
  have := List.Nodup.length_le_card h.stk_nodup
  simpa using this

theorem work_len_le (h : Inv g c) : c.work.length ≤ n := by
  have := List.Nodup.length_le_card h.work_nodup
  simpa using this

end Inv

end Sigref.Tarjan
