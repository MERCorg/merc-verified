import MercVerified.Refinement.Refinement
import MercVerified.Lts.Proofs.Foundation_Proofs
import Aeneas.Std.WP

/-!
# Generic loop lemmas

The translated `for`-loops all have the same shape: a `loop` over a `Range` (or slice
iterator) whose body first calls `next` and then either finishes or does one step of work.
The lemmas below let the per-loop proofs state just the two cases (one work step and the
exhausted iterator) and get the whole-loop statement.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow

namespace MercVerified.Refinement.Proofs

/-- A `loop` over a `Range` starting at `start` with end `e`, whose state is `s`, terminates
    with a result satisfying `post` provided `inv i s` is preserved by every work step
    (`i < e`) and the exhausted case (`i = e`) establishes `post`. -/
theorem range_loop_spec {σ ρ : Type}
    (body : (core.ops.range.Range Std.Usize × σ) →
      Result (ControlFlow (core.ops.range.Range Std.Usize × σ) ρ))
    (inv : Nat → σ → Prop) (post : ρ → Prop) (e : Std.Usize)
    (hsome : ∀ (i : Std.Usize) (s : σ), i.val < e.val → inv i.val s →
      ∃ (i1 : Std.Usize) (s' : σ), i1.val = i.val + 1 ∧
        body (({ start := i, «end» := e } : core.ops.range.Range Std.Usize), s)
          = ok (cont (({ start := i1, «end» := e } : core.ops.range.Range Std.Usize), s')) ∧
        inv (i.val + 1) s')
    (hnone : ∀ (i : Std.Usize) (s : σ), i.val = e.val → inv i.val s →
      ∃ r, body (({ start := i, «end» := e } : core.ops.range.Range Std.Usize), s)
        = ok (done r) ∧ post r)
    (start : Std.Usize) (s0 : σ) (hst : start.val ≤ e.val) (h0 : inv start.val s0) :
    ∃ r, loop body (({ start := start, «end» := e } : core.ops.range.Range Std.Usize), s0)
      = ok r ∧ post r := by
  apply Std.WP.spec_imp_exists
  apply loop.spec_decr_nat
    (measure := fun x => e.val - x.1.start.val)
    (inv := fun x => x.1.«end» = e ∧ x.1.start.val ≤ e.val ∧ inv x.1.start.val x.2)
  · rintro ⟨⟨i, e'⟩, s⟩ ⟨hend, hle, hinv⟩
    simp only at hend hle hinv
    subst hend
    by_cases hlt : i.val < e'.val
    · obtain ⟨i1, s', hi1, hb, hinv'⟩ := hsome i s hlt hinv
      exact Std.WP.exists_imp_spec ⟨cont _, hb, ⟨rfl, by simp only; omega, by simpa [hi1] using hinv'⟩,
        by simp only; omega⟩
    · have heq : i.val = e'.val := by omega
      obtain ⟨r, hb, hp⟩ := hnone i s heq hinv
      exact Std.WP.exists_imp_spec ⟨done r, hb, hp⟩
  · exact ⟨rfl, hst, h0⟩

open verified.merc_utilities.tagged_index (TagIndex)
open MercVerified.Lts.Proofs

/-- `Usize::MAX + 1 = 2^bits`, so `Usize.max < 2 ^ bits`. -/
theorem usize_max_succ : Usize.max + 1 = 2 ^ UScalarTy.Usize.numBits := by
  rw [Usize.max_def]
  have : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  simp [UScalarTy.numBits, Usize.numBits] at *

/-- Indexing a `Vec` by a plain in-bounds `usize`. -/
theorem vec_index_ok {U : Type} (v : alloc.vec.Vec U) (i : Std.Usize)
    (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U) v i
      = ok (v.val[i.val]'h) := by
  have hs := Slice.index_usize_spec v.slice i (by simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h)
  obtain ⟨x, hx, hxe⟩ := Std.WP.spec_imp_exists hs
  simp only [alloc.vec.Vec.index, core.slice.index.Usize.index]
  rw [hx, hxe]
  rfl

/-- Mutably indexing a `Vec` by a plain in-bounds `usize`: the read value and the write-back
    (`Slice.set`). -/
theorem vec_index_mut_ok {U : Type} (v : alloc.vec.Vec U) (i : Std.Usize)
    (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice U) v i
      = ok (v.val[i.val]'h, fun u => ({ slice := v.slice.set i u } : alloc.vec.Vec U)) := by
  have hs := Slice.index_mut_usize_spec v.slice i (by simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h)
  obtain ⟨⟨x, back⟩, hx, hxe, hb⟩ := Std.WP.spec_imp_exists hs
  simp only [alloc.vec.Vec.index_mut, core.slice.index.Usize.index_mut]
  rw [hx]
  subst hb
  simp [hxe, Functor.map]
  rfl

/-- Mutably indexing a `Vec` by an in-bounds tagged `usize`. -/
theorem vec_tagged_index_mut_ok {U Tag : Type} (v : alloc.vec.Vec U) (t : TagIndex Std.Usize Tag)
    (h : t.index.val < v.val.length) :
    verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) v t
      = ok (v.val[t.index.val]'h, fun u => ({ slice := v.slice.set t.index u } : alloc.vec.Vec U)) := by
  rw [vec_tagged_index_mut_eq]
  have hs := Slice.index_mut_usize_spec v.slice t.index (by simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h)
  obtain ⟨⟨x, back⟩, hx, hxe, hb⟩ := Std.WP.spec_imp_exists hs
  rw [hx]
  subst hb
  simp [hxe]
  rfl

/-- A `loop` whose state carries a progress counter `idx x` that the invariant `inv m x` pins to
    `m`: if every state with `m < K` steps to a state with counter `m + 1`, and the state with
    counter `K` finishes with a result satisfying `Q`, the loop returns such a result. -/
theorem loop_nat_spec {σ ρ : Type} (body : σ → Result (ControlFlow σ ρ)) (idx : σ → Nat)
    (inv : Nat → σ → Prop) (Q : ρ → Prop) (K : Nat)
    (hidx : ∀ m x, inv m x → idx x = m) (hle : ∀ m x, inv m x → m ≤ K)
    (hstep : ∀ m x, m < K → inv m x → ∃ x', body x = ok (cont x') ∧ inv (m + 1) x')
    (hdone : ∀ x, inv K x → ∃ y, body x = ok (done y) ∧ Q y)
    (x0 : σ) (h0 : inv 0 x0) :
    ∃ y, loop body x0 = ok y ∧ Q y := by
  apply Std.WP.spec_imp_exists
  apply loop.spec_decr_nat (measure := fun x => K - idx x)
    (inv := fun x => ∃ m, inv m x)
  · rintro x ⟨m, hm⟩
    have hi := hidx m x hm
    by_cases hlt : m < K
    · obtain ⟨x', hb, hx'⟩ := hstep m x hlt hm
      exact Std.WP.exists_imp_spec ⟨cont x', hb, ⟨m + 1, hx'⟩, by
        have := hidx _ _ hx'; omega⟩
    · have hK : m = K := le_antisymm (hle m x hm) (by omega)
      subst hK
      obtain ⟨y, hb, hy⟩ := hdone x hm
      exact Std.WP.exists_imp_spec ⟨done y, hb, hy⟩
  · exact ⟨0, h0⟩

end MercVerified.Refinement.Proofs
