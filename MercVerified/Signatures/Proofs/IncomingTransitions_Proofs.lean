import MercVerified.Signatures.IncomingTransitions
import MercVerified.Signatures.Proofs.Partition_Proofs
import Aeneas.Std.WP

/-!
# Proofs for the `IncomingTransitions::new` correctness contract

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

`IncomingTransitionsCorrect` (stated in
`MercVerified/Signatures/IncomingTransitions.lean`) is the gating lemma for
`strong_run_worklist_loop_partial_correct`: the worklist invariant's soundness
conjunct - "a block that is not on the worklist is settled" - and its completeness
conjunct - "refinement never separates bisimilar states" - both need
`mark_dirty_new_blocks` to re-mark exactly those states that have an edge into a freshly
created block, and `mark_dirty_new_blocks` reads that off `incoming`.

`IncomingTransitions::new` (`incoming_transitions.rs:282`) builds `incoming` in seven
stages, which this file takes one at a time:

1. `new_labels n` / `new_states n` - `n` zeroed slots for the flat transition arrays.
2. `new_counts (n+1)` - `n+1` zeroed counters, one sentinel slot per the Rust comment.
3. `count_all_incoming` - increments `counts[to]` once per outgoing transition.
4. `prefix_sum` - turns the counts into start offsets and writes the total at index `n`.
5. `copy_prefix` - snapshots the offsets as placement cursors.
6. `place_all_incoming` - scatters each transition at the cursor of its *target*.
7. `sort_all_incoming` - insertion-sorts each state's range by label.

`incoming_transitions` (`incoming_transitions.rs:323`) then reads a state's range back
out of the flat arrays.

## Status

Proved below:

* Stage 1: `new_labels_spec`, `new_states_spec`.
* Stage 2: `new_counts_spec`.
* Stage 3: `count_all_incoming_state_spec` - per state, the counters hold the initial value
  plus the number of transitions towards each slot that the enumerated states report
  (`seenCount`), via `count_incoming_loop_spec` and `count_all_incoming_loop_spec`.
* Stage 4: `prefix_sum_spec` - the counts become the CSR offset array `r[j] =
  uTotal (counts[0] + … + counts[j-1])` for `j ≤ n`, via `prefix_sum_loop_spec`.
* Stage 5: `copy_prefix_spec` (plus the `copy_prefix_getElem` reading), via the generic
  `gather_loop_spec`.
* Stage 6 (in progress): the list-level reading of the two flat arrays (`pairAt`,
  `slotEntries`, and how a `List.set` acts on it), the per-state content of a slot
  (`towards1`, with `towards1_succ_self` / `towards1_succ_ne`) and the inner scan
  (`place_incoming_loop_spec`): one state's transitions are written at
  `cursor0[target] + (how many preceding transitions of that state target the same slot)`,
  each carrying `(label, this state)`, so slot `j` ends up holding exactly that state's
  pairs towards `j` in order. The write-stays-in-its-own-slot fact is not re-derived per
  iteration but taken as `SepInv` and discharged once, by the outer scan
  (`place_all_incoming_loop_spec`), which is next.

Remaining: the outer scan (`place_all_incoming_loop_spec`), stage 7 (`sort_all_incoming`),
the public-wrapper extraction for `count_all_incoming` / `copy_prefix` / `prefix_sum`'s
callers, and the extraction lemma `incoming_transitions_spec`.

The three `new_*_spec` theorems share one generic loop induction (`constPush_loop_spec`),
and `copy_prefix` a second (`gather_loop_spec`). Stage 6 has the same "range over states,
mutate several vectors" shape as `gather_loop_spec`, but needs a cursor/scatter invariant on
top of it: the transitions of the enumerated states, in order, are written at
`r[target] + (how many transitions towards that target came before)`, which is the whole
content of `IncomingTransitionsCorrect`. Stage 7 is a stable insertion sort per range, which
only has to be a permutation of each range.

Stages 3, 6 and 7 all take the enumeration and the transition count of the `LTS` implementor
as hypotheses: `LTS.WellFormed` (`MercVerified/Basic.lean`) constrains `outgoing_transitions`
but says nothing about `iter_states` or `num_of_transitions`, which is what the final
extraction lemma needs.
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open verified.merc_lts.lts.LTS (toLTS tr)

namespace MercVerified.Signatures.Proofs

set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option allowUnsafeReducibility true
attribute [local reducible] Aeneas.Std.WP.Post

abbrev Sz := Std.Usize
abbrev ItSz := core.ops.range.Range Sz

/-- The zeroed `TagIndex` a freshly allocated label slot holds. An `abbrev`, not a `def`:
    `alloc.vec.Vec.push` is `@[irreducible]`, so a `def`d name could not be unified with the
    structure literal the translated body pushes. -/
abbrev zeroLabel : TagIndex Sz LabelTag := { index := 0#usize, marker := () }

/-- The zeroed `TagIndex` a freshly allocated state slot holds. -/
abbrev zeroState : TagIndex Sz StateTag := { index := 0#usize, marker := () }

/-! ## A generic "for `i` in `[0, n)`, push `x`" loop

`new_labels_loop`, `new_states_loop` and `new_counts_loop` are the same loop at three
element types, so the loop induction is done once here and instantiated three times. -/

/-- Invariant of the const-push loop: the range's end is pinned to `n`, `start` has not
    overrun it, and the accumulator holds exactly the processed prefix. -/
def constPushInv {α : Type} (n : Sz) (x : α) : ItSz × alloc.vec.Vec α → Prop :=
  fun st =>
    st.1.end = n ∧ st.1.start.val ≤ n.val ∧ st.2.val = List.replicate st.1.start.val x

def constPushMeasure {α : Type} (st : ItSz × alloc.vec.Vec α) : Nat :=
  st.1.end.val - st.1.start.val

/-- A loop whose body is "advance the range, or stop; push `x` and continue" fills the
    accumulator with `n` copies of `x`, starting from the empty vector. -/
theorem constPush_loop_spec {α : Type} (x : α)
    (body : ItSz → alloc.vec.Vec α → Result (ControlFlow (ItSz × alloc.vec.Vec α) (alloc.vec.Vec α)))
    (hstep : ∀ (it : ItSz) (v : alloc.vec.Vec α), v.val.length < Usize.max →
      it.start.val < it.end.val →
      ∃ (it1 : ItSz) (v1 : alloc.vec.Vec α),
        body it v = ok (cont (it1, v1)) ∧
        it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧ v1.val = v.val ++ [x])
    (hdone : ∀ (it : ItSz) (v : alloc.vec.Vec α), it.end.val ≤ it.start.val →
      body it v = ok (done v))
    (n : Sz) :
    Aeneas.Std.WP.spec
        (@loop (ItSz × alloc.vec.Vec α) (alloc.vec.Vec α) (fun p => body p.1 p.2)
          ({ start := 0#usize, «end» := n }, alloc.vec.Vec.new α))
        (fun v : alloc.vec.Vec α => v.val = List.replicate n.val x) := by
  apply loop.spec_decr_nat
    (measure := constPushMeasure)
    (inv := constPushInv n x)
    (post := fun v : alloc.vec.Vec α => v.val = List.replicate n.val x)
    (body := fun p => body p.1 p.2)
    (x := ({ start := 0#usize, «end» := n }, alloc.vec.Vec.new α))
  · intro st hinv
    rcases hinv with ⟨hend, hle, hval⟩
    by_cases hlt : st.1.start.val < st.1.end.val
    · have hlen : st.2.val.length < Usize.max := by
        rw [hval]
        exact lt_of_lt_of_le (by simpa [hend] using hlt) (sz_val_le_max n)
      rcases hstep st.1 st.2 hlen hlt with ⟨it1, v1, hbody, hstart, hend', hvval⟩
      have hinv' : constPushInv n x (it1, v1) := by
        refine ⟨hend'.trans hend, ?_, ?_⟩
        · rw [hstart]
          have hltn : st.1.start.val < n.val := by simpa [hend] using hlt
          omega
        · rw [hvval, hval, hstart, ← Nat.succ_eq_add_one, replicate_append_succ]
      have hlt' : constPushMeasure (it1, v1) < constPushMeasure st := by
        change (it1.end.val - it1.start.val) < (st.1.end.val - st.1.start.val)
        rw [hstart, hend', hend]
        rw [hend] at hlt
        omega
      exact Std.WP.exists_imp_spec ⟨cont (it1, v1), hbody, hinv', hlt'⟩
    · have hge : st.1.end.val ≤ st.1.start.val := by omega
      have hstart : st.1.start.val = n.val := by
        apply Nat.le_antisymm hle
        rw [← hend]; exact hge
      have hpost : st.2.val = List.replicate n.val x := by
        rw [hval, hstart]
      exact Std.WP.exists_imp_spec ⟨done st.2, hdone st.1 st.2 hge, hpost⟩
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · simp

/-! ## Stages 1 and 2: the zeroed arrays -/

theorem new_labels_step (it : ItSz) (v : alloc.vec.Vec (TagIndex Sz LabelTag))
    (hlen : v.val.length < Usize.max) (h : it.start.val < it.end.val) :
    ∃ (it1 : ItSz) (v1 : alloc.vec.Vec (TagIndex Sz LabelTag)),
      verified.merc_lts.incoming_transitions.new_labels_loop.body it v = ok (cont (it1, v1)) ∧
      it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
      v1.val = v.val ++ [zeroLabel] := by
  rcases next_range_some it h with ⟨o, it1, hnext, hopt, hstart, hend⟩
  rcases vec_push_val v zeroLabel hlen with ⟨v1, hpush, hvval⟩
  refine ⟨it1, v1, ?_, hstart, hend, hvval⟩
  unfold verified.merc_lts.incoming_transitions.new_labels_loop.body
  rw [hnext, hopt]
  simp [merc_utilities.tagged_index.TagIndex.new_eq, hpush]

theorem new_labels_done (it : ItSz) (v : alloc.vec.Vec (TagIndex Sz LabelTag))
    (h : it.end.val ≤ it.start.val) :
    verified.merc_lts.incoming_transitions.new_labels_loop.body it v = ok (done v) := by
  rcases next_range_none it h with ⟨o, it1, hnext, hopt, hident⟩
  unfold verified.merc_lts.incoming_transitions.new_labels_loop.body
  rw [hnext, hopt]
  simp

/-- `new_labels n` is the flat label array of `n` zeroed slots. -/
theorem new_labels_spec (n : Sz) :
    ∃ v : alloc.vec.Vec (TagIndex Sz LabelTag),
      verified.merc_lts.incoming_transitions.new_labels n = ok v ∧
      v.val = List.replicate n.val zeroLabel := by
  rcases Std.WP.spec_imp_exists
      (constPush_loop_spec zeroLabel
        verified.merc_lts.incoming_transitions.new_labels_loop.body
        new_labels_step new_labels_done n) with ⟨v, hloop, hval⟩
  refine ⟨v, ?_, hval⟩
  unfold verified.merc_lts.incoming_transitions.new_labels
  simp only [alloc.vec.Vec.with_capacity,
    verified.merc_lts.incoming_transitions.new_labels_loop]
  rw [hloop]

theorem new_states_step (it : ItSz) (v : alloc.vec.Vec (TagIndex Sz StateTag))
    (hlen : v.val.length < Usize.max) (h : it.start.val < it.end.val) :
    ∃ (it1 : ItSz) (v1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.new_states_loop.body it v = ok (cont (it1, v1)) ∧
      it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
      v1.val = v.val ++ [zeroState] := by
  rcases next_range_some it h with ⟨o, it1, hnext, hopt, hstart, hend⟩
  rcases vec_push_val v zeroState hlen with ⟨v1, hpush, hvval⟩
  refine ⟨it1, v1, ?_, hstart, hend, hvval⟩
  unfold verified.merc_lts.incoming_transitions.new_states_loop.body
  rw [hnext, hopt]
  simp [merc_utilities.tagged_index.TagIndex.new_eq, hpush]

theorem new_states_done (it : ItSz) (v : alloc.vec.Vec (TagIndex Sz StateTag))
    (h : it.end.val ≤ it.start.val) :
    verified.merc_lts.incoming_transitions.new_states_loop.body it v = ok (done v) := by
  rcases next_range_none it h with ⟨o, it1, hnext, hopt, hident⟩
  unfold verified.merc_lts.incoming_transitions.new_states_loop.body
  rw [hnext, hopt]
  simp

/-- `new_states n` is the flat source-state array of `n` zeroed slots. -/
theorem new_states_spec (n : Sz) :
    ∃ v : alloc.vec.Vec (TagIndex Sz StateTag),
      verified.merc_lts.incoming_transitions.new_states n = ok v ∧
      v.val = List.replicate n.val zeroState := by
  rcases Std.WP.spec_imp_exists
      (constPush_loop_spec zeroState
        verified.merc_lts.incoming_transitions.new_states_loop.body
        new_states_step new_states_done n) with ⟨v, hloop, hval⟩
  refine ⟨v, ?_, hval⟩
  unfold verified.merc_lts.incoming_transitions.new_states
  simp only [alloc.vec.Vec.with_capacity,
    verified.merc_lts.incoming_transitions.new_states_loop]
  rw [hloop]

theorem new_counts_step (it : ItSz) (v : alloc.vec.Vec Sz)
    (hlen : v.val.length < Usize.max) (h : it.start.val < it.end.val) :
    ∃ (it1 : ItSz) (v1 : alloc.vec.Vec Sz),
      verified.merc_lts.incoming_transitions.new_counts_loop.body it v = ok (cont (it1, v1)) ∧
      it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
      v1.val = v.val ++ [0#usize] := by
  rcases next_range_some it h with ⟨o, it1, hnext, hopt, hstart, hend⟩
  rcases vec_push_val v (0#usize) hlen with ⟨v1, hpush, hvval⟩
  refine ⟨it1, v1, ?_, hstart, hend, hvval⟩
  unfold verified.merc_lts.incoming_transitions.new_counts_loop.body
  rw [hnext, hopt]
  simp [hpush]

theorem new_counts_done (it : ItSz) (v : alloc.vec.Vec Sz) (h : it.end.val ≤ it.start.val) :
    verified.merc_lts.incoming_transitions.new_counts_loop.body it v = ok (done v) := by
  rcases next_range_none it h with ⟨o, it1, hnext, hopt, hident⟩
  unfold verified.merc_lts.incoming_transitions.new_counts_loop.body
  rw [hnext, hopt]
  simp

/-- `new_counts n` is `n` zeroed counters. `IncomingTransitions::new` calls it with
    `num_of_states + 1`, the extra slot being the sentinel the Rust comment mentions. -/
theorem new_counts_spec (n : Sz) :
    ∃ v : alloc.vec.Vec Sz,
      verified.merc_lts.incoming_transitions.new_counts n = ok v ∧
      v.val = List.replicate n.val (0#usize) := by
  rcases Std.WP.spec_imp_exists
      (constPush_loop_spec (0#usize)
        verified.merc_lts.incoming_transitions.new_counts_loop.body
        new_counts_step new_counts_done n) with ⟨v, hloop, hval⟩
  refine ⟨v, ?_, hval⟩
  unfold verified.merc_lts.incoming_transitions.new_counts
  simp only [alloc.vec.Vec.with_capacity,
    verified.merc_lts.incoming_transitions.new_counts_loop]
  rw [hloop]

/-! ## Stage 4: `prefix_sum`

`prefix_sum` (`incoming_transitions.rs:171`) turns the per-state counts into the CSR
offset array. Each iteration reads slot `i`, *writes the running total back into that
slot*, and only then adds `counts[i]` to the total, so slot `j` ends up holding the
*exclusive* prefix sum; afterwards the grand total is written into slot `n`. The result
satisfies

* `r[j] = counts[0] + … + counts[j-1]` for `0 ≤ j ≤ n` (so `r[0] = 0` and `r[n]` is the
  total number of transitions), and
* slots past `n` are untouched.

`place_all_incoming` then uses `r[j]` as the start of state `j`'s range and `r[j+1]` as
its end.

`UScalar.add` is a *checked* add (`UScalar.add = UScalar.tryMk ty (x.val + y.val)`), so
the loop can in principle fail on overflow. The theorem below is therefore stated for
inputs whose running totals all fit in a `usize`, which is what `IncomingTransitions::new`
supplies: the grand total is the number of transitions, bounded by the length of the
outgoing arrays. -/

/-- The total of `c`'s first `k` entries, in `Nat`. The `usize` running offset of
    `prefix_sum` is always `uTotal (natSum c k)`: `uTotal` inverts `.val` on naturals
    below `2^numBits`, and `uTotal_val_of_lt` / `sz_eq_from_val` turn that back into an
    equation of `usize`s. -/
def natSum (c : List Sz) (k : Nat) : Nat := ((c.take k).map (fun x => x.val)).sum

private lemma natSum_zero (c : List Sz) : natSum c 0 = 0 := by simp [natSum]

/-- `Usize.max` is one below `2^numBits`, so a total bounded by it fits. -/
private lemma lt_two_pow_of_le_max {k : Nat} (h : k ≤ Usize.max) :
    k < 2 ^ UScalarTy.Usize.numBits := by
  have h2 : Usize.max + 1 = 2 ^ UScalarTy.Usize.numBits := by
    simp [Usize.max, Usize.numBits]
  omega

/-- Extending the prefix by one slot adds exactly that slot's value. -/
private lemma natSum_succ (c : List Sz) (i : Nat) (h : i < c.length) :
    natSum c (i + 1) = natSum c i + c[i].val := by
  have htake : c.take (i + 1) = c.take i ++ [c[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    simp
  unfold natSum
  rw [htake, List.map_append, List.sum_append]
  simp

/-- `List.set` reads back as "the new value at the updated slot, the old value
    everywhere else". The accumulator is read through `getD` so that the statement needs
    no bound on the *updated* list; `prefix_sum`'s own bound hypotheses supply the one
    for the pre-`set` list.

    `List.getD l n d` is by definition `l[n]?.getD d`, and `List.set` recurses through
    `brecOn`, so the statement is phrased with `getElem?` (the caller's `getD`-form goal
    is the same term) and the two `Nat` case splits are discharged by `grind`. -/
private lemma gds {α : Type} : ∀ (l : List α) (i k : Nat) (x d : α), k < l.length →
    (l.set i x)[k]?.getD d = if k = i then x else l[k]?.getD d := by
  intro l
  induction l with
  | nil => intro i k x d h; simp at h
  | cons a l ih =>
    intro i k x d hk
    rcases i with (_ | i)
    · rcases k with (_ | k)
      · simp
      · simp
    · rcases k with (_ | k)
      · simp
      · grind [ih i k x d (by simpa using hk)]

/-- The same, phrased with `List.getD`, which is the form the invariants use. -/
private lemma getD_set {α : Type} (l : List α) (i k : Nat) (x d : α) (hk : k < l.length) :
    (l.set i x).getD k d = if k = i then x else l.getD k d := by
  show (l.set i x)[k]?.getD d = if k = i then x else l[k]?.getD d
  exact gds l i k x d hk


/-- State of the `prefix_sum` scan: a range, the mutated counts and the running offset. -/
abbrev PsSt := ItSz × alloc.vec.Vec Sz × Sz

/-- Invariant of the scan at range position `start`:
    * the range's end is pinned to `n` and `start` has not overrun it;
    * the running offset is the total of the *original* `c`'s first `start` entries;
    * the accumulator is as long as `c`, its first `start` slots hold those running
      totals, and every remaining slot still holds `c`'s original value;
    * the checked add will not overflow at any slot this loop still has to visit. -/
def prefixSumInv (c : alloc.vec.Vec Sz) (n : Sz) : PsSt → Prop :=
  fun st =>
    st.1.end = n ∧ st.1.start.val ≤ n.val ∧
    st.2.2 = uTotal (natSum c.val st.1.start.val) ∧
    st.2.1.val.length = c.val.length ∧
    (∀ k, k < st.2.1.val.length →
      st.2.1.val.getD k 0#usize =
        if k < st.1.start.val then uTotal (natSum c.val k) else c.val.getD k 0#usize) ∧
    (∀ j, j + 1 ≤ st.1.end.val →
      natSum c.val j + (c.val.getD j 0#usize).val ≤ Usize.max)

/-- On return, the offset is the grand total and the visited slots hold the running
    totals; slots from `n` on are still `c`'s original values. -/
def prefixSumPost (c : alloc.vec.Vec Sz) (n : Sz) : (alloc.vec.Vec Sz × Sz) → Prop :=
  fun p =>
    p.2 = uTotal (natSum c.val n.val) ∧
    p.1.val.length = c.val.length ∧
    (∀ k, k < p.1.val.length →
      p.1.val.getD k 0#usize =
        if k < n.val then uTotal (natSum c.val k) else c.val.getD k 0#usize)

/-- One iteration of `prefix_sum_loop.body`: write the *current* offset into slot
    `start`, then add that slot's old value into the offset. -/
theorem prefix_sum_step (it : ItSz) (v : alloc.vec.Vec Sz)
    (off : Sz) (hidx : it.start.val < v.val.length) (h : it.start.val < it.end.val)
    (hmax : off.val + v.val[it.start.val].val ≤ Usize.max) :
    ∃ (it1 : ItSz) (v1 : alloc.vec.Vec Sz) (off1 : Sz),
      verified.merc_lts.incoming_transitions.prefix_sum_loop.body it v off
        = ok (cont (it1, v1, off1)) ∧
      it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
      v1.val = v.val.set it.start.val off ∧
      off1.val = off.val + v.val[it.start.val].val := by
  rcases next_range_some it h with ⟨o, it1, hnext, hopt, hstart, hend⟩
  have hidx' := Aeneas.Std.alloc.vec.Vec.index_usize_spec v it.start hidx
  rcases Std.WP.spec_imp_exists hidx' with ⟨x, hx, hxv⟩
  have hidxS : v.index_usize it.start = ok (v.val[it.start.val]) := by
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hx, hxv]
  have himutS : v.index_mut_usize it.start
      = ok (v.val[it.start.val], fun x => v.set it.start x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxS]
  have hadd := Usize.add_spec (x := off) (y := v.val[it.start.val]) hmax
  rcases Std.WP.spec_imp_exists hadd with ⟨z, hz, hzval⟩
  refine ⟨it1, v.set it.start off, z, ?_, hstart, hend, ?_, ?_⟩
  · unfold verified.merc_lts.incoming_transitions.prefix_sum_loop.body
    rw [hnext]
    simp [hopt, hidxS, himutS, hz]
  · simp
  · rw [hzval]

/-- The `end ≤ start` case: the range is exhausted, counts and offset are returned. -/
theorem prefix_sum_done (it : ItSz) (v : alloc.vec.Vec Sz) (off : Sz)
    (hge : it.end.val ≤ it.start.val) :
    verified.merc_lts.incoming_transitions.prefix_sum_loop.body it v off
      = ok (done (v, off)) := by
  rcases next_range_none it hge with ⟨o, it1, hnext, hopt, hident⟩
  unfold verified.merc_lts.incoming_transitions.prefix_sum_loop.body
  rw [hnext, hopt]
  simp [hident]

/-- The `prefix_sum` scan, run from a fresh offset over `[0, n)`, returns the grand total
    together with the counts vector updated in place. -/
theorem prefix_sum_loop_spec (c : alloc.vec.Vec Sz) (n : Sz)
    (hc : n.val < c.val.length)
    (hnoovf : ∀ k, k ≤ n.val → natSum c.val k ≤ Usize.max) :
    Aeneas.Std.WP.spec
      (@loop PsSt (alloc.vec.Vec Sz × Sz)
        (fun p => verified.merc_lts.incoming_transitions.prefix_sum_loop.body
          p.1 p.2.1 p.2.2)
        ({ start := 0#usize, «end» := n }, c, 0#usize))
      (prefixSumPost c n) := by
  apply loop.spec_decr_nat
    (measure := fun st : PsSt => st.1.end.val - st.1.start.val)
    (inv := prefixSumInv c n)
    (post := prefixSumPost c n)
    (body := fun p => verified.merc_lts.incoming_transitions.prefix_sum_loop.body
      p.1 p.2.1 p.2.2)
    (x := ({ start := 0#usize, «end» := n }, c, 0#usize))
  · intro st hinv
    rcases hinv with ⟨hend, hle, hoff, hlen, hpt, hovf⟩
    by_cases hlt : st.1.start.val < st.1.end.val
    · have hltn : st.1.start.val < n.val := by simpa [hend] using hlt
      have hidx : st.1.start.val < st.2.1.val.length := by rw [hlen]; exact hltn.trans hc
      have hcount : st.2.1.val[st.1.start.val] = c.val.getD st.1.start.val 0#usize := by
        have h := hpt st.1.start.val hidx
        rw [if_neg (by omega)] at h
        exact (List.getD_eq_getElem st.2.1.val 0#usize hidx).symm.trans h
      have hmax : st.2.2.val + st.2.1.val[st.1.start.val].val ≤ Usize.max := by
        rw [hcount, hoff, uTotal_val_of_lt (lt_two_pow_of_le_max (hnoovf _ (by omega)))]
        exact hovf st.1.start.val (by omega)
      rcases prefix_sum_step st.1 st.2.1 st.2.2 hidx hlt hmax with
        ⟨it1, v1, off1, hbody, hstart, hend', hvval, hoffval⟩
      have hoff1 : off1 = uTotal (natSum c.val (st.1.start.val + 1)) := by
        apply sz_eq_from_val
        rw [hoffval, hcount, hoff,
          uTotal_val_of_lt (lt_two_pow_of_le_max (hnoovf _ (by omega)))]
        rw [uTotal_val_of_lt (lt_two_pow_of_le_max (hnoovf _ (by omega))),
          natSum_succ c.val st.1.start.val (by omega),
          List.getD_eq_getElem c.val 0#usize (by omega)]
      have hinv' : prefixSumInv c n (it1, v1, off1) := by
        refine ⟨hend'.trans hend, ?_, ?_, ?_, ?_, ?_⟩
        · change it1.start.val ≤ n.val
          rw [hstart]
          omega
        · change off1 = uTotal (natSum c.val it1.start.val)
          rw [hstart]
          exact hoff1
        · change v1.val.length = c.val.length
          rw [hvval, List.length_set, hlen]
        · change ∀ k, k < v1.val.length →
            v1.val.getD k 0#usize =
              if k < it1.start.val then uTotal (natSum c.val k) else c.val.getD k 0#usize
          intro k hk
          have hk' : k < st.2.1.val.length := by
            rw [hvval, List.length_set] at hk
            exact hk
          have hset := getD_set st.2.1.val st.1.start.val k st.2.2 0#usize hk'
          rw [hvval, hset, hstart]
          by_cases hks : k = st.1.start.val
          · subst hks
            rw [if_pos (by omega), if_pos (by omega), hoff]
          · have h := hpt k hk'
            by_cases hltk : k < st.1.start.val
            · rw [if_neg (by omega), h, if_pos (by omega), if_pos (by omega)]
            · rw [if_neg (by omega), h, if_neg (by omega), if_neg (by omega)]
        · change ∀ j, j + 1 ≤ it1.end.val →
            natSum c.val j + (c.val.getD j 0#usize).val ≤ Usize.max
          intro j hj
          exact hovf j (by simpa [hend'] using hj)
      have hlt' : (it1.end.val - it1.start.val) < (st.1.end.val - st.1.start.val) := by
        rw [hstart, hend', hend]
        rw [hend] at hlt
        omega
      exact Std.WP.exists_imp_spec ⟨cont (it1, v1, off1), hbody, hinv', hlt'⟩
    · have hge : st.1.end.val ≤ st.1.start.val := by omega
      have hstart : st.1.start.val = n.val := by
        apply Nat.le_antisymm hle
        rw [← hend]; exact hge
      refine Std.WP.exists_imp_spec ⟨done (st.2.1, st.2.2),
        prefix_sum_done st.1 st.2.1 st.2.2 hge, ?_⟩
      refine ⟨by
        change st.2.2 = uTotal (natSum c.val n.val)
        rw [← hstart]
        exact hoff, hlen, ?_⟩
      intro k hk
      rw [← hstart]
      exact hpt k hk
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp
    · change 0#usize = uTotal (natSum c.val 0)
      rw [natSum_zero, uTotal_zero]
    · rfl
    · simp
    · intro j hj
      have h1 : j + 1 ≤ n.val := hj
      have hjl : j < c.val.length := by omega
      have h2 := hnoovf (j + 1) h1
      rw [natSum_succ c.val j hjl, ← List.getD_eq_getElem c.val 0#usize hjl] at h2
      omega

/-- `prefix_sum c n` turns the counts into the CSR offset array: slot `j ≤ n` holds the
    total of `c`'s first `j` entries, and the length is unchanged. -/
theorem prefix_sum_spec (c : alloc.vec.Vec Sz) (n : Sz)
    (hc : n.val < c.val.length)
    (hnoovf : ∀ k, k ≤ n.val → natSum c.val k ≤ Usize.max) :
    ∃ r : alloc.vec.Vec Sz,
      verified.merc_lts.incoming_transitions.prefix_sum c n = ok r ∧
      r.val.length = c.val.length ∧
      ∀ k, k < n.val + 1 → r.val.getD k 0#usize = uTotal (natSum c.val k) := by
  rcases Std.WP.spec_imp_exists (prefix_sum_loop_spec c n hc hnoovf) with ⟨p, hloop, hpost⟩
  rcases hpost with ⟨hoff, hlen, hpt⟩
  have hidx : n.val < p.1.val.length := by rw [hlen]; exact hc
  have hmain : ∀ (counts1 : alloc.vec.Vec Sz) (offset : Sz),
      n.val < counts1.val.length →
      loop (fun p => verified.merc_lts.incoming_transitions.prefix_sum_loop.body
            p.1 p.2.1 p.2.2)
          ({ start := 0#usize, «end» := n }, c, 0#usize) = ok (counts1, offset) →
      verified.merc_lts.incoming_transitions.prefix_sum c n
        = ok (counts1.set n offset) := by
    intro counts1 offset hbound h
    unfold verified.merc_lts.incoming_transitions.prefix_sum
    simp only [verified.merc_lts.incoming_transitions.prefix_sum_loop]
    rw [h]
    simp [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize,
      alloc.vec.Vec.index_mut_slice_index, hbound]
  refine ⟨p.1.set n p.2, hmain p.1 p.2 hidx hloop, ?_, ?_⟩
  · simp only [Aeneas.Std.alloc.vec.Vec.set_val_eq]
    rw [List.length_set, hlen]
  · intro k hk
    simp only [Aeneas.Std.alloc.vec.Vec.set_val_eq]
    rw [getD_set p.1.val n.val k p.2 0#usize (by rw [hlen]; omega)]
    by_cases hkn : k = n.val
    · rw [hkn, if_pos rfl, hoff]
    · have hlt : k < n.val := by omega
      have h := hpt k (by omega)
      rw [if_pos hlt] at h
      rw [if_neg hkn]
      exact h

/-! ## Stage 3: `count_all_incoming`

`count_allcoming`'s inner loop (`count_incoming`, `incoming_transitions.rs:219`) walks the
transitions `outgoing_transitions` reports for one state and bumps `counts[transition.to]`
once per transition; `count_all_incoming` (`:164`) runs it over every state `iter_states`
reports. So afterwards slot `j` holds the number of transitions of the whole LTS whose
target is `j`.

Each bump is a *checked* `Usize` addition into a bounds-checked slot, so both loops are
stated under two hypotheses that the caller discharges from the LTS's own contract
(`LTS.WellFormed` supplies the bounds):

* `hin`: every transition's target index is a valid slot of `counts`, and
* `hovf`: no slot can overflow, i.e. `counts`'s original value plus the number of ticks
  still coming is representable. -/

/-- The number of transitions of `ts` whose target index is `j`. -/
def toCount (ts : List Transition) (j : Nat) : Nat :=
  (ts.filter (fun t => t.to.index.val = j)).length

/-- What visiting `t` once adds to slot `j`. -/
def tick (t : Transition) (j : Nat) : Nat :=
  if t.to.index.val = j then 1 else 0

theorem toCount_nil (j : Nat) : toCount [] j = 0 := by simp [toCount]

theorem toCount_cons (t : Transition) (ts : List Transition)
    (j : Nat) : toCount (t :: ts) j = tick t j + toCount ts j := by
  simp [toCount, tick, List.filter_cons]
  split <;> simp
  omega

/-- A transition that is in the list contributes at least one to its own slot. -/
theorem toCount_pos_of_mem {t : Transition} {l : List Transition} (hmem : t ∈ l) :
    1 ≤ toCount l t.to.index.val := by
  have h1 : t ∈ l.filter (fun x => decide (x.to.index.val = t.to.index.val)) :=
    List.mem_filter.mpr ⟨hmem, by simp⟩
  have h2 : 0 < (l.filter (fun x => decide (x.to.index.val = t.to.index.val))).length :=
    List.length_pos_of_mem h1
  rw [toCount]
  omega

/-- If the remainder after the first `k` entries starts with `t`, taking one entry more
    appends exactly that `t`. -/
private theorem take_head (l : List Transition) (k : Nat) (t : Transition) (tl : List Transition)
    (h : l = l.take k ++ t :: tl) :
    l.take (k + 1) = l.take k ++ [t] := by
  have hmin : min k l.length = k := by
    by_cases hkl : k ≤ l.length
    · exact Nat.min_eq_left hkl
    · have h2 := congrArg List.length h
      rw [List.length_append, List.length_cons, List.length_take,
        Nat.min_eq_right (by omega)] at h2
      omega
  have hg : l[k]? = some t := by
    rw [h, List.getElem?_append_right (by
          rw [List.length_take]
          exact Nat.min_le_left k l.length),
        List.length_take, hmin]
    simp
  calc l.take (k + 1) = l.take k ++ l[k]?.toList := List.take_add_one ..
    _ = l.take k ++ [t] := by rw [hg]; simp

/-- `IteratorIntoIter.next` pops the head off a non-empty vector. -/
private theorem vec_next_some {α : Type} (v : alloc.vec.Vec α)
    (t : α) (tl : List α) (h : v.val = t :: tl) :
    alloc.vec.into_iter.IteratorIntoIter.next (v : alloc.vec.into_iter.IntoIter α)
      ⦃ p => p.1 = some t ∧ p.2.val = tl ⦄ := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all

/-- Equation form of `vec_next_some`, for rewriting inside `do` blocks. -/
private theorem vec_next_eq {α : Type} (v : alloc.vec.Vec α)
    (t : α) (tl : List α) (h : v.val = t :: tl) :
    ∃ (o : Option α) (it1 : alloc.vec.into_iter.IntoIter α),
      alloc.vec.into_iter.IteratorIntoIter.next (v : alloc.vec.into_iter.IntoIter α)
        = ok (o, it1) ∧ o = some t ∧ it1.val = tl := by
  have hn : alloc.vec.into_iter.IteratorIntoIter.next (v : alloc.vec.into_iter.IntoIter α)
      ⦃ p => p.1 = some t ∧ p.2.val = tl ⦄ := vec_next_some v t tl h
  rcases Std.WP.spec_imp_exists hn with ⟨p, hp, hpt⟩
  cases p with
  | mk o it1 => exact ⟨o, it1, hp, hpt.1, hpt.2⟩

/-- One iteration of `count_incoming_loop.body`: bump slot `t.to` by one.

    The new slot value is existentially quantified with its `Nat` value pinned down, so
    that the caller never has to re-analyse the checked addition. -/
theorem count_incoming_step
    (iter : alloc.vec.Vec Transition) (counts : alloc.vec.Vec Sz)
    (t : Transition) (tl : List Transition)
    (hiter : iter.val = t :: tl)
    (hidx : t.to.index.val < counts.val.length)
    (hadd : (counts.val.getD t.to.index.val 0#usize).val + 1 ≤ Usize.max) :
    ∃ (iter1 : alloc.vec.Vec Transition) (counts1 : alloc.vec.Vec Sz) (z : Sz),
      verified.merc_lts.incoming_transitions.count_incoming_loop.body iter counts
        = ok (cont (iter1, counts1)) ∧
      iter1.val = tl ∧
      counts1.val = counts.val.set t.to.index.val z ∧
      z.val = (counts.val.getD t.to.index.val 0#usize).val + 1 := by
  have hidx' := Aeneas.Std.alloc.vec.Vec.index_usize_spec counts t.to.index hidx
  rcases Std.WP.spec_imp_exists hidx' with ⟨x, hx, hxv⟩
  have hidxS : counts.index_usize t.to.index = ok (counts.val[t.to.index.val]'hidx) := by
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hx, hxv]
  have hget : (counts.val[t.to.index.val]'hidx).val
      = (counts.val.getD t.to.index.val 0#usize).val := by grind
  have hadd' : (counts.val[t.to.index.val]'hidx).val + 1 ≤ Usize.max := by grind
  have hsz := Usize.add_spec (x := counts.val[t.to.index.val]'hidx) (y := 1#usize) hadd'
  rcases Std.WP.spec_imp_exists hsz with ⟨z, hzok, hzval⟩
  have himutS : counts.index_mut_usize t.to.index
      = ok (counts.val[t.to.index.val]'hidx, fun x => counts.set t.to.index x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxS]
  refine ⟨alloc.vec.Vec.from tl (by grind), alloc.vec.Vec.from (counts.val.set t.to.index.val z)
      (by grind), z, ?_, alloc.vec.Vec.from_val _ _, alloc.vec.Vec.from_val _ _, ?_⟩
  · rcases vec_next_eq iter t tl hiter with ⟨o, it1, hnext, ho, hitl⟩
    have hnew : alloc.vec.Vec.from tl (by grind) = it1 :=
      alloc.vec.Vec.ext _ _ ((alloc.vec.Vec.from_val _ _).trans hitl.symm)
    unfold verified.merc_lts.incoming_transitions.count_incoming_loop.body
    rw [hnext, ← hnew]
    cases o with
    | none => simp at ho
    | some t' =>
      simp at ho
      subst t'
      simp [himutS, hzok]
      congr 1
  · rw [hzval, hget]
    norm_num

/-- `toCount` splits over `++`. -/
theorem toCount_append (a b : List Transition) (j : Nat) :
    toCount (a ++ b) j = toCount a j + toCount b j := by
  simp [toCount, List.filter_append, List.length_append]

/-- `toCount` of a singleton is that transition's tick. -/
theorem toCount_single (t : Transition) (j : Nat) : toCount [t] j = tick t j := by
  simpa [toCount_nil] using toCount_cons t [] j

/-- `IteratorIntoIter.next` on an exhausted vector reports `none` and hands the vector
    back. -/
private theorem vec_next_none {α : Type} (v : alloc.vec.Vec α) (h : v.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next (v : alloc.vec.into_iter.IntoIter α)
      ⦃ p => p.1 = none ∧ p.2 = v ⦄ := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all

/-- State of the `count_incoming` scan: the transitions still to visit and the counters. -/
abbrev CiSt := alloc.vec.into_iter.IntoIter Transition × alloc.vec.Vec Sz

/-- Invariant of the scan after `trans.val.length - st.1.val.length` transitions have been
    visited:
    * the rest of the iterator is the correspondingly dropped tail of `trans`;
    * the counters are as long as `c0`, and slot `j` holds `c0`'s slot `j` plus the
      number of already-visited transitions whose target is `j`;
    * those visited ticks and the not-yet-visited ones add up to the total, so the
      checked addition cannot overflow in the remaining steps either;
    * no slot can overflow. -/
def CiInv (trans : alloc.vec.Vec Transition) (c0 : alloc.vec.Vec Sz) : CiSt → Prop :=
  fun st =>
    st.1.val = trans.val.drop (trans.val.length - st.1.val.length) ∧
    st.2.val.length = c0.val.length ∧
    (∀ j, j < st.2.val.length →
      (st.2.val.getD j 0#usize).val = (c0.val.getD j 0#usize).val
        + toCount (trans.val.take (trans.val.length - st.1.val.length)) j) ∧
    (∀ j, j < st.2.val.length →
      toCount (trans.val.take (trans.val.length - st.1.val.length)) j
        + toCount (trans.val.drop (trans.val.length - st.1.val.length)) j = toCount trans.val j) ∧
    (∀ j, j < st.2.val.length →
      (c0.val.getD j 0#usize).val + toCount trans.val j ≤ Usize.max)

/-- On return, slot `j` of the counters holds `c0`'s slot `j` plus the number of
    transitions of `trans` whose target is `j`. -/
def CiPost (trans : alloc.vec.Vec Transition) (c0 : alloc.vec.Vec Sz)
    (counts : alloc.vec.Vec Sz) : Prop :=
  counts.val.length = c0.val.length ∧
  ∀ j, j < counts.val.length →
    (counts.val.getD j 0#usize).val = (c0.val.getD j 0#usize).val + toCount trans.val j

/-- The exhausted case of the inner counting loop: the counters are returned as they are. -/
theorem count_incoming_done (st : CiSt) (h : st.1.val = []) :
    verified.merc_lts.incoming_transitions.count_incoming_loop.body st.1 st.2
      = ok (done st.2) := by
  have hn : alloc.vec.into_iter.IteratorIntoIter.next
        (st.1 : alloc.vec.into_iter.IntoIter Transition)
      ⦃ p => p.1 = none ∧ p.2 = st.1 ⦄ := vec_next_none st.1 h
  rcases Std.WP.spec_imp_exists hn with ⟨p, hp, hpt⟩
  cases p with
  | mk o it1 =>
    simp only at hpt
    have hit1 : it1 = st.1 := hpt.2
    unfold verified.merc_lts.incoming_transitions.count_incoming_loop.body
    rw [hp, hpt.1, hit1]
    simp

/-- The `count_incoming` scan, run over a whole transition vector, returns the counters
    with slot `j` raised by the number of transitions of `trans` whose target is `j`. -/
theorem count_incoming_loop_spec (trans : alloc.vec.Vec Transition) (c0 : alloc.vec.Vec Sz)
    (hin : ∀ t, t ∈ trans.val → t.to.index.val < c0.val.length)
    (hovf : ∀ j, j < c0.val.length →
      (c0.val.getD j 0#usize).val + toCount trans.val j ≤ Usize.max) :
    ∃ (counts : alloc.vec.Vec Sz),
      (@loop CiSt (alloc.vec.Vec Sz)
        (fun p => verified.merc_lts.incoming_transitions.count_incoming_loop.body p.1 p.2)
        ((trans : alloc.vec.into_iter.IntoIter Transition), c0)) = ok counts ∧
      CiPost trans c0 counts := by
  have hspec : (@loop CiSt (alloc.vec.Vec Sz)
          (fun p => verified.merc_lts.incoming_transitions.count_incoming_loop.body p.1 p.2)
          ((trans : alloc.vec.into_iter.IntoIter Transition), c0)) ⦃ CiPost trans c0 ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : CiSt => st.1.val.length)
      (inv := CiInv trans c0)
      (post := CiPost trans c0)
      (body := fun p => verified.merc_lts.incoming_transitions.count_incoming_loop.body p.1 p.2)
      (x := (trans, c0))
    · intro st hinv
      rcases hinv with ⟨hiter, hlen, hval, hcons, hovf'⟩
      set k := trans.val.length - st.1.val.length with hkdef
      by_cases hnil : st.1.val = []
      · refine Std.WP.exists_imp_spec ⟨done st.2, count_incoming_done st hnil, ?_⟩
        refine ⟨hlen, ?_⟩
        intro j hj
        have hklen : k = trans.val.length := by
          have h1 := congrArg List.length hiter
          rw [hnil, List.length_nil, List.length_drop] at h1
          omega
        have hval' := hval j hj
        rw [hklen, List.take_length] at hval'
        exact hval'
      · obtain ⟨t, tl, hst⟩ := List.exists_cons_of_ne_nil hnil
        have hdrop : trans.val.drop k = t :: tl := hiter.symm.trans hst
        have hk : k = trans.val.length - (t :: tl).length := by
          rw [← hst]
        have hle : (t :: tl).length ≤ trans.val.length := by
          have h1 := congrArg List.length hdrop
          rw [List.length_drop] at h1
          omega
        have hmem : t ∈ trans.val.drop k := by
          rw [← hiter]
          exact hst.symm ▸ List.mem_cons_self
        have hlen1 : (t :: tl).length + k = trans.val.length := by
          rw [hk, Nat.add_comm]
          exact Nat.sub_add_cancel hle
        have hidx : t.to.index.val < st.2.val.length := by
          rw [hlen]
          exact hin t (List.mem_of_mem_drop hmem)
        have hmax : (st.2.val.getD t.to.index.val 0#usize).val + 1 ≤ Usize.max := by
          have hv := hval t.to.index.val hidx
          have hc := hcons t.to.index.val hidx
          have ho := hovf' t.to.index.val hidx
          have hedrop : 1 ≤ toCount (trans.val.drop k) t.to.index.val :=
            toCount_pos_of_mem hmem
          have h1 : 1 ≤ toCount (trans.val.take k) t.to.index.val
              + toCount (trans.val.drop k) t.to.index.val := by omega
          omega
        rcases count_incoming_step st.1 st.2 t tl hst hidx hmax with
          ⟨iter1, counts1, z, hbody, hit1, hset, hz⟩
        have hiter' : tl = trans.val.drop (k + 1) := by
          have h1 : (trans.val.drop k).drop 1 = trans.val.drop (k + 1) := by
            simp [Nat.add_comm]
          rw [← h1, ← hiter, hst]
          rfl
        have hk1 : trans.val.length - iter1.val.length = k + 1 := by
          rw [hit1]
          have h1 : (t :: tl).length = tl.length + 1 := by simp
          omega
        have hiter'' : iter1.val = trans.val.drop (trans.val.length - iter1.val.length) := by
          calc iter1.val = tl := hit1
            _ = trans.val.drop (k + 1) := hiter'
            _ = trans.val.drop (trans.val.length - iter1.val.length) := by rw [hk1]
        refine Std.WP.exists_imp_spec
          ⟨cont (iter1, counts1), hbody, ⟨hiter'', ?_, ?_, ?_, ?_⟩, ?_⟩
        · -- the counters keep their length
          rw [hset, List.length_set, hlen]
        · -- slot-wise: one more tick
          intro j hj
          have hj' : j < st.2.val.length := by
            rw [hset, List.length_set] at hj
            exact hj
          have hshape : trans.val = trans.val.take k ++ t :: tl := by
            calc trans.val = trans.val.take k ++ trans.val.drop k :=
                  (List.take_append_drop k trans.val).symm
              _ = trans.val.take k ++ st.1.val := by rw [hiter]
              _ = trans.val.take k ++ t :: tl := by rw [hst]
          have htake : trans.val.take (k + 1) = trans.val.take k ++ [t] :=
            take_head trans.val k t tl hshape
          have hget := getD_set st.2.val t.to.index.val j z 0#usize hj'
          rw [hset, hget]
          have htake' : trans.val.take (trans.val.length - iter1.val.length)
              = trans.val.take k ++ [t] := by rw [hk1, htake]
          by_cases hji : j = t.to.index.val
          · subst hji
            rw [if_pos rfl, hz, hval t.to.index.val hidx, htake', toCount_append, toCount_single]
            simp [tick]
            omega
          · have hne : t.to.index.val ≠ j := by omega
            rw [if_neg hji, hval j hj', htake', toCount_append, toCount_single]
            simp [tick, hne]
        · -- the visited and unvisited ticks still add up
          intro j hj
          have hj' : j < st.2.val.length := by
            rw [hset, List.length_set] at hj
            exact hj
          rw [hk1, ← hiter']
          have hshape : trans.val = trans.val.take k ++ t :: tl := by
            calc trans.val = trans.val.take k ++ trans.val.drop k :=
                  (List.take_append_drop k trans.val).symm
              _ = trans.val.take k ++ st.1.val := by rw [hiter]
              _ = trans.val.take k ++ t :: tl := by rw [hst]
          have hcat : trans.val.take (k + 1) ++ tl = trans.val := by
            calc trans.val.take (k + 1) ++ tl
                = (trans.val.take k ++ [t]) ++ tl := by rw [take_head trans.val k t tl hshape]
                _ = trans.val.take k ++ (t :: tl) := by simp
                _ = trans.val := hshape.symm
          calc toCount (trans.val.take (k + 1)) j + toCount tl j
              = toCount (trans.val.take (k + 1) ++ tl) j := (toCount_append _ _ j).symm
            _ = toCount trans.val j := by rw [hcat]
        · -- the overflow bound is inherited
          intro j hj
          rw [hset, List.length_set] at hj
          exact hovf' j hj
        · -- the rest of the iterator got shorter
          rw [hit1, hst]
          simp
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [List.drop_zero]
      · rfl
      · intro j hj
        simp [List.take_zero, toCount_nil]
      · intro j hj
        simp [List.take_zero, toCount_nil, List.drop_zero]
      · exact hovf
  rcases Std.WP.spec_imp_exists hspec with ⟨p, hloop, hpost⟩
  exact ⟨p, hloop, hpost⟩

/-- `count_incoming_loop` in equation form. -/
theorem count_incoming_spec (trans : alloc.vec.Vec Transition) (c0 : alloc.vec.Vec Sz)
    (hin : ∀ t, t ∈ trans.val → t.to.index.val < c0.val.length)
    (hovf : ∀ j, j < c0.val.length →
      (c0.val.getD j 0#usize).val + toCount trans.val j ≤ Usize.max) :
    ∃ (counts : alloc.vec.Vec Sz),
      verified.merc_lts.incoming_transitions.count_incoming_loop trans c0 = ok counts ∧
      CiPost trans c0 counts := by
  rcases count_incoming_loop_spec trans c0 hin hovf with ⟨counts, hloop, hpost⟩
  refine ⟨counts, ?_, hpost⟩
  unfold verified.merc_lts.incoming_transitions.count_incoming_loop
  rw [hloop]

/-! ### The outer scan: `count_all_incoming`

`count_all_incoming` (`:163`) runs the per-state scan `count_incoming` (proved above as
`count_incoming_spec`) once per state the LTS enumerates. So the outer loop only has to keep
track of *how many states* it has visited: "the transitions counted so far" becomes "the
transitions of the states counted so far", and the per-state invariant is reused verbatim in the
form `CiPost` of one state on top of the counters reached so far.

Both hypotheses of the inner scan are discharged here as well: the target bound from the
per-state hypothesis, and the overflow bound from the bound for the whole state list, since one
state's tick is one summand of `seenCount`. -/

/-- The transitions a state contributes to the count: whatever `outgoing_transitions` reports
    for it, or nothing when that call fails. -/
def outVec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (s : TagIndex Sz StateTag) : alloc.vec.Vec Transition :=
  @Result.cases (alloc.vec.Vec Transition) (fun _ => alloc.vec.Vec Transition)
    (LTSInst.outgoing_transitions sys s)
    (fun ts => ts) (fun _ _ => alloc.vec.Vec.new Transition)
    (alloc.vec.Vec.new Transition)

/-- A successful `outgoing_transitions` call reports exactly the state's contribution. -/
theorem outVec_of_ok {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (h : LTSInst.outgoing_transitions sys s = ok ts) :
    outVec LTSInst sys s = ts := by
  show @Result.cases (alloc.vec.Vec Transition) (fun _ => alloc.vec.Vec Transition)
      (LTSInst.outgoing_transitions sys s)
      (fun ts => ts) (fun _ _ => alloc.vec.Vec.new Transition)
    (alloc.vec.Vec.new Transition) = ts
  rw [h]
  rfl

/-- Hence, for a successful call, the call reports `outVec` itself. -/
theorem outVec_eq_ok {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (h : LTSInst.outgoing_transitions sys s = ok ts) :
    LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s) := by
  have h2 : outVec LTSInst sys s = ts := outVec_of_ok LTSInst sys s ts h
  rw [h, h2]

/-- The number of transitions towards slot `j` that the first `k` states of `states`
    contribute. -/
def seenCount {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (k j : Nat) : Nat :=
  ((states.take k).map (fun s => toCount (outVec LTSInst sys s).val j)).sum

/-- Before any state is visited nothing has been counted. -/
theorem seenCount_zero {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (j : Nat) : seenCount LTSInst sys states 0 j = 0 := by
  simp [seenCount]

/-- Visiting one state more adds exactly that state's transitions towards `j`. -/
theorem seenCount_succ {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (k : Nat) (s : TagIndex Sz StateTag)
    (tl : List (TagIndex Sz StateTag)) (j : Nat) (h : states = states.take k ++ s :: tl) :
    seenCount LTSInst sys states (k + 1) j
      = toCount (outVec LTSInst sys s).val j + seenCount LTSInst sys states k j := by
  have hmin : min k states.length = k := by
    by_cases hkl : k ≤ states.length
    · exact Nat.min_eq_left hkl
    · have h2 := congrArg List.length h
      rw [List.length_append, List.length_cons, List.length_take,
        Nat.min_eq_right (by omega)] at h2
      omega
  have hg : states[k]? = some s := by
    rw [h, List.getElem?_append_right (by
          rw [List.length_take]
          exact Nat.min_le_left k states.length),
        List.length_take, hmin]
    simp
  have ht : List.take (k + 1) states = List.take k states ++ [s] := by
    rw [List.take_add_one, hg]
    rfl
  unfold seenCount
  rw [ht, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_singleton]
  omega

/-- Counting more states can only add ticks. -/
theorem seenCount_mono {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (k m j : Nat) (h : k ≤ m) :
    seenCount LTSInst sys states k j ≤ seenCount LTSInst sys states m j := by
  have h1 : seenCount LTSInst sys states m j
      = ((List.take k states).map (fun s => toCount (outVec LTSInst sys s).val j)).sum
        + (((List.take m states).drop k).map
            (fun s => toCount (outVec LTSInst sys s).val j)).sum := by
    unfold seenCount
    calc ((List.take m states).map (fun s => toCount (outVec LTSInst sys s).val j)).sum
        = ((List.take k (List.take m states) ++ (List.take m states).drop k).map
            (fun s => toCount (outVec LTSInst sys s).val j)).sum := by
            rw [List.take_append_drop k (List.take m states)]
      _ = ((List.take k states ++ (List.take m states).drop k).map
            (fun s => toCount (outVec LTSInst sys s).val j)).sum := by
            rw [List.take_take, Nat.min_eq_left h]
      _ = ((List.take k states).map (fun s => toCount (outVec LTSInst sys s).val j)).sum
          + (((List.take m states).drop k).map
              (fun s => toCount (outVec LTSInst sys s).val j)).sum := by
            rw [List.map_append, List.sum_append]
  rw [h1]
  have h2 : 0 ≤ (((List.take m states).drop k).map
      (fun s => toCount (outVec LTSInst sys s).val j)).sum :=
    List.sum_nonneg (fun s _ => Nat.zero_le _)
  unfold seenCount
  omega

/-- State of the outer counting loop: the states still to visit and the counters. -/
abbrev CaSt := alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag) × alloc.vec.Vec Sz

/-- Invariant of the outer scan after `states.length - st.1.val.length` states have been
    visited:
    * the rest of the iterator is the correspondingly dropped tail of `states`;
    * the counters are as long as `c0`, and slot `j` holds `c0`'s slot `j` plus the number
      of transitions towards `j` that the visited states contribute;
    * no slot can overflow, because the total over all of `states` is representable. -/
def CaInv {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (c0 : alloc.vec.Vec Sz) : CaSt → Prop :=
  fun st =>
    st.1.val = states.drop (states.length - st.1.val.length) ∧
    st.2.val.length = c0.val.length ∧
    (∀ j, j < st.2.val.length →
      (st.2.val.getD j 0#usize).val = (c0.val.getD j 0#usize).val
        + seenCount LTSInst sys states (states.length - st.1.val.length) j) ∧
    (∀ j, j < st.2.val.length →
      (c0.val.getD j 0#usize).val + seenCount LTSInst sys states states.length j ≤ Usize.max)

/-- On return, slot `j` of the counters holds `c0`'s slot `j` plus the number of transitions
    towards `j` that *all* of `states` contribute. -/
def CaPost {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (c0 counts : alloc.vec.Vec Sz) : Prop :=
  counts.val.length = c0.val.length ∧
  ∀ j, j < counts.val.length →
    (counts.val.getD j 0#usize).val = (c0.val.getD j 0#usize).val
      + seenCount LTSInst sys states states.length j

/-- The exhausted case of the outer loop: the counters are returned as they are, and by the
    invariant they already hold every state's contribution. -/
theorem count_all_incoming_done {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (c0 : alloc.vec.Vec Sz) (st : CaSt)
    (h : st.1.val = []) (hinv : CaInv LTSInst sys states c0 st) :
    verified.merc_lts.incoming_transitions.count_all_incoming_loop.body
        LTSInst sys st.1 st.2 = ok (done st.2) ∧
      CaPost LTSInst sys states c0 st.2 := by
  have hn : alloc.vec.into_iter.IteratorIntoIter.next
        (st.1 : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag))
      ⦃ p => p.1 = none ∧ p.2 = st.1 ⦄ := vec_next_none st.1 h
  rcases Std.WP.spec_imp_exists hn with ⟨p, hp, hpt⟩
  cases p with
  | mk o it1 =>
    simp only at hpt
    have hit1 : it1 = st.1 := hpt.2
    refine ⟨?_, ?_⟩
    · unfold verified.merc_lts.incoming_transitions.count_all_incoming_loop.body
      rw [hp, hpt.1, hit1]
      simp
    · rcases hinv with ⟨hiter, hlen, hval, hovf⟩
      refine ⟨hlen, ?_⟩
      intro j hj
      have hz : states.drop (states.length - st.1.val.length) = [] := hiter.symm.trans h
      have h1 : states.length - (states.length - st.1.val.length) = 0 := by
        rw [← List.length_drop, hz, List.length_nil]
      have hklen : states.length - st.1.val.length = states.length := by omega
      have hval' := hval j hj
      rw [hklen] at hval'
      exact hval'

/-- One state of the outer scan: `count_incoming` runs on the state just read, and the
    counters come back with that state's transitions added, so the new counters satisfy
    `CiPost` for that state on top of the old ones. -/
theorem count_all_incoming_step {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (v : alloc.vec.Vec (TagIndex Sz StateTag)) (counts : alloc.vec.Vec Sz)
    (s : TagIndex Sz StateTag) (tl : List (TagIndex Sz StateTag))
    (hiter : v.val = s :: tl)
    (hout : LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hin : ∀ t, t ∈ (outVec LTSInst sys s).val → t.to.index.val < counts.val.length)
    (hmax : ∀ j, j < counts.val.length →
      (counts.val.getD j 0#usize).val + toCount (outVec LTSInst sys s).val j ≤ Usize.max) :
    ∃ (iter1 : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag))
      (counts1 : alloc.vec.Vec Sz),
      verified.merc_lts.incoming_transitions.count_all_incoming_loop.body
          LTSInst sys v counts
        = ok (cont (iter1, counts1)) ∧
      iter1.val = tl ∧
      CiPost (outVec LTSInst sys s) counts counts1 := by
  rcases count_incoming_spec (outVec LTSInst sys s) counts hin hmax with
    ⟨counts1, hinner, hpost⟩
  rcases vec_next_eq v s tl hiter with ⟨o, it1, hnext, ho, hitl⟩
  have hcount : verified.merc_lts.incoming_transitions.count_incoming
      LTSInst sys s counts = ok counts1 := by
    unfold verified.merc_lts.incoming_transitions.count_incoming
    simp only [hout, alloc.vec.IntoIteratorVec.into_iter, bind_tc_ok]
    exact hinner
  refine ⟨it1, counts1, ?_, hitl, hpost⟩
  unfold verified.merc_lts.incoming_transitions.count_all_incoming_loop.body
  rw [hnext]
  simp [ho, hcount]

/-- `count_all_incoming_loop`, run over a whole state vector: on return, slot `j` of the
    counters holds `c0`'s slot `j` plus the number of transitions towards `j` that the
    enumerated states report. -/
theorem count_all_incoming_loop_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (c0 : alloc.vec.Vec Sz)
    (hout : ∀ s, LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hin : ∀ s, s ∈ sv.val → ∀ t, t ∈ (outVec LTSInst sys s).val → t.to.index.val < c0.val.length)
    (hovf : ∀ j, j < c0.val.length →
      (c0.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j ≤ Usize.max) :
    ∃ (counts : alloc.vec.Vec Sz),
      (@loop CaSt (alloc.vec.Vec Sz)
        (fun p => verified.merc_lts.incoming_transitions.count_all_incoming_loop.body
          LTSInst sys p.1 p.2)
        ((sv : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag)), c0)) = ok counts ∧
      CaPost LTSInst sys sv.val c0 counts := by
  have hspec : (@loop CaSt (alloc.vec.Vec Sz)
          (fun p => verified.merc_lts.incoming_transitions.count_all_incoming_loop.body
            LTSInst sys p.1 p.2)
          ((sv : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag)), c0))
        ⦃ CaPost LTSInst sys sv.val c0 ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : CaSt => st.1.val.length)
      (inv := CaInv LTSInst sys sv.val c0)
      (post := CaPost LTSInst sys sv.val c0)
      (body := fun p => verified.merc_lts.incoming_transitions.count_all_incoming_loop.body
        LTSInst sys p.1 p.2)
      (x := (sv, c0))
    · intro st hinv
      rcases hinv with ⟨hiter, hlen, hval, hovf'⟩
      have hinv' : CaInv LTSInst sys sv.val c0 st := ⟨hiter, hlen, hval, hovf'⟩
      set k := sv.val.length - st.1.val.length with hkdef
      by_cases hnil : st.1.val = []
      · rcases count_all_incoming_done LTSInst sys sv.val c0 st hnil hinv' with
          ⟨hbody, hpost⟩
        exact Std.WP.exists_imp_spec ⟨done st.2, hbody, hpost⟩
      · obtain ⟨s, sl, hst⟩ := List.exists_cons_of_ne_nil hnil
        have hdrop : sv.val.drop k = s :: sl := hiter.symm.trans hst
        have hle : (s :: sl).length ≤ sv.val.length := by
          have h1 := congrArg List.length hdrop
          rw [List.length_drop] at h1
          omega
        have hpos : 0 < (s :: sl).length := by
          rw [List.length_cons]
          omega
        have hksub : k ≤ sv.val.length := by
          have h1 := congrArg List.length hiter
          rw [List.length_drop] at h1
          omega
        have hmem : s ∈ sv.val.drop k := by
          rw [← hiter]
          rw [hst]
          exact List.mem_cons_self
        have hshape : sv.val = sv.val.take k ++ s :: sl := by
          calc sv.val = sv.val.take k ++ sv.val.drop k :=
                (List.take_append_drop k sv.val).symm
            _ = sv.val.take k ++ st.1.val := by rw [hiter]
            _ = sv.val.take k ++ s :: sl := by rw [hst]
        have hsucc (j : Nat) : seenCount LTSInst sys sv.val (k + 1) j
            = toCount (outVec LTSInst sys s).val j + seenCount LTSInst sys sv.val k j :=
          seenCount_succ LTSInst sys sv.val k s sl j hshape
        have hstlen : st.1.val.length = sl.length + 1 := by rw [hst]; simp
        have hmax : ∀ j, j < st.2.val.length →
            (st.2.val.getD j 0#usize).val + toCount (outVec LTSInst sys s).val j ≤ Usize.max := by
          intro j hj
          have hv := hval j hj
          have ho := hovf' j hj
          have hpos' : 0 < sl.length + 1 := by
            have : sl.length + 1 = (s :: sl).length := by simp
            rw [this]; exact hpos
          have hmono : toCount (outVec LTSInst sys s).val j
              + seenCount LTSInst sys sv.val k j
                ≤ seenCount LTSInst sys sv.val sv.val.length j := by
            have h1 := seenCount_mono LTSInst sys sv.val (k + 1) sv.val.length j
              (by rw [hkdef, hstlen]; omega)
            rwa [hsucc j] at h1
          rw [hv]
          omega
        rcases count_all_incoming_step LTSInst sys st.1 st.2 s sl hst (hout s)
            (fun t ht => by rw [hlen]; exact hin s (List.mem_of_mem_drop hmem) t ht) hmax with
          ⟨iter1, counts1, hbody, hit1, hpost⟩
        have hle' : sl.length + 1 ≤ sv.val.length := by
          have h1 : (s :: sl).length = sl.length + 1 := by simp
          calc sl.length + 1 = (s :: sl).length := h1.symm
            _ ≤ sv.val.length := hle
        have hk1 : sv.val.length - iter1.val.length = k + 1 := by
          rw [hit1]
          rw [hkdef, hstlen]
          omega
        have hiter'' : iter1.val = sv.val.drop (sv.val.length - iter1.val.length) := by
          calc iter1.val = sl := hit1
            _ = sv.val.drop (k + 1) := by
              have h1 : (sv.val.drop k).drop 1 = sv.val.drop (k + 1) := by
                simp [Nat.add_comm]
              rw [← h1, ← hiter, hst]
              rfl
            _ = sv.val.drop (sv.val.length - iter1.val.length) := by rw [hk1]
        have hinv'' : CaInv LTSInst sys sv.val c0 (iter1, counts1) := by
          unfold CaInv
          refine ⟨hiter'', ?_, ?_, ?_⟩
          · exact hpost.1.trans hlen
          · intro j hj
            have hj2 : j < counts1.val.length := hj
            have hj' := lt_of_lt_of_eq hj2 hpost.1
            have hv := hval j hj'
            have hpc := hpost.2 j hj2
            have hpair : (iter1, counts1).2 = counts1 := rfl
            rw [hpair, hk1, hsucc j]
            omega
          · intro j hj
            have hj2 : j < counts1.val.length := hj
            exact hovf' j (lt_of_lt_of_eq hj2 hpost.1)
        refine Std.WP.exists_imp_spec ⟨cont (iter1, counts1), hbody, hinv'', ?_⟩
        · rw [hit1, hst]
          simp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [List.drop_zero]
      · rfl
      · intro j hj
        simp [seenCount_zero]
      · exact hovf
  rcases Std.WP.spec_imp_exists hspec with ⟨p, hloop, hpost⟩
  exact ⟨p, hloop, hpost⟩

/-- `count_all_incoming_loop` in equation form. -/
theorem count_all_incoming_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (c0 : alloc.vec.Vec Sz)
    (hout : ∀ s, LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hin : ∀ s, s ∈ sv.val → ∀ t, t ∈ (outVec LTSInst sys s).val → t.to.index.val < c0.val.length)
    (hovf : ∀ j, j < c0.val.length →
      (c0.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j ≤ Usize.max) :
    ∃ (counts : alloc.vec.Vec Sz),
      verified.merc_lts.incoming_transitions.count_all_incoming_loop
          LTSInst (sv : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag)) sys c0 = ok counts ∧
      CaPost LTSInst sys sv.val c0 counts := by
  rcases count_all_incoming_loop_spec LTSInst sys sv c0 hout hin hovf with ⟨counts, hloop, hpost⟩
  refine ⟨counts, ?_, hpost⟩
  unfold verified.merc_lts.incoming_transitions.count_all_incoming_loop
  rw [hloop]

/-- `count_all_incoming` over the states the LTS reports. -/
theorem count_all_incoming_state_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (c0 : alloc.vec.Vec Sz)
    (hiter : LTSInst.iter_states sys = ok sv)
    (hout : ∀ s, LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hin : ∀ s, s ∈ sv.val → ∀ t, t ∈ (outVec LTSInst sys s).val → t.to.index.val < c0.val.length)
    (hovf : ∀ j, j < c0.val.length →
      (c0.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j ≤ Usize.max) :
    ∃ (counts : alloc.vec.Vec Sz),
      verified.merc_lts.incoming_transitions.count_all_incoming LTSInst sys c0 = ok counts ∧
      CaPost LTSInst sys sv.val c0 counts := by
  rcases count_all_incoming_spec LTSInst sys sv c0 hout hin hovf with ⟨counts, hloop, hpost⟩
  refine ⟨counts, ?_, hpost⟩
  unfold verified.merc_lts.incoming_transitions.count_all_incoming
  simp only [hiter, alloc.vec.IntoIteratorVec.into_iter, bind_tc_ok]
  exact hloop

/-! ## A generic "for `i` in `[0, n)`, gather `source[i]`" loop

`copy_prefix_loop` reads slot `i` of a source vector and appends it to a fresh
accumulator. `place_all_incoming`'s and `sort_all_incoming`'s outer loops have the same
shape (a range plus a mutable accumulator), so the induction is done once here. -/

/-- Invariant of the gather loop: the range's end is pinned to `n`, `start` has not
    overrun it, and the accumulator holds `f 0, …, f (start-1)`.

    `f` is a total `Nat → α`, and the accumulator is read through the total `List.getD`
    with fallback `d`, so no index needs a bound proof anywhere in the statement; the
    caller discharges the bounds once, turning the post back into `getElem`. -/
def gatherInv {α : Type} (n : Sz) (f : Nat → α) (d : α) :
    ItSz × alloc.vec.Vec α → Prop :=
  fun st =>
    st.1.end = n ∧ st.1.start.val ≤ n.val ∧ st.2.val.length = st.1.start.val ∧
      (∀ k, k < st.1.start.val → st.2.val.getD k d = f k)

/-- A loop whose body is "advance the range, or stop; append `f start` and continue"
    copies `f 0, …, f (n-1)` into the accumulator. -/
theorem gather_loop_spec {α : Type} (n : Sz) (f : Nat → α) (d : α) (hn : n.val < Usize.max)
    (body : ItSz → alloc.vec.Vec α → Result (ControlFlow (ItSz × alloc.vec.Vec α) (alloc.vec.Vec α)))
    (hstep : ∀ (it : ItSz) (v : alloc.vec.Vec α), it.end = n →
      v.val.length < Usize.max → it.start.val < it.end.val →
      v.val.length = it.start.val →
      ∃ (it1 : ItSz) (v1 : alloc.vec.Vec α),
        body it v = ok (cont (it1, v1)) ∧
        it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
        v1.val = v.val ++ [f it.start.val])
    (hdone : ∀ (it : ItSz) (v : alloc.vec.Vec α), it.end.val ≤ it.start.val →
      body it v = ok (done v)) :
    Aeneas.Std.WP.spec
        (@loop (ItSz × alloc.vec.Vec α) (alloc.vec.Vec α) (fun p => body p.1 p.2)
          ({ start := 0#usize, «end» := n }, alloc.vec.Vec.new α))
        (fun r : alloc.vec.Vec α =>
          r.val.length = n.val ∧ ∀ k, k < n.val → r.val.getD k d = f k) := by
  apply loop.spec_decr_nat
    (measure := constPushMeasure)
    (inv := gatherInv n f d)
    (post := fun r : alloc.vec.Vec α =>
      r.val.length = n.val ∧ ∀ k, k < n.val → r.val.getD k d = f k)
    (body := fun p => body p.1 p.2)
    (x := ({ start := 0#usize, «end» := n }, alloc.vec.Vec.new α))
  · intro st hinv
    rcases hinv with ⟨hend, hle, hlen, hpt⟩
    by_cases hlt : st.1.start.val < st.1.end.val
    · have hlen2 : st.2.val.length < Usize.max := by omega
      rcases hstep st.1 st.2 hend hlen2 hlt hlen with ⟨it1, v1, hbody, hstart, hend', hvval⟩
      have hinv' : gatherInv n f d (it1, v1) := by
        refine ⟨hend'.trans hend, ?_, ?_, ?_⟩
        · change it1.start.val ≤ n.val
          rw [hstart]
          have hltn : st.1.start.val < n.val := by simpa [hend] using hlt
          omega
        · change v1.val.length = it1.start.val
          simp [hvval, hlen, hstart]
        · change ∀ k, k < it1.start.val → v1.val.getD k d = f k
          intro k hk
          rw [hvval]
          rcases Nat.lt_or_ge k st.2.val.length with hkl | hkl
          · rw [List.getD_append _ _ d k hkl, hpt k (by omega)]
          · have hk1 : k < st.2.val.length + 1 := by omega
            rw [show k = st.2.val.length by omega]
            simp [hlen]
      have hlt' : constPushMeasure (it1, v1) < constPushMeasure st := by
        change (it1.end.val - it1.start.val) < (st.1.end.val - st.1.start.val)
        rw [hstart, hend', hend]
        rw [hend] at hlt
        omega
      exact Std.WP.exists_imp_spec ⟨cont (it1, v1), hbody, hinv', hlt'⟩
    · have hge : st.1.end.val ≤ st.1.start.val := by omega
      have hstart : st.1.start.val = n.val := by
        apply Nat.le_antisymm hle
        rw [← hend]; exact hge
      have hpost : st.2.val.length = n.val ∧ ∀ k, k < n.val → st.2.val.getD k d = f k := by
        refine ⟨hlen ▸ hstart, fun k hk => hpt k (by omega)⟩
      exact Std.WP.exists_imp_spec ⟨done st.2, hdone st.1 st.2 hge, hpost⟩
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro k hk
      exact absurd hk (by simp)

/-- One iteration of `copy_prefix_loop.body`. -/
theorem copy_prefix_step (source : alloc.vec.Vec Sz) (it : ItSz) (r : alloc.vec.Vec Sz)
    (hidx : it.start.val < source.val.length) (hlen : r.val.length < Usize.max)
    (h : it.start.val < it.end.val) :
    ∃ (it1 : ItSz) (r1 : alloc.vec.Vec Sz),
      verified.merc_lts.incoming_transitions.copy_prefix_loop.body source it r
        = ok (cont (it1, r1)) ∧
      it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
      r1.val = r.val ++ [source.val[it.start.val]] := by
  have hnext := next_range_some it h
  rcases hnext with ⟨o, it1, hnext_e, hopt, hstart', hend'⟩
  have hidx' := Aeneas.Std.alloc.vec.Vec.index_usize_spec source it.start hidx
  rcases Std.WP.spec_imp_exists hidx' with ⟨x, hx, hxv⟩
  have hidx_u : source.index_usize it.start = ok (source.val[it.start.val]) := by
    rw [hx, hxv]
  have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Sz) source it.start
      = ok (source.val[it.start.val]) := by
    simpa [alloc.vec.Vec.index_slice_index] using hidx_u
  rcases vec_push_val r (source.val[it.start.val]) hlen with ⟨r1, hpush, hr1⟩
  refine ⟨it1, r1, ?_, hstart', hend', hr1⟩
  unfold verified.merc_lts.incoming_transitions.copy_prefix_loop.body
  rw [hnext_e]
  simp [hopt, hidx_u, hpush]

/-- The `end ≤ start` case: the range is exhausted and the accumulator is returned. -/
theorem copy_prefix_done (source : alloc.vec.Vec Sz) (it : ItSz) (r : alloc.vec.Vec Sz)
    (hge : it.end.val ≤ it.start.val) :
    verified.merc_lts.incoming_transitions.copy_prefix_loop.body source it r
      = ok (done r) := by
  have hnext := next_range_none it hge
  rcases hnext with ⟨o, it1, hnext_e, hopt, hident⟩
  unfold verified.merc_lts.incoming_transitions.copy_prefix_loop.body
  rw [hnext_e]
  simp [hopt, hident]

/-- `copy_prefix_loop source [0, n)` copies `source`'s first `n` slots, in order. -/
theorem copy_prefix_spec (n : Sz) (source : alloc.vec.Vec Sz)
    (hn : n.val < Usize.max) (hsrc : n.val ≤ source.val.length) :
    Aeneas.Std.WP.spec
      (verified.merc_lts.incoming_transitions.copy_prefix_loop
        { start := 0#usize, «end» := n } source (alloc.vec.Vec.new Sz))
      (fun r : alloc.vec.Vec Sz =>
        r.val.length = n.val ∧
          ∀ k, k < n.val → r.val.getD k 0#usize = source.val.getD k 0#usize) := by
  exact gather_loop_spec n (fun i => source.val.getD i 0#usize) (0#usize : Sz) hn
    (fun it v => verified.merc_lts.incoming_transitions.copy_prefix_loop.body source it v)
    (fun it r hend hlen hlt hvlen => by
      have hidx : it.start.val < source.val.length := by
        rw [hend] at hlt
        omega
      rcases copy_prefix_step source it r hidx hlen hlt with
        ⟨it1, r1, hbody, hs, he, hv⟩
      refine ⟨it1, r1, hbody, hs, he, ?_⟩
      rw [hv, List.getD_eq_getElem source.val _ hidx])
    (fun it r hge => copy_prefix_done source it r hge)

/-- The `getElem` reading of `copy_prefix_spec`: for every in-range index, the copy
    agrees with the source. Both bounds are hypotheses, so the statement needs no
    length side conditions. -/
theorem copy_prefix_getElem (n : Sz) (source : alloc.vec.Vec Sz) (r : alloc.vec.Vec Sz)
    (hlen : r.val.length = n.val)
    (hpt : ∀ k, k < n.val → r.val.getD k 0#usize = source.val.getD k 0#usize) :
    ∀ k (hk : k < r.val.length) (hs : k < source.val.length),
      r.val[k]'hk = source.val[k]'hs := by
  intro k hk hs
  exact (List.getD_eq_getElem r.val _ hk).symm.trans
    ((hpt k (by omega)).trans (List.getD_eq_getElem source.val _ hs))

/-! ## Stage 6: `place_all_incoming`

`place_all_incoming` (`incoming_transitions.rs:193`) runs `place_incoming` (`:227`) once per
state `iter_states` reports, and `place_incoming` walks the transitions
`outgoing_transitions` reports for that state, writing each one at the current cursor of its
*target* and bumping that cursor. So the `(label, source)` pair of the `i`-th transition
towards `j` lands at `r[j] + (how many transitions towards `j` came before)`.

The invariant is therefore stated as an exact list equality per CSR slot, which is what
`IncomingTransitionsCorrect` asks for:

* `pairAt`/`slotEntries` read the two flat arrays as one list of pairs, `slotEntries a b`
  being the pairs at the positions `[a, b)`. A slot's range is thus a *list*, and "the
  slot holds the transitions that target it" is an equation between lists, with no
  extensionality or `List.Perm` reasoning in the way.
* The cursor equation `cursor[j] = r[j] + (placed towards j)` turns "the next free position
  of slot `j`" into a number, which is what the generated code computes.
* The two together are enough to read off the ranges: at the end of the outer loop the
  cursor of slot `j` *is* `r[j+1]`, because `r[j+1] = r[j] + counts[j]` (`natSum_succ`)
  and `counts[j]` is the total number of transitions towards `j`.

The first building blocks below are pure list lemmas about that reading. -/

/-- The two flat arrays, read as one list of pairs: the pair stored at position `p`. -/
def pairAt (labels : List (TagIndex Sz LabelTag)) (src : List (TagIndex Sz StateTag))
    (p : Nat) : (TagIndex Sz LabelTag × TagIndex Sz StateTag) :=
  (labels.getD p zeroLabel, src.getD p zeroState)

/-- The pairs stored at the positions `[a, b)`. Empty when `b ≤ a`, which is what makes
    the read total: an out-of-range position reads back as the zeroed `TagIndex` that a
    freshly allocated slot holds. -/
def slotEntries (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (a b : Nat) : List (TagIndex Sz LabelTag × TagIndex Sz StateTag) :=
  (List.range' a (b - a)).map (fun p => pairAt labels src p)

/-- `List.getD` reading a `List.set` at the written position, with no bound on the list:
    past-the-end reads back as the default on both sides. -/
private lemma gds_self {α : Type} (l : List α) (i : Nat) (x d : α) :
    (l.set i x).getD i d = if i < l.length then x else d := by
  show (l.set i x)[i]?.getD d = if i < l.length then x else d
  rw [List.getElem?_set_self']
  by_cases hlt : i < l.length
  · simp [hlt]
  · rw [List.getElem?_eq_none (by omega)]
    simp [hlt]

/-- `List.getD` reading a `List.set` anywhere else, again with no bound on the list. -/
private lemma gds_ne {α : Type} (l : List α) (i k : Nat) (x d : α) (hne : k ≠ i) :
    (l.set i x).getD k d = l.getD k d := by
  show (l.set i x)[k]?.getD d = l[k]?.getD d
  rw [List.getElem?_set, if_neg (Ne.symm hne)]

/-- `List.range'` loses no element when one position is appended. -/
theorem range'_append_succ (a m : Nat) : List.range' a (m + 1) = List.range' a m ++ [a + m] := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
      have h1 : List.range' a (m + 2) = a :: List.range' (a + 1) (m + 1) := List.range'_succ
      have h2 : List.range' a (m + 1) = a :: List.range' (a + 1) m := List.range'_succ
      have h3 := ih (a + 1)
      rw [h1, h2, h3]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- A slot whose end does not pass its start holds nothing. -/
theorem slotEntries_of_le (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (a b : Nat) (hba : b ≤ a) :
    slotEntries labels src a b = [] := by
  unfold slotEntries
  simp [Nat.sub_eq_zero_of_le hba]

/-- One more position in a slot. The bound is what makes the statement hold: without
    `a ≤ b` the new position can fall outside `[a, b+1)` altogether. -/
theorem slotEntries_succ (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (a b : Nat) (hab : a ≤ b) :
    slotEntries labels src a (b + 1) = slotEntries labels src a b ++ [pairAt labels src b] := by
  unfold slotEntries
  have h : (b + 1) - a = (b - a) + 1 := by omega
  have hab' : a + (b - a) = b := Nat.add_sub_of_le hab
  rw [h, range'_append_succ, List.map_append, List.map_cons, hab']
  simp

/-- A pair read off a written array at an untouched position is the old pair. -/
theorem pairAt_set_ne (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (p q : Nat) (x : TagIndex Sz LabelTag)
    (y : TagIndex Sz StateTag) (hpq : p ≠ q) :
    pairAt (labels.set q x) (src.set q y) p = pairAt labels src p := by
  unfold pairAt
  rw [gds_ne labels q p x zeroLabel hpq, gds_ne src q p y zeroState hpq]

/-- A pair read off a written array at the written position is the new pair. -/
theorem pairAt_set_self (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (p : Nat) (x : TagIndex Sz LabelTag)
    (y : TagIndex Sz StateTag) (hp : p < labels.length) (hp' : p < src.length) :
    pairAt (labels.set p x) (src.set p y) p = (x, y) := by
  unfold pairAt
  rw [gds_self labels p x zeroLabel, gds_self src p y zeroState, if_pos hp, if_pos hp']

/-- A write outside a slot's range leaves the slot alone. -/
theorem slotEntries_set_of_lt_or_ge (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (p a b : Nat) (x : TagIndex Sz LabelTag)
    (y : TagIndex Sz StateTag) (hnot : ¬(a ≤ p ∧ p < b)) :
    slotEntries (labels.set p x) (src.set p y) a b = slotEntries labels src a b := by
  unfold slotEntries
  refine List.map_congr_left ?_
  intro q hq
  obtain ⟨i, hi, hqi⟩ := List.mem_range'.mp hq
  exact pairAt_set_ne labels src q p x y (by omega)

/-- A write at the position just past a slot extends it by exactly that pair: the old
    entries are untouched and the new last entry is the pair read off the written arrays. -/
theorem slotEntries_set_succ (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (p a b : Nat) (x : TagIndex Sz LabelTag)
    (y : TagIndex Sz StateTag) (hp : p = b) (hab : a ≤ b) :
    slotEntries (labels.set p x) (src.set p y) a (b + 1)
      = slotEntries labels src a b ++ [pairAt (labels.set p x) (src.set p y) b] := by
  rw [slotEntries_succ _ _ _ _ hab]
  refine congrArg (fun l => l ++ [pairAt (labels.set p x) (src.set p y) b]) ?_
  exact slotEntries_set_of_lt_or_ge labels src p a b x y (by rw [hp]; omega)

/-- The `(label, source)` pairs that the first `k` states of `states` contribute to slot `j`,
    in the order `place_all_incoming` writes them: state by state, and inside a state in the
    order `outgoing_transitions` reports. -/
def towards {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (k j : Nat) :
    List (TagIndex Sz LabelTag × TagIndex Sz StateTag) :=
  (states.take k).flatMap (fun s =>
    ((outVec LTSInst sys s).val.filter (fun t => t.to.index.val = j)).map
      (fun t => (t.label, s)))

/-- Before any state is visited nothing has been written. -/
theorem towards_zero {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (j : Nat) : towards LTSInst sys states 0 j = [] := by
  simp [towards]

/-- Visiting one state more appends exactly that state's transitions towards `j`. -/
theorem towards_succ {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (k : Nat) (s : TagIndex Sz StateTag)
    (tl : List (TagIndex Sz StateTag)) (j : Nat) (h : states = states.take k ++ s :: tl) :
    towards LTSInst sys states (k + 1) j
      = towards LTSInst sys states k j
        ++ ((outVec LTSInst sys s).val.filter (fun t => t.to.index.val = j)).map
          (fun t => (t.label, s)) := by
  have ht : List.take (k + 1) states = List.take k states ++ [s] := by
    have hmin : min k states.length = k := by
      by_cases hkl : k ≤ states.length
      · exact Nat.min_eq_left hkl
      · have h2 := congrArg List.length h
        rw [List.length_append, List.length_cons, List.length_take,
          Nat.min_eq_right (by omega)] at h2
        omega
    have hg : states[k]? = some s := by
      rw [h, List.getElem?_append_right (by
            rw [List.length_take]
            exact Nat.min_le_left k states.length),
        List.length_take, hmin]
      simp
    rw [List.take_add_one, hg]
    rfl
  unfold towards
  rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
  simp

/-- Every pair in `towards` is a reported transition: the "no spurious entries" half of
    `IncomingTransitionsCorrect`, read off the definition. -/
theorem mem_towards {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (k j : Nat) (l : TagIndex Sz LabelTag)
    (s : TagIndex Sz StateTag) (h : (l, s) ∈ towards LTSInst sys states k j) :
    ∃ t, t ∈ (outVec LTSInst sys s).val ∧ t.label = l ∧ t.to.index.val = j := by
  rw [towards, List.mem_flatMap] at h
  obtain ⟨a, _, hflat⟩ := h
  rw [List.mem_map] at hflat
  obtain ⟨t, hts, hpair⟩ := hflat
  rw [List.mem_filter] at hts
  injection hpair with hl ha
  refine ⟨t, ?_, hl, of_decide_eq_true hts.2⟩
  rw [← ha]
  exact hts.1

/-- One iteration of `place_incoming_loop.body`: the transition `t` is written as the pair
    `(t.label, state_index)` at the current cursor of its target, and that cursor is bumped.

    The new cursor value is existentially quantified with its `Nat` value pinned down, as in
    `count_incoming_step`, so that the caller never has to re-analyse the checked addition. -/
theorem place_incoming_step
    (state_index : TagIndex Sz StateTag) (iter : alloc.vec.Vec Transition)
    (cursor : alloc.vec.Vec Sz) (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src : alloc.vec.Vec (TagIndex Sz StateTag))
    (t : Transition) (tl : List Transition)
    (hiter : iter.val = t :: tl)
    (hidx : t.to.index.val < cursor.val.length)
    (hpos : cursor.val[t.to.index.val]'hidx < labels.val.length)
    (hpos' : cursor.val[t.to.index.val]'hidx < src.val.length)
    (hadd : (cursor.val[t.to.index.val]'hidx).val + 1 ≤ Usize.max) :
    ∃ (iter1 : alloc.vec.Vec Transition) (cursor1 : alloc.vec.Vec Sz)
      (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)) (z : Sz),
      verified.merc_lts.incoming_transitions.place_incoming_loop.body state_index iter cursor
          labels src
        = ok (cont (iter1, cursor1, labels1, src1)) ∧
      iter1.val = tl ∧
      cursor1.val = cursor.val.set t.to.index.val z ∧
      labels1.val = labels.val.set (cursor.val[t.to.index.val]'hidx) t.label ∧
      src1.val = src.val.set (cursor.val[t.to.index.val]'hidx) state_index ∧
      z.val = (cursor.val[t.to.index.val]'hidx).val + 1 := by
  rcases Std.WP.spec_imp_exists
      (Aeneas.Std.alloc.vec.Vec.index_usize_spec cursor t.to.index hidx) with ⟨pos, hposok, hposval⟩
  have hposL : pos.val < labels.val.length := by grind
  have hposF : pos.val < src.val.length := by grind
  have hadd' : pos.val + 1 ≤ Usize.max := by grind
  have hidxL := Aeneas.Std.alloc.vec.Vec.index_usize_spec labels pos hposL
  rcases Std.WP.spec_imp_exists hidxL with ⟨y, hy, hyv⟩
  have hidxLS : labels.index_usize pos = ok (labels.val[pos.val]'hposL) := by
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have hidxF := Aeneas.Std.alloc.vec.Vec.index_usize_spec src pos hposF
  rcases Std.WP.spec_imp_exists hidxF with ⟨w, hw, hwv⟩
  have hidxFS : src.index_usize pos = ok (src.val[pos.val]'hposF) := by
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hw, hwv]
  have himutC : cursor.index_mut_usize t.to.index
      = ok (cursor.val[t.to.index.val]'hidx, fun x => cursor.set t.to.index x) := by
    simp [alloc.vec.Vec.index_mut_usize, hposok, hposval]
  have himutL : labels.index_mut_usize pos
      = ok (labels.val[pos.val]'hposL, fun x => labels.set pos x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxLS]
  have himutF : src.index_mut_usize pos
      = ok (src.val[pos.val]'hposF, fun x => src.set pos x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxFS]
  have hsz := Usize.add_spec (x := pos) (y := 1#usize) hadd'
  rcases Std.WP.spec_imp_exists hsz with ⟨z, hzok, hzval⟩
  refine ⟨alloc.vec.Vec.from tl (by grind),
    alloc.vec.Vec.from (cursor.val.set t.to.index.val z) (by grind),
    alloc.vec.Vec.from (labels.val.set pos.val t.label) (by grind),
    alloc.vec.Vec.from (src.val.set pos.val state_index) (by grind),
    z, ?_, alloc.vec.Vec.from_val _ _, alloc.vec.Vec.from_val _ _,
    by grind, by grind, ?_⟩
  · rcases vec_next_eq iter t tl hiter with ⟨o, it1, hnext, ho, hitl⟩
    have hnew : alloc.vec.Vec.from tl (by grind) = it1 :=
      alloc.vec.Vec.ext _ _ ((alloc.vec.Vec.from_val _ _).trans hitl.symm)
    unfold verified.merc_lts.incoming_transitions.place_incoming_loop.body
    rw [hnext, ← hnew]
    cases o with
    | none => simp at ho
    | some t' =>
      simp at ho
      subst t'
      simp [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index,
        hposok, himutL, himutF, himutC]
      rw [← hposval, hzok]
      simp
      congr 1
  rw [hzval]
  grind

/-- The pairs towards `j` that the first `k` transitions of `ts` contribute, in placement
    order: the transitions of the prefix, filtered by target, each tagged with the source
    state. -/
def towards1 (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition) (k j : Nat) :
    List (TagIndex Sz LabelTag × TagIndex Sz StateTag) :=
  ((ts.val.take k).filter (fun t => t.to.index.val = j)).map (fun t => (t.label, s))

/-- Before any transition is placed nothing has been written. -/
theorem towards1_zero (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition) (j : Nat) :
    towards1 s ts 0 j = [] := by
  simp [towards1]

/-- Filtering a singleton by the target test. -/
private theorem filter_singleton (t : Transition) (j : Nat) :
    [t].filter (fun t => t.to.index.val = j) = if t.to.index.val = j then [t] else [] := by
  by_cases h : t.to.index.val = j <;> simp [h]

/-- Placing one transition that targets the slot appends its pair. -/
theorem towards1_succ_self (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (k : Nat) (t : Transition) (tl : List Transition) (j : Nat)
    (h : ts.val = ts.val.take k ++ t :: tl) (hjt : t.to.index.val = j) :
    towards1 s ts (k + 1) j = towards1 s ts k j ++ [(t.label, s)] := by
  unfold towards1
  rw [take_head ts.val k t tl h, List.filter_append, filter_singleton t j, if_pos hjt,
    List.map_append]
  simp

/-- Placing one transition that targets another slot leaves the slot alone. -/
theorem towards1_succ_ne (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (k : Nat) (t : Transition) (tl : List Transition) (j : Nat)
    (h : ts.val = ts.val.take k ++ t :: tl) (hjt : t.to.index.val ≠ j) :
    towards1 s ts (k + 1) j = towards1 s ts k j := by
  unfold towards1
  rw [take_head ts.val k t tl h, List.filter_append, filter_singleton t j, if_neg hjt,
    List.map_append]
  simp

/-- Placing one transition more appends its pair exactly when it targets the slot. -/
theorem towards1_succ (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (k : Nat) (t : Transition) (tl : List Transition) (j : Nat)
    (h : ts.val = ts.val.take k ++ t :: tl) :
    towards1 s ts (k + 1) j
      = towards1 s ts k j ++ (if t.to.index.val = j then [(t.label, s)] else []) := by
  by_cases hjt : t.to.index.val = j
  · rw [if_pos hjt, towards1_succ_self s ts k t tl j h hjt]
  · rw [if_neg hjt, towards1_succ_ne s ts k t tl j h hjt]
    simp

/-- Once the whole vector has been placed, the slot holds the pairs of *all* of the
    state's transitions towards it. -/
theorem towards1_all (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition) (j : Nat) :
    towards1 s ts ts.val.length j
      = (ts.val.filter (fun t => t.to.index.val = j)).map (fun t => (t.label, s)) := by
  unfold towards1
  rw [List.take_length]

/-- A write stays clear of the already-written part of every slot: no position this state
    writes - `cursor0[ti] + (how many of the state's transitions towards `ti` are already
    placed)`, for any target `ti` and any progress `k` - lies in `[lb j, cursor0[j])` for a
    slot `j`. For `j` the state's own target the write is at or past `cursor0[j]`, so it is
    automatically outside; for the other slots this is the CSR separation
    (`lb j = r[j]`, `cursor0[j] = r[j] + seen j`), which the outer scan discharges once. -/
def SepInv (cursor0 : alloc.vec.Vec Sz) (lb : Nat → Nat) (ts : alloc.vec.Vec Transition) : Prop :=
  ∀ j ti k, j < cursor0.val.length → ti < cursor0.val.length → k ≤ ts.val.length →
    ¬((lb j) ≤ (cursor0.val.getD ti 0#usize).val + toCount (ts.val.take k) ti ∧
      (cursor0.val.getD ti 0#usize).val + toCount (ts.val.take k) ti
        < (cursor0.val.getD j 0#usize).val)

/-- State of the inner placement loop: the transitions still to visit, and the three
    arrays that are written. -/
abbrev PiSt := alloc.vec.into_iter.IntoIter Transition × alloc.vec.Vec Sz
  × alloc.vec.Vec (TagIndex Sz LabelTag) × alloc.vec.Vec (TagIndex Sz StateTag)

/-- Invariant of the inner scan after `ts.val.length - st.1.val.length` of the state's
    transitions have been placed:
    * the rest of the iterator is the correspondingly dropped tail of `ts`;
    * the three arrays keep their lengths, slot `j` of the cursor has advanced by the
      number of placed transitions towards `j`, and slot `j`'s range holds exactly the
      pairs of those transitions;
    * nothing below the starting cursor `cursor0[j]` has been touched. -/
def PiInv (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (cursor0 : alloc.vec.Vec Sz) (lb : Nat → Nat)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) : PiSt → Prop :=
  fun st =>
    st.1.val = ts.val.drop (ts.val.length - st.1.val.length) ∧
    st.2.1.val.length = cursor0.val.length ∧
    st.2.2.1.val.length = labels0.val.length ∧
    st.2.2.2.val.length = src0.val.length ∧
    (∀ j, j < cursor0.val.length →
      (st.2.1.val.getD j 0#usize).val = (cursor0.val.getD j 0#usize).val
        + toCount (ts.val.take (ts.val.length - st.1.val.length)) j) ∧
    (∀ j, j < cursor0.val.length →
      slotEntries st.2.2.1.val st.2.2.2.val (cursor0.val.getD j 0#usize).val
          (st.2.1.val.getD j 0#usize).val
        = towards1 s ts (ts.val.length - st.1.val.length) j) ∧
    (∀ j, j < cursor0.val.length →
      slotEntries st.2.2.1.val st.2.2.2.val (lb j) (cursor0.val.getD j 0#usize).val
        = slotEntries labels0.val src0.val (lb j) (cursor0.val.getD j 0#usize).val)

/-- On return, every transition of `ts` has been placed: the cursor of `j` has advanced by
    the number of `ts`'s transitions towards `j`, the range `[cursor0[j], cursor[j])` holds
    exactly their pairs, and everything below `cursor0[j]` is as it was. -/
def PiPost (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (cursor0 : alloc.vec.Vec Sz) (lb : Nat → Nat)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (cursor : alloc.vec.Vec Sz) (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src : alloc.vec.Vec (TagIndex Sz StateTag)) : Prop :=
  cursor.val.length = cursor0.val.length ∧
  (∀ j, j < cursor0.val.length →
    (cursor.val.getD j 0#usize).val = (cursor0.val.getD j 0#usize).val + toCount ts.val j) ∧
  (∀ j, j < cursor0.val.length →
    slotEntries labels.val src.val (cursor0.val.getD j 0#usize).val
      (cursor.val.getD j 0#usize).val = towards1 s ts ts.val.length j) ∧
  (∀ j, j < cursor0.val.length →
    slotEntries labels.val src.val (lb j) (cursor0.val.getD j 0#usize).val
      = slotEntries labels0.val src0.val (lb j) (cursor0.val.getD j 0#usize).val)

/-- The exhausted case of the inner placement loop: the three arrays are returned as they
    are. -/
theorem place_incoming_done (s : TagIndex Sz StateTag) (st : PiSt) (h : st.1.val = []) :
    verified.merc_lts.incoming_transitions.place_incoming_loop.body s st.1 st.2.1 st.2.2.1
        st.2.2.2
      = ok (done (st.2.1, st.2.2.1, st.2.2.2)) := by
  have hn : alloc.vec.into_iter.IteratorIntoIter.next
        (st.1 : alloc.vec.into_iter.IntoIter Transition)
      ⦃ p => p.1 = none ∧ p.2 = st.1 ⦄ := vec_next_none st.1 h
  rcases Std.WP.spec_imp_exists hn with ⟨p, hp, hpt⟩
  cases p with
  | mk o it1 =>
    simp only at hpt
    have hit1 : it1 = st.1 := hpt.2
    unfold verified.merc_lts.incoming_transitions.place_incoming_loop.body
    rw [hp, hpt.1, hit1]
    simp

/-- The carried result of the placement loop: the three arrays, with the iterator dropped. -/
abbrev PiRes := alloc.vec.Vec Sz × alloc.vec.Vec (TagIndex Sz LabelTag)
  × alloc.vec.Vec (TagIndex Sz StateTag)

/-- Reading the two flat arrays through `getD` is the same as through a checked read. -/
private theorem getElem_eq_getD {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l[i]'h = l.getD i d := by
  have h1 : l[i]? = some l[i] := List.getElem?_eq_getElem h
  calc l[i]'h = (l[i]?).getD d := by rw [h1]; rfl
    _ = l.getD i d := (List.getD_eq_getElem?_getD (a := d)).symm

/-- The `place_incoming` scan of one state (`incoming_transitions.rs:227`), run over the
    transition vector `ts` of that state: starting from the cursor `cursor0` and the two flat
    arrays, every transition of `ts` is written to the position
    `cursor0[target] + (how many of the preceding transitions of `ts` target the same slot)`,
    carrying the pair `(label, this state)`. Hence on return the range `[cursor0[j], cursor[j])`
    holds exactly the pairs of `ts`'s transitions towards `j`, in order, and slot `j`'s cursor
    is `cursor0[j] +` their number. `hsep` is what keeps the writes inside the range they
    extend, so nothing below `cursor0[j]` changes. -/
theorem place_incoming_loop_spec
    (s : TagIndex Sz StateTag) (ts : alloc.vec.Vec Transition)
    (cursor0 : alloc.vec.Vec Sz) (lb : Nat → Nat)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (hsep : SepInv cursor0 lb ts)
    (hin : ∀ t, t ∈ ts.val → t.to.index.val < cursor0.val.length)
    (hlens : labels0.val.length = src0.val.length)
    (hfill : ∀ j, j < cursor0.val.length →
      (cursor0.val.getD j 0#usize).val + toCount ts.val j ≤ labels0.val.length)
    (hadd : ∀ j, j < cursor0.val.length →
      (cursor0.val.getD j 0#usize).val + toCount ts.val j + 1 ≤ Usize.max) :
    ∃ (cursor : alloc.vec.Vec Sz) (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src : alloc.vec.Vec (TagIndex Sz StateTag)),
      (@loop PiSt PiRes
        (fun st => verified.merc_lts.incoming_transitions.place_incoming_loop.body s st.1
          st.2.1 st.2.2.1 st.2.2.2)
        ((ts : alloc.vec.into_iter.IntoIter Transition), (cursor0, (labels0, src0))))
        = ok (cursor, labels, src) ∧
      PiPost s ts cursor0 lb labels0 src0 cursor labels src := by
  have hspec : (@loop PiSt PiRes
          (fun st => verified.merc_lts.incoming_transitions.place_incoming_loop.body s st.1
            st.2.1 st.2.2.1 st.2.2.2)
          ((ts : alloc.vec.into_iter.IntoIter Transition), (cursor0, (labels0, src0))))
        ⦃ fun c : PiRes => PiPost s ts cursor0 lb labels0 src0 c.1 c.2.1 c.2.2 ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : PiSt => st.1.val.length)
      (inv := PiInv s ts cursor0 lb labels0 src0)
      (post := fun c : PiRes => PiPost s ts cursor0 lb labels0 src0 c.1 c.2.1 c.2.2)
      (body := fun st => verified.merc_lts.incoming_transitions.place_incoming_loop.body s st.1
        st.2.1 st.2.2.1 st.2.2.2)
      (x := ((ts : alloc.vec.into_iter.IntoIter Transition), (cursor0, (labels0, src0))))
    · intro st hinv
      rcases hinv with ⟨hiter, hlenC, hlenL, hlenS, hval, hcont, hprot⟩
      set k := ts.val.length - st.1.val.length with hkdef
      by_cases hnil : st.1.val = []
      · refine Std.WP.exists_imp_spec
          ⟨done (st.2.1, st.2.2.1, st.2.2.2), place_incoming_done s st hnil, ?_⟩
        have hklen : k = ts.val.length := by
          have h1 := congrArg List.length hiter
          rw [hnil, List.length_nil, List.length_drop] at h1
          omega
        refine ⟨hlenC, ?_, ?_, ?_⟩
        · intro j hj
          have hval' := hval j hj
          rw [hklen, List.take_length] at hval'
          exact hval'
        · intro j hj
          have hcont' : slotEntries st.2.2.1.val st.2.2.2.val
              (cursor0.val.getD j 0#usize).val (st.2.1.val.getD j 0#usize).val
              = towards1 s ts ts.val.length j := by
            rw [← hklen]
            exact hcont j hj
          exact hcont'
        · exact hprot
      · obtain ⟨t, tl, hst⟩ := List.exists_cons_of_ne_nil hnil
        have hdrop : ts.val.drop k = t :: tl := hiter.symm.trans hst
        have hk : k = ts.val.length - (t :: tl).length := by
          rw [← hst]
        have hle : (t :: tl).length ≤ ts.val.length := by
          have h1 := congrArg List.length hdrop
          rw [List.length_drop] at h1
          omega
        have hmem : t ∈ ts.val.drop k := by
          rw [← hiter]
          exact hst.symm ▸ List.mem_cons_self
        have hlen1 : (t :: tl).length + k = ts.val.length := by
          rw [hk, Nat.add_comm]
          exact Nat.sub_add_cancel hle
        have htmem : t ∈ ts.val := List.mem_of_mem_drop hmem
        have hidx0 : t.to.index.val < cursor0.val.length := hin t htmem
        have hidx : t.to.index.val < st.2.1.val.length := by
          rw [hlenC]
          exact hidx0
        -- the position this transition is written at, and the bounds the body checks
        have hposgd : (st.2.1.val.getD t.to.index.val 0#usize).val
            = (cursor0.val.getD t.to.index.val 0#usize).val
              + toCount (ts.val.take k) t.to.index.val := hval t.to.index.val hidx0
        have hgetE : (st.2.1.val[t.to.index.val]'hidx) = st.2.1.val.getD t.to.index.val 0#usize :=
          getElem_eq_getD st.2.1.val t.to.index.val 0#usize hidx
        have hgetEv : (st.2.1.val[t.to.index.val]'hidx).val
            = (st.2.1.val.getD t.to.index.val 0#usize).val := congrArg UScalar.val hgetE
        have hcat : ts.val.take k ++ ts.val.drop k = ts.val := List.take_append_drop k ts.val
        have hshape : ts.val = ts.val.take k ++ t :: tl := by
          calc ts.val = ts.val.take k ++ ts.val.drop k := hcat.symm
            _ = ts.val.take k ++ st.1.val := by rw [hiter]
            _ = ts.val.take k ++ t :: tl := by rw [hst]
        have htk1 : ts.val.take (k + 1) = ts.val.take k ++ [t] :=
          take_head ts.val k t tl hshape
        have hcountle : (st.2.1.val.getD t.to.index.val 0#usize).val + 1
            ≤ (cursor0.val.getD t.to.index.val 0#usize).val
              + toCount ts.val t.to.index.val := by
          have hedrop : 1 ≤ toCount (ts.val.drop k) t.to.index.val :=
            toCount_pos_of_mem hmem
          have hdropcount : toCount (ts.val.take k) t.to.index.val
              + toCount (ts.val.drop k) t.to.index.val
            = toCount ts.val t.to.index.val :=
            (toCount_append _ _ _).symm.trans (by rw [hcat])
          have hsingle : toCount [t] t.to.index.val = 1 := by
            rw [toCount_single]
            simp [tick]
          have htk1count : toCount (ts.val.take (k + 1)) t.to.index.val
              = toCount (ts.val.take k) t.to.index.val + 1 := by
            rw [htk1, toCount_append, hsingle]
          calc (st.2.1.val.getD t.to.index.val 0#usize).val + 1
              = (cursor0.val.getD t.to.index.val 0#usize).val
                  + toCount (ts.val.take (k + 1)) t.to.index.val := by
                rw [hposgd, htk1count]
                omega
            _ ≤ (cursor0.val.getD t.to.index.val 0#usize).val
                  + toCount ts.val t.to.index.val := by omega
        have hposL : (st.2.1.val.getD t.to.index.val 0#usize).val < st.2.2.1.val.length := by
          have h2 := hfill t.to.index.val hidx0
          rw [← hlenL] at h2
          omega
        have hposL' : (st.2.1.val.getD t.to.index.val 0#usize).val < st.2.2.2.val.length := by
          have h2 := hfill t.to.index.val hidx0
          rw [hlens, ← hlenS] at h2
          omega
        have hmaxL : (st.2.1.val.getD t.to.index.val 0#usize).val + 1 ≤ Usize.max := by
          have h2 := hadd t.to.index.val hidx0
          omega
        have hposlt : (st.2.1.val[t.to.index.val]'hidx).val < st.2.2.1.val.length :=
          hgetE ▸ hposL
        have hposlt' : (st.2.1.val[t.to.index.val]'hidx).val < st.2.2.2.val.length :=
          hgetE ▸ hposL'
        have hmax : (st.2.1.val[t.to.index.val]'hidx).val + 1 ≤ Usize.max :=
          hgetE ▸ hmaxL
        rcases place_incoming_step s st.1 st.2.1 st.2.2.1 st.2.2.2 t tl hst hidx hposlt
            hposlt' hmax with
          ⟨iter1, cursor1, labels1, src1, z, hbody, hit1, hsetC, hsetL, hsetS, hz⟩
        have hzgd : z.val = (st.2.1.val.getD t.to.index.val 0#usize).val + 1 := by
          rw [hz, hgetEv]
        have hsetL' : labels1.val = st.2.2.1.val.set
            (st.2.1.val.getD t.to.index.val 0#usize).val t.label := by
          rw [hsetL, hgetEv]
        have hsetS' : src1.val = st.2.2.2.val.set
            (st.2.1.val.getD t.to.index.val 0#usize).val s := by
          rw [hsetS, hgetEv]
        have hiter' : tl = ts.val.drop (k + 1) := by
          have h1 : (ts.val.drop k).drop 1 = ts.val.drop (k + 1) := by
            simp [Nat.add_comm]
          rw [← h1, ← hiter, hst]
          rfl
        have hk1 : ts.val.length - iter1.val.length = k + 1 := by
          rw [hit1]
          have h1 : (t :: tl).length = tl.length + 1 := by simp
          omega
        have hiter'' : iter1.val = ts.val.drop (ts.val.length - iter1.val.length) := by
          calc iter1.val = tl := hit1
            _ = ts.val.drop (k + 1) := hiter'
            _ = ts.val.drop (ts.val.length - iter1.val.length) := by rw [hk1]
        refine Std.WP.exists_imp_spec
          ⟨cont (iter1, (cursor1, (labels1, src1))), hbody,
            ⟨hiter'', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · -- the three arrays keep their lengths
          rw [hsetC, List.length_set, hlenC]
        · rw [hsetL, List.length_set, hlenL]
        · rw [hsetS, List.length_set, hlenS]
        · -- slot-wise: the cursor of the transition's own target ticks, the others do not
          intro j hj
          have hj' : j < st.2.1.val.length := by
            rw [hlenC]
            exact hj
          have hget := getD_set st.2.1.val t.to.index.val j z 0#usize hj'
          rw [hsetC, hget]
          have htake' : ts.val.take (ts.val.length - iter1.val.length)
              = ts.val.take k ++ [t] := by rw [hk1, htk1]
          by_cases hji : j = t.to.index.val
          · subst hji
            have hidx1 : t.to.index.val < cursor0.val.length := hidx0
            rw [if_pos rfl, hzgd, hval t.to.index.val hidx1, htake', toCount_append]
            simp [toCount]
            omega
          · have hne : t.to.index.val ≠ j := by omega
            rw [if_neg hji, hval j hj, htake', toCount_append]
            simp [toCount, hne]
        · -- slot-wise: the range this state extends holds exactly the placed pairs
          intro j hj
          have hj1 : j < st.2.1.val.length := by
            rw [hlenC]
            exact hj
          by_cases hji : j = t.to.index.val
          · subst hji
            rw [hsetC, hsetL', hsetS']
            have hget := getD_set st.2.1.val t.to.index.val t.to.index.val z 0#usize hidx
            rw [hget, if_pos rfl, hzgd]
            have hcont' := hcont t.to.index.val hj
            rw [slotEntries_set_succ st.2.2.1.val st.2.2.2.val
              (st.2.1.val.getD t.to.index.val 0#usize).val
              (cursor0.val.getD t.to.index.val 0#usize).val
              (st.2.1.val.getD t.to.index.val 0#usize).val t.label s rfl]
            · rw [hcont', pairAt_set_self st.2.2.1.val st.2.2.2.val
                (st.2.1.val.getD t.to.index.val 0#usize).val t.label s hposL hposL']
              rw [hk1]
              exact (towards1_succ_self s ts k t tl t.to.index.val hshape rfl).symm
            · omega
          · have hne : t.to.index.val ≠ j := by omega
            have hsep' := hsep t.to.index.val j k hidx0 hj (by
              rw [hkdef]
              exact Nat.sub_le ts.val.length st.1.val.length)
            have hget := getD_set st.2.1.val t.to.index.val j z 0#usize hj1
            rw [hsetC, hget, if_neg hji]
            have hcont'' : slotEntries st.2.2.1.val st.2.2.2.val
                (cursor0.val.getD j 0#usize).val
                ((cursor0.val.getD j 0#usize).val + toCount (ts.val.take k) j)
              = towards1 s ts k j := by
              have hc := hcont j hj
              rw [hval j hj] at hc
              exact hc
            rw [← hposgd] at hsep'
            rw [hsetL', hsetS', hval j hj,
              slotEntries_set_of_lt_or_ge st.2.2.1.val st.2.2.2.val
                (st.2.1.val.getD t.to.index.val 0#usize).val (cursor0.val.getD j 0#usize).val
                ((cursor0.val.getD j 0#usize).val + toCount (ts.val.take k) j) t.label s hsep']
            rw [hcont'']
            rw [hk1]
            exact (towards1_succ_ne s ts k t tl j hshape hne).symm
        · -- slot-wise: nothing below the starting cursor has been touched
          intro j hj
          rw [hsetL', hsetS']
          have hsep' := hsep j t.to.index.val k hj hidx0 (by
            rw [hkdef]
            exact Nat.sub_le ts.val.length st.1.val.length)
          rw [← hposgd] at hsep'
          exact slotEntries_set_of_lt_or_ge st.2.2.1.val st.2.2.2.val
            (st.2.1.val.getD t.to.index.val 0#usize).val (lb j)
            (cursor0.val.getD j 0#usize).val t.label s hsep'
        · -- the rest of the iterator got shorter
          rw [hit1, hst]
          simp
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.drop_zero]
      · rfl
      · rfl
      · rfl
      · intro j hj
        simp [List.take_zero, toCount_nil]
      · intro j hj
        rw [Nat.sub_self, towards1_zero]
        exact slotEntries_of_le _ _ _ _ (le_refl _)
      · intro j hj
        rfl
  rcases Std.WP.spec_imp_exists hspec with ⟨p, hloop, hpost⟩
  exact ⟨p.1, p.2.1, p.2.2, hloop, hpost⟩

end MercVerified.Signatures.Proofs
