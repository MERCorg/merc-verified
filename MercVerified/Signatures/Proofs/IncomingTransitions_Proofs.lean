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
  (`place_all_incoming_loop_spec`), which is next. `SepInv` has two parts - writes avoid
  `[lb j, cursor0[j])` for every slot `j`, and avoid the already-written part
  `[cursor0[j], cursor0[j] + seen j)` of any other slot - so the inner scan's postcondition
  also records that `[lb j, cursor0[j])` is unchanged, which the outer scan needs to be able
  to concatenate each state's contribution to the range it extends.

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

/-- The write performed for the `k`-th transition `t` of `ts` is `p = cursor0[ti] +
    (how many of the state's earlier transitions towards `ti` are already placed)`, where
    `ti` is `t`'s own target.

    A write by one state must never land inside a part of a slot that is already accounted
    for. So for every slot `j` we require two things:
    * `p` is outside `[lb j, cursor0[j])`, so the scan leaves the part of the slot below the
      starting cursor alone. For `j` the state's own target the write is at or past
      `cursor0[j]`; for the other slots this is the CSR separation
      (`lb j = r[j]`, `cursor0[j] = r[j] + seen j`), which the outer scan discharges once;
    * unless `j` is the transition's own target, `p` is outside
      `[cursor0[j], cursor0[j] + seen j)`, so the scan leaves the already-written part of
      every other slot alone. Again the CSR separation gives this.

    `k` and `t` are quantified together, with `t` the transition `ts` actually reports at
    position `k`, because only then is `cursor0[ti] + seen k ti` the *next* free position of
    slot `ti` and hence the only position this state can write. The offsets are compared
    across `ti` and `j`, so the pair `(k, t)` has to be pinned down for the statement to be
    true; the separation argument below uses the fact that a transition towards `ti` is still
    unplaced at position `k`. -/
def SepInv (cursor0 : alloc.vec.Vec Sz) (lb : Nat → Nat) (ts : alloc.vec.Vec Transition) : Prop :=
  ∀ (k : Nat) (t : Transition) (j : Nat), k < ts.val.length → ts.val[k]? = some t →
    j < cursor0.val.length → t.to.index.val < cursor0.val.length →
    (¬((lb j) ≤ (cursor0.val.getD t.to.index.val 0#usize).val
            + toCount (ts.val.take k) t.to.index.val ∧
        (cursor0.val.getD t.to.index.val 0#usize).val
            + toCount (ts.val.take k) t.to.index.val
          < (cursor0.val.getD j 0#usize).val)) ∧
    (j = t.to.index.val ∨
      ¬((cursor0.val.getD j 0#usize).val
          ≤ (cursor0.val.getD t.to.index.val 0#usize).val
            + toCount (ts.val.take k) t.to.index.val ∧
        (cursor0.val.getD t.to.index.val 0#usize).val
            + toCount (ts.val.take k) t.to.index.val
          < (cursor0.val.getD j 0#usize).val + toCount (ts.val.take k) j))

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
      = slotEntries labels0.val src0.val (lb j) (cursor0.val.getD j 0#usize).val) ∧
  labels.val.length = labels0.val.length ∧
  src.val.length = src0.val.length

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

/-- The transition a scan is about to place, read off the state's own list. -/
private theorem getElem?_of_drop {α : Type} {l : List α} {k : Nat} (hk : k < l.length)
    {t : α} {tl : List α} (hshape : l = l.take k ++ t :: tl) : l[k]? = some t := by
  have hkle : k ≤ l.length := by omega
  have hmin : min k l.length = k := Nat.min_eq_left hkle
  rw [hshape, List.getElem?_append_right (by rw [List.length_take, hmin]),
    List.length_take, hmin, Nat.sub_self]
  rfl

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
      (cursor0.val.getD j 0#usize).val + toCount ts.val j ≤ Usize.max) :
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
        refine ⟨hlenC, ?_, ?_, ?_, hlenL, hlenS⟩
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
        have hklt : k < ts.val.length := by
          have hpos : 0 < (t :: tl).length := by simp
          rw [hk]
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
        have hkt : ts.val[k]? = some t := getElem?_of_drop hklt hshape
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
          omega -- from hcountle and h2
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
            have hsep' := hsep k t j hklt hkt hj hidx0
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
                ((cursor0.val.getD j 0#usize).val + toCount (ts.val.take k) j) t.label s
                (hsep'.2.resolve_left hne.symm)]
            rw [hcont'']
            rw [hk1]
            exact (towards1_succ_ne s ts k t tl j hshape hne).symm
        · -- slot-wise: nothing below the starting cursor has been touched
          intro j hj
          rw [hsetL', hsetS']
          have hsep' := hsep k t j hklt hkt hj hidx0
          rw [← hposgd] at hsep'
          exact (slotEntries_set_of_lt_or_ge st.2.2.1.val st.2.2.2.val
            (st.2.1.val.getD t.to.index.val 0#usize).val (lb j)
            (cursor0.val.getD j 0#usize).val t.label s hsep'.1).trans (hprot j hj)
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

/-! ## Stage 6b: the outer scan `place_all_incoming`

`place_all_incoming` (`:193`) runs `place_incoming` once per state the LTS enumerates, on the
cursor that stage 5 copied from the CSR offsets. So the outer loop only has to keep track of
*how many states* it has visited; per state it reuses `place_incoming_loop_spec` verbatim,
with the three facts that lemma asks for supplied by the outer invariant and the CSR
separation:

* the *target* bound, because the offsets have one slot per state and every transition's
  target is a state index;
* the *fits* and *no overflow* bounds, because the range of slot `j` is
  `[r[j], r[j] + total j) = [r[j], r[j+1])`, and `[r[j], r[n])` is within the transition
  arrays;
* the *separation* `SepInv`, which is `sepInv_of_csr` below: the ranges of two different
  slots never overlap, so a state's write lands either below `r[j]` or at or past
  `r[j+1]`.

The slot's content then concatenates: `[r[j], cursor[j])` is what the visited states wrote,
and this state's contribution is appended to it. -/

/-- Counting more states cannot subtract ticks. -/
theorem seenCount_nonneg {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (k j : Nat) : 0 ≤ seenCount LTSInst sys states k j := by
  unfold seenCount
  exact List.sum_nonneg (fun s _ => Nat.zero_le _)

/-- `toCount` splits over `take`/`drop`. -/
theorem toCount_take_drop (ts : List Transition) (k j : Nat) :
    toCount (ts.take k) j + toCount (ts.drop k) j = toCount ts j := by
  have h := congrArg (fun l => toCount l j) (List.take_append_drop k ts)
  rwa [toCount_append] at h

/-- A prefix of a transition list holds no more ticks towards a slot than the whole list. -/
theorem toCount_take_le (ts : List Transition) (k j : Nat) :
    toCount (ts.take k) j ≤ toCount ts j := by
  have h := toCount_take_drop ts k j
  omega

/-- Two adjacent ranges of a slot read as one range. -/
theorem slotEntries_append (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    slotEntries labels src a c = slotEntries labels src a b ++ slotEntries labels src b c := by
  have h1 : c - a = (b - a) + (c - b) := by omega
  have h3 : List.range' a (b - a) ++ List.range' b (c - b) = List.range' a ((b - a) + (c - b)) := by
    have hshift : a + 1 * (b - a) = b := by omega
    have hstep : List.range' a (b - a) ++ List.range' b (c - b)
        = List.range' a (b - a) ++ List.range' (a + 1 * (b - a)) (c - b) := by
      rw [hshift]
    calc
      List.range' a (b - a) ++ List.range' b (c - b) = _ := hstep
      _ = _ := List.range'_append (step := 1)
  unfold slotEntries
  rw [h1, ← h3, List.map_append]

/-- An element read at position `k` lies in the tail dropped from `k`. -/
private theorem mem_drop_of_getElem? {α : Type} (l : List α) (k : Nat) (a : α)
    (h : l[k]? = some a) : a ∈ l.drop k := by
  induction l generalizing k a with
  | nil => simp at h
  | cons x l ih =>
    cases k with
    | zero => simp at h; subst h; exact List.mem_cons_self
    | succ k => exact ih k a h

/-- The CSR separation discharges `SepInv` for the scan of one state.

    The offsets are non-decreasing and `r[j+1] = r[j] + (total number of transitions towards
    `j)`, so the ranges of two different slots never overlap. A write for the state's
    `k`-th transition, at `cursor[ti] + (how many of its earlier transitions towards `ti` are
    placed)`, lies in `[r[ti], r[ti+1])` - the upper bound is strict because the transition
    being placed is itself still unplaced. So for a slot `j` that is not the write's own
    target, the write is either below `r[j]` or at or past `r[j+1]`, and hence outside both
    `[lb j, cursor[j])` and `[cursor[j], cursor[j] + seen j)` with `lb j = r[j]`. -/
theorem sepInv_of_csr {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (states : List (TagIndex Sz StateTag)) (kout : Nat) (tl : List (TagIndex Sz StateTag))
    (s : TagIndex Sz StateTag) (r cursor0 : alloc.vec.Vec Sz)
    (hshape : states = states.take kout ++ s :: tl)
    (hmono : ∀ i, i + 1 < r.val.length →
      (r.val.getD i 0#usize).val ≤ (r.val.getD (i+1) 0#usize).val)
    (hcsr : ∀ j, j + 1 < r.val.length →
      (r.val.getD j 0#usize).val + seenCount LTSInst sys states states.length j
        = (r.val.getD (j+1) 0#usize).val)
    (hcur : ∀ j, j < cursor0.val.length →
      (cursor0.val.getD j 0#usize).val = (r.val.getD j 0#usize).val
        + seenCount LTSInst sys states kout j)
    (hseplen : cursor0.val.length + 1 = r.val.length) :
    SepInv cursor0 (fun j => (r.val.getD j 0#usize).val) (outVec LTSInst sys s) := by
  have hkle : kout + 1 ≤ states.length := by
    have h1 := congrArg List.length hshape
    rw [List.length_append, List.length_cons, List.length_take] at h1
    by_cases h : kout ≤ states.length
    · rw [Nat.min_eq_left h] at h1
      omega
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))] at h1
      omega
  have hrle : ∀ (a b : Nat), a ≤ b → b < r.val.length →
      (r.val.getD a 0#usize).val ≤ (r.val.getD b 0#usize).val := by
    intro a b
    induction b with
    | zero =>
        intro hab _
        rcases Nat.le_zero.mp hab with rfl
        exact Nat.le_refl _
    | succ b ih =>
        intro hab hb
        rcases Nat.eq_or_lt_of_le hab with rfl | hlt
        · exact Nat.le_refl _
        · exact le_trans (ih (Nat.le_of_lt_succ hlt) (by omega)) (hmono b hb)
  intro k t j hklt hkt hj hitx
  generalize hts : (outVec LTSInst sys s).val = ts
  rw [hts] at hkt
  -- the transition being placed is still unplaced, so it counts towards its own target
  have hmem : t ∈ ts.drop k := mem_drop_of_getElem? _ _ _ hkt
  have hB : 1 ≤ toCount (ts.drop k) t.to.index.val := toCount_pos_of_mem hmem
  have hA : toCount (ts.take k) t.to.index.val + toCount (ts.drop k) t.to.index.val
      = toCount ts t.to.index.val := toCount_take_drop ts k t.to.index.val
  have hA' : toCount (ts.take k) j ≤ toCount ts j := toCount_take_le ts k j
  have hcur' := hcur t.to.index.val hitx
  have hcsr' := hcsr t.to.index.val (by omega)
  have hsplit (m : Nat) : seenCount LTSInst sys states (kout + 1) m
      = toCount ts m + seenCount LTSInst sys states kout m :=
    hts ▸ seenCount_succ LTSInst sys states kout s tl m hshape
  have hsplit' := hsplit t.to.index.val
  have hkmono : kout ≤ states.length := by omega
  have hmonoLt (m : Nat) : seenCount LTSInst sys states (kout + 1) m
      ≤ seenCount LTSInst sys states states.length m :=
    seenCount_mono LTSInst sys states (kout + 1) states.length m hkle
  have hmono' := hmonoLt t.to.index.val
  dsimp only
  -- the write position, its lower and its strict upper bound
  have hlo : 0 ≤ (cursor0.val.getD t.to.index.val 0#usize).val
      + toCount (ts.take k) t.to.index.val := by
    have h := seenCount_nonneg LTSInst sys states kout t.to.index.val
    omega
  have hhi : (cursor0.val.getD t.to.index.val 0#usize).val
      + toCount (ts.take k) t.to.index.val
      < (r.val.getD (t.to.index.val + 1) 0#usize).val := by
    omega
  refine ⟨?_, ?_⟩
  · rcases lt_trichotomy t.to.index.val j with hlt | heq | hgt
    · -- the write lands below the start of `j`'s range
      intro hcon
      have h1 := hcon.1
      have h2 := hrle (t.to.index.val + 1) j (by omega) (by omega)
      omega
    · -- `j` is the write's own slot, so the write is at or past its end
      intro hcon
      have h1 : (cursor0.val.getD t.to.index.val 0#usize).val
          + toCount (ts.take k) t.to.index.val
          < (cursor0.val.getD t.to.index.val 0#usize).val := heq.symm ▸ hcon.2
      omega
    · -- the write lands at or past the end of `j`'s range
      intro hcon
      have h1 := hcon.2
      have h2 := hrle (j + 1) t.to.index.val (by omega) (by omega)
      have h3 := hcsr j (by omega)
      have h4 := hcur j hj
      have h5 := seenCount_mono LTSInst sys states kout states.length j hkmono
      have h6 := seenCount_nonneg LTSInst sys states kout j
      omega
  · rcases lt_trichotomy t.to.index.val j with hlt | heq | hgt
    · refine Or.inr ?_
      intro hcon
      have h1 := hcon.1
      have h2 := hrle (t.to.index.val + 1) j (by omega) (by omega)
      have h3 := hcur j (by omega)
      have h4 := seenCount_nonneg LTSInst sys states kout j
      omega
    · exact Or.inl heq.symm
    · refine Or.inr ?_
      intro hcon
      have h1 := hcon.2
      have h2 := hrle (j + 1) t.to.index.val (by omega) (by omega)
      have h3 := hcsr j (by omega)
      have h4 := hcur j hj
      have h5 := seenCount_mono LTSInst sys states kout states.length j hkmono
      have h6 := hsplit j
      have h7 := hA'
      have h8 := hmonoLt j
      omega

/-- `place_incoming` for one state, in equation form. -/
theorem place_incoming_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (s : TagIndex Sz StateTag) (cursor : alloc.vec.Vec Sz)
    (labels : alloc.vec.Vec (TagIndex Sz LabelTag)) (src : alloc.vec.Vec (TagIndex Sz StateTag))
    (lb : Nat → Nat)
    (hout : LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hsep : SepInv cursor lb (outVec LTSInst sys s))
    (hin : ∀ t, t ∈ (outVec LTSInst sys s).val → t.to.index.val < cursor.val.length)
    (hlens : labels.val.length = src.val.length)
    (hfill : ∀ j, j < cursor.val.length →
      (cursor.val.getD j 0#usize).val + toCount (outVec LTSInst sys s).val j
        ≤ labels.val.length)
    (hadd : ∀ j, j < cursor.val.length →
      (cursor.val.getD j 0#usize).val + toCount (outVec LTSInst sys s).val j ≤ Usize.max) :
    ∃ (cursor1 : alloc.vec.Vec Sz) (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.place_incoming LTSInst sys s cursor labels src
        = ok (cursor1, labels1, src1) ∧
      PiPost s (outVec LTSInst sys s) cursor lb labels src cursor1 labels1 src1 := by
  rcases place_incoming_loop_spec s (outVec LTSInst sys s) cursor lb labels src hsep hin hlens
      hfill hadd with ⟨cursor1, labels1, src1, hloop, hpost⟩
  refine ⟨cursor1, labels1, src1, ?_, hpost⟩
  unfold verified.merc_lts.incoming_transitions.place_incoming
  simp only [hout, alloc.vec.IntoIteratorVec.into_iter, bind_tc_ok]
  exact hloop

/-- State of the outer placement loop: the states still to visit and the three arrays. -/
abbrev PaSt := alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag) × alloc.vec.Vec Sz
  × alloc.vec.Vec (TagIndex Sz LabelTag) × alloc.vec.Vec (TagIndex Sz StateTag)

/-- Invariant of the outer placement loop after `sv.val.length - st.1.val.length` states have
    been visited:
    * the rest of the iterator is the correspondingly dropped tail of `sv`;
    * the three arrays keep their lengths;
    * the cursor of slot `j` is `r[j] +` the number of transitions towards `j` that the
      visited states contribute;
    * the range `[r[j], cursor[j])` holds exactly those transitions' pairs, in the order
      `place_all_incoming` writes them. -/
def PaInv {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (r : alloc.vec.Vec Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) : PaSt → Prop :=
  fun st =>
    st.1.val = sv.val.drop (sv.val.length - st.1.val.length) ∧
    st.2.1.val.length = sv.val.length ∧
    st.2.2.1.val.length = labels0.val.length ∧
    st.2.2.2.val.length = src0.val.length ∧
    (∀ j, j < sv.val.length →
      (st.2.1.val.getD j 0#usize).val = (r.val.getD j 0#usize).val
        + seenCount LTSInst sys sv.val (sv.val.length - st.1.val.length) j) ∧
    (∀ j, j < sv.val.length →
      slotEntries st.2.2.1.val st.2.2.2.val (r.val.getD j 0#usize).val
          (st.2.1.val.getD j 0#usize).val
        = towards LTSInst sys sv.val (sv.val.length - st.1.val.length) j)

/-- On return, the cursor of slot `j` is `r[j] +` the number of transitions towards `j` that
    *all* of the enumerated states contribute, and `[r[j], cursor[j])` holds exactly their
    pairs. -/
def PaPost {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (r : alloc.vec.Vec Sz)
    (cursor : alloc.vec.Vec Sz) (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src : alloc.vec.Vec (TagIndex Sz StateTag)) : Prop :=
  cursor.val.length = sv.val.length ∧
  (∀ j, j < sv.val.length →
    (cursor.val.getD j 0#usize).val = (r.val.getD j 0#usize).val
      + seenCount LTSInst sys sv.val sv.val.length j) ∧
  (∀ j, j < sv.val.length →
    slotEntries labels.val src.val (r.val.getD j 0#usize).val
        (cursor.val.getD j 0#usize).val
      = towards LTSInst sys sv.val sv.val.length j)

/-- The exhausted case of the outer placement loop: the arrays are returned as they are. -/
theorem place_all_incoming_done {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (r : alloc.vec.Vec Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (st : PaSt) (h : st.1.val = [])
    (hinv : PaInv LTSInst sys sv r labels0 src0 st) :
    verified.merc_lts.incoming_transitions.place_all_incoming_loop.body
        LTSInst sys st.1 st.2.1 st.2.2.1 st.2.2.2 = ok (done st.2) ∧
      PaPost LTSInst sys sv r st.2.1 st.2.2.1 st.2.2.2 := by
  have hn : alloc.vec.into_iter.IteratorIntoIter.next
        (st.1 : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag))
      ⦃ p => p.1 = none ∧ p.2 = st.1 ⦄ := vec_next_none st.1 h
  rcases Std.WP.spec_imp_exists hn with ⟨p, hp, hpt⟩
  cases p with
  | mk o it1 =>
    simp only at hpt
    have hit1 : it1 = st.1 := hpt.2
    refine ⟨?_, ?_⟩
    · unfold verified.merc_lts.incoming_transitions.place_all_incoming_loop.body
      rw [hp, hpt.1, hit1]
      simp
    · rcases hinv with ⟨hiter, hlenC, hlenL, hlenS, hval, hcont⟩
      refine ⟨hlenC, ?_, ?_⟩
      · intro j hj
        have hz : sv.val.drop (sv.val.length - st.1.val.length) = [] :=
          hiter.symm.trans h
        have h1 : sv.val.length - (sv.val.length - st.1.val.length) = 0 := by
          rw [← List.length_drop, hz, List.length_nil]
        have hklen : sv.val.length - st.1.val.length = sv.val.length := by omega
        have hval' := hval j hj
        rw [hklen] at hval'
        exact hval'
      · intro j hj
        have hz : sv.val.drop (sv.val.length - st.1.val.length) = [] :=
          hiter.symm.trans h
        have h1 : sv.val.length - (sv.val.length - st.1.val.length) = 0 := by
          rw [← List.length_drop, hz, List.length_nil]
        have hklen : sv.val.length - st.1.val.length = sv.val.length := by omega
        have hcont' := hcont j hj
        rw [hklen] at hcont'
        exact hcont'

/-- One step of the outer placement loop: run `place_incoming` on the next state `s` of the
    enumeration, whose transitions `ts` are the ones `stage 5`'s cursor already makes room
    for. The loop invariant carries the new cursor and the new range contents: the range of
    slot `j` is the concatenation of what the visited states wrote to it. -/
theorem place_all_incoming_step {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (r : alloc.vec.Vec Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (st : PaSt)
    (s : TagIndex Sz StateTag) (sl : List (TagIndex Sz StateTag)) (k : Nat)
    (hst : st.1.val = s :: sl) (hiter : st.1.val = sv.val.drop k)
    (hinv : PaInv LTSInst sys sv r labels0 src0 st)
    (hout : LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hin : ∀ t, t ∈ (outVec LTSInst sys s).val → t.to.index.val + 1 < r.val.length)
    (hlens : labels0.val.length = src0.val.length)
    (hrlen : sv.val.length + 1 = r.val.length)
    (hmono : ∀ i, i + 1 < r.val.length →
      (r.val.getD i 0#usize).val ≤ (r.val.getD (i+1) 0#usize).val)
    (hcsr : ∀ j, j + 1 < r.val.length →
      (r.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j
        = (r.val.getD (j+1) 0#usize).val)
    (hfill : ∀ j, j < r.val.length → (r.val.getD j 0#usize).val ≤ labels0.val.length)
    (hlenmax : labels0.val.length ≤ Usize.max) :
    ∃ (iter1 : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag))
      (cursor1 : alloc.vec.Vec Sz) (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.place_all_incoming_loop.body
          LTSInst sys st.1 st.2.1 st.2.2.1 st.2.2.2
        = ok (cont (iter1, (cursor1, (labels1, src1)))) ∧
      iter1.val = sl ∧
      PaInv LTSInst sys sv r labels0 src0 (iter1, (cursor1, (labels1, src1))) := by
  rcases hinv with ⟨_, hlenC, hlenL, hlenS, hval, hcont⟩
  have hdrop : sv.val.drop k = s :: sl := hiter.symm.trans hst
  have hklen : sv.val.length = k + sl.length + 1 := by
    have h1 := congrArg List.length hdrop
    rw [List.length_drop, List.length_cons] at h1
    omega
  have hkle : k + 1 ≤ sv.val.length := by omega
  have hshape : sv.val = sv.val.take k ++ s :: sl :=
    (List.take_append_drop k sv.val).symm.trans (by rw [hdrop])
  have hkdef : k = sv.val.length - st.1.val.length := by
    have h1 := congrArg List.length hst
    rw [List.length_cons] at h1
    omega
  have hval' : ∀ j, j < st.2.1.val.length →
      (st.2.1.val.getD j 0#usize).val = (r.val.getD j 0#usize).val
        + seenCount LTSInst sys sv.val k j := by
    intro j hj
    have hj' : j < sv.val.length := by rw [← hlenC]; exact hj
    have h := hval j hj'
    rw [← hkdef] at h
    exact h
  have hsplit (m : Nat) : seenCount LTSInst sys sv.val (k + 1) m
      = toCount (outVec LTSInst sys s).val m + seenCount LTSInst sys sv.val k m :=
    seenCount_succ LTSInst sys sv.val k s sl m hshape
  have hmonoLt (m : Nat) : seenCount LTSInst sys sv.val (k + 1) m
      ≤ seenCount LTSInst sys sv.val sv.val.length m :=
    seenCount_mono LTSInst sys sv.val (k + 1) sv.val.length m hkle
  -- `r[j]` leaves room for this state's transitions, and the increment still fits
  have hfill' : ∀ j, j < st.2.1.val.length →
      (st.2.1.val.getD j 0#usize).val + toCount (outVec LTSInst sys s).val j
        ≤ st.2.2.1.val.length := by
    intro j hj
    have h1 := hval' j hj
    have h2 := hcsr j (by omega)
    have h3 := hfill (j + 1) (by omega)
    calc (st.2.1.val.getD j 0#usize).val + toCount (outVec LTSInst sys s).val j
        = (r.val.getD j 0#usize).val
            + (toCount (outVec LTSInst sys s).val j + seenCount LTSInst sys sv.val k j) := by
              rw [h1]; omega
      _ = (r.val.getD j 0#usize).val + seenCount LTSInst sys sv.val (k + 1) j := by
            rw [hsplit j]
      _ ≤ (r.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j := by
            have h4 := hmonoLt j
            omega
      _ = (r.val.getD (j + 1) 0#usize).val := h2
      _ ≤ labels0.val.length := h3
      _ = st.2.2.1.val.length := hlenL.symm
  have hadd' : ∀ j, j < st.2.1.val.length →
      (st.2.1.val.getD j 0#usize).val + toCount (outVec LTSInst sys s).val j ≤ Usize.max := by
    intro j hj
    have h1 := hfill' j hj
    have h2 : st.2.2.1.val.length ≤ Usize.max := by rw [hlenL]; exact hlenmax
    exact h1.trans h2
  -- the CSR offsets separate this state's transitions from what is already placed
  have hsep : SepInv st.2.1 (fun j => (r.val.getD j 0#usize).val) (outVec LTSInst sys s) :=
    sepInv_of_csr LTSInst sys sv.val k sl s r st.2.1 hshape hmono hcsr
      (fun j hj => hval' j hj)
      (by rw [hlenC, hrlen])
  rcases place_incoming_spec LTSInst sys s st.2.1 st.2.2.1 st.2.2.2
      (fun j => (r.val.getD j 0#usize).val) hout hsep
      (fun t ht => by
        have h1 := hin t ht
        have h2 : st.2.1.val.length + 1 = r.val.length := by rw [hlenC, hrlen]
        omega)
      (by rw [hlenL, hlens, hlenS]) hfill' hadd'
    with ⟨cursor1, labels1, src1, hplace, hpost⟩
  rcases hpost with ⟨hclen, hccur, hcent, hprot, hllen, hslen⟩
  rcases vec_next_eq st.1 s sl hst with ⟨o, it1, hnext, ho, hit1⟩
  have hlen' : sv.val.length - it1.val.length = k + 1 := by rw [hit1]; omega
  refine ⟨it1, cursor1, labels1, src1, ?_, hit1, ?_⟩
  · unfold verified.merc_lts.incoming_transitions.place_all_incoming_loop.body
    rw [hnext]
    simp [ho, hplace, bind_tc_ok]
  · refine ⟨?_, hclen.trans hlenC, hllen.trans hlenL, hslen.trans hlenS, ?_, ?_⟩
    · -- the iterator is the tail of `sv`
      have h1 : sv.val.length - sl.length = k + 1 := by
        have h2 := congrArg List.length hdrop
        rw [List.length_drop, List.length_cons] at h2
        omega
      have h2 : sv.val.drop (k + 1) = sl := by
        calc sv.val.drop (k + 1) = (sv.val.drop k).drop 1 :=
              (List.drop_drop (i := 1) (j := k)).symm
          _ = (s :: sl).drop 1 := by rw [hdrop]
          _ = sl := rfl
      rw [hit1, h1]
      exact h2.symm
    · intro j hj
      have hj1 : j < st.2.1.val.length := by rw [hlenC]; exact hj
      have hcur := hccur j hj1
      have hval'' := hval' j hj1
      rw [hcur, hval'', hlen', hsplit j]
      omega
    · intro j hj
      have hj1 : j < st.2.1.val.length := by rw [hlenC]; exact hj
      have h1 := hcent j hj1
      have h2 := hcont j hj
      have h2' : slotEntries st.2.2.1.val st.2.2.2.val (r.val.getD j 0#usize).val
          (st.2.1.val.getD j 0#usize).val = towards LTSInst sys sv.val k j := by
        have h := h2
        rw [← hkdef] at h
        exact h
      have h3 := hprot j hj1
      have happ : slotEntries labels1.val src1.val (r.val.getD j 0#usize).val
            (cursor1.val.getD j 0#usize).val
          = slotEntries labels1.val src1.val (r.val.getD j 0#usize).val
              (st.2.1.val.getD j 0#usize).val
            ++ slotEntries labels1.val src1.val (st.2.1.val.getD j 0#usize).val
              (cursor1.val.getD j 0#usize).val := by
        refine slotEntries_append _ _ _ _ _ ?_ ?_
        · have h := hval' j hj1
          omega
        · have h := hccur j hj1
          omega
      rw [happ, h3, h2', h1, hlen',
        towards_succ LTSInst sys sv.val k s sl j hshape,
        towards1_all s (outVec LTSInst sys s) j]

/-- The outer placement loop: every state the LTS enumerates gets its outgoing transitions
    written into the arrays, in enumeration order, and on return the cursor of slot `j` has
    advanced by the number of transitions towards `j` that the whole enumeration
    contributes, with exactly their pairs in `[r[j], cursor[j])`. -/
theorem place_all_incoming_loop_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (r : alloc.vec.Vec Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (st : PaSt)
    (hinv : PaInv LTSInst sys sv r labels0 src0 st)
    (hout : ∀ s, s ∈ sv.val → LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hin : ∀ s, s ∈ sv.val → ∀ t, t ∈ (outVec LTSInst sys s).val →
      t.to.index.val + 1 < r.val.length)
    (hlens : labels0.val.length = src0.val.length)
    (hrlen : sv.val.length + 1 = r.val.length)
    (hmono : ∀ i, i + 1 < r.val.length →
      (r.val.getD i 0#usize).val ≤ (r.val.getD (i+1) 0#usize).val)
    (hcsr : ∀ j, j + 1 < r.val.length →
      (r.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j
        = (r.val.getD (j+1) 0#usize).val)
    (hfill : ∀ j, j < r.val.length → (r.val.getD j 0#usize).val ≤ labels0.val.length)
    (hlenmax : labels0.val.length ≤ Usize.max) :
    ∃ (cursor1 : alloc.vec.Vec Sz) (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.place_all_incoming_loop LTSInst st.1 sys
          st.2.1 st.2.2.1 st.2.2.2 = ok (cursor1, labels1, src1) ∧
      PaPost LTSInst sys sv r cursor1 labels1 src1 := by
  have hspec : verified.merc_lts.incoming_transitions.place_all_incoming_loop LTSInst st.1 sys
          st.2.1 st.2.2.1 st.2.2.2
        ⦃ fun c : PiRes => PaPost LTSInst sys sv r c.1 c.2.1 c.2.2 ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : PaSt => st.1.val.length)
      (inv := PaInv LTSInst sys sv r labels0 src0)
      (post := fun c : PiRes => PaPost LTSInst sys sv r c.1 c.2.1 c.2.2)
      (body := fun st => verified.merc_lts.incoming_transitions.place_all_incoming_loop.body
        LTSInst sys st.1 st.2.1 st.2.2.1 st.2.2.2)
      (x := st)
    · intro st hinv
      by_cases hnil : st.1.val = []
      · rcases place_all_incoming_done LTSInst sys sv r labels0 src0 st hnil hinv with
          ⟨hdone, hpost⟩
        exact Std.WP.exists_imp_spec ⟨done st.2, hdone, hpost⟩
      · obtain ⟨s, sl, hst⟩ := List.exists_cons_of_ne_nil hnil
        have hiter : st.1.val = sv.val.drop (sv.val.length - st.1.val.length) := hinv.1
        have hdrop : sv.val.drop (sv.val.length - st.1.val.length) = s :: sl :=
          hiter.symm.trans hst
        have hmem : s ∈ sv.val :=
          List.mem_of_mem_drop (by rw [hdrop]; exact List.mem_cons_self)
        rcases place_all_incoming_step LTSInst sys sv r labels0 src0 st s sl
            (sv.val.length - st.1.val.length) hst hiter hinv (hout s hmem) (hin s hmem)
            hlens hrlen hmono hcsr hfill hlenmax
          with ⟨iter1, cursor1, labels1, src1, hbody, hit1, hinv1⟩
        refine Std.WP.exists_imp_spec
          ⟨cont (iter1, (cursor1, (labels1, src1))), hbody, hinv1, ?_⟩
        rw [hit1, hst]
        simp
    · exact hinv
  rcases Std.WP.spec_imp_exists hspec with ⟨c, hloop, hpost⟩
  exact ⟨c.1, c.2.1, c.2.2, hloop, hpost⟩

/-- `place_all_incoming` (`:193`): with the state enumeration coming from `iter_states`, the
    whole placement of every state's outgoing transitions is `PaPost`. -/
theorem place_all_incoming_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (sv : alloc.vec.Vec (TagIndex Sz StateTag)) (r : alloc.vec.Vec Sz)
    (cursor0 : alloc.vec.Vec Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (hiter : LTSInst.iter_states sys = ok sv)
    (hclen : cursor0.val.length = sv.val.length)
    (hcget : ∀ k, k < sv.val.length →
      cursor0.val.getD k 0#usize = r.val.getD k 0#usize)
    (hout : ∀ s, s ∈ sv.val → LTSInst.outgoing_transitions sys s = ok (outVec LTSInst sys s))
    (hin : ∀ s, s ∈ sv.val → ∀ t, t ∈ (outVec LTSInst sys s).val →
      t.to.index.val + 1 < r.val.length)
    (hlens : labels0.val.length = src0.val.length)
    (hrlen : sv.val.length + 1 = r.val.length)
    (hmono : ∀ i, i + 1 < r.val.length →
      (r.val.getD i 0#usize).val ≤ (r.val.getD (i+1) 0#usize).val)
    (hcsr : ∀ j, j + 1 < r.val.length →
      (r.val.getD j 0#usize).val + seenCount LTSInst sys sv.val sv.val.length j
        = (r.val.getD (j+1) 0#usize).val)
    (hfill : ∀ j, j < r.val.length → (r.val.getD j 0#usize).val ≤ labels0.val.length)
    (hlenmax : labels0.val.length ≤ Usize.max) :
    ∃ (cursor1 : alloc.vec.Vec Sz) (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.place_all_incoming LTSInst sys cursor0
          labels0 src0 = ok (cursor1, labels1, src1) ∧
      PaPost LTSInst sys sv r cursor1 labels1 src1 := by
  have hinv0 : PaInv LTSInst sys sv r labels0 src0
      ((sv : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag)), (cursor0, (labels0, src0))) :=
    ⟨by simp, hclen, rfl, rfl,
      by intro j hj; rw [hcget j hj]; simp [seenCount],
      by intro j hj; rw [hcget j hj]; simp [towards, slotEntries]⟩
  rcases place_all_incoming_loop_spec LTSInst sys sv r labels0 src0
      ((sv : alloc.vec.into_iter.IntoIter (TagIndex Sz StateTag)), (cursor0, (labels0, src0)))
      hinv0 hout hin hlens hrlen hmono hcsr hfill hlenmax with ⟨cursor1, labels1, src1, hloop, hpost⟩
  refine ⟨cursor1, labels1, src1, ?_, hpost⟩
  unfold verified.merc_lts.incoming_transitions.place_all_incoming
  simp only [hiter, alloc.vec.IntoIteratorVec.into_iter, bind_tc_ok]
  exact hloop


/-! ## Stage 7: `sort_all_incoming`

`sort_all_incoming` (`incoming_transitions.rs:206`) insertion-sorts the range of every state:
`sort_incoming` walks the range `[start, end)` from the second position, and for each position
`i` runs `insert_sorted`, which holds the pair at `i` aside and shifts everything to its left
that sorts after it. Nothing here is about *order*: `IncomingTransitionsCorrect` only asks
which pairs a state's range holds, so the invariant is a positional description of the shift,
from which "the range as a whole holds the same pairs" follows by a bijection of positions.

The contract needs one thing from stage 6: for every state, the pairs that
`place_all_incoming` wrote into its range (`towards`). So it suffices to track, for each state,
that the range it handed over still holds the same pairs afterwards.

* `insert_sorted_loop` - the inner shifting loop of `insert_sorted`; its invariant is
  `IsInv`, which describes where every position of `[start, i]` gets its pair from.
* `sort_incoming_loop` - the walk over the range, accumulating the sorted prefix.
* `sort_all_incoming_loop` - the walk over the states, each sorting its own range.
-/

/-- Two flat arrays carry the same pairs in the window `[a, b)`. -/
def sameWindow (labels : List (TagIndex Sz LabelTag)) (src : List (TagIndex Sz StateTag))
    (labels0 : List (TagIndex Sz LabelTag)) (src0 : List (TagIndex Sz StateTag))
    (a b : Nat) : Prop :=
  ∀ x, x ∈ slotEntries labels src a b ↔ x ∈ slotEntries labels0 src0 a b

/-- Every position of `[a, b)` is one of the positions a window runs over. -/
private theorem mem_range'_of_lt {a b p : Nat} (h1 : a ≤ p) (h2 : p < b) :
    p ∈ List.range' a (b - a) := by
  rw [List.mem_range']
  exact ⟨p - a, by omega, by omega⟩

/-- Every position of `[a, b)` is read back by the window's entries. -/
private theorem mem_map_window {α : Type} {f : Nat → α} {a b p : Nat}
    (h1 : a ≤ p) (h2 : p < b) :
    f p ∈ (List.range' a (b - a)).map f :=
  List.mem_map.mpr ⟨p, mem_range'_of_lt h1 h2, rfl⟩

/-- If reading position `p` of the new arrays is reading position `φ p` of the old ones, and
    `φ` maps the window onto itself, then both windows hold the same pairs. Injectivity is not
    needed: surjectivity of `φ` turns every old pair into a new one, and `h2` turns every new
    pair into an old one. -/
private theorem mem_map_eq_of_reindex {α : Type} {f f0 : Nat → α} {a b : Nat} (φ : Nat → Nat)
    (h1 : ∀ p, a ≤ p → p < b → f p = f0 (φ p))
    (h2 : ∀ p, a ≤ p → p < b → a ≤ φ p ∧ φ p < b)
    (h3 : ∀ q, a ≤ q → q < b → ∃ p, a ≤ p ∧ p < b ∧ φ p = q) :
    ∀ x, x ∈ (List.range' a (b - a)).map f ↔ x ∈ (List.range' a (b - a)).map f0 := by
  intro x
  constructor
  · intro hx
    obtain ⟨p, hp, hfx⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, hpos⟩ := List.mem_range'.mp hp
    have hpa : a ≤ p := by omega
    have hpb : p < b := by omega
    have hr := h2 p hpa hpb
    exact List.mem_map.mpr ⟨φ p, mem_range'_of_lt hr.1 hr.2, (h1 p hpa hpb).symm.trans hfx⟩
  · intro hx
    obtain ⟨q, hq, hfx⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, hpos⟩ := List.mem_range'.mp hq
    have hqa : a ≤ q := by omega
    have hqb : q < b := by omega
    rcases h3 q hqa hqb with ⟨p, hpa, hpb, hφ⟩
    refine List.mem_map.mpr ⟨p, mem_range'_of_lt hpa hpb, ?_⟩
    rw [h1 p hpa hpb, hφ]
    exact hfx

/-- Where the pair held aside at position `i` ends up, once it comes to rest at `j`: below `j`
    positions are untouched, `j` receives the held pair, and everything above `j` has been
    shifted up by one position, so it holds what one position lower held. -/
private def insPos (i j p : Nat) : Nat :=
  if p < j then p else if p = j then i else p - 1

private theorem insPos_lt {i j p : Nat} (hp : p < j) : insPos i j p = p := by
  simp [insPos, hp]

private theorem insPos_eq {i j : Nat} : insPos i j j = i := by
  simp [insPos]

private theorem insPos_gt {i j p : Nat} (h1 : j < p) : insPos i j p = p - 1 := by
  have h2 : ¬(p = j) := by omega
  have h3 : ¬(p < j) := by omega
  simp [insPos, h3, h2]

/-- Within `[0, i]` the reindexing of an insertion is injective: two positions are sent to the
    same original position only if they are the same position. -/
private theorem insPos_inj {i j : Nat} (hj : j ≤ i) {p q : Nat} (h1 : p ≤ i) (h2 : q ≤ i)
    (hp : insPos i j p = insPos i j q) : p = q := by
  by_cases hpl : p < j <;> by_cases hql : q < j <;>
    by_cases hpe : p = j <;> by_cases hqe : q = j
  all_goals simp [insPos, hpl, hpe, hql, hqe] at hp
  all_goals omega

/-- Every original position of `[0, i]` is read from some position of `[0, i]`. -/
private theorem insPos_surj {i j : Nat} (hj : j ≤ i) {q : Nat} (h1 : q ≤ i) :
    ∃ p, p ≤ i ∧ insPos i j p = q := by
  by_cases hqe : q = j
  · subst q
    by_cases hji : j = i
    · exact ⟨i, by omega, by rw [hji]; exact insPos_eq⟩
    · exact ⟨j + 1, by omega, by rw [insPos_gt (by omega)]; omega⟩
  by_cases hql : q < j
  · exact ⟨q, h1, insPos_lt hql⟩
  by_cases hqi : q = i
  · exact ⟨j, hj, by rw [hqi]; exact insPos_eq⟩
  exact ⟨q + 1, by omega, by rw [insPos_gt (by omega)]; omega⟩

/-- A window holding the same pairs as before, extended by one position that also holds the
    same pair, holds the same pairs as the extended window. -/
private theorem sameWindow_succ (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (labels0 : List (TagIndex Sz LabelTag))
    (src0 : List (TagIndex Sz StateTag)) (a b : Nat) (hab : a ≤ b)
    (h : sameWindow labels src labels0 src0 a b)
    (hv : pairAt labels src b = pairAt labels0 src0 b) :
    sameWindow labels src labels0 src0 a (b + 1) := by
  intro x
  simp only [slotEntries_succ _ _ _ _ hab, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h' | h')
    · exact Or.inl ((h x).mp h')
    · right; rw [← hv]; exact h'
  · rintro (h' | h')
    · exact Or.inl ((h x).mpr h')
    · right; rw [hv]; exact h'


/-- State of the insertion loop: the two arrays, and how far left the pair held aside at `i`
    still has to travel. -/
abbrev IsSt := alloc.vec.Vec (TagIndex Sz LabelTag)
  × alloc.vec.Vec (TagIndex Sz StateTag) × Sz

/-- Invariant of the insertion: with `j` the position the held pair has reached so far,
    * everything below `j` is as it was;
    * everything between `j` and `i` has been shifted up by one position, so position `p`
      holds what position `p - 1` held;
    * nothing above `i` has been touched, and both arrays keep their lengths. -/
def IsInv (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start i j : Nat) : IsSt → Prop :=
  fun st =>
    start ≤ j ∧ j ≤ i ∧
    st.1.val.length = labels0.val.length ∧
    st.2.1.val.length = src0.val.length ∧
    labels0.val.length = src0.val.length ∧
    (∀ p, p < j → pairAt st.1.val st.2.1.val p = pairAt labels0.val src0.val p) ∧
    (∀ p, j < p → p ≤ i →
      pairAt st.1.val st.2.1.val p = pairAt labels0.val src0.val (p - 1)) ∧
    (∀ p, i < p → pairAt st.1.val st.2.1.val p = pairAt labels0.val src0.val p)

/-- The scalar carried by `1#usize`; `omega` treats `UScalar.val` of a literal as an opaque
    atom, so the generated `j - 1#usize` has to be opened up explicitly. -/
private theorem one_val : (1#usize : Sz).val = 1 := rfl

/-- `j ≤ start`: there is nothing left of `j` to compare against, so the held pair is already
    in place. -/
theorem insert_sorted_done_start (start : Sz) (label : TagIndex Sz LabelTag)
    (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src : alloc.vec.Vec (TagIndex Sz StateTag)) (j : Sz) (hle : j.val ≤ start.val) :
    verified.merc_lts.incoming_transitions.insert_sorted_loop.body start label labels src j
      = ok (done (labels, src, j)) := by
  have h' : ¬(j > start) := by simp [hle]
  unfold verified.merc_lts.incoming_transitions.insert_sorted_loop.body
  rw [if_neg h']

/-- The pair left of `j` does not sort after the held pair, so the held pair is already in
    place. -/
theorem insert_sorted_done_cmp (start : Sz) (label : TagIndex Sz LabelTag)
    (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src : alloc.vec.Vec (TagIndex Sz StateTag)) (j : Sz)
    (hlen : labels.val.length = src.val.length) (hj : j.val < labels.val.length)
    (hstart : start.val < j.val)
    (hcmp : (labels.val.getD (j.val - 1) zeroLabel).index.val ≤ label.index.val) :
    verified.merc_lts.incoming_transitions.insert_sorted_loop.body start label labels src j
      = ok (done (labels, src, j)) := by
  have h' : j > start := by simp [hstart]
  have hpos : j.val - 1 < labels.val.length := by omega
  have hpos' : j.val - 1 < src.val.length := by omega
  have hsub : 1 ≤ j.val := by omega
  rcases Std.WP.spec_imp_exists (Usize.sub_spec (x := j) (y := 1#usize) hsub) with
    ⟨i, hi, hival⟩
  rcases hival with ⟨hival', hivalle⟩
  simp only [one_val] at hival' hivalle
  have hposI : i.val < labels.val.length := by rw [hival']; exact hpos
  have hidxL : labels.index_usize i = ok (labels.val[i.val]'hposI) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec labels i hposI
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have hget : labels.val[i.val]'hposI = labels.val.getD (j.val - 1) zeroLabel := by
    calc labels.val[i.val]'hposI = labels.val.getD i.val zeroLabel :=
        getElem_eq_getD labels.val i.val zeroLabel hposI
      _ = labels.val.getD (j.val - 1) zeroLabel := by rw [hival']
  have hnD : ¬((labels.val.getD (j.val - 1) zeroLabel).index > label.index) := by
    simpa using hcmp
  unfold verified.merc_lts.incoming_transitions.insert_sorted_loop.body
  rw [if_pos h', hi]
  simp only [bind_tc_ok, alloc.vec.Vec.index_slice_index, hidxL, hget, tag_value_id]
  split
  · rename_i hbad
    exact absurd hbad hnD
  · simp

/-- The pair left of `j` sorts after the held pair: it moves up to `j`, and the scan
    continues one position further left. -/
theorem insert_sorted_step
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (start : Sz) (label : TagIndex Sz LabelTag) (i : Sz) (j : Sz)
    (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src : alloc.vec.Vec (TagIndex Sz StateTag))
    (hi : i.val < labels0.val.length) (hstart : start.val < j.val)
    (hcmp : label.index.val < (labels.val.getD (j.val - 1) zeroLabel).index.val)
    (hinv : IsInv labels0 src0 start.val i.val j.val (labels, src, j)) :
    ∃ (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)) (j1 : Sz),
      verified.merc_lts.incoming_transitions.insert_sorted_loop.body start label labels src j
        = ok (cont (labels1, src1, j1)) ∧
      j1.val = j.val - 1 ∧
      labels1.val = labels.val.set j.val (labels.val.getD (j.val - 1) zeroLabel) ∧
      src1.val = src.val.set j.val (src.val.getD (j.val - 1) zeroState) ∧
      IsInv labels0 src0 start.val i.val j1.val (labels1, src1, j1) := by
  rcases hinv with ⟨hstart0, hji, hlenL, hlenS, hlen0, hA, hB, hC⟩
  simp only [] at hstart0 hji hlenL hlenS hlen0 hA hB hC
  have hi' : i.val < src.val.length := by omega
  have h' : j > start := by simp [hstart]
  have hpos : j.val - 1 < labels.val.length := by omega
  have hpos' : j.val - 1 < src.val.length := by omega
  have hjlt : j.val < labels.val.length := by omega
  have hjlt' : j.val < src.val.length := by omega
  have hsub : 1 ≤ j.val := by omega
  rcases Std.WP.spec_imp_exists (Usize.sub_spec (x := j) (y := 1#usize) hsub) with
    ⟨j1, hj1, hj1all⟩
  rcases hj1all with ⟨hj1val, hj1le⟩
  simp only [one_val] at hj1val hj1le
  have hpos1 : j1.val < labels.val.length := by rw [hj1val]; exact hpos
  have hidxL : labels.index_usize j1 = ok (labels.val[j1.val]'hpos1) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec labels j1 hpos1
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have hidxLj : labels.index_usize j = ok (labels.val[j.val]'hjlt) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec labels j hjlt
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have hidxFj : src.index_usize j = ok (src.val[j.val]'hjlt') := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec src j hjlt'
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have himutLj : labels.index_mut_usize j
      = ok (labels.val[j.val]'hjlt, fun x => labels.set j x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxLj]
  have himutFj : src.index_mut_usize j
      = ok (src.val[j.val]'hjlt', fun x => src.set j x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxFj]
  have hget : labels.val[j1.val]'hpos1 = labels.val.getD (j.val - 1) zeroLabel := by
    calc labels.val[j1.val]'hpos1 = labels.val.getD j1.val zeroLabel :=
        getElem_eq_getD labels.val j1.val zeroLabel hpos1
      _ = labels.val.getD (j.val - 1) zeroLabel := by rw [hj1val]
  have hgetL : labels.val[j.val]'hjlt = labels.val.getD j.val zeroLabel :=
    getElem_eq_getD labels.val j.val zeroLabel hjlt
  have hgetF : src.val[j.val]'hjlt' = src.val.getD j.val zeroState :=
    getElem_eq_getD src.val j.val zeroState hjlt'
  have hgtI : (labels.val[j1.val]'hpos1).index > label.index := by
    rw [hget]; simpa using hcmp
  have hgtD : (labels.val.getD (j.val - 1) zeroLabel).index > label.index := by
    simpa using hcmp
  have hposF1 : j1.val < src.val.length := by rw [hj1val]; exact hpos'
  have hidxF1 : src.index_usize j1 = ok (src.val[j1.val]'hposF1) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec src j1 hposF1
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have hgetF1 : src.val[j1.val]'hposF1 = src.val.getD (j.val - 1) zeroState := by
    calc src.val[j1.val]'hposF1 = src.val.getD j1.val zeroState :=
        getElem_eq_getD src.val j1.val zeroState hposF1
      _ = src.val.getD (j.val - 1) zeroState := by rw [hj1val]
  refine ⟨labels.set j (labels.val.getD (j.val - 1) zeroLabel),
    src.set j (src.val.getD (j.val - 1) zeroState),
    j1, ?_, hj1val,
    alloc.vec.Vec.set_val_eq labels j _,
    alloc.vec.Vec.set_val_eq src j _, ?_⟩
  · unfold verified.merc_lts.incoming_transitions.insert_sorted_loop.body
    rw [if_pos h', hj1]
    simp only [bind_tc_ok, alloc.vec.Vec.index_slice_index, hidxL, hget, tag_value_id,
      hidxF1, hgetF1]
    split
    · simp [alloc.vec.Vec.index_mut_slice_index, himutLj, himutFj]
    · rename_i hbad
      exact absurd hgtD (by simpa using hbad)
  · refine ⟨by omega, by omega, ?_, ?_, hlen0, ?_, ?_, ?_⟩
    · simp only [alloc.vec.Vec.set_val_eq, List.length_set]; omega
    · simp only [alloc.vec.Vec.set_val_eq, List.length_set]; omega
    · intro p hp
      simp only [alloc.vec.Vec.set_val_eq]
      rw [pairAt_set_ne labels.val src.val p j.val _ _ (by omega), hA p (by omega)]
    · intro p hp1 hp2
      simp only [alloc.vec.Vec.set_val_eq]
      by_cases hpj : p = j.val
      · subst hpj
        rw [pairAt_set_self labels.val src.val j.val _ _ hjlt hjlt']
        exact hA (j.val - 1) (by omega)
      · rw [pairAt_set_ne labels.val src.val p j.val _ _ (by omega), hB p (by omega) hp2]
    · intro p hp
      simp only [alloc.vec.Vec.set_val_eq]
      rw [pairAt_set_ne labels.val src.val p j.val _ _ (by omega), hC p hp]

/-- Loop invariant of the insertion scan, at whatever position the scan has reached: the
    pairs seen so far are only the ones of the range it walks over, and the position is
    still inside the two arrays. -/
def IsLoop (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start i : Nat) : IsSt → Prop :=
  fun st => IsInv labels0 src0 start i st.2.2.val st ∧ st.2.2.val < labels0.val.length

/-- What the insertion scan leaves behind, at the position it came to rest at: everything
    left of it is as it was, everything right of it up to `i` has been shifted up by one
    position, and both arrays keep their length. -/
def IsPost (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start i : Nat) : IsSt → Prop :=
  fun st =>
    start ≤ st.2.2.val ∧
    st.2.2.val ≤ i ∧
    st.1.val.length = labels0.val.length ∧
    st.2.1.val.length = src0.val.length ∧
    (∀ p, p < st.2.2.val → pairAt st.1.val st.2.1.val p = pairAt labels0.val src0.val p) ∧
    (∀ p, st.2.2.val < p → p ≤ i → pairAt st.1.val st.2.1.val p
      = pairAt labels0.val src0.val (p - 1)) ∧
    (∀ p, i < p → pairAt st.1.val st.2.1.val p = pairAt labels0.val src0.val p)

/-- The pair arrays have equally long, and the position the scan reaches is inside them. -/
theorem isPost_of_inv (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start i : Nat) (st : IsSt)
    (hinv : IsInv labels0 src0 start i st.2.2.val st) :
    IsPost labels0 src0 start i st := by
  rcases hinv with ⟨hstart, hjle, hlenL, hlenS, _, hA, hB, hC⟩
  exact ⟨hstart, hjle, hlenL, hlenS, hA, hB, hC⟩

theorem insert_sorted_loop_spec
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (start : Sz) (label : TagIndex Sz LabelTag) (i : Sz) (j : Sz)
    (hi : i.val < labels0.val.length)
    (hloop : IsLoop labels0 src0 start.val i.val (labels0, src0, j)) :
    ∃ (st : IsSt),
      verified.merc_lts.incoming_transitions.insert_sorted_loop labels0 src0 start label j
        = ok st ∧
      IsPost labels0 src0 start.val i.val st := by
  have hspec : (@loop IsSt IsSt
        (fun st => verified.merc_lts.incoming_transitions.insert_sorted_loop.body start label
          st.1 st.2.1 st.2.2)
        (labels0, src0, j))
      ⦃ fun st : IsSt => IsPost labels0 src0 start.val i.val st ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : IsSt => st.2.2.val)
      (inv := fun st : IsSt => IsLoop labels0 src0 start.val i.val st)
      (post := fun st : IsSt => IsPost labels0 src0 start.val i.val st)
      (body := fun st => verified.merc_lts.incoming_transitions.insert_sorted_loop.body start
        label st.1 st.2.1 st.2.2)
      (x := (labels0, src0, j))
    · intro st hinv
      rcases hinv with ⟨hinv, hjlt⟩
      rcases hinv with ⟨hstart0, hji, hlenL, hlenS, hlen0, hA, hB, hC⟩
      by_cases hle : st.2.2.val ≤ start.val
      · refine Std.WP.exists_imp_spec
          ⟨done st, insert_sorted_done_start start label st.1 st.2.1 st.2.2 hle, ?_⟩
        exact isPost_of_inv labels0 src0 start.val i.val st
          ⟨by omega, hji, hlenL, hlenS, hlen0, hA, hB, hC⟩
      · have hgt : start.val < st.2.2.val := by omega
        have hjlt' : st.2.2.val < src0.val.length := by omega
        by_cases hcmp :
            (st.1.val.getD (st.2.2.val - 1) zeroLabel).index.val > label.index.val
        · obtain ⟨labels1, src1, j1, hbody, hj1val, hlenL', hlenS', hinv'⟩ :=
            insert_sorted_step labels0 src0 start label i st.2.2 st.1 st.2.1
              hi hgt (by simpa using hcmp)
              ⟨by omega, hji, hlenL, hlenS, hlen0, hA, hB, hC⟩
          refine Std.WP.exists_imp_spec ⟨cont (labels1, src1, j1), hbody, ?_⟩
          show IsLoop labels0 src0 start.val i.val (labels1, src1, j1) ∧ j1.val < st.2.2.val
          unfold IsLoop
          have htuple : (labels1, src1, j1).2.2.val = j1.val := rfl
          refine ⟨⟨hinv', ?_⟩, by omega⟩
          rw [htuple]
          omega
        · refine Std.WP.exists_imp_spec
            ⟨done st,
              insert_sorted_done_cmp start label st.1 st.2.1 st.2.2 (by omega) (by omega) hgt
                (by simpa using hcmp),
              ?_⟩
          exact isPost_of_inv labels0 src0 start.val i.val st
            ⟨by omega, hji, hlenL, hlenS, hlen0, hA, hB, hC⟩

    · exact hloop
  rcases Std.WP.spec_imp_exists hspec with ⟨st, hloop', hpost⟩
  exact ⟨st, hloop', hpost⟩

/-- What `insert_sorted` leaves behind: the window `[start, i + 1)` holds the pairs it held
    before - the one that was held aside only moves inside that window - everything above `i`
    is untouched, and both arrays keep their length. -/
def IsIns (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start i : Nat)
    (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src1 : alloc.vec.Vec (TagIndex Sz StateTag)) : Prop :=
  sameWindow labels1.val src1.val labels0.val src0.val start (i + 1) ∧
  (∀ p, i < p → pairAt labels1.val src1.val p = pairAt labels0.val src0.val p) ∧
  labels1.val.length = labels0.val.length ∧
  src1.val.length = src0.val.length ∧
  (∀ p, p < start → pairAt labels1.val src1.val p = pairAt labels0.val src0.val p)

theorem insert_sorted_spec
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (start : Sz) (i : Sz) (hstart : start.val ≤ i.val) (hi : i.val < labels0.val.length)
    (hlen0 : labels0.val.length = src0.val.length) :
    ∃ (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.insert_sorted labels0 src0 start i
        = ok (labels1, src1) ∧
      IsIns labels0 src0 start.val i.val labels1 src1 := by
  have hi' : i.val < src0.val.length := by omega
  have hidxL : labels0.index_usize i = ok (labels0.val.getD i.val zeroLabel) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec labels0 i hi
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv,
      getElem_eq_getD labels0.val i.val zeroLabel hi]
  have hidxF : src0.index_usize i = ok (src0.val.getD i.val zeroState) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec src0 i hi'
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv,
      getElem_eq_getD src0.val i.val zeroState hi']
  have hinv0 : IsInv labels0 src0 start.val i.val i.val (labels0, src0, i) := by
    refine ⟨hstart, le_rfl, rfl, rfl, hlen0, ?_, ?_, ?_⟩
    · intro p _
      rfl
    · intro p h1 h2
      omega
    · intro p _
      rfl
  obtain ⟨st, hloop, hpost⟩ :=
    insert_sorted_loop_spec labels0 src0 start (labels0.val.getD i.val zeroLabel) i i hi
      ⟨hinv0, hi⟩
  rcases st with ⟨labels1, src1, j⟩
  have htuple : (labels1, src1, j).2.2.val = j.val := rfl
  unfold IsPost at hpost
  rw [htuple] at hpost
  rcases hpost with ⟨hstartj, hjle, hlenL, hlenS, hA, hB, hC⟩
  have hjlt : j.val < labels1.val.length := by rw [hlenL]; omega
  have hjlt' : j.val < src1.val.length := by rw [hlenS]; omega
  have hidxLj : labels1.index_usize j = ok (labels1.val[j.val]'hjlt) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec labels1 j hjlt
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have hidxFj : src1.index_usize j = ok (src1.val[j.val]'hjlt') := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec src1 j hjlt'
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv]
  have himutLj : labels1.index_mut_usize j
      = ok (labels1.val[j.val]'hjlt, fun x => labels1.set j x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxLj]
  have himutFj : src1.index_mut_usize j
      = ok (src1.val[j.val]'hjlt', fun x => src1.set j x) := by
    simp [alloc.vec.Vec.index_mut_usize, hidxFj]
  refine ⟨labels1.set j (labels0.val.getD i.val zeroLabel),
    src1.set j (src0.val.getD i.val zeroState), ?_, ?_⟩
  · unfold verified.merc_lts.incoming_transitions.insert_sorted
    simp only [alloc.vec.Vec.index_slice_index, hidxL, hidxF, bind_tc_ok]
    rw [hloop]
    simp [alloc.vec.Vec.index_mut_slice_index, himutLj, himutFj]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x
      unfold slotEntries
      refine mem_map_eq_of_reindex
        (f := fun p => pairAt (labels1.set j (labels0.val.getD i.val zeroLabel)).val
            (src1.set j (src0.val.getD i.val zeroState)).val p)
        (f0 := fun p => pairAt labels0.val src0.val p) (a := start.val) (b := i.val + 1)
        (fun p => insPos i.val j.val p) ?_ ?_ ?_ x
      · intro p h1 h2
        by_cases hpj : p = j.val
        · subst hpj
          simp only [alloc.vec.Vec.set_val_eq, pairAt, gds_self, if_pos hjlt, if_pos hjlt']
          rw [insPos_eq]
        · simp only [alloc.vec.Vec.set_val_eq]
          rw [pairAt_set_ne labels1.val src1.val p j.val _ _ (by omega)]
          by_cases hpl : p < j.val
          · rw [insPos_lt hpl]
            exact hA p hpl
          · rw [insPos_gt (by omega)]
            exact hB p (by omega) (by omega)
      · intro p h1 h2
        by_cases hpl : p < j.val
        · rw [insPos_lt hpl]
          exact ⟨h1, by omega⟩
        · by_cases hpj : p = j.val
          · subst hpj
            rw [insPos_eq]
            exact ⟨hstart, by omega⟩
          · rw [insPos_gt (by omega)]
            exact ⟨by omega, by omega⟩
      · intro q h1 h2
        by_cases hqj : q = j.val
        · by_cases hji : j.val = i.val
          · exact ⟨i.val, by omega, by omega, by rw [hqj, hji, insPos_eq]⟩
          · exact ⟨j.val + 1, by omega, by omega, by
              rw [insPos_gt (i := i.val) (j := j.val) (p := j.val + 1) (by omega)]
              omega⟩
        · by_cases hqi : q = i.val
          · exact ⟨j.val, hstartj, by omega, by rw [hqi, insPos_eq]⟩
          · by_cases hql : q < j.val
            · exact ⟨q, h1, by omega, by rw [insPos_lt hql]⟩
            · exact ⟨q + 1, by omega, by omega, by
                rw [insPos_gt (i := i.val) (j := j.val) (p := q + 1) (by omega)]
                omega⟩
    · intro p hp
      simp only [alloc.vec.Vec.set_val_eq]
      rw [pairAt_set_ne labels1.val src1.val p j.val _ _ (by omega)]
      exact hC p hp
    · simp only [alloc.vec.Vec.set_val_eq, List.length_set]
      exact hlenL
    · simp only [alloc.vec.Vec.set_val_eq, List.length_set]
      exact hlenS
    · intro p hp
      simp only [alloc.vec.Vec.set_val_eq]
      rw [pairAt_set_ne labels1.val src1.val p j.val _ _ (by omega)]
      exact hA p (by omega)

/-- Two windows that are chained hold the same pairs. -/
private theorem sameWindow_trans (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (labels0 : List (TagIndex Sz LabelTag))
    (src0 : List (TagIndex Sz StateTag)) (labels2 : List (TagIndex Sz LabelTag))
    (src2 : List (TagIndex Sz StateTag)) (a b : Nat)
    (h1 : sameWindow labels src labels0 src0 a b)
    (h2 : sameWindow labels0 src0 labels2 src2 a b) :
    sameWindow labels src labels2 src2 a b := by
  intro x
  exact (h1 x).trans (h2 x)

/-- State of the insertion-sort scan: the positions left to insert, and the two arrays. -/
abbrev SorSt := (core.ops.range.Range Std.Usize)
  × alloc.vec.Vec (TagIndex Sz LabelTag) × alloc.vec.Vec (TagIndex Sz StateTag)

/-- Invariant of the scan, where `it.start` is the next position to be inserted and `stop` the
    end of the range being sorted. Either the scan has not started yet, or:
    * the scan has not run past the range: `start ≤ it.start ≤ stop`, and `stop` fits in the
      arrays;
    * the range `[start, it.start)` holds the pairs it held before, and nothing from `it.start`
      on has been touched;
    * both arrays keep their length. -/
def SorInv (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start stop : Sz) : SorSt → Prop :=
  fun st =>
    (st.1.start.val = start.val + 1 ∧
     st.2.1.val = labels0.val ∧
     st.2.2.val = src0.val ∧
     st.1.end.val = stop.val ∧
     stop.val ≤ st.2.1.val.length ∧
     st.2.1.val.length = st.2.2.val.length) ∨
    (start.val ≤ st.1.start.val ∧
     st.1.start.val ≤ stop.val ∧
     st.1.end.val = stop.val ∧
     stop.val ≤ st.2.1.val.length ∧
     st.2.1.val.length = st.2.2.val.length ∧
     sameWindow st.2.1.val st.2.2.val labels0.val src0.val start.val st.1.start.val ∧
     (∀ p, st.1.start.val ≤ p → pairAt st.2.1.val st.2.2.val p
       = pairAt labels0.val src0.val p) ∧
     st.2.1.val.length = labels0.val.length ∧
     st.2.2.val.length = src0.val.length ∧
     (∀ p, p < start.val → pairAt st.2.1.val st.2.2.val p
       = pairAt labels0.val src0.val p))

/-- What the scan leaves behind: the range `[start, stop)` holds the pairs it held before, both
    arrays keep their length, and the points outside that range are untouched - below `start`
    because the scan never writes there, and from `stop` on because the scan never reaches there. -/
def SorPost (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start stop : Sz)
    (r : alloc.vec.Vec (TagIndex Sz LabelTag) × alloc.vec.Vec (TagIndex Sz StateTag)) : Prop :=
  sameWindow r.1.val r.2.val labels0.val src0.val start.val stop.val ∧
  r.1.val.length = labels0.val.length ∧
  r.2.val.length = src0.val.length ∧
  (∀ p, p < start.val → pairAt r.1.val r.2.val p = pairAt labels0.val src0.val p) ∧
  (∀ p, stop.val ≤ p → pairAt r.1.val r.2.val p = pairAt labels0.val src0.val p)

theorem sort_incoming_loop_spec
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (iter : core.ops.range.Range Std.Usize) (start : Sz)
    (hinv : SorInv labels0 src0 start iter.end (iter, labels0, src0)) :
    ∃ (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.sort_incoming_loop iter labels0 src0 start
        = ok (labels1, src1) ∧
      SorPost labels0 src0 start iter.end (labels1, src1) := by
  have hspec : (@loop SorSt (alloc.vec.Vec (TagIndex Sz LabelTag)
        × alloc.vec.Vec (TagIndex Sz StateTag))
      (fun st => verified.merc_lts.incoming_transitions.sort_incoming_loop.body start
        st.1 st.2.1 st.2.2)
      (iter, labels0, src0))
      ⦃ fun r => SorPost labels0 src0 start iter.end r ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : SorSt => st.1.end.val - st.1.start.val)
      (inv := fun st : SorSt => SorInv labels0 src0 start iter.end st)
      (post := fun r => SorPost labels0 src0 start iter.end r)
      (body := fun st => verified.merc_lts.incoming_transitions.sort_incoming_loop.body start
        st.1 st.2.1 st.2.2)
      (x := (iter, labels0, src0))
    · intro st hinv
      unfold SorInv at hinv
      rcases hinv with ⟨hit, hsameL, hsameS, hend, hbound, hlen0⟩ | ⟨hstart0, hnext0, hend,
        hbound, hlen0, hwin, habove, hlenL, hlenS, hbelow0⟩
      · by_cases hdone : st.1.end.val ≤ st.1.start.val
        · obtain ⟨o, iter1, hnext, hone, hident⟩ := next_range_none st.1 hdone
          have hbody :
              verified.merc_lts.incoming_transitions.sort_incoming_loop.body start st.1 st.2.1
                  st.2.2 = ok (done (st.2.1, st.2.2)) := by
            unfold verified.merc_lts.incoming_transitions.sort_incoming_loop.body
            rw [hnext, hone]
            simp
          refine Std.WP.exists_imp_spec ⟨done (st.2.1, st.2.2), hbody, ?_⟩
          show sameWindow st.2.1.val st.2.2.val labels0.val src0.val start.val iter.end.val ∧
            st.2.1.val.length = labels0.val.length ∧ st.2.2.val.length = src0.val.length ∧
            (∀ p, p < start.val → pairAt st.2.1.val st.2.2.val p
              = pairAt labels0.val src0.val p) ∧
            (∀ p, iter.end.val ≤ p → pairAt st.2.1.val st.2.2.val p
              = pairAt labels0.val src0.val p)
          rw [hsameL, hsameS]
          exact ⟨fun _ => Iff.rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
        · have hlt : st.1.start.val < st.1.end.val := by omega
          obtain ⟨o, iter1, hnext, hsome, hstart1, hend1⟩ := next_range_some st.1 hlt
          have hstart0 : start.val ≤ st.1.start.val := by omega
          have hend1v : iter1.end.val = st.1.end.val := congrArg _ hend1
          obtain ⟨labels1, src1, hsort, hins⟩ :=
            insert_sorted_spec st.2.1 st.2.2 start st.1.start hstart0 (by omega) hlen0
          have hbody :
              verified.merc_lts.incoming_transitions.sort_incoming_loop.body start st.1 st.2.1
                  st.2.2 = ok (cont (iter1, labels1, src1)) := by
            unfold verified.merc_lts.incoming_transitions.sort_incoming_loop.body
            rw [hnext, hsome]
            simp [hsort]
          refine Std.WP.exists_imp_spec ⟨cont (iter1, labels1, src1), hbody, ?_⟩
          change SorInv labels0 src0 start iter.end (iter1, labels1, src1) ∧
            (iter1.end.val - iter1.start.val) < (st.1.end.val - st.1.start.val)
          rcases hins with ⟨hwin', htail, hlenL', hlenS', hbelow⟩
          have hlt' : (iter1.end.val - iter1.start.val) < (st.1.end.val - st.1.start.val) := by
            omega
          have hinv' : SorInv labels0 src0 start iter.end (iter1, labels1, src1) := by
            show (iter1.start.val = start.val + 1 ∧
              labels1.val = labels0.val ∧
              src1.val = src0.val ∧
              iter1.end.val = iter.end.val ∧
              iter.end.val ≤ labels1.val.length ∧
              labels1.val.length = src1.val.length) ∨
              (start.val ≤ iter1.start.val ∧
               iter1.start.val ≤ iter.end.val ∧
               iter1.end.val = iter.end.val ∧
               iter.end.val ≤ labels1.val.length ∧
               labels1.val.length = src1.val.length ∧
               sameWindow labels1.val src1.val labels0.val src0.val start.val iter1.start.val ∧
               (∀ p, iter1.start.val ≤ p →
                 pairAt labels1.val src1.val p = pairAt labels0.val src0.val p) ∧
               labels1.val.length = labels0.val.length ∧
               src1.val.length = src0.val.length ∧
               (∀ p, p < start.val → pairAt labels1.val src1.val p
                 = pairAt labels0.val src0.val p))
            refine Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · omega
            · omega
            · omega
            · omega
            · rw [hlenL', hlenS']
              exact hlen0
            · rw [hstart1]
              rw [hsameL, hsameS] at hwin'
              exact hwin'
            · intro p hp
              rw [hstart1] at hp
              exact (htail p (by omega)).trans (by rw [hsameL, hsameS])
            · exact hlenL'.trans (congrArg _ hsameL)
            · exact hlenS'.trans (congrArg _ hsameS)
            · intro p hp
              exact (hbelow p hp).trans (by rw [hsameL, hsameS])
          exact ⟨hinv', hlt'⟩
      · by_cases hdone : st.1.end.val ≤ st.1.start.val
        · obtain ⟨o, iter1, hnext, hone, hident⟩ := next_range_none st.1 hdone
          have hbody :
              verified.merc_lts.incoming_transitions.sort_incoming_loop.body start st.1 st.2.1
                  st.2.2 = ok (done (st.2.1, st.2.2)) := by
            unfold verified.merc_lts.incoming_transitions.sort_incoming_loop.body
            rw [hnext, hone]
            simp
          refine Std.WP.exists_imp_spec ⟨done (st.2.1, st.2.2), hbody, ?_⟩
          show sameWindow st.2.1.val st.2.2.val labels0.val src0.val start.val iter.end.val ∧
            st.2.1.val.length = labels0.val.length ∧ st.2.2.val.length = src0.val.length ∧
            (∀ p, p < start.val → pairAt st.2.1.val st.2.2.val p
              = pairAt labels0.val src0.val p) ∧
            (∀ p, iter.end.val ≤ p → pairAt st.2.1.val st.2.2.val p
              = pairAt labels0.val src0.val p)
          have heq : st.1.start.val = iter.end.val := by omega
          rw [heq] at hwin habove
          exact ⟨hwin, hlenL, hlenS, hbelow0, habove⟩
        · have hlt : st.1.start.val < st.1.end.val := by omega
          obtain ⟨o, iter1, hnext, hsome, hstart1, hend1⟩ := next_range_some st.1 hlt
          have hend1v : iter1.end.val = st.1.end.val := congrArg _ hend1
          obtain ⟨labels1, src1, hsort, hins⟩ :=
            insert_sorted_spec st.2.1 st.2.2 start st.1.start hstart0 (by omega) hlen0
          have hbody :
              verified.merc_lts.incoming_transitions.sort_incoming_loop.body start st.1 st.2.1
                  st.2.2 = ok (cont (iter1, labels1, src1)) := by
            unfold verified.merc_lts.incoming_transitions.sort_incoming_loop.body
            rw [hnext, hsome]
            simp [hsort]
          refine Std.WP.exists_imp_spec ⟨cont (iter1, labels1, src1), hbody, ?_⟩
          change SorInv labels0 src0 start iter.end (iter1, labels1, src1) ∧
            (iter1.end.val - iter1.start.val) < (st.1.end.val - st.1.start.val)
          rcases hins with ⟨hwin', htail, hlenL', hlenS', hbelow⟩
          have hlt' : (iter1.end.val - iter1.start.val) < (st.1.end.val - st.1.start.val) := by
            omega
          have hwin'' : sameWindow labels1.val src1.val labels0.val src0.val start.val
              (st.1.start.val + 1) :=
            sameWindow_trans labels1.val src1.val st.2.1.val st.2.2.val labels0.val src0.val
              start.val (st.1.start.val + 1) hwin'
              (sameWindow_succ st.2.1.val st.2.2.val labels0.val src0.val start.val
                st.1.start.val (by omega) hwin (habove st.1.start.val (by omega)))
          have hinv' : SorInv labels0 src0 start iter.end (iter1, labels1, src1) := by
            show (iter1.start.val = start.val + 1 ∧
              labels1.val = labels0.val ∧
              src1.val = src0.val ∧
              iter1.end.val = iter.end.val ∧
              iter.end.val ≤ labels1.val.length ∧
              labels1.val.length = src1.val.length) ∨
              (start.val ≤ iter1.start.val ∧
               iter1.start.val ≤ iter.end.val ∧
               iter1.end.val = iter.end.val ∧
               iter.end.val ≤ labels1.val.length ∧
               labels1.val.length = src1.val.length ∧
               sameWindow labels1.val src1.val labels0.val src0.val start.val iter1.start.val ∧
               (∀ p, iter1.start.val ≤ p →
                 pairAt labels1.val src1.val p = pairAt labels0.val src0.val p) ∧
               labels1.val.length = labels0.val.length ∧
               src1.val.length = src0.val.length ∧
               (∀ p, p < start.val → pairAt labels1.val src1.val p
                 = pairAt labels0.val src0.val p))
            refine Or.inr ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hlenL', hlenS']
              exact hlen0
            · rw [hstart1]
              exact hwin''
            · intro p hp
              rw [hstart1] at hp
              exact (htail p (by omega)).trans (habove p (by omega))
            · exact hlenL'.trans hlenL
            · exact hlenS'.trans hlenS
            · intro p hp
              exact (hbelow p hp).trans (hbelow0 p hp)
          exact ⟨hinv', hlt'⟩
    · exact hinv
  rcases Std.WP.spec_imp_exists hspec with ⟨r, hloop', hpost⟩
  exact ⟨r.1, r.2, hloop', hpost⟩

/-- `sort_incoming labels from start stop` leaves the range `[start, stop)` holding the pairs it
    held before.

    `sort_incoming` starts its scan at the checked value `start + 1#usize`, so the statement
    carries the corresponding no-overflow hypothesis; this is supplied by
    `IncomingTransitions::new`, where every start offset is bounded by the number of
    transitions. -/
theorem sort_incoming_spec
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (start stop : Sz)
    (hlen0 : labels0.val.length = src0.val.length)
    (hbound : stop.val ≤ labels0.val.length)
    (hnoovf : start.val + 1 ≤ Usize.max) :
    ∃ (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.sort_incoming labels0 src0 start stop
        = ok (labels1, src1) ∧
      SorPost labels0 src0 start stop (labels1, src1) := by
  have hadd := Usize.add_spec (x := start) (y := 1#usize) hnoovf
  rcases Std.WP.spec_imp_exists hadd with ⟨i, hadd_eq, hi_val⟩
  have hi : i = uTotal (start.val + 1) := by
    apply sz_eq_from_val
    rw [hi_val, one_val, uTotal_val_of_lt (lt_two_pow_of_le_max hnoovf)]
  have hadd_eq' : start + 1#usize = ok (uTotal (start.val + 1)) :=
    hadd_eq.trans (congrArg ok hi)
  have hinv0 : SorInv labels0 src0 start stop
      ({ start := uTotal (start.val + 1), «end» := stop }, labels0, src0) := by
    refine Or.inl ⟨?_, ?_, ?_, ?_, hbound, hlen0⟩
    · show (uTotal (start.val + 1)).val = start.val + 1
      exact uTotal_val_of_lt (lt_two_pow_of_le_max hnoovf)
    · rfl
    · rfl
    · rfl
  obtain ⟨labels1, src1, hloop, hpost⟩ :=
    sort_incoming_loop_spec labels0 src0
      { start := uTotal (start.val + 1), «end» := stop } start hinv0
  refine ⟨labels1, src1, ?_, hpost⟩
  unfold verified.merc_lts.incoming_transitions.sort_incoming
  rw [hadd_eq']
  simp only [bind_tc_ok]
  exact hloop

/-! ## Stage 8: `sort_all_incoming`

`sort_all_incoming` (`incoming_transitions.rs:206`) walks the states `0, …, n-1` and hands
each of them to `sort_incoming` with the CSR offsets `c[j]`, `c[j+1]` as its range. Sorting
one range does not disturb the others: `sort_incoming` only moves pairs inside `[c[j], c[j+1])`,
everything below `c[j]` and everything from `c[j+1]` on is left pointwise alone, and the CSR
offsets are non-decreasing - so the ranges of the other states are either wholly below or
wholly above the range being sorted.

The invariant therefore says, for every state:
* already visited (`j < it.start`): its range holds the same pairs as it did before the
  walk, unordered;
* not yet visited (`it.start ≤ j`): its range is pointwise untouched.

and the postcondition keeps only the first half, which is all `incoming_transitions` reads. -/

/-- A count below `2^numBits` fits in a `usize`, i.e. is at most `Usize.max`. -/
private lemma le_max_of_lt_two_pow {k : Nat} (h : k < 2 ^ UScalarTy.Usize.numBits) :
    k ≤ Usize.max := by
  have h2 : Usize.max + 1 = 2 ^ UScalarTy.Usize.numBits := by
    simp [Usize.max, Usize.numBits]
  omega

/-- Two flat arrays that read alike at every position of `[a, b)` carry the same pairs in
    that window. -/
private theorem sameWindow_of_pairAt_eq (labels : List (TagIndex Sz LabelTag))
    (src : List (TagIndex Sz StateTag)) (labels0 : List (TagIndex Sz LabelTag))
    (src0 : List (TagIndex Sz StateTag)) (a b : Nat)
    (h : ∀ p, a ≤ p → p < b → pairAt labels src p = pairAt labels0 src0 p) :
    sameWindow labels src labels0 src0 a b :=
  by
    intro x
    show x ∈ (List.range' a (b - a)).map (fun p => pairAt labels src p) ↔
      x ∈ (List.range' a (b - a)).map (fun p => pairAt labels0 src0 p)
    exact mem_map_eq_of_reindex (f := fun p => pairAt labels src p)
      (f0 := fun p => pairAt labels0 src0 p) (id : Nat → Nat) (fun p h1 h2 => h p h1 h2)
      (fun p h1 h2 => ⟨h1, h2⟩) (fun q h1 h2 => ⟨q, h1, h2, rfl⟩) x

/-- Two flat arrays that agree at every position of `[a, b)` carry the same pairs in that
    window. -/
private theorem sameWindow_congr {labels : List (TagIndex Sz LabelTag)}
    {src : List (TagIndex Sz StateTag)} {labels0 : List (TagIndex Sz LabelTag)}
    {src0 : List (TagIndex Sz StateTag)} {a b : Nat}
    (h : ∀ p, a ≤ p → p < b → pairAt labels src p = pairAt labels0 src0 p) :
    sameWindow labels src labels0 src0 a b := by
  intro x
  show x ∈ (List.range' a (b - a)).map (fun p => pairAt labels src p) ↔
    x ∈ (List.range' a (b - a)).map (fun p => pairAt labels0 src0 p)
  constructor
  · intro hx
    obtain ⟨p, hp, hxf⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, hpos⟩ := List.mem_range'.mp hp
    have hpa : a ≤ p := by omega
    have hpb : p < b := by omega
    rw [h p hpa hpb] at hxf
    exact List.mem_map.mpr ⟨p, mem_range'_of_lt hpa hpb, hxf⟩
  · intro hx
    obtain ⟨p, hp, hxf⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, hpos⟩ := List.mem_range'.mp hp
    have hpa : a ≤ p := by omega
    have hpb : p < b := by omega
    rw [(h p hpa hpb).symm] at hxf
    exact List.mem_map.mpr ⟨p, mem_range'_of_lt hpa hpb, hxf⟩

/-- The CSR offsets are non-decreasing, so `a ≤ b` gives `c[a] ≤ c[b]`. -/
private theorem getD_mono {c : alloc.vec.Vec Sz} {a b : Nat}
    (hmono : ∀ i, i + 1 < c.val.length → (c.val.getD i 0#usize).val
      ≤ (c.val.getD (i + 1) 0#usize).val)
    (hab : a ≤ b) (hb : b + 1 ≤ c.val.length) :
    (c.val.getD a 0#usize).val ≤ (c.val.getD b 0#usize).val := by
  induction b generalizing a with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab0 : a ≤ b
    · exact (ih hab0 (by omega)).trans (hmono b (by omega))
    · have ha : a = b + 1 := by omega
      subst ha
      exact Nat.le_refl _

/-- State of the outer sorting loop: the states still to visit, and the two flat arrays. -/
abbrev SaSt := core.ops.range.Range Sz × alloc.vec.Vec (TagIndex Sz LabelTag)
  × alloc.vec.Vec (TagIndex Sz StateTag)

/-- Invariant of `sort_all_incoming_loop` after the states below `it.start` have been
    visited: the walk has not overrun `n`, both arrays keep their length, and every state's
    range `[c[j], c[j+1])` still holds the pairs of `labels0`/`src0` - unorderedly if the
    state has been visited, pointwise if it has not. -/
def SaInv (c : alloc.vec.Vec Sz) (n : Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) : SaSt → Prop :=
  fun st =>
    st.1.start.val ≤ n.val ∧
    st.1.end.val = n.val ∧
    st.2.1.val.length = labels0.val.length ∧
    st.2.2.val.length = src0.val.length ∧
    (∀ j, j < n.val →
      (j < st.1.start.val →
        sameWindow st.2.1.val st.2.2.val labels0.val src0.val
          (c.val.getD j 0#usize).val (c.val.getD (j + 1) 0#usize).val) ∧
      (st.1.start.val ≤ j →
        ∀ p, (c.val.getD j 0#usize).val ≤ p → p < (c.val.getD (j + 1) 0#usize).val →
          pairAt st.2.1.val st.2.2.val p = pairAt labels0.val src0.val p))

/-- On return, every state's range holds the pairs of `labels0`/`src0` it held on entry,
    and both arrays keep their length. -/
def SaPost (c : alloc.vec.Vec Sz) (n : Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (r : alloc.vec.Vec (TagIndex Sz LabelTag) × alloc.vec.Vec (TagIndex Sz StateTag)) : Prop :=
  r.1.val.length = labels0.val.length ∧
  r.2.val.length = src0.val.length ∧
  (∀ j, j < n.val → sameWindow r.1.val r.2.val labels0.val src0.val
    (c.val.getD j 0#usize).val (c.val.getD (j + 1) 0#usize).val)

/-- The exhausted walk returns the arrays as they are. -/
private theorem sort_all_incoming_done (c : alloc.vec.Vec Sz) (n : Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (st : SaSt)
    (hinv : SaInv c n labels0 src0 st) (hge : n.val ≤ st.1.start.val) :
    verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body
        c st.1 st.2.1 st.2.2 = ok (done (st.2.1, st.2.2)) ∧
      SaPost c n labels0 src0 (st.2.1, st.2.2) := by
  rcases hinv with ⟨hle, hend_n, hlenL, hlenS, hwin⟩
  have hfin : st.1.end.val ≤ st.1.start.val := by omega
  obtain ⟨o, iter1, hnext, hone, hident⟩ := next_range_none st.1 hfin
  have hbody :
      verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body
        c st.1 st.2.1 st.2.2 = ok (done (st.2.1, st.2.2)) := by
    unfold verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body
    rw [hnext, hone, hident]
    simp
  refine ⟨hbody, ⟨hlenL, hlenS, ?_⟩⟩
  intro j hj
  exact (hwin j hj).1 (by omega)

/-- One state of the walk: `sort_incoming` on the range `[c[j], c[j+1])` of the next state
    `j = it.start`, which leaves every other state's range alone. -/
private theorem sort_all_incoming_step (c : alloc.vec.Vec Sz) (n : Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (st : SaSt)
    (hinv : SaInv c n labels0 src0 st) (hne : ¬ n.val ≤ st.1.start.val)
    (hrlen : n.val + 1 ≤ c.val.length) (hclen : c.val.length + 1 ≤ Usize.max)
    (hmono : ∀ i, i + 1 < c.val.length → (c.val.getD i 0#usize).val
      ≤ (c.val.getD (i + 1) 0#usize).val)
    (hfill : ∀ j, j < c.val.length → (c.val.getD j 0#usize).val ≤ labels0.val.length)
    (hlen0 : labels0.val.length = src0.val.length)
    (hlenmax : labels0.val.length + 1 ≤ Usize.max) :
    ∃ (iter1 : core.ops.range.Range Sz)
      (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body
          c st.1 st.2.1 st.2.2 = ok (cont (iter1, labels1, src1)) ∧
      iter1.start.val = st.1.start.val + 1 ∧ iter1.end = st.1.end ∧
      SaInv c n labels0 src0 (iter1, labels1, src1) := by
  have hcl : c.length = c.val.length := rfl
  rcases hinv with ⟨hle, hend_n, hlenL, hlenS, hwin⟩
  have hlen0' : st.2.1.val.length = st.2.2.val.length :=
    hlenL.trans (hlen0.trans hlenS.symm)
  have hlt : st.1.start.val < n.val := by omega
  have hlt1 : st.1.start.val < st.1.end.val := by omega
  obtain ⟨o, iter1, hnext, hsome, hstart1, hend1⟩ := next_range_some st.1 hlt1
  have hend1v : iter1.end.val = st.1.end.val := congrArg _ hend1
  have hidx0 : c.index_usize st.1.start = ok (c.val.getD st.1.start.val 0#usize) := by
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec c st.1.start (by omega)
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    rw [← alloc.vec.Vec.index_slice_index]
    rw [alloc.vec.Vec.index_slice_index, hy, hyv,
      getElem_eq_getD c.val st.1.start.val 0#usize (by omega)]
  have hadd1v : st.1.start.val + 1 ≤ Usize.max := by omega
  obtain ⟨i1, hadd1_eq, hi1⟩ :=
    Std.WP.spec_imp_exists (Usize.add_spec (x := st.1.start) (y := 1#usize) hadd1v)
  have hi1v : i1.val = st.1.start.val + 1 := by rw [hi1, one_val]
  have hidx1 : c.index_usize i1 = ok (c.val.getD i1.val 0#usize) := by
    have hbound : i1.val < c.val.length := by rw [hi1v]; omega
    have hl := Aeneas.Std.alloc.vec.Vec.index_usize_spec c i1 (by rw [hcl]; exact hbound)
    rcases Std.WP.spec_imp_exists hl with ⟨y, hy, hyv⟩
    have hidxI : c.index_usize i1 = ok (c.val[i1.val]) := by
      rw [← alloc.vec.Vec.index_slice_index]
      rw [alloc.vec.Vec.index_slice_index, hy, hyv]
    rw [hidxI]
    exact congrArg ok (getElem_eq_getD c.val i1.val 0#usize hbound)
  have hbound : (c.val.getD (st.1.start.val + 1) 0#usize).val ≤ st.2.1.val.length := by
    have h := hfill (st.1.start.val + 1) (by omega)
    rwa [← hlenL] at h
  have hnoovf : (c.val.getD st.1.start.val 0#usize).val + 1 ≤ Usize.max := by
    have hmono' := hmono st.1.start.val (by omega)
    omega
  obtain ⟨labels1, src1, hsort, hpost⟩ :=
    sort_incoming_spec st.2.1 st.2.2 (c.val.getD st.1.start.val 0#usize)
      (c.val.getD (st.1.start.val + 1) 0#usize) hlen0' hbound hnoovf
  have hbody :
      verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body
        c st.1 st.2.1 st.2.2 = ok (cont (iter1, labels1, src1)) := by
    unfold verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body
    simp only [alloc.vec.Vec.index_slice_index]
    rw [hnext, hsome]
    have hsort' :
        verified.merc_lts.incoming_transitions.sort_incoming st.2.1 st.2.2
          ((c.val[st.1.start.val]?).getD 0#usize)
          ((c.val[st.1.start.val + 1]?).getD 0#usize) = ok (labels1, src1) := by
      simpa only [List.getD] using hsort
    simp [hidx0, hadd1_eq, hidx1, hi1v, hsort']
  refine ⟨iter1, labels1, src1, hbody, hstart1, hend1, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · change iter1.start.val ≤ n.val
    have h1 := hstart1
    omega
  · change iter1.end.val = n.val
    exact hend1v.trans hend_n
  · exact hpost.2.1.trans hlenL
  · exact hpost.2.2.1.trans hlenS
  · intro j hj
    by_cases hltj : j < st.1.start.val
    · -- already visited: the window `[c[j], c[j+1])` ends at or below `c[start]`, where
      -- `SorPost` leaves every point alone, so the window still holds the pairs of `labels0`
      refine ⟨?_, ?_⟩
      · intro hjl
        refine sameWindow_trans labels1.val src1.val st.2.1.val st.2.2.val labels0.val src0.val
          (c.val.getD j 0#usize).val (c.val.getD (j + 1) 0#usize).val ?_ ((hwin j hj).1 hltj)
        refine sameWindow_congr ?_
        intro p hp1 hp2
        have hm : (c.val.getD (j + 1) 0#usize).val
            ≤ (c.val.getD st.1.start.val 0#usize).val :=
          getD_mono hmono (by omega) (by omega)
        exact hpost.2.2.2.1 p
          (by simpa [one_val] using lt_of_lt_of_le (by simpa [one_val] using hp2) hm)
      · intro hjl
        have hjl' : iter1.start.val ≤ j := hjl
        have hfalse : False := by omega
        exact hfalse.elim
    · by_cases hjeq : j = st.1.start.val
      · -- the state sorted just now: its window is the one `SorPost` sorted
        subst hjeq
        refine ⟨?_, ?_⟩
        · intro hjl
          refine sameWindow_trans labels1.val src1.val st.2.1.val st.2.2.val labels0.val src0.val
            (c.val.getD st.1.start.val 0#usize).val
            (c.val.getD (st.1.start.val + 1) 0#usize).val hpost.1
            (sameWindow_of_pairAt_eq st.2.1.val st.2.2.val labels0.val src0.val
              (c.val.getD st.1.start.val 0#usize).val
              (c.val.getD (st.1.start.val + 1) 0#usize).val
              (fun p hp1 hp2 => (hwin st.1.start.val hj).2 (by omega) p hp1 hp2))
        · intro hjl
          have hjl' : iter1.start.val ≤ st.1.start.val := hjl
          have hfalse : False := by omega
          exact hfalse.elim
      · -- not yet visited: the window lies at or above the sorted range, where `SorPost`
        -- says every point already holds the pair of `labels0`/`src0`
        refine ⟨?_, ?_⟩
        · intro hjl
          have hjl'' : j < iter1.start.val := hjl
          have hfalse : False := by omega
          exact hfalse.elim
        · intro hjl p hp1 hp2
          have hm : (c.val.getD (st.1.start.val + 1) 0#usize).val
              ≤ (c.val.getD j 0#usize).val :=
            getD_mono hmono (by omega) (by omega)
          exact (hpost.2.2.2.2 p (le_trans hm hp1)).trans
            ((hwin j hj).2 (by omega) p hp1 hp2)

/-- `sort_all_incoming` over the states `0, …, n-1`. -/
theorem sort_all_incoming_loop_spec (c : alloc.vec.Vec Sz) (n : Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag)) (st : SaSt)
    (hinv : SaInv c n labels0 src0 st)
    (hrlen : n.val + 1 ≤ c.val.length) (hclen : c.val.length + 1 ≤ Usize.max)
    (hmono : ∀ i, i + 1 < c.val.length → (c.val.getD i 0#usize).val
      ≤ (c.val.getD (i + 1) 0#usize).val)
    (hfill : ∀ j, j < c.val.length → (c.val.getD j 0#usize).val ≤ labels0.val.length)
    (hlen0 : labels0.val.length = src0.val.length)
    (hlenmax : labels0.val.length + 1 ≤ Usize.max) :
    ∃ (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.sort_all_incoming_loop st.1 c st.2.1 st.2.2
        = ok (labels1, src1) ∧
      SaPost c n labels0 src0 (labels1, src1) := by
  have hspec : verified.merc_lts.incoming_transitions.sort_all_incoming_loop st.1 c st.2.1
          st.2.2
        ⦃ fun r : alloc.vec.Vec (TagIndex Sz LabelTag)
              × alloc.vec.Vec (TagIndex Sz StateTag) => SaPost c n labels0 src0 r ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun st : SaSt => st.1.end.val - st.1.start.val)
      (inv := fun st : SaSt => SaInv c n labels0 src0 st)
      (post := fun r => SaPost c n labels0 src0 r)
      (body := fun st => verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body
        c st.1 st.2.1 st.2.2)
      (x := st)
    · intro s hinv
      by_cases hge : n.val ≤ s.1.start.val
      · rcases sort_all_incoming_done c n labels0 src0 s hinv hge with ⟨hdone, hpost⟩
        exact Std.WP.exists_imp_spec ⟨done (s.2.1, s.2.2), hdone, hpost⟩
      · rcases sort_all_incoming_step c n labels0 src0 s hinv hge hrlen hclen
          hmono hfill hlen0 hlenmax
          with ⟨iter1, labels1, src1, hbody, hstart1, hend1, hinv1⟩
        refine Std.WP.exists_imp_spec ⟨cont (iter1, labels1, src1), hbody, hinv1, ?_⟩
        have hend1v : iter1.end.val = s.1.end.val := congrArg _ hend1
        have hle := hinv.1
        have hend_n := hinv.2
        rw [hend1v, hstart1]
        omega
    · exact hinv
  rcases Std.WP.spec_imp_exists hspec with ⟨r, hloop, hpost⟩
  exact ⟨r.1, r.2, hloop, hpost⟩

/-- `sort_all_incoming` walks the states `0, …, n-1`. -/
theorem sort_all_incoming_spec
    (c : alloc.vec.Vec Sz) (n : Sz)
    (labels0 : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src0 : alloc.vec.Vec (TagIndex Sz StateTag))
    (hrlen : n.val + 1 ≤ c.val.length) (hclen : c.val.length + 1 ≤ Usize.max)
    (hmono : ∀ i, i + 1 < c.val.length → (c.val.getD i 0#usize).val
      ≤ (c.val.getD (i + 1) 0#usize).val)
    (hfill : ∀ j, j < c.val.length → (c.val.getD j 0#usize).val ≤ labels0.val.length)
    (hlen0 : labels0.val.length = src0.val.length)
    (hlenmax : labels0.val.length + 1 ≤ Usize.max) :
    ∃ (labels1 : alloc.vec.Vec (TagIndex Sz LabelTag))
      (src1 : alloc.vec.Vec (TagIndex Sz StateTag)),
      verified.merc_lts.incoming_transitions.sort_all_incoming c labels0 src0 n
        = ok (labels1, src1) ∧
      SaPost c n labels0 src0 (labels1, src1) := by
  have hinv : SaInv c n labels0 src0 ⟨{ start := 0#usize, «end» := n }, labels0, src0⟩ := by
    refine ⟨Nat.zero_le n.val, rfl, rfl, rfl, ?_⟩
    intro j hj
    exact ⟨fun hjl => absurd hjl (Nat.not_lt_zero j), fun _ p hp1 hp2 => rfl⟩
  rcases sort_all_incoming_loop_spec c n labels0 src0
      ⟨{ start := 0#usize, «end» := n }, labels0, src0⟩ hinv hrlen hclen hmono hfill hlen0 hlenmax
    with ⟨labels1, src1, hloop, hpost⟩
  exact ⟨labels1, src1, hloop, hpost⟩

/-! ## Stage 9: the extraction lemma `incoming_transitions`

`incoming_transitions` (`incoming_transitions.rs:323`) is the public reader: it takes the
CSR offsets of state `s`, and walks the two flat arrays over the range
`[state2incoming[s], state2incoming[s+1])`, packing each position into a
`FromTransition { label, from }`. The loop is again a plain "advance the range and push"
loop, so the induction is `gather_from_loop_spec` below - the shifted form of
`gather_loop_spec`, since the walk starts at the state's start offset rather than at `0`. -/

/-- Appending one element to a list leaves the reads below the old length alone. -/
private theorem getD_append_push_lt {α : Type} (l : List α) (a d : α) (k : Nat)
    (hk : k < l.length) : (l ++ [a]).getD k d = l.getD k d := by
  show (l ++ [a])[k]?.getD d = l[k]?.getD d
  exact List.getD_append l [a] d k hk

/-- Appending one element to a list: the read at the old length is the new element. -/
private theorem getD_append_push_end {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  show (l ++ [a])[l.length]?.getD d = a
  rw [List.getElem?_append_right (by simp)]
  simp

/-- The shifted form of `gatherInv`: the walk starts at `s`, so the accumulator holds
    `f (s+0), …, f (s+k-1)` and its length is `start - s`. -/
def gatherFromInv {α : Type} (n s : Sz) (f : Nat → α) (d : α) :
    ItSz × alloc.vec.Vec α → Prop :=
  fun st =>
    st.1.end = n ∧ s.val ≤ st.1.start.val ∧ st.1.start.val ≤ n.val ∧
      st.2.val.length = st.1.start.val - s.val ∧
      (∀ k, k < st.1.start.val - s.val → st.2.val.getD k d = f (k + s.val))

/-- A loop whose body is "advance the range, or stop; append `f start` and continue",
    started at `s` instead of at `0`, copies `f s, …, f (n-1)` into the accumulator. -/
theorem gather_from_loop_spec {α : Type} (n s : Sz) (f : Nat → α) (d : α) (hsn : s.val ≤ n.val)
    (hn : n.val < Usize.max)
    (body : ItSz → alloc.vec.Vec α →
      Result (ControlFlow (ItSz × alloc.vec.Vec α) (alloc.vec.Vec α)))
    (hstep : ∀ (it : ItSz) (v : alloc.vec.Vec α), it.end = n →
      v.val.length < Usize.max → it.start.val < it.end.val →
      v.val.length = it.start.val - s.val →
      ∃ (it1 : ItSz) (v1 : alloc.vec.Vec α),
        body it v = ok (cont (it1, v1)) ∧
        it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
        v1.val = v.val ++ [f it.start.val])
    (hdone : ∀ (it : ItSz) (v : alloc.vec.Vec α), it.end.val ≤ it.start.val →
      body it v = ok (done v)) :
    Aeneas.Std.WP.spec
        (@loop (ItSz × alloc.vec.Vec α) (alloc.vec.Vec α) (fun p => body p.1 p.2)
          ({ start := s, «end» := n }, alloc.vec.Vec.new α))
        (fun r : alloc.vec.Vec α =>
          r.val.length = n.val - s.val ∧
            ∀ k, k < n.val - s.val → r.val.getD k d = f (k + s.val)) := by
  apply loop.spec_decr_nat
    (measure := constPushMeasure)
    (inv := gatherFromInv n s f d)
    (post := fun r : alloc.vec.Vec α =>
      r.val.length = n.val - s.val ∧
        ∀ k, k < n.val - s.val → r.val.getD k d = f (k + s.val))
    (body := fun p => body p.1 p.2)
    (x := ({ start := s, «end» := n }, alloc.vec.Vec.new α))
  · intro st hinv
    rcases hinv with ⟨hend, hle, hle2, hlen, hpt⟩
    by_cases hlt : st.1.start.val < st.1.end.val
    · have hlen2 : st.2.val.length < Usize.max := by omega
      rcases hstep st.1 st.2 hend hlen2 hlt hlen with ⟨it1, v1, hbody, hstart, hend', hvval⟩
      have hinv' : gatherFromInv n s f d (it1, v1) := by
        refine ⟨hend'.trans hend, ?_, ?_, ?_, ?_⟩
        · change s.val ≤ it1.start.val
          rw [hstart]; omega
        · change it1.start.val ≤ n.val
          have hltn : st.1.start.val < n.val := by simpa [hend] using hlt
          rw [hstart]; omega
        · change v1.val.length = it1.start.val - s.val
          have h1 : st.1.start.val + 1 - s.val = st.1.start.val - s.val + 1 := by omega
          simp [hvval, hlen, hstart, h1]
        · change ∀ k, k < it1.start.val - s.val → v1.val.getD k d = f (k + s.val)
          intro k hk
          rw [hvval]
          by_cases hkl : k < st.2.val.length
          · rw [getD_append_push_lt _ _ _ k hkl, hpt k (by omega)]
          · have hkeq : k = st.2.val.length := by omega
            subst hkeq
            rw [getD_append_push_end]
            have hsub : st.2.val.length + s.val = st.1.start.val := by omega
            change f st.1.start.val = f (st.2.val.length + s.val)
            rw [hsub]
      have hlt' : constPushMeasure (it1, v1) < constPushMeasure st := by
        change (it1.end.val - it1.start.val) < (st.1.end.val - st.1.start.val)
        rw [hstart, hend', hend]
        rw [hend] at hlt
        omega
      exact Std.WP.exists_imp_spec ⟨cont (it1, v1), hbody, hinv', hlt'⟩
    · have hge : st.1.end.val ≤ st.1.start.val := by omega
      have hstart : st.1.start.val = n.val := by
        apply Nat.le_antisymm hle2
        rw [← hend]; exact hge
      have hpost : st.2.val.length = n.val - s.val ∧
          ∀ k, k < n.val - s.val → st.2.val.getD k d = f (k + s.val) := by
        refine ⟨by rw [hlen, hstart], fun k hk => hpt k (by omega)⟩
      exact Std.WP.exists_imp_spec ⟨done st.2, hdone st.1 st.2 hge, hpost⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · exact Nat.le_refl _
    · exact hsn
    · simp
    · intro k hk
      exact absurd hk (by simp)

/-- The empty `FromTransition`, read by `getD` at an out-of-range position. -/
private abbrev zeroFT : FromTransition := ⟨zeroLabel, zeroState⟩

/-- The `FromTransition` stored at position `p` of the two flat arrays. -/
private def ftAt (labels : List (TagIndex Sz LabelTag)) (src : List (TagIndex Sz StateTag))
    (p : Nat) : FromTransition :=
  ⟨(pairAt labels src p).1, (pairAt labels src p).2⟩

/-- One iteration of `incoming_transitions_loop.body`: the pair at the range's start is
    pushed and the range advances. -/
theorem incoming_transitions_loop_step
    (labels : alloc.vec.Vec (TagIndex Sz LabelTag))
    (src : alloc.vec.Vec (TagIndex Sz StateTag))
    (it : ItSz) (res : alloc.vec.Vec FromTransition)
    (hlen : labels.val.length = src.val.length)
    (hlt : it.start.val < it.end.val) (hbound : it.start.val < labels.val.length)
    (hmax : res.val.length < Usize.max) :
    ∃ (it1 : ItSz) (res1 : alloc.vec.Vec FromTransition),
      verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop.body
          labels src it res = ok (cont (it1, res1)) ∧
      it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
      res1.val = res.val ++ [ftAt labels.val src.val it.start.val] := by
  have hsrc : it.start.val < src.val.length := by rw [← hlen]; exact hbound
  rcases next_range_some it hlt with ⟨o, it1, hnext, hopt, hstart, hend⟩
  rcases Std.WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec labels it.start hbound)
    with ⟨x0, hidx0, hx0⟩
  rcases Std.WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec src it.start hsrc)
    with ⟨x1, hidx1, hx1⟩
  rcases vec_push_val res (ftAt labels.val src.val it.start.val) hmax
    with ⟨res1, hpush, hresval⟩
  refine ⟨it1, res1, ?_, hstart, hend, hresval⟩
  unfold verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop.body
  rw [hnext]
  simp only [hopt, alloc.vec.Vec.index_slice_index]
  rw [hidx0, hidx1, hx0, hx1, hpush]
  rfl

end MercVerified.Signatures.Proofs
