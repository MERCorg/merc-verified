import MercVerified.Refinement.Proofs.QuotientRust_Proofs
import MercVerified.Refinement.Proofs.BranchingTop_Proofs
import MercVerified.Refinement.Refinement

/-!
# `tau_cycle_elimination_and_reorder` and `branching_bisim_sigref`: statements

Remaining statements of the preprocessing verification (plan: `docs/preprocessing-plan.md`, stages
B2, B4, B5). The proofs are still `sorry`; the finished building blocks are
`SccRust_Proofs` (`tau_scc_spec`), `TopoSortRust_Proofs` (`sort_topological_hidden_spec`),
`QuotientRust_Proofs` (`collect_spec`, `push_transitions_spec`, `build_body_step` partially) and
`LtsData_Proofs` (`RawOf`, `raw_valid`, `raw_outgoing`, `assert_valid_ok`).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition TransitionLabel LTS)
open verified.merc_collections.indexed_partition (IndexedPartition BlockTag)
open verified.merc_lts.labelled_transition_system (LabelledTransitionSystem)
open merc_collections.compressed_vec (ByteCompressedVec)
open MercVerified.Lts.Proofs MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

/-- The `(label, target)` pairs stored for the block `b` of a raw LTS, in order. -/
def segPairs (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (b : Nat) : List QElem :=
  List.zip ((labs.drop (off.getD b 0)).take (off.getD (b + 1) 0 - off.getD b 0))
    ((tos.drop (off.getD b 0)).take (off.getD (b + 1) 0 - off.getD b 0))

section Build

open verified.merc_reduction.quotient

/-- The block loop of `quotient_build` sorts and deduplicates every row. -/
theorem build_loop_spec (out0 : alloc.vec.Vec (alloc.vec.Vec QElem)) (K : Nat) (e : Std.Usize)
    (he : e.val = K) (hBig : tot out0 K < Std.Usize.max)
    (st0 : ByteCompressedVec Std.Usize) (lb0 : ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (tb0 : ByteCompressedVec (TagIndex Std.Usize StateTag))
    (hst : ByteCompressedVec.toList st0 = []) (hlb : ByteCompressedVec.toList lb0 = [])
    (htb : ByteCompressedVec.toList tb0 = []) (hlen : out0.val.length = K) :
    ∃ st lb tb Ls, quotient_build_loop { start := 0#usize, «end» := e } out0 st0 lb0 tb0 = ok (st, lb, tb) ∧
      Ls.length = K ∧
      (∀ b, b < K → List.Pairwise qLt (Ls.getD b []) ∧
        ∀ x, x ∈ Ls.getD b [] ↔ x ∈ rowOf out0 b) ∧
      (ByteCompressedVec.toList st).map (fun u : Std.Usize => u.val) = offs Ls K ∧
      ByteCompressedVec.toList lb = Ls.flatten.map Prod.fst ∧
      ByteCompressedVec.toList tb = Ls.flatten.map Prod.snd := by
  sorry

/-- `quotient_build` produces a valid raw LTS whose block `b` holds the sorted, deduplicated pairs of
    row `b`, with the labels of `lts` and the block of the initial state as initial state. -/
theorem quotient_build_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (n0 : Std.Usize) (hns : LTSInst.num_of_states sys = ok n0)
    (ip : IndexedPartition) (hip : ip.partition.val.length = n0.val)
    (hbK : ∀ s : TagIndex Std.Usize StateTag, s.index.val < n0.val →
      (bk ip s.index.val).index.val < ip.num_of_blocks.val)
    (hK : 1 ≤ ip.num_of_blocks.val)
    (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem)) (hlen : outgoing.val.length = ip.num_of_blocks.val)
    (hBig : tot outgoing ip.num_of_blocks.val < Std.Usize.max) :
    ∃ (Q : LabelledTransitionSystem Label) (off : List Nat)
      (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag)),
      verified.merc_reduction.quotient.quotient_build LTSInst
        verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
        sys ip outgoing = ok Q ∧
      RawOf Q ip.num_of_blocks.val off labs tos ∧ RawGood Q ip.num_of_blocks.val off labs tos ∧
      (∃ sl, LTSInst.labels sys = ok sl ∧ Q.labels.val = sl.val) ∧
      (∃ i, LTSInst.initial_state_index sys = ok i ∧
        Q.initial_state.index.val = (bk ip i.index.val).index.val) ∧
      ∀ b (hb : b < ip.num_of_blocks.val),
        List.Pairwise qLt (segPairs off labs tos b) ∧
        ∀ x, x ∈ segPairs off labs tos b ↔ x ∈ rowOf outgoing b := by
  sorry

/-- **`quotient_lts_naive` (both elimination flags set) computes the τ-SCC quotient.**
    `ip` numbers the states by their τ-SCC (as returned by `tau_scc_decomposition_iterative`). -/
theorem quotient_lts_naive_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (n0 : Std.Usize) (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hnlt : n0.val < Usize.max)
    (ip : IndexedPartition) (k : Nat)
    (hlen : ip.partition.val.length = n0.val) (hnb : ip.num_of_blocks.val = max 1 k)
    (hscc : Sigref.Tarjan.IsSccPartition (gOf LTSInst sys hn0 hnlt)
      (view n0.val (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val) k) :
    ∃ (Q : LabelledTransitionSystem Label) (off : List Nat)
      (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag)),
      verified.merc_reduction.quotient.quotient_lts_naive LTSInst
        verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
        sys ip true true = ok Q ∧
      RawOf Q k off labs tos ∧ RawGood Q k off labs tos ∧
      (∃ sl, LTSInst.labels sys = ok sl ∧ Q.labels.val = sl.val) ∧
      (∃ i, LTSInst.initial_state_index sys = ok i ∧
        Q.initial_state.index.val = (bk ip i.index.val).index.val) ∧
      -- the transitions: `[s] -μ→ [t]` iff `s -μ→ t` for some members, unless `μ = τ` inside a block
      ∀ b, b < k → ∀ (μ : TagIndex Std.Usize LabelTag) (c : Std.Usize),
        (μ, ({ index := c, marker := () } : TagIndex Std.Usize StateTag)) ∈
            segPairs off labs tos b ↔
          ∃ s t, (bk ip s.index.val).index.val = b ∧ (bk ip t.index.val).index.val = c.val ∧
            s.index.val < n0.val ∧ MercVerified.Lts.tr LTSInst sys s μ t ∧
            ¬ (μ.index.val = 0 ∧ b = c.val) := by
  sorry

end Build

section Permute

/-- `invert_permutation` inverts a bijection of `0..n`. -/
theorem invert_permutation_spec (perm : Slice (TagIndex Std.Usize StateTag)) (n : Nat)
    (hlen : perm.val.length = n) (hlt : ∀ p ∈ perm.val, p.index.val < n)
    (hinj : (perm.val.map (fun p => p.index.val)).Nodup) :
    ∃ inv : alloc.vec.Vec (TagIndex Std.Usize StateTag),
      verified.merc_lts.labelled_transition_system.invert_permutation perm = ok inv ∧
      inv.val.length = n ∧
      ∀ b (hb : b < n), ∃ h : (perm.val[b]'(by omega)).index.val < inv.val.length,
        (inv.val[(perm.val[b]'(by omega)).index.val]'h).index.val = b := by
  sorry

/-- **`new_from_permutation_vec` renames the states by the permutation**: the block `b` of the
    result at position `perm b` holds the transitions of `b` with renamed targets. -/
theorem new_from_permutation_vec_spec {Label : Type} (TLInst : TransitionLabel Label)
    {Q : LabelledTransitionSystem Label} {n : Nat} {off : List Nat}
    {labs : List (TagIndex Std.Usize LabelTag)} {tos : List (TagIndex Std.Usize StateTag)}
    (hR : RawOf Q n off labs tos) (hG : RawGood Q n off labs tos)
    (hlab : 1 ≤ Q.labels.val.length)
    (htau : ∃ t, Q.labels.val[0]? = some t ∧ TLInst.is_tau_label t = ok true)
    (perm : Slice (TagIndex Std.Usize StateTag)) (hlen : perm.val.length = n)
    (hlt : ∀ p ∈ perm.val, p.index.val < n) (hinj : (perm.val.map (fun p => p.index.val)).Nodup) :
    ∃ (R : LabelledTransitionSystem Label) (off' : List Nat)
      (labs' : List (TagIndex Std.Usize LabelTag)) (tos' : List (TagIndex Std.Usize StateTag)),
      verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec
        TLInst Q perm = ok R ∧
      RawOf R n off' labs' tos' ∧ RawGood R n off' labs' tos' ∧ R.labels.val = Q.labels.val ∧
      R.initial_state.index.val = (perm.val.getD Q.initial_state.index.val default).index.val ∧
      ∀ b, b < n →
        segPairs off' labs' tos' (perm.val.getD b default).index.val =
          (segPairs off labs tos b).map
            (fun x => (x.1, ({ index := (perm.val.getD x.2.index.val default).index, marker := () } :
              TagIndex Std.Usize StateTag))) := by
  sorry

end Permute

section Top

/-- **`tau_cycle_elimination_and_reorder` (with `eliminate_tau_selfloops = true`)**: the result is a
    well-formed, topologically ordered LTS (`BranchingLtsAssumptions`) that is branching bisimilar
    to the input via the state map `f`, which sends `state` to the returned state. -/
theorem tau_cycle_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (state : TagIndex Std.Usize StateTag) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hstate : state.index.val < n0.val) :
    ∃ (R : LabelledTransitionSystem Label) (state' : TagIndex Std.Usize StateTag) (f : ℕ → ℕ),
      verified.merc_reduction.signatures.tau_cycle_elimination_and_reorder LTSInst sys state true = ok (R, state') ∧
      state'.index.val = f state.index.val ∧
      Sigref.IsCrossBB (MercVerified.Lts.toLTS LTSInst sys)
        (MercVerified.Lts.toLTS
          (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS LTSInst.TransitionLabelInst) R)
        (fun s s' => s.index.val < n0.val ∧ s'.index.val = f s.index.val) ∧
      (let I := LabelledTransitionSystem.Insts.Merc_ltsLtsLTS LTSInst.TransitionLabelInst
       MercVerified.Lts.WellFormed I R ∧ StateCountFits I R ∧ BranchingLtsAssumptions I R) := by
  sorry

/-- **`branching_bisim_sigref` for `divergence_preserving = false`.** -/
theorem branching_bisim_sigref_correct {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (state : TagIndex Std.Usize StateTag) (timing : merc_utilities.timing.Timing) :
    BranchingBisimSigrefCorrectSpec LTSInst sys hwf hass state timing := by
  sorry

end Top

end MercVerified.Refinement.Proofs
