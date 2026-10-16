import MercVerified.Refinement.Proofs.QuotientRust_Proofs
import MercVerified.Refinement.Proofs.BranchingTop_Proofs
import MercVerified.Refinement.Refinement
import MercLib.Sigref.Proofs.TarjanBridge_Proofs
import MercLib.Sigref.Proofs.Scc_Proofs

/-!
# `tau_cycle_elimination_and_reorder` and `branching_bisim_sigref`

The preprocessing verification (plan: `docs/preprocessing-plan.md`, stages B2, B4, B5): the
quotient by the τ-SCCs (`quotient_lts_naive_spec`), the renumbering (`new_from_permutation_vec_spec`),
their composition (`tau_cycle_spec`: a branching bisimulation onto a topologically ordered LTS) and
the headline `branching_bisim_sigref_correct` (`BranchingBisimSigrefCorrectSpec`). Building blocks:
`SccRust_Proofs` (`tau_scc_spec`), `TopoSortRust_Proofs` (`sort_topological_hidden_spec`),
`QuotientRust_Proofs` and `LtsData_Proofs` (`RawOf`, `raw_valid`, `raw_outgoing`, `assert_valid_ok`),
and the abstract `MercLib.Sigref.quotientTauAcyclic`/`isTauSccPartition_of_scc`.

Machine-generated; may be freely edited or regenerated (see AGENTS.md).
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

/-- Loop-induction helper for `build_loop_spec`: reduces all `K` blocks while keeping the invariant
    `BuildInv`, and returns the accumulated rows satisfying the goal conditions. -/
theorem build_loop_ind (out0 : alloc.vec.Vec (alloc.vec.Vec QElem)) (K : Nat) (e : Std.Usize)
    (he : e.val = K) (hBig : tot out0 K < Std.Usize.max) :
    ∀ (m : Nat) (i : Std.Usize) (out : alloc.vec.Vec (alloc.vec.Vec QElem))
      (st : ByteCompressedVec Std.Usize) (lb : ByteCompressedVec (TagIndex Std.Usize LabelTag))
      (tb : ByteCompressedVec (TagIndex Std.Usize StateTag)) (Ls : List (List QElem)),
      e.val - i.val = m → i.val ≤ e.val →
      BuildInv out0 K i.val Ls out st lb tb →
      ∃ st' lb' tb' Ls', quotient_build_loop { start := i, «end» := e } out st lb tb = ok (st', lb', tb') ∧
        Ls'.length = K ∧
        (∀ b, b < K → List.Pairwise qLt (Ls'.getD b []) ∧
          ∀ x, x ∈ Ls'.getD b [] ↔ x ∈ rowOf out0 b) ∧
        (ByteCompressedVec.toList st').map (fun u : Std.Usize => u.val) = offs Ls' K ∧
        ByteCompressedVec.toList lb' = Ls'.flatten.map Prod.fst ∧
        ByteCompressedVec.toList tb' = Ls'.flatten.map Prod.snd ∧
        Ls'.flatten.length ≤ tot out0 K := by
  intro m
  induction m with
  | zero =>
    intro i out st lb tb Ls hm hle hinv
    obtain ⟨hLs, hsorted, hmem, holen, hrowlt, hrowge, hstl, hlbl, htbl, htlen⟩ := hinv
    have hiK : i.val = K := by omega
    refine ⟨st, lb, tb, Ls, ?_, ?_, ?_, ?_, hlbl, htbl, ?_⟩
    · unfold quotient_build_loop
      apply loop_done'
      show quotient_build_loop.body { start := i, «end» := e } out st lb tb = _
      have hge : i.val ≥ e.val := by omega
      obtain ⟨o, iter1, hnext, ho, hident⟩ := next_range_none ({ start := i, «end» := e }) hge
      unfold quotient_build_loop.body
      rw [hnext, ho]
      simp
    · rw [hiK] at hLs
      exact hLs
    · intro b hb
      have hbi : b < i.val := by omega
      have hlenb : b < Ls.length := by
        rw [hLs]
        omega
      have hgetd : Ls.getD b [] = Ls[b]'(by omega) := by
        unfold List.getD
        rw [List.getElem?_eq_getElem hlenb]
        simp
      constructor
      · rw [hgetd]
        exact hsorted b hbi
      · intro x
        rw [hgetd]
        exact hmem b hbi x
    · rw [hiK] at hstl
      exact hstl
    · rw [hiK] at htlen
      exact htlen
  | succ m ih =>
    intro i out st lb tb Ls hm hle hinv
    obtain ⟨i1, out1, st1, lb1, tb1, Ls1, hi1, hbody, hinv1⟩ :=
      build_body_step out0 K e i he (by omega) hBig out st lb tb Ls hinv
    have hm1 : e.val - i1.val = m := by rw [hi1]; omega
    have hle1 : i1.val ≤ e.val := by rw [hi1]; omega
    obtain ⟨st', lb', tb', Ls', hloop, hlen', hb, hstl', hlbl', htbl', htlen'⟩ :=
      ih i1 out1 st1 lb1 tb1 Ls1 hm1 (by rw [hi1]; omega) (by simpa [← hi1] using hinv1)
    refine ⟨st', lb', tb', Ls', ?_, hlen', hb, hstl', hlbl', htbl', htlen'⟩
    unfold quotient_build_loop at hloop ⊢
    rw [loop_cont' _ _ _ hbody]
    exact hloop

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
      ByteCompressedVec.toList tb = Ls.flatten.map Prod.snd ∧
      Ls.flatten.length ≤ tot out0 K := by
  refine (build_loop_ind out0 K e he hBig) K 0#usize out0 st0 lb0 tb0 [] ?_ ?_ ?_
  · simp [he]
  · simp
  · refine ⟨rfl, ?_, ?_, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b hb
      have hz0 : (0#usize : Std.Usize).val = 0 := rfl
      rw [hz0] at hb
      omega
    · intro b hb
      have hz0 : (0#usize : Std.Usize).val = 0 := rfl
      rw [hz0] at hb
      omega
    · intro b hb
      have hz0 : (0#usize : Std.Usize).val = 0 := rfl
      rw [hz0] at hb
      omega
    · intro b hb; rfl
    · rw [hst]; rfl
    · rw [hlb]; rfl
    · rw [htb]; rfl
    · simp

/-! ## Offset lemmas for `quotient_build_spec` -/

theorem offs_length (Ls : List (List QElem)) (K : Nat) : (offs Ls K).length = K := by
  simp [offs]

theorem offD_offs (Ls : List (List QElem)) {K b : Nat} (hb : b < K) :
    (offs Ls K ++ [Ls.flatten.length]).getD b 0 = ((Ls.take b).flatten).length := by
  unfold offs
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hb),
    List.getElem?_map, List.getElem?_eq_getElem (by simpa using hb)]
  simp

theorem offD_succ (Ls : List (List QElem)) {K b : Nat} (hb : b < K) (hLs : Ls.length = K) :
    (offs Ls K ++ [Ls.flatten.length]).getD (b + 1) 0 = ((Ls.take (b + 1)).flatten).length := by
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hb) with h | h
  · exact offD_offs Ls h
  · subst h
    have ht : Ls.take (b + 1) = Ls := by
      rw [show b + 1 = Ls.length by omega, List.take_length]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [offs_length])]
    simp [ht, offs_length]

theorem take_succ_flatten_length (Ls : List (List QElem)) {b : Nat} (hb : b < Ls.length) :
    ((Ls.take (b + 1)).flatten).length = ((Ls.take b).flatten).length + (Ls[b]'hb).length := by
  rw [← List.take_append_getElem hb, List.flatten_append]
  simp

theorem take_succ_sub (Ls : List (List QElem)) {b : Nat} (hb : b < Ls.length) :
    ((Ls.take (b + 1)).flatten).length - ((Ls.take b).flatten).length = (Ls[b]'hb).length := by
  rw [take_succ_flatten_length Ls hb]
  omega

theorem flatten_split (Ls : List (List QElem)) {b : Nat} (hb : b < Ls.length) :
    Ls.flatten = (Ls.take b).flatten ++ (Ls[b]'hb ++ (Ls.drop (b + 1)).flatten) := by
  induction b generalizing Ls with
  | zero =>
    cases Ls with
    | nil => simp at hb
    | cons x xs => simp
  | succ k ih =>
    cases Ls with
    | nil => simp at hb
    | cons x xs =>
      simp only [List.length_cons] at hb
      have hk : k < xs.length := by omega
      have hih := ih xs hk
      rw [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ, List.flatten_cons, hih]
      simp [List.append_assoc]

theorem flatten_take_drop (Ls : List (List QElem)) {b : Nat} (hb : b < Ls.length) :
    (Ls.flatten.drop ((Ls.take b).flatten).length).take (Ls[b]'hb).length = Ls[b]'hb := by
  rw [flatten_split Ls hb, List.drop_left, List.take_left]

theorem labs_take_drop (Ls : List (List QElem)) {b : Nat} (hb : b < Ls.length) :
    ((Ls.flatten.map Prod.fst).drop ((Ls.take b).flatten).length).take (Ls[b]'hb).length
      = (Ls[b]'hb).map Prod.fst := by
  rw [← List.map_drop, ← List.map_take, flatten_take_drop Ls hb]

theorem tos_take_drop (Ls : List (List QElem)) {b : Nat} (hb : b < Ls.length) :
    ((Ls.flatten.map Prod.snd).drop ((Ls.take b).flatten).length).take (Ls[b]'hb).length
      = (Ls[b]'hb).map Prod.snd := by
  rw [← List.map_drop, ← List.map_take, flatten_take_drop Ls hb]

theorem segPairs_of_offs (Ls : List (List QElem)) {K : Nat} (hLs : Ls.length = K)
    {b : Nat} (hb : b < K) :
    segPairs (offs Ls K ++ [Ls.flatten.length]) (Ls.flatten.map Prod.fst) (Ls.flatten.map Prod.snd) b
      = Ls[b]'(by omega) := by
  have hbl : b < Ls.length := by omega
  unfold segPairs
  rw [offD_offs Ls hb, offD_succ Ls hb hLs, take_succ_sub Ls hbl,
    labs_take_drop Ls hbl, tos_take_drop Ls hbl, List.zip_map']
  simp [Prod.mk.eta]

theorem segPairs_getElem? (Ls : List (List QElem)) {K : Nat} (hLs : Ls.length = K)
    {b k : Nat} (hb : b < K) (hk : k < (Ls[b]'(by omega)).length)
    (hkf : ((Ls.take b).flatten).length + k < (Ls.flatten.map Prod.fst).length)
    (hks : ((Ls.take b).flatten).length + k < (Ls.flatten.map Prod.snd).length) :
    (segPairs (offs Ls K ++ [Ls.flatten.length]) (Ls.flatten.map Prod.fst)
        (Ls.flatten.map Prod.snd) b)[k]?
      = some ((Ls.flatten.map Prod.fst)[((Ls.take b).flatten).length + k]'hkf,
              (Ls.flatten.map Prod.snd)[((Ls.take b).flatten).length + k]'hks) := by
  have hbl : b < Ls.length := by omega
  unfold segPairs
  rw [offD_offs Ls hb, offD_succ Ls hb hLs, take_succ_sub Ls hbl,
    List.zip_eq_zipWith, List.getElem?_zipWith]
  rw [List.getElem?_take, ite_eq_left hk, List.getElem?_take, ite_eq_left hk, List.getElem?_drop,
    List.getElem?_drop, List.getElem?_eq_getElem hkf, List.getElem?_eq_getElem hks]

/-! ## Helpers for `quotient_build_spec` -/

theorem qLt_irrefl (a : QElem) : ¬ qLt a a := by unfold qLt; omega

theorem pairwise_qLt_nodup {l : List QElem} (h : List.Pairwise qLt l) : l.Nodup :=
  h.nodup

theorem mem_outVec_iff_tr {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (s : TagIndex Std.Usize StateTag)
    (hs : ∃ ts : alloc.vec.Vec Transition, LTSInst.outgoing_transitions sys s = ok ts)
    (μ : TagIndex Std.Usize LabelTag) (t : TagIndex Std.Usize StateTag) :
    (⟨μ, t⟩ : Transition) ∈ (outVec LTSInst sys s).val ↔ MercVerified.Lts.tr LTSInst sys s μ t := by
  constructor
  · intro h
    obtain ⟨ts, hts⟩ := hs
    exact ⟨ts, hts, by rwa [outVec_of_ok LTSInst sys s ts hts] at h⟩
  · rintro ⟨ts, hts, hmem⟩
    rw [outVec_of_ok LTSInst sys s ts hts]
    exact hmem

theorem mem_keptList {ip : IndexedPartition} (s : TagIndex Std.Usize StateTag)
    (l : List Transition) (x : QElem) :
    x ∈ keptList ip s l ↔ ∃ t ∈ l, keepB ip s t = true ∧ x = elemD ip t := by
  unfold keptList
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hx⟩
    by_cases hk : keepB ip s t = true
    · exact ⟨t, ht, hk, by simp [hk] at hx; exact hx.symm⟩
    · simp [hk] at hx
  · rintro ⟨t, ht, hk, rfl⟩
    exact ⟨t, ht, by simp [hk]⟩

theorem mem_rowAcc {ip : IndexedPartition}
    (tsOf : TagIndex Std.Usize StateTag → List Transition)
    (ps : List (TagIndex Std.Usize StateTag)) (c : Nat) (x : QElem) :
    x ∈ rowAcc ip tsOf ps c ↔
      ∃ s ∈ ps, (bk ip s.index.val).index.val = c ∧ x ∈ keptList ip s (tsOf s) := by
  unfold rowAcc
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hx⟩
    by_cases hc : (bk ip s.index.val).index.val = c
    · exact ⟨s, hs, hc, by simpa [hc] using hx⟩
    · simp [hc] at hx
  · rintro ⟨s, hs, hc, hx⟩
    exact ⟨s, hs, by simp [hc, hx]⟩

theorem mem_rowAcc_snd_lt {ip : IndexedPartition}
    {tsOf : TagIndex Std.Usize StateTag → List Transition}
    {ps : List (TagIndex Std.Usize StateTag)} {c : Nat} {x : QElem}
    (hx : x ∈ rowAcc ip tsOf ps c)
    (hbound : ∀ s ∈ ps, ∀ t ∈ tsOf s, t.to.index.val < ip.partition.val.length)
    (hbK : ∀ s : TagIndex Std.Usize StateTag, s.index.val < ip.partition.val.length →
      (bk ip s.index.val).index.val < ip.num_of_blocks.val) :
    x.2.index.val < ip.num_of_blocks.val := by
  rw [mem_rowAcc] at hx
  obtain ⟨s, hs, _, hx⟩ := hx
  rw [mem_keptList] at hx
  obtain ⟨t, ht, _, rfl⟩ := hx
  show (elemD ip t).2.index.val < _
  unfold elemD
  exact hbK t.to (hbound s hs t ht)

theorem mem_rowAcc_fst_lt {ip : IndexedPartition}
    {tsOf : TagIndex Std.Usize StateTag → List Transition}
    {ps : List (TagIndex Std.Usize StateTag)} {c : Nat} {x : QElem} {L : Nat}
    (hx : x ∈ rowAcc ip tsOf ps c)
    (hbound : ∀ s ∈ ps, ∀ t ∈ tsOf s, t.label.index.val < L) :
    x.1.index.val < L := by
  rw [mem_rowAcc] at hx
  obtain ⟨s, hs, _, hx⟩ := hx
  rw [mem_keptList] at hx
  obtain ⟨t, ht, _, rfl⟩ := hx
  show (elemD ip t).1.index.val < L
  unfold elemD
  exact hbound s hs t ht

theorem offs_getD_take (Ls : List (List QElem)) (K : Nat) {b : Nat} (hb : b < K) :
    (offs Ls K).getD b 0 = ((Ls.take b).flatten).length := by
  unfold offs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hb)]
  simp

theorem offs_pairwise (Ls : List (List QElem)) (K : Nat) :
    (offs Ls K ++ [Ls.flatten.length]).Pairwise (· ≤ ·) := by
  rw [List.pairwise_append]
  refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
  · unfold offs
    apply List.Pairwise.map
    · intro a b hab
      have hab' : a ≤ b := le_of_lt hab
      have htt : (Ls.take b).take a = Ls.take a := by
        rw [List.take_take, Nat.min_eq_left hab']
      have hpre : Ls.take a <+: Ls.take b := by
        rw [← htt]; exact List.take_prefix a (Ls.take b)
      simpa using hpre.flatten.length_le
    · exact List.pairwise_lt_range
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    unfold offs at ha
    rw [List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    exact (List.take_prefix j Ls).flatten.length_le

/-- The `i`-th element of `Ls.flatten` in a block `s < Ls.length` is the corresponding element of
    `Ls[s]`. -/
theorem flatten_getElem_row (Ls : List (List QElem)) {s i : Nat} (hs : s < Ls.length)
    (hi : i < Ls.flatten.length)
    (hlo : ((Ls.take s).flatten).length ≤ i)
    (hhi : i < ((Ls.take s).flatten).length + (Ls[s]'hs).length) :
    Ls.flatten[i]'hi =
      (Ls[s]'hs)[i - ((Ls.take s).flatten).length]'(by omega) := by
  have hsplit : Ls.flatten =
      (Ls.take s).flatten ++ (Ls[s]'hs ++ (Ls.drop (s + 1)).flatten) := flatten_split Ls hs
  have hq : Ls.flatten[i]? =
      some ((Ls[s]'hs)[i - ((Ls.take s).flatten).length]'(by omega)) := by
    rw [hsplit, List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem hi]
  exact hq

/-- `quotient_build` produces a valid raw LTS whose block `b` holds the sorted, deduplicated pairs of
    row `b`, with the labels of `lts` and the block of the initial state as initial state. -/
theorem quotient_build_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (n0 : Std.Usize) (hns : LTSInst.num_of_states sys = ok n0)
    (ip : IndexedPartition) (hip : ip.partition.val.length = n0.val)
    (hbK : ∀ s : TagIndex Std.Usize StateTag, s.index.val < n0.val →
      (bk ip s.index.val).index.val < ip.num_of_blocks.val)
    (hnb : ip.num_of_blocks.val ≤ n0.val)
    (hK : 1 ≤ ip.num_of_blocks.val)
    (outgoing : alloc.vec.Vec (alloc.vec.Vec QElem)) (hlen : outgoing.val.length = ip.num_of_blocks.val)
    (hBig : tot outgoing ip.num_of_blocks.val < Std.Usize.max)
    (sv : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (_hsv : LTSInst.iter_states sys = ok sv)
    (hmem : ∀ s, s ∈ sv.val ↔ s.index.val < n0.val)
    (hrow : ∀ c, rowOf outgoing c = rowAcc ip (fun s => (outVec LTSInst sys s).val) sv.val c) :
    ∃ (Q : LabelledTransitionSystem Label) (off : List Nat)
      (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag)),
      verified.merc_reduction.quotient.quotient_build LTSInst
        verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition
        sys ip outgoing = ok Q ∧
      RawOf Q ip.num_of_blocks.val off labs tos ∧ RawGood Q ip.num_of_blocks.val off labs tos ∧
      (∃ sl, LTSInst.labels sys = ok sl ∧ Q.labels.val = sl.val) ∧
      (∃ i, LTSInst.initial_state_index sys = ok i ∧
        Q.initial_state.index.val = (bk ip i.index.val).index.val) ∧
      ∀ b, b < ip.num_of_blocks.val →
        List.Pairwise qLt (segPairs off labs tos b) ∧
        ∀ x, x ∈ segPairs off labs tos b ↔ x ∈ rowOf outgoing b := by
  obtain ⟨hhid, ⟨sl, hsl, hsl1, ht0, hlab⟩, hclone, hfit, hinit⟩ := hass
  obtain ⟨st0, hst_new, hst0⟩ := merc_collections.compressed_vec.ByteCompressedVec.new_spec UIdx
  obtain ⟨lb0, hlb_new, hlb0⟩ := merc_collections.compressed_vec.ByteCompressedVec.new_spec LIdx
  obtain ⟨tb0, htb_new, htb0⟩ := merc_collections.compressed_vec.ByteCompressedVec.new_spec SIdx
  have he : (alloc.vec.Vec.len outgoing).val = ip.num_of_blocks.val := by
    rw [vec_len_val']; exact hlen
  obtain ⟨st, lb, tb, Ls, hloop, hLlen, hsortmem, hstl, hlbl, htbl, htlen⟩ :=
    build_loop_spec outgoing ip.num_of_blocks.val (alloc.vec.Vec.len outgoing) he hBig
      st0 lb0 tb0 hst0 hlb0 htb0 hlen
  have hlnb : (ByteCompressedVec.toList lb).length ≤ Std.Usize.max := by
    rw [hlbl, List.length_map]; omega
  obtain ⟨i1, hlen_lb, hi1v⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec LIdx lb hlnb
  have hi1v' : i1.val = Ls.flatten.length := by rw [hi1v, hlbl, List.length_map]
  have hstlen : (ByteCompressedVec.toList st).length = ip.num_of_blocks.val := by
    have h := congrArg List.length hstl
    simpa [List.length_map, offs_length] using h
  have hKlt : ip.num_of_blocks.val < Std.Usize.max := by
    have hfit' : n0.val * (n0.val + 2) ≤ Std.Usize.max := hfit n0 hns
    have hmul : ip.num_of_blocks.val * (ip.num_of_blocks.val + 2) ≤ n0.val * (n0.val + 2) :=
      Nat.mul_le_mul hnb (by omega)
    nlinarith [hK, hmul, hfit']
  obtain ⟨st2, hpst, hst2⟩ :=
    merc_collections.compressed_vec.ByteCompressedVec.push_spec UIdx st i1 (by rw [hstlen]; exact hKlt)
  have hst2v : (ByteCompressedVec.toList st2).map (fun u : Std.Usize => u.val) =
      offs Ls ip.num_of_blocks.val ++ [Ls.flatten.length] := by
    rw [hst2, List.map_append, hstl]; simp [hi1v']
  obtain ⟨ti, hti, htilt⟩ := hinit n0 hns
  have htip : ti.index.val < ip.partition.val.length := by rw [hip]; exact htilt
  set ti1 : TagIndex Std.Usize BlockTag := ip.partition.val[ti.index.val]'htip with hti1def
  have hti1 : verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition.block_number
      ip ti = ok ti1 := ip_block_number ip ti htip
  have hi2 : verified.merc_utilities.tagged_index.TagIndex.value core.marker.CopyUsize ti1 = ok ti1.index :=
    tag_value_id _ ti1
  set ti2 : TagIndex Std.Usize StateTag := { index := ti1.index, marker := () } with hti2def
  have hti2 : verified.merc_utilities.tagged_index.TagIndex.new StateTag ti1.index = ok ti2 := by
    simp [ti2]
  have hbk_ti : ti2.index.val = (bk ip ti.index.val).index.val := by
    simp [ti2, ti1, bk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htip]
  obtain ⟨v, hv, hvslice⟩ : ∃ r, _ = r ∧ Std.WP.spec r _ :=
    ⟨_, rfl, alloc.slice.Slice.to_vec_spec LTSInst.TransitionLabelInst.corecloneCloneInst sl (fun x _ => hclone x)⟩
  cases v <;> simp only [Std.WP.spec_ok, Std.WP.spec_vis, Std.WP.spec_div] at hvslice
  rename_i v
  have hvval : v.val = sl.val := by rw [alloc.vec.Vec.val, hvslice]
  set Q : LabelledTransitionSystem Label :=
    { states := st2, transition_labels := lb, transition_to := tb, labels := v, initial_state := ti2 }
    with hQdef
  have hmemlt : ∀ s ∈ sv.val, s.index.val < n0.val := fun s hs => (hmem s).1 hs
  have hbound_target : ∀ s ∈ sv.val, ∀ t ∈ (outVec LTSInst sys s).val,
      t.to.index.val < ip.partition.val.length := by
    intro s hs t ht
    obtain ⟨ts, hts, htlt⟩ := hwf.2.1 n0 hns s (hmemlt s hs)
    have htlt' : t.to.index.val < n0.val := by
      rw [outVec_of_ok LTSInst sys s ts hts] at ht
      exact htlt t ht
    rw [hip]; exact htlt'
  have hbound_label : ∀ s ∈ sv.val, ∀ t ∈ (outVec LTSInst sys s).val,
      t.label.index.val < sl.val.length := by
    intro s hs t ht
    obtain ⟨ts, hts, _⟩ := hwf.2.1 n0 hns s (hmemlt s hs)
    have htr : MercVerified.Lts.tr LTSInst sys s t.label t.to :=
      (mem_outVec_iff_tr LTSInst sys s ⟨ts, hts⟩ t.label t.to).1 (by simpa using ht)
    exact hlab s t.label t.to htr
  have hbK' : ∀ s : TagIndex Std.Usize StateTag, s.index.val < ip.partition.val.length →
      (bk ip s.index.val).index.val < ip.num_of_blocks.val :=
    fun s hs => hbK s (by rw [← hip]; exact hs)
  have hRawOf : RawOf Q ip.num_of_blocks.val
      (offs Ls ip.num_of_blocks.val ++ [Ls.flatten.length])
      (Ls.flatten.map Prod.fst) (Ls.flatten.map Prod.snd) :=
    { st := hst2v
      lab := hlbl
      tl := htbl
      offlen := by rw [List.length_append, offs_length]; simp
      mono := offs_pairwise Ls ip.num_of_blocks.val
      last := by
        rw [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
          List.length_map]
      len_eq := by rw [List.length_map, List.length_map]
      tlt := by
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨x, hx, rfl⟩ := ht
        obtain ⟨l', hl'mem, hxl'⟩ := List.mem_flatten.mp hx
        obtain ⟨b, hb', hb'eq⟩ := List.getElem_of_mem hl'mem
        have hbKb : b < ip.num_of_blocks.val := by rw [← hLlen]; exact hb'
        have hgetdb : Ls.getD b [] = Ls[b]'hb' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb']; rfl
        have hxLb : x ∈ Ls[b]'hb' := by rw [hb'eq]; exact hxl'
        have hxrow0 : x ∈ Ls.getD b [] := by rw [hgetdb]; exact hxLb
        have hxrow : x ∈ rowOf outgoing b := ((hsortmem b hbKb).2 x).1 hxrow0
        rw [hrow b] at hxrow
        exact mem_rowAcc_snd_lt hxrow hbound_target hbK'
      init := by
        show ti2.index.val < ip.num_of_blocks.val
        rw [hbk_ti]
        exact hbK ti htilt
      small := (Nat.mul_le_mul hnb (by omega)).trans (hfit n0 hns)
      tmax := by
        show (Ls.flatten.map Prod.fst).length < Std.Usize.max
        rw [List.length_map]; omega }
  have hRawGood : RawGood Q ip.num_of_blocks.val
      (offs Ls ip.num_of_blocks.val ++ [Ls.flatten.length])
      (Ls.flatten.map Prod.fst) (Ls.flatten.map Prod.snd) :=
    { labs_lt := by
        intro l hl
        rw [List.mem_map] at hl
        obtain ⟨x, hx, rfl⟩ := hl
        obtain ⟨l', hl'mem, hxl'⟩ := List.mem_flatten.mp hx
        obtain ⟨b, hb', hb'eq⟩ := List.getElem_of_mem hl'mem
        have hbK : b < ip.num_of_blocks.val := by rw [← hLlen]; exact hb'
        have hgetdb : Ls.getD b [] = Ls[b]'hb' := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb']; rfl
        have hxLb : x ∈ Ls[b]'hb' := by rw [hb'eq]; exact hxl'
        have hxrow0 : x ∈ Ls.getD b [] := by rw [hgetdb]; exact hxLb
        have hxrow : x ∈ rowOf outgoing b := ((hsortmem b hbK).2 x).1 hxrow0
        rw [hrow b] at hxrow
        have := mem_rowAcc_fst_lt hxrow hbound_label
        show (x.1).index.val < Q.labels.val.length
        rw [hQdef]; simpa [hvval] using this
      nodup := by
        intro s hs i j hoffi hij hoffj hi hj hi' hj' hlabij htosij
        have hbL : s < Ls.length := by rw [hLlen]; exact hs
        have hoff_s : (offs Ls ip.num_of_blocks.val ++ [Ls.flatten.length]).getD s 0 =
            ((Ls.take s).flatten).length := offD_offs Ls hs
        have hoff_s1 : (offs Ls ip.num_of_blocks.val ++ [Ls.flatten.length]).getD (s+1) 0 =
            ((Ls.take (s+1)).flatten).length := offD_succ Ls hs hLlen
        rw [hoff_s] at hoffi
        rw [hoff_s1, take_succ_flatten_length Ls hbL] at hoffj
        have hiLf : i < Ls.flatten.length := by rw [List.length_map] at hi; exact hi
        have hjLf : j < Ls.flatten.length := by rw [List.length_map] at hj; exact hj
        have hkl : i - ((Ls.take s).flatten).length < (Ls[s]'hbL).length := by omega
        have hml : j - ((Ls.take s).flatten).length < (Ls[s]'hbL).length := by omega
        have hfj_lo : ((Ls.take s).flatten).length ≤ j := by omega
        have hf_i := flatten_getElem_row Ls hbL hiLf hoffi (by omega)
        have hf_j := flatten_getElem_row Ls hbL hjLf hfj_lo (by omega)
        have he1 : (Ls.flatten[i]'hiLf).1.index.val = (Ls.flatten[j]'hjLf).1.index.val := by
          have hh := congrArg (fun t : TagIndex Std.Usize LabelTag => t.index.val) hlabij
          rw [List.getElem_map, List.getElem_map] at hh
          exact hh
        have he2 : (Ls.flatten[i]'hiLf).2.index.val = (Ls.flatten[j]'hjLf).2.index.val := by
          have hh := congrArg (fun t : TagIndex Std.Usize StateTag => t.index.val) htosij
          rw [List.getElem_map, List.getElem_map] at hh
          exact hh
        have hfl_eq : Ls.flatten[i]'hiLf = Ls.flatten[j]'hjLf := qelem_ext he1 he2
        rw [hf_i, hf_j] at hfl_eq
        have hpair : List.Pairwise qLt (Ls[s]'hbL) := by
          have := (hsortmem s hs).1
          rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbL] at this
        have hkm := (List.Nodup.getElem_inj_iff (pairwise_qLt_nodup hpair) (hi := hkl) (hj := hml)).mp hfl_eq
        omega }
  refine ⟨Q, offs Ls ip.num_of_blocks.val ++ [Ls.flatten.length],
    Ls.flatten.map Prod.fst, Ls.flatten.map Prod.snd, ?hbuild, hRawOf, hRawGood, ?hlabels, ?hinitQ, ?hseg⟩
  · have hlabq : 1 ≤ Q.labels.val.length := by rw [hQdef]; simpa [hvval] using hsl1
    have htauq : ∃ t, Q.labels.val[0]? = some t ∧
        LTSInst.TransitionLabelInst.is_tau_label t = ok true := by
      obtain ⟨t, ht, ht'⟩ := ht0
      exact ⟨t, by rw [hQdef]; simpa [hvval] using ht, ht'⟩
    have hav := assert_valid_ok LTSInst.TransitionLabelInst hRawOf hRawGood hlabq htauq
    have hlb_tb : lb0 = tb0 := by
      have h2 : (merc_collections.compressed_vec.ByteCompressedVec.new LIdx) =
          (merc_collections.compressed_vec.ByteCompressedVec.new SIdx) := rfl
      have h3 : (ok lb0 : Result (merc_collections.compressed_vec.ByteCompressedVec
          (verified.merc_utilities.tagged_index.TagIndex Std.Usize verified.merc_lts.lts.LabelTag))) = ok tb0 :=
        hlb_new.symm.trans (h2.trans htb_new)
      exact Result.ok.injEq.mp h3
    have hloop' : quotient_build_loop { start := 0#usize, «end» := outgoing.len }
        outgoing st0 lb0 lb0 = ok (st, lb, tb) := by
      rw [← hlb_tb] at hloop; exact hloop
    unfold verified.merc_reduction.quotient.quotient_build
    rw [hst_new, hlb_new]
    simp only [hloop', hti, hti1, hi2, hti2, hsl, hv, bind_ok]
    show (do
      let i1 ← ByteCompressedVec.len LIdx lb
      let states2 ← ByteCompressedVec.push UIdx st i1
      verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.from_raw_parts
        LTSInst.TransitionLabelInst ti2 states2 lb tb v) = ok Q
    simp only [hlen_lb, hpst, bind_ok]
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.from_raw_parts
    rw [← hQdef]
    simp only [hav, bind_ok]
  · exact ⟨sl, hsl, by rw [hQdef]; exact hvval⟩
  · exact ⟨ti, hti, by rw [hQdef]; exact hbk_ti⟩
  · intro b hb
    have hbL : b < Ls.length := by rw [hLlen]; exact hb
    have hsp : segPairs (offs Ls ip.num_of_blocks.val ++ [Ls.flatten.length])
        (Ls.flatten.map Prod.fst) (Ls.flatten.map Prod.snd) b = Ls[b]'hbL :=
      segPairs_of_offs Ls hLlen hb
    have hgetdb : Ls.getD b [] = Ls[b]'hbL := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbL]; rfl
    refine ⟨?_, ?_⟩
    · rw [hsp]
      have := (hsortmem b hb).1
      rwa [hgetdb] at this
    · intro x
      rw [hsp]
      have := (hsortmem b hb).2 x
      rwa [hgetdb] at this

theorem sum_map_add_nat {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem map_sum_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ a, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; have := h a; omega

theorem keepB_eq_true_iff (ip : IndexedPartition) (s : TagIndex Std.Usize StateTag) (t : Transition) :
    keepB ip s t = true ↔
      ¬(t.label.index.val = 0 ∧
        (bk ip s.index.val).index.val = (bk ip t.to.index.val).index.val) := by
  unfold keepB
  by_cases hA : t.label.index.val = 0
  · by_cases hB : (bk ip s.index.val).index.val = (bk ip t.to.index.val).index.val <;>
      simp [hA, hB]
  · by_cases hB : (bk ip s.index.val).index.val = (bk ip t.to.index.val).index.val <;>
      simp [hA, hB]

theorem nodup_sum_ite_eq_le (l : List Nat) (c L : Nat) (h : l.Nodup) :
    (l.map (fun b => if c = b then L else 0)).sum ≤ L := by
  have key : (l.map (fun b => if c = b then L else 0)).sum = if c ∈ l then L else 0 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp h
      rw [List.map_cons, List.sum_cons, ih hl]
      by_cases hca : c = a
      · rw [ite_eq_left hca]
        have hcl : ¬ c ∈ l := by rw [hca]; exact ha
        rw [ite_eq_right hcl]
        have hmem : c ∈ a :: l := List.mem_cons.mpr (Or.inl hca)
        rw [ite_eq_left hmem]
        omega
      · rw [ite_eq_right hca]
        by_cases hcl : c ∈ l
        · have hmem : c ∈ a :: l := List.mem_cons.mpr (Or.inr hcl)
          rw [ite_eq_left hcl, ite_eq_left hmem]
          omega
        · have hmem : ¬ c ∈ a :: l := by
            rw [List.mem_cons]; rintro (h | h) <;> [exact hca h; exact hcl h]
          rw [ite_eq_right hcl, ite_eq_right hmem]
  rw [key]
  split_ifs <;> omega

theorem sum_rowAcc_le (ip : IndexedPartition)
    (tsOf : TagIndex Std.Usize StateTag → List Transition)
    (ps : List (TagIndex Std.Usize StateTag)) (K : Nat) :
    ((List.range K).map (fun b => (rowAcc ip tsOf ps b).length)).sum ≤
      (ps.map (fun s => (keptList ip s (tsOf s)).length)).sum := by
  induction ps with
  | nil => simp [rowAcc]
  | cons s ps ih =>
    have hlen : ∀ b, (rowAcc ip tsOf (s :: ps) b).length =
        (if (bk ip s.index.val).index.val = b then (keptList ip s (tsOf s)).length else 0) +
          (rowAcc ip tsOf ps b).length := by
      intro b
      unfold rowAcc
      rw [List.flatMap_cons, List.length_append]
      split_ifs <;> simp
    calc ((List.range K).map (fun b => (rowAcc ip tsOf (s :: ps) b).length)).sum
        = ((List.range K).map (fun b =>
            (if (bk ip s.index.val).index.val = b then (keptList ip s (tsOf s)).length else 0) +
              (rowAcc ip tsOf ps b).length)).sum := by
          apply congrArg List.sum; apply List.map_congr_left; intro b _; exact hlen b
      _ = ((List.range K).map (fun b =>
            if (bk ip s.index.val).index.val = b then (keptList ip s (tsOf s)).length else 0)).sum +
          ((List.range K).map (fun b => (rowAcc ip tsOf ps b).length)).sum :=
          sum_map_add_nat _ _ _
      _ ≤ (keptList ip s (tsOf s)).length +
          (ps.map (fun s => (keptList ip s (tsOf s)).length)).sum := by
          apply Nat.add_le_add
          · exact nodup_sum_ite_eq_le _ _ _ List.nodup_range
          · exact ih
      _ = ((s :: ps).map (fun s => (keptList ip s (tsOf s)).length)).sum := by simp

/-- **`quotient_lts_naive` (both elimination flags set) computes the τ-SCC quotient.**
    `ip` numbers the states by their τ-SCC (as returned by `tau_scc_decomposition_iterative`). -/
theorem quotient_lts_naive_spec {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (n0 : Std.Usize) (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val)
    (hnlt : n0.val < Usize.max)
    (ip : IndexedPartition) (k : Nat)
    (hlen : ip.partition.val.length = n0.val) (hnb : ip.num_of_blocks.val = max 1 k)
    (hscc : MercLib.Tarjan.IsSccPartition (gOf LTSInst sys hn0 hnlt)
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
  have hhid := hass.1
  -- `k ≥ 1`, hence `ip.num_of_blocks.val = k`.
  have hk1 : 1 ≤ k := by
    have := hscc.1 ⟨0, hn0⟩
    omega
  have hnk : ip.num_of_blocks.val = k := by rw [hnb, max_eq_right hk1]
  have hK : 1 ≤ ip.num_of_blocks.val := by omega
  -- `ip.num_of_blocks.val ≤ n0.val`: the block map is surjective onto `Fin k`.
  have hknb : ip.num_of_blocks.val ≤ n0.val := by
    rw [hnk]
    have hf : Function.Injective
        (fun b : Fin k => Classical.choose (hscc.2.1 b.val b.isLt)) := by
      intro b1 b2 h
      have h1 := Classical.choose_spec (hscc.2.1 b1.val b1.isLt)
      have h2 := Classical.choose_spec (hscc.2.1 b2.val b2.isLt)
      change Classical.choose (hscc.2.1 b1.val b1.isLt) =
        Classical.choose (hscc.2.1 b2.val b2.isLt) at h
      rw [h] at h1
      exact Fin.ext (h1.symm.trans h2)
    have := Fintype.card_le_of_injective
      (fun b : Fin k => Classical.choose (hscc.2.1 b.val b.isLt)) hf
    simpa using this
  -- every state's block is `< ip.num_of_blocks.val`.
  have hbK : ∀ s : TagIndex Std.Usize StateTag, s.index.val < n0.val →
      (bk ip s.index.val).index.val < ip.num_of_blocks.val := by
    intro s hs
    have hslen : s.index.val < ip.partition.val.length := by rw [hlen]; exact hs
    have hv : view n0.val (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val
        ⟨s.index.val, hs⟩ = (bk ip s.index.val).index.val := by
      rw [view_get (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val
        ⟨s.index.val, hs⟩ hslen]
      simp only [bk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hslen, Option.getD_some]
    have hk := hscc.1 ⟨s.index.val, hs⟩
    rw [hv] at hk
    rw [hnk]; exact hk
  -- run the collection loop.
  obtain ⟨sv, outgoing, hsv, hnd, hmem, hcoll, hlenO, hrow⟩ :=
    collect_spec LTSInst sys hwf n0 hns hhid ip hlen hbK
  obtain ⟨sv', m, hsv', hnd', hmem', hm, hmlt, hsum⟩ := hwf.2.2 n0 hns
  have hsvEq : sv = sv' := by
    have h : (ok sv : Result (alloc.vec.Vec (TagIndex Std.Usize StateTag))) = ok sv' :=
      hsv.symm.trans hsv'
    exact Result.ok.injEq.mp h
  -- `tot` fits in a `usize`.
  have hBig : tot outgoing ip.num_of_blocks.val < Std.Usize.max := by
    have h1 : tot outgoing ip.num_of_blocks.val ≤
        (sv.val.map (fun s => (outVec LTSInst sys s).val.length)).sum := by
      unfold tot
      calc ((List.range ip.num_of_blocks.val).map (fun b => (rowOf outgoing b).length)).sum
          = ((List.range ip.num_of_blocks.val).map (fun b =>
              (rowAcc ip (fun s => (outVec LTSInst sys s).val) sv.val b).length)).sum := by
            apply congrArg List.sum; apply List.map_congr_left
            intro b _; rw [hrow b]
        _ ≤ (sv.val.map (fun s =>
              (keptList ip s ((fun s => (outVec LTSInst sys s).val) s)).length)).sum :=
            sum_rowAcc_le ip _ sv.val ip.num_of_blocks.val
        _ ≤ (sv.val.map (fun s => (outVec LTSInst sys s).val.length)).sum :=
            map_sum_le _ _ _ (fun s => by unfold keptList; exact List.length_filterMap_le _ _)
    have h2 : (sv.val.map (fun s => (outVec LTSInst sys s).val.length)).sum ≤ m.val := by
      rw [hsvEq]
      exact hsum (fun s => outVec LTSInst sys s) (fun s hs => by
        obtain ⟨ts, hts, _⟩ := hwf.2.1 n0 hns s ((hmem' s).1 hs)
        exact outVec_eq_ok LTSInst sys s ts hts)
    omega
  obtain ⟨Q, off, labs, tos, hbuild, hRaw, hGood, hlabs, hinitQ, hchar⟩ :=
    quotient_build_spec LTSInst sys hwf hass n0 hns ip hlen hbK hknb hK outgoing hlenO hBig
      sv hsv hmem hrow
  refine ⟨Q, off, labs, tos, ?_, ?_, ?_, hlabs, hinitQ, ?_⟩
  · unfold verified.merc_reduction.quotient.quotient_lts_naive
    simp only [hcoll, bind_ok]
    exact hbuild
  · rw [← hnk]; exact hRaw
  · rw [← hnk]; exact hGood
  · intro b hb μ c
    rw [← hnk] at hb
    rw [(hchar b hb).2, hrow b]
    constructor
    · intro hx
      rw [mem_rowAcc] at hx
      obtain ⟨s, hs, hbs, hx⟩ := hx
      rw [mem_keptList] at hx
      obtain ⟨t, ht, hkeep, heq⟩ := hx
      have hμ : μ = t.label := congrArg Prod.fst heq
      have hc : c = (bk ip t.to.index.val).index :=
        congrArg (fun x => x.index) (congrArg Prod.snd heq)
      have hcv : (bk ip t.to.index.val).index.val = c.val := (congrArg UScalar.val hc).symm
      refine ⟨s, t.to, hbs, hcv, (hmem s).1 hs, ?_, ?_⟩
      · obtain ⟨ts, hts, _⟩ := hwf.2.1 n0 hns s ((hmem s).1 hs)
        have houtmem : (⟨μ, t.to⟩ : Transition) ∈ (outVec LTSInst sys s).val := by
          rw [hμ]; exact ht
        exact (mem_outVec_iff_tr LTSInst sys s ⟨ts, hts⟩ μ t.to).1 houtmem
      · have hkb := (keepB_eq_true_iff ip s t).1 hkeep
        rintro ⟨h10, hbc⟩
        exact hkb ⟨by rw [← hμ]; exact h10, by rw [hbs, hbc, hcv]⟩
    · rintro ⟨s, t, hbs, hct, hsn, htr, hne⟩
      obtain ⟨ts, hts, htmem⟩ := htr
      have hs : s ∈ sv.val := (hmem s).2 hsn
      have ht' : (⟨μ, t⟩ : Transition) ∈ (outVec LTSInst sys s).val := by
        rw [outVec_of_ok LTSInst sys s ts hts]; exact htmem
      have hnot : ¬(μ.index.val = 0 ∧
          (bk ip s.index.val).index.val = (bk ip t.index.val).index.val) := by
        intro hcon; exact hne ⟨hcon.1, by rw [← hbs, hcon.2, hct]⟩
      have hkeep : keepB ip s (⟨μ, t⟩ : Transition) = true :=
        (keepB_eq_true_iff ip s (⟨μ, t⟩ : Transition)).2 hnot
      have heq : (μ, ({ index := c, marker := () } : TagIndex Std.Usize StateTag)) =
          elemD ip (⟨μ, t⟩ : Transition) := by
        unfold elemD
        rw [Prod.mk.injEq]
        exact ⟨rfl, by congr 1; exact (UScalar.eq_of_val_eq hct).symm⟩
      exact (mem_rowAcc (fun s => (outVec LTSInst sys s).val) sv.val b
          (μ, ({ index := c, marker := () } : TagIndex Std.Usize StateTag))).2
        ⟨s, hs, hbs, (mem_keptList s ((fun s => (outVec LTSInst sys s).val) s)
          (μ, ({ index := c, marker := () } : TagIndex Std.Usize StateTag))).2
            ⟨⟨μ, t⟩, ht', hkeep, heq⟩⟩

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
  unfold verified.merc_lts.labelled_transition_system.invert_permutation
  have hcl : ∀ x : TagIndex Std.Usize StateTag,
      (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone StateTag
      core.clone.CloneUsize).clone x = ok x := by
    intro x
    simp [verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone.clone]
  have hnew0 : verified.merc_utilities.tagged_index.TagIndex.new StateTag 0#usize =
      ok ({ index := 0#usize, marker := () } : TagIndex Std.Usize StateTag) := by simp
  obtain ⟨inverse, hinv, hres⟩ : ∃ r, _ = r ∧ Std.WP.spec r _ :=
    ⟨_, rfl, alloc.vec.from_elem_spec (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone StateTag core.clone.CloneUsize) ({ index := 0#usize, marker := () } : TagIndex Std.Usize StateTag) (Slice.len perm) (hcl _)⟩
  cases inverse <;> simp only [Std.WP.spec_ok, Std.WP.spec_vis, Std.WP.spec_div] at hres
  rename_i inverse
  obtain ⟨hinvv, _⟩ := hres
  have hSlen : (Slice.len perm).val = n := by simpa [Slice.len] using hlen
  rw [hnew0]
  simp only [bind_ok]
  rw [hinv]
  simp only [bind_ok]
  have hinvlen : inverse.val.length = n := by rw [hinvv]; simp [hSlen]
  unfold verified.merc_lts.labelled_transition_system.invert_permutation_loop
  have key := range_loop_spec
    (σ := alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (ρ := alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (fun x => verified.merc_lts.labelled_transition_system.invert_permutation_loop.body perm x.1 x.2)
    (fun m r => r.val.length = n ∧ ∀ q (hq : q < m) (hqn : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < r.val.length,
        (r.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (fun r => r.val.length = n ∧ ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < r.val.length,
        (r.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (Slice.len perm) ?hsome ?hnone 0#usize inverse (by simp) ⟨hinvlen, by intro q hq hqn; simp at hq⟩
  case hsome =>
    intro i m hi hm
    have hiN : i.val < n := by omega
    obtain ⟨o, it1, hnext, hsome, hs1, he1⟩ := MercVerified.Lts.Proofs.next_range_some
      ({ start := i, «end» := Slice.len perm } : core.ops.range.Range Std.Usize) (by simpa using hi)
    obtain ⟨st1, en1⟩ := it1
    simp only at hs1 he1
    have hit1 : ({ start := st1, «end» := en1 } : core.ops.range.Range Std.Usize) =
        { start := st1, «end» := Slice.len perm } := by rw [he1]
    rw [hit1] at hnext
    have hiO : i.val < perm.val.length := by omega
    obtain ⟨ti1, hti1e, hti1'⟩ : ∃ r, _ = r ∧ Std.WP.spec r _ :=
      ⟨_, rfl, Slice.index_usize_spec perm i hiO⟩
    cases ti1 <;> simp only [Std.WP.spec_ok, Std.WP.spec_vis, Std.WP.spec_div] at hti1'
    rename_i ti1
    have hj : (perm.val[i.val]'hiO).index.val < m.val.length := by
      rw [hm.1]; exact hlt _ (List.getElem_mem hiO)
    have hmut := vec_index_mut_ok m (perm.val[i.val]'hiO).index hj
    set m1 : alloc.vec.Vec (TagIndex Std.Usize StateTag) :=
      ({ slice := m.slice.set (perm.val[i.val]'hiO).index
          ({ index := i, marker := () } : TagIndex Std.Usize StateTag) } :
        alloc.vec.Vec (TagIndex Std.Usize StateTag)) with hm1
    have hm1v : m1.val = m.val.set (perm.val[i.val]'hiO).index.val
        ({ index := i, marker := () } : TagIndex Std.Usize StateTag) := by
      simp [hm1, alloc.vec.Vec.val, Slice.set_val_eq]
    have hm1len : m1.val.length = n := by rw [hm1v]; simp [hm.1]
    refine ⟨st1, m1, hs1, ?_, hm1len, ?_⟩
    · unfold verified.merc_lts.labelled_transition_system.invert_permutation_loop.body
      rw [hnext, hsome]
      have hnewi : verified.merc_utilities.tagged_index.TagIndex.new StateTag i =
          ok ({ index := i, marker := () } : TagIndex Std.Usize StateTag) := by simp
      simp only [bind_ok]
      show (do
        let ti ← verified.merc_utilities.tagged_index.TagIndex.new StateTag i
        let ti1 ← perm.index_usize i
        let i' ← verified.merc_utilities.tagged_index.TagIndex.value core.marker.CopyUsize ti1
        let (_, index_mut_back) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice (TagIndex Std.Usize StateTag)) m i'
        ok (cont (({ start := st1, «end» := Slice.len perm } : core.ops.range.Range Std.Usize),
          index_mut_back ti))) = _
      rw [hnewi]
      simp only
      rw [hti1e]
      simp only [verified.merc_utilities.tagged_index.TagIndex.value]
      subst hti1'
      simp only [bind_tc_ok]
      rw [hmut]
      simp [hm1]
    · intro q hq hqn
      have hqO : q < perm.val.length := by omega
      have hjm : (perm.val[q]'hqO).index.val < m1.val.length := by
        rw [hm1len]; exact hlt _ (List.getElem_mem hqO)
      refine ⟨hjm, ?_⟩
      by_cases hqi : q = i.val
      · subst hqi
        simp only [hm1v]
        rw [List.getElem_set_self]
      · have hlt' : q < i.val := by omega
        have hne : (perm.val[q]'hqO).index.val ≠ (perm.val[i.val]'hiO).index.val := by
          intro h
          have hmq : q < (perm.val.map (fun t => t.index.val)).length := by simpa using hqO
          have hmi : i.val < (perm.val.map (fun t => t.index.val)).length := by simpa using hiO
          have := (List.Nodup.getElem_inj_iff hinj (hi := hmq) (hj := hmi)).1 (by simpa using h)
          exact hqi this
        obtain ⟨h0, h1⟩ := hm.2 q hlt' hqn
        simp only [hm1v]
        rw [List.getElem_set_ne (Ne.symm hne)]
        exact h1
  case hnone =>
    intro i m hi hm
    obtain ⟨o, it1, hnext, hone, hident⟩ := MercVerified.Lts.Proofs.next_range_none
      ({ start := i, «end» := Slice.len perm } : core.ops.range.Range Std.Usize) (by simp [hi])
    refine ⟨m, ?_, hm.1, ?_⟩
    · unfold verified.merc_lts.labelled_transition_system.invert_permutation_loop.body
      rw [hnext, hone]
      simp
    · intro q hq
      exact hm.2 q (by rw [hSlen] at hi; omega) hq
  obtain ⟨r, hr, hp⟩ := key
  exact ⟨r, hr, hp.1, hp.2⟩

/-- Renaming a target state by the permutation slice (default when out of range). -/
def prename (perm : Slice (TagIndex Std.Usize StateTag)) (t : TagIndex Std.Usize StateTag) :
    TagIndex Std.Usize StateTag :=
  perm.val.getD t.index.val default

theorem slice_index_ok' {α : Type} (s : Slice α) (i : Std.Usize) (h : i.val < s.val.length) :
    Slice.index_usize s i = ok (s.val[i.val]'h) := by
  have hs := Slice.index_usize_spec s i h
  obtain ⟨x, hx, hxe⟩ : ∃ r, _ = r ∧ Std.WP.spec r _ := ⟨_, rfl, hs⟩
  cases x <;> simp only [Std.WP.spec_ok, Std.WP.spec_vis, Std.WP.spec_div] at hxe
  rename_i x
  rw [hx, hxe]

/-- The old block index assigned to the new position `j` by the inverse permutation. -/
def invAt (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (j : Nat) : Nat :=
  (inverse.val.getD j default).index.val

/-- The renamed block (list of `(label, renamed target)` pairs) placed at new position `j`. -/
def renamedBlock (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag)) (j : Nat) : List QElem :=
  (segPairs off labs tos (invAt inverse j)).map (fun x => (x.1, prename perm x.2))

/-- The first `N` renamed blocks. -/
def blocksList (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag)) (N : Nat) : List (List QElem) :=
  (List.range N).map (renamedBlock inverse off labs tos perm)

theorem segPairs_fst (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (b : Nat)
    (_h1 : off.getD (b + 1) 0 ≤ labs.length) (h0 : off.getD b 0 ≤ off.getD (b + 1) 0)
    (h1' : off.getD (b + 1) 0 ≤ tos.length) :
    (segPairs off labs tos b).map Prod.fst =
      (labs.drop (off.getD b 0)).take (off.getD (b + 1) 0 - off.getD b 0) := by
  unfold segPairs
  rw [List.map_fst_zip]
  simp only [List.length_take, List.length_drop]
  omega

theorem segPairs_snd (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (b : Nat)
    (h1 : off.getD (b + 1) 0 ≤ labs.length) (h0 : off.getD b 0 ≤ off.getD (b + 1) 0)
    (_h1' : off.getD (b + 1) 0 ≤ tos.length) :
    (segPairs off labs tos b).map Prod.snd =
      (tos.drop (off.getD b 0)).take (off.getD (b + 1) 0 - off.getD b 0) := by
  unfold segPairs
  rw [List.map_snd_zip]
  simp only [List.length_take, List.length_drop]
  omega

theorem renamedBlock_fst (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag)) (j : Nat)
    (h1 : off.getD (invAt inverse j + 1) 0 ≤ labs.length)
    (h0 : off.getD (invAt inverse j) 0 ≤ off.getD (invAt inverse j + 1) 0)
    (h1' : off.getD (invAt inverse j + 1) 0 ≤ tos.length) :
    (renamedBlock inverse off labs tos perm j).map Prod.fst =
      (labs.drop (off.getD (invAt inverse j) 0)).take
        (off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0) := by
  unfold renamedBlock
  rw [List.map_map]
  exact segPairs_fst off labs tos (invAt inverse j) h1 h0 h1'

theorem renamedBlock_snd (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag)) (j : Nat)
    (h1 : off.getD (invAt inverse j + 1) 0 ≤ labs.length)
    (h0 : off.getD (invAt inverse j) 0 ≤ off.getD (invAt inverse j + 1) 0)
    (h1' : off.getD (invAt inverse j + 1) 0 ≤ tos.length) :
    (renamedBlock inverse off labs tos perm j).map Prod.snd =
      ((tos.drop (off.getD (invAt inverse j) 0)).take
        (off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0)).map (prename perm) := by
  unfold renamedBlock
  simp only [List.map_map, Function.comp_def]
  rw [show (fun x : QElem => prename perm x.2) = (prename perm) ∘ Prod.snd from rfl]
  rw [← List.map_map, segPairs_snd off labs tos (invAt inverse j) h1 h0 h1']

theorem blocksList_length (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag)) (N : Nat) :
    (blocksList inverse off labs tos perm N).length = N := by
  unfold blocksList; simp

theorem blocksList_succ (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag)) (N : Nat) :
    blocksList inverse off labs tos perm (N + 1) =
      blocksList inverse off labs tos perm N ++ [renamedBlock inverse off labs tos perm N] := by
  unfold blocksList
  rw [List.range_succ, List.map_append]
  simp

theorem blocksList_flatten_fst_succ (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag)) (N : Nat) :
    (blocksList inverse off labs tos perm (N + 1)).flatten.map Prod.fst =
      (blocksList inverse off labs tos perm N).flatten.map Prod.fst ++
        (renamedBlock inverse off labs tos perm N).map Prod.fst := by
  rw [blocksList_succ, List.flatten_append, List.map_append]
  simp

theorem blocksList_flatten_snd_succ (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag)) (N : Nat) :
    (blocksList inverse off labs tos perm (N + 1)).flatten.map Prod.snd =
      (blocksList inverse off labs tos perm N).flatten.map Prod.snd ++
        (renamedBlock inverse off labs tos perm N).map Prod.snd := by
  rw [blocksList_succ, List.flatten_append, List.map_append]
  simp

theorem offs_blocksList_succ (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)) (off : List Nat)
    (labs : List (TagIndex Std.Usize LabelTag)) (tos : List (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag)) (N : Nat) :
    offs (blocksList inverse off labs tos perm (N + 1)) (N + 1) =
      offs (blocksList inverse off labs tos perm N) N ++
        [(blocksList inverse off labs tos perm N).flatten.length] := by
  unfold offs
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    congr 1
    rw [blocksList_succ,
      List.take_append_of_le_length (by rw [blocksList_length]; exact Nat.le_of_lt hj)]
  · simp [blocksList_succ, blocksList_length]

theorem prename_getD (perm : Slice (TagIndex Std.Usize StateTag)) (t : TagIndex Std.Usize StateTag) :
    perm.val.getD t.index.val default = prename perm t := rfl

/-- A `Nodup` list of naturals all below `n` and of length `n` contains every `j < n`. -/
theorem mem_of_nodup_length {l : List Nat} {n : Nat} (hnd : l.Nodup) (hlen : l.length = n)
    (hlt : ∀ x ∈ l, x < n) : ∀ j < n, j ∈ l := by
  have hsub : l.toFinset ⊆ Finset.range n := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_range]
    exact hlt x hx
  have hcard : (Finset.range n).card ≤ l.toFinset.card := by
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd, hlen]
  have heq : l.toFinset = Finset.range n := Finset.eq_of_subset_of_card_le hsub hcard
  intro j hj
  rw [← List.mem_toFinset, heq, Finset.mem_range]
  exact hj

/-- An injective `perm` (given by the `.index` values) into `[0, n)` is onto. -/
theorem perm_surj {n : Nat} {perm : Slice (TagIndex Std.Usize StateTag)}
    (hlen : perm.val.length = n) (hlt : ∀ p ∈ perm.val, p.index.val < n)
    (hinj : (perm.val.map (fun p => p.index.val)).Nodup) :
    ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j := by
  intro j hj
  have hmem : j ∈ perm.val.map (fun p => p.index.val) :=
    mem_of_nodup_length hinj (by simp [hlen])
      (fun x hx => by
        rw [List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact hlt p hp) j hj
  rw [List.mem_map] at hmem
  obtain ⟨p, hp, hpj⟩ := hmem
  obtain ⟨b, hb, hbp⟩ := List.getElem_of_mem hp
  have hbP : b < perm.val.length := hb
  have hbn : b < n := by rw [hlen] at hbP; exact hbP
  refine ⟨b, hbn, ?_⟩
  rw [List.getD_eq_getElem perm.val default hb, hbp]
  exact hpj

/-- `invAt inverse` inverts `perm` on `.index` values. -/
theorem invAt_perm {n : Nat} {perm : Slice (TagIndex Std.Usize StateTag)}
    {inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)} (_hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    {b : Nat} (hb : b < n) :
    invAt inverse ((perm.val.getD b default).index.val) = b := by
  have hb' : b < perm.val.length := by omega
  rw [List.getD_eq_getElem perm.val default hb']
  obtain ⟨h, hh⟩ := hinv b hb
  unfold invAt
  rw [List.getD_eq_getElem inverse.val default h]
  exact hh

/-- The offset at the last position is `B`. -/
theorem off_getD_last_idx {off : List Nat} {B : Nat} (hlast : off.getLast? = some B) :
    off.getD (off.length - 1) 0 = B := by
  have hne : off ≠ [] := by intro h; rw [h] at hlast; simp at hlast
  have h1 : off.length - 1 < off.length := by
    have := List.length_pos_of_ne_nil hne; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
  have h2 := List.getLast?_eq_getElem? (l := off)
  rw [hlast, List.getElem?_eq_getElem h1] at h2
  exact (Option.some.inj h2).symm

/-- The offset function is monotone. -/
theorem off_getD_mono {off : List Nat} (hmono : off.Pairwise (· ≤ ·)) {a b : Nat}
    (ha : a < off.length) (hb : b < off.length) (hab : a ≤ b) :
    off.getD a 0 ≤ off.getD b 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.getD_some, Option.getD_some]
  rcases Nat.lt_or_eq_of_le hab with h | h
  · exact List.pairwise_iff_getElem.mp hmono a b ha hb h
  · subst h; rfl

/-- The offset at `b` never exceeds the last offset. -/
theorem off_getD_le_last {off : List Nat} {B : Nat} (hmono : off.Pairwise (· ≤ ·))
    (hlast : off.getLast? = some B) {b : Nat} (hb : b < off.length) :
    off.getD b 0 ≤ B := by
  have hne : off ≠ [] := by intro h; rw [h] at hb; simp at hb
  have hlen : 1 ≤ off.length := List.length_pos_of_ne_nil hne
  exact le_trans
    (off_getD_mono hmono hb (by omega) (by omega))
    (le_of_eq (off_getD_last_idx hlast))

/-- `invAt` maps `[0, n)` into `[0, n)`. -/
theorem invAt_lt {n : Nat} {perm : Slice (TagIndex Std.Usize StateTag)}
    {inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)} (hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j)
    {j : Nat} (hj : j < n) : invAt inverse j < n := by
  obtain ⟨b, hb, hbj⟩ := hsurj j hj
  rw [← hbj, invAt_perm hinvlen hlen hinv hb]
  exact hb

/-- `invAt` is injective on `[0, n)`. -/
theorem invAt_inj {n : Nat} {perm : Slice (TagIndex Std.Usize StateTag)}
    {inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)} (hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j)
    {j1 j2 : Nat} (h1 : j1 < n) (h2 : j2 < n)
    (heq : invAt inverse j1 = invAt inverse j2) : j1 = j2 := by
  obtain ⟨b1, hb1, hb1j⟩ := hsurj j1 h1
  obtain ⟨b2, hb2, hb2j⟩ := hsurj j2 h2
  rw [← hb1j, invAt_perm hinvlen hlen hinv hb1, ← hb2j, invAt_perm hinvlen hlen hinv hb2] at heq
  rw [← hb1j, ← hb2j, heq]

/-- `invAt` is onto `[0, n)`. -/
theorem invAt_range_mem {n : Nat} {perm : Slice (TagIndex Std.Usize StateTag)}
    {inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)} (hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j) :
    ∀ j < n, j ∈ (List.range n).map (invAt inverse) := by
  have hnd : ((List.range n).map (invAt inverse)).Nodup :=
    List.Nodup.map_on
      (fun a ha b hb h =>
        invAt_inj hinvlen hlen hinv hsurj (List.mem_range.mp ha) (List.mem_range.mp hb) h)
      List.nodup_range
  have hlen' : ((List.range n).map (invAt inverse)).length = n := by simp
  have hlt : ∀ x ∈ (List.range n).map (invAt inverse), x < n := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact invAt_lt hinvlen hlen hinv hsurj (List.mem_range.mp ha)
  exact mem_of_nodup_length hnd hlen' hlt

/-- Two `Nodup` lists with the same elements are permutations. -/
theorem perm_of_nodup_iff {l₁ l₂ : List Nat} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : List.Perm l₁ l₂ := by
  rw [List.perm_iff_count]
  intro a
  rw [List.Nodup.count h1, List.Nodup.count h2]
  simp only [hmem a]

/-- The list of inverse indices is a permutation of `List.range n`. -/
theorem map_invAt_perm {n : Nat} {perm : Slice (TagIndex Std.Usize StateTag)}
    {inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag)} (hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j) :
    List.Perm ((List.range n).map (invAt inverse)) (List.range n) := by
  apply perm_of_nodup_iff
  · exact List.Nodup.map_on
      (fun a ha b hb h =>
        invAt_inj hinvlen hlen hinv hsurj (List.mem_range.mp ha) (List.mem_range.mp hb) h)
      List.nodup_range
  · exact List.nodup_range
  · intro a
    constructor
    · intro ha
      rw [List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      exact List.mem_range.mpr (invAt_lt hinvlen hlen hinv hsurj (List.mem_range.mp hb))
    · intro ha
      exact invAt_range_mem hinvlen hlen hinv hsurj a (List.mem_range.mp ha)

/-- The labels of block `b`, as a contiguous slice of `labs`. -/
def segAt (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag)) (b : Nat) :
    List (TagIndex Std.Usize LabelTag) :=
  (labs.drop (off.getD b 0)).take (off.getD (b + 1) 0 - off.getD b 0)

/-- `renamedBlock`'s labels are exactly the contiguous slice `segAt`. -/
theorem renamedBlock_fst' {n : Nat} (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag))
    (hmono : off.Pairwise (· ≤ ·)) (hlast : off.getLast? = some labs.length)
    (hle : labs.length = tos.length) (hoff : off.length = n + 1)
    {j : Nat} (hj : invAt inverse j < n) :
    (renamedBlock inverse off labs tos perm j).map Prod.fst = segAt off labs (invAt inverse j) := by
  have h1 : off.getD (invAt inverse j + 1) 0 ≤ labs.length :=
    off_getD_le_last hmono hlast (by omega)
  have h0 : off.getD (invAt inverse j) 0 ≤ off.getD (invAt inverse j + 1) 0 :=
    off_getD_mono hmono (by omega) (by omega) (by omega)
  have h1' : off.getD (invAt inverse j + 1) 0 ≤ tos.length := by rw [← hle]; exact h1
  exact renamedBlock_fst inverse off labs tos perm j h1 h0 h1'

/-- The length of the `segAt` slice is the offset difference. -/
theorem segAt_length (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (hmono : off.Pairwise (· ≤ ·)) (hlast : off.getLast? = some labs.length)
    {b : Nat} (hb : b + 1 < off.length) :
    (segAt off labs b).length = off.getD (b + 1) 0 - off.getD b 0 := by
  unfold segAt
  rw [List.length_take, List.length_drop]
  have hle : off.getD (b + 1) 0 ≤ labs.length :=
    off_getD_le_last hmono hlast (by omega)
  have h0 : off.getD b 0 ≤ off.getD (b + 1) 0 := off_getD_mono hmono (by omega) (by omega) (by omega)
  omega

/-- `(blocksList n).flatten.map Prod.fst` is a flattening of the slices `segAt (invAt j)`. -/
theorem blocksList_flatten_fst_eq (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag))
    {n : Nat} (hmono : off.Pairwise (· ≤ ·)) (hlast : off.getLast? = some labs.length)
    (hle : labs.length = tos.length) (hoff : off.length = n + 1)
    (hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j) (c : Nat) (hc : c ≤ n) :
    (blocksList inverse off labs tos perm c).flatten.map Prod.fst =
      ((List.range c).map (fun j => segAt off labs (invAt inverse j))).flatten := by
  unfold blocksList
  rw [List.map_flatten, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  show (renamedBlock inverse off labs tos perm j).map Prod.fst = segAt off labs (invAt inverse j)
  exact renamedBlock_fst' inverse off labs tos perm hmono hlast hle hoff
    (invAt_lt hinvlen hlen hinv hsurj (by omega))

/-- The total length of the renamed blocks is the sum of the corresponding offset differences. -/
theorem blocksList_flatten_length_eq (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag))
    {n : Nat} (hmono : off.Pairwise (· ≤ ·)) (hlast : off.getLast? = some labs.length)
    (hle : labs.length = tos.length) (hoff : off.length = n + 1)
    (hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j) (c : Nat) (hc : c ≤ n) :
    (blocksList inverse off labs tos perm c).flatten.length =
      ((List.range c).map
        (fun j => off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0)).sum := by
  rw [← List.length_map (f := Prod.fst),
    blocksList_flatten_fst_eq inverse off labs tos perm hmono hlast hle hoff hinvlen hlen hinv hsurj c hc]
  rw [List.length_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  show (segAt off labs (invAt inverse j)).length = off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0
  exact segAt_length off labs hmono hlast (by
    have := invAt_lt hinvlen hlen hinv hsurj (j := j) (by omega)
    omega)

/-- Sum of a prefix is at most the whole sum (for naturals). -/
theorem sum_take_le (l : List Nat) (c : Nat) : (l.take c).sum ≤ l.sum := by
  have := List.sum_append (l₁ := l.take c) (l₂ := l.drop c)
  rw [List.take_append_drop] at this
  rw [this]; omega

/-- The offset differences telescope. -/
theorem sum_off_sub (off : List Nat) (hmono : off.Pairwise (· ≤ ·)) :
    ∀ N, N + 1 ≤ off.length →
      ((List.range N).map (fun b => off.getD (b + 1) 0 - off.getD b 0)).sum =
        off.getD N 0 - off.getD 0 0 := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro hN
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h1 : off.getD N 0 ≤ off.getD (N + 1) 0 :=
      off_getD_mono hmono (by omega) (by omega) (by omega)
    have h2 : off.getD 0 0 ≤ off.getD N 0 :=
      off_getD_mono hmono (by omega) (by omega) (by omega)
    omega

/-- The last offset is `labs.length`. -/
theorem off_getD_last {off : List Nat} {B : Nat} (hlast : off.getLast? = some B)
    {N : Nat} (hoff : off.length = N + 1) : off.getD N 0 = B := by
  have h := off_getD_last_idx (off := off) hlast
  rw [hoff, show N + 1 - 1 = N by omega] at h
  exact h

/-- The total length of the renamed blocks is bounded by `labs.length`. -/
theorem blocksList_flatten_length_le (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag))
    {n : Nat} (hmono : off.Pairwise (· ≤ ·)) (hlast : off.getLast? = some labs.length)
    (hle : labs.length = tos.length) (hoff : off.length = n + 1)
    (hinvlen : inverse.val.length = n)
    (hlen : perm.val.length = n)
    (hinv : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q)
    (hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j) (c : Nat) (hc : c ≤ n) :
    (blocksList inverse off labs tos perm c).flatten.length ≤ labs.length := by
  rw [blocksList_flatten_length_eq inverse off labs tos perm hmono hlast hle hoff hinvlen hlen hinv hsurj c hc]
  -- prefix sum <= full (reindexed) sum <= labs.length
  have hperm : List.Perm ((List.range n).map (invAt inverse)) (List.range n) :=
    map_invAt_perm hinvlen hlen hinv hsurj
  have hreindex :
      ((List.range n).map (fun j => off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0)).sum =
        ((List.range n).map (fun b => off.getD (b + 1) 0 - off.getD b 0)).sum := by
    rw [show (fun j => off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0) =
      (fun b => off.getD (b + 1) 0 - off.getD b 0) ∘ (invAt inverse) from rfl]
    rw [← List.map_map]
    exact List.Perm.sum_eq (List.Perm.map
      (fun b => off.getD (b + 1) 0 - off.getD b 0) hperm)
  have hprefix : ((List.range c).map (fun j => off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0)).sum ≤
      ((List.range n).map (fun j => off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0)).sum := by
    have htake : List.range c = (List.range n).take c := by
      rw [List.take_range, Nat.min_eq_left hc]
    rw [htake, List.map_take]
    exact sum_take_le _ c
  have hfull := sum_off_sub off hmono n (by omega)
  have hlast' : off.getD n 0 = labs.length := off_getD_last hlast hoff
  calc
    ((List.range c).map (fun j => off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0)).sum
        ≤ ((List.range n).map (fun j => off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0)).sum := hprefix
    _ = ((List.range n).map (fun b => off.getD (b + 1) 0 - off.getD b 0)).sum := hreindex
    _ = off.getD n 0 - off.getD 0 0 := hfull
    _ = labs.length - off.getD 0 0 := by rw [hlast']
    _ ≤ labs.length := Nat.sub_le _ _

/-- The inner loop of `new_from_permutation_vec`: it replays a run `[start, end)` of the input
    `transition_labels`/`transition_to` into the accumulators, renaming targets by `perm`. -/
theorem nfp_inner_spec (bcv : ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (bcv1 : ByteCompressedVec (TagIndex Std.Usize StateTag))
    (perm : Slice (TagIndex Std.Usize StateTag))
    (hperm : ∀ t ∈ ByteCompressedVec.toList bcv1, t.index.val < perm.val.length) :
    ∀ (m : Nat) (iter : core.ops.range.Range Std.Usize)
      (tl : ByteCompressedVec (TagIndex Std.Usize LabelTag))
      (tt : ByteCompressedVec (TagIndex Std.Usize StateTag)),
      iter.«end».val - iter.start.val = m →
      iter.«end».val ≤ (ByteCompressedVec.toList bcv).length →
      iter.«end».val ≤ (ByteCompressedVec.toList bcv1).length →
      (ByteCompressedVec.toList tl).length + m < Std.Usize.max →
      (ByteCompressedVec.toList tt).length + m < Std.Usize.max →
      ∃ tl' tt',
        verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0
          iter bcv bcv1 perm tl tt = ok (tl', tt') ∧
        ByteCompressedVec.toList tl' = ByteCompressedVec.toList tl ++
          ((ByteCompressedVec.toList bcv).drop iter.start.val).take m ∧
        ByteCompressedVec.toList tt' = ByteCompressedVec.toList tt ++
          (((ByteCompressedVec.toList bcv1).drop iter.start.val).take m).map (prename perm) := by
  intro m
  induction m with
  | zero =>
    intro iter tl tt _ _ _ _ _
    refine ⟨tl, tt, ?_, by simp, by simp⟩
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0
    apply loop_done'
    show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0.body
      bcv bcv1 perm iter tl tt = _
    have hge : iter.start.val ≥ iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hident⟩ := next_range_none iter hge
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0.body
    rw [hnext, ho]
    simp
  | succ m ih =>
    intro iter tl tt hm hend hend1 hl ht
    have hlt : iter.start.val < iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hstart', hend'⟩ := next_range_some iter hlt
    have hi1 : iter.start.val < (ByteCompressedVec.toList bcv).length := by omega
    have hi2 : iter.start.val < (ByteCompressedVec.toList bcv1).length := by omega
    have e1 := merc_collections.compressed_vec.ByteCompressedVec.index_spec LIdx bcv iter.start hi1
    have e2 := merc_collections.compressed_vec.ByteCompressedVec.index_spec SIdx bcv1 iter.start hi2
    obtain ⟨tl1, hp1, hv1⟩ := merc_collections.compressed_vec.ByteCompressedVec.push_spec LIdx tl
      ((ByteCompressedVec.toList bcv)[iter.start.val]) (by omega)
    have ht1 : ((ByteCompressedVec.toList bcv1)[iter.start.val]).index.val < perm.val.length :=
      hperm _ (List.getElem_mem hi2)
    obtain ⟨tt1, hp2, hv2⟩ := merc_collections.compressed_vec.ByteCompressedVec.push_spec SIdx tt
      (perm.val[((ByteCompressedVec.toList bcv1)[iter.start.val]).index.val]'ht1) (by omega)
    have hn1 : iter1.«end».val - iter1.start.val = m := by rw [hend']; omega
    obtain ⟨tl', tt', hloop, hlt', htt'⟩ := ih iter1 tl1 tt1 hn1
      (by rw [hend']; exact hend) (by rw [hend']; exact hend1)
      (by rw [hv1]; simp; omega) (by rw [hv2]; simp; omega)
    refine ⟨tl', tt', ?_, ?_, ?_⟩
    · unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0 at hloop ⊢
      have hbody : verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0.body
          bcv bcv1 perm iter tl tt = ok (cont (iter1, tl1, tt1)) := by
        unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0.body
        have hidx := slice_index_ok' perm ((ByteCompressedVec.toList bcv1)[iter.start.val]).index ht1
        simp [hnext, ho, e1, e2, hidx, hp1, hp2]
      rw [loop_cont' _ _ _ hbody]
      exact hloop
    · rw [hlt', hv1, hstart']
      have htake : ((ByteCompressedVec.toList bcv).drop iter.start.val).take (m + 1) =
          ((ByteCompressedVec.toList bcv)[iter.start.val]'hi1) ::
            ((ByteCompressedVec.toList bcv).drop (iter.start.val + 1)).take m := by
        rw [List.drop_eq_getElem_cons hi1, List.take_succ_cons]
      rw [htake]; simp
    · rw [htt', hv2, hstart']
      have htake : ((ByteCompressedVec.toList bcv1).drop iter.start.val).take (m + 1) =
          ((ByteCompressedVec.toList bcv1)[iter.start.val]'hi2) ::
            ((ByteCompressedVec.toList bcv1).drop (iter.start.val + 1)).take m := by
        rw [List.drop_eq_getElem_cons hi2, List.take_succ_cons]
      have hpre : prename perm ((ByteCompressedVec.toList bcv1)[iter.start.val]'hi2) =
          perm.val[((ByteCompressedVec.toList bcv1)[iter.start.val]).index.val]'ht1 := by
        unfold prename
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1]
        rfl
      rw [htake, List.map_cons, hpre]
      simp

theorem renamedBlock_length {n : Nat} (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag))
    (hmono : off.Pairwise (· ≤ ·)) (hlast : off.getLast? = some labs.length)
    (hle : labs.length = tos.length) (hoff : off.length = n + 1) {j : Nat}
    (hj : invAt inverse j < n) :
    (renamedBlock inverse off labs tos perm j).length =
      off.getD (invAt inverse j + 1) 0 - off.getD (invAt inverse j) 0 := by
  rw [← List.length_map (f := Prod.fst),
    renamedBlock_fst' inverse off labs tos perm hmono hlast hle hoff hj]
  exact segAt_length off labs hmono hlast (by omega)

theorem blocksList_flatten_length_succ (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag)) (N : Nat) :
    (blocksList inverse off labs tos perm (N + 1)).flatten.length =
      (blocksList inverse off labs tos perm N).flatten.length +
        (renamedBlock inverse off labs tos perm N).length := by
  have h := congrArg List.length (blocksList_flatten_fst_succ inverse off labs tos perm N)
  simpa only [List.length_append, List.length_map] using h

/-- Invariant for the outer loop of `new_from_permutation_vec`. -/
def NfpInv (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (perm : Slice (TagIndex Std.Usize StateTag))
    (c : Nat) (states : ByteCompressedVec Std.Usize)
    (TL : ByteCompressedVec (TagIndex Std.Usize LabelTag))
    (TT : ByteCompressedVec (TagIndex Std.Usize StateTag)) : Prop :=
  (ByteCompressedVec.toList states).map (fun u => u.val) =
      offs (blocksList inverse off labs tos perm c) c ∧
  ByteCompressedVec.toList TL = (blocksList inverse off labs tos perm c).flatten.map Prod.fst ∧
  ByteCompressedVec.toList TT = (blocksList inverse off labs tos perm c).flatten.map Prod.snd

/-- The outer loop of `new_from_permutation_vec`: walks the permutation, recording offsets in
    `states` and concatenating the renamed blocks into the transition vectors. -/
theorem nfp_outer_spec {Label : Type} (lts : LabelledTransitionSystem Label)
    (perm : Slice (TagIndex Std.Usize StateTag))
    (inverse : alloc.vec.Vec (TagIndex Std.Usize StateTag))
    {n : Nat} {off : List Nat} {labs : List (TagIndex Std.Usize LabelTag)}
    {tos : List (TagIndex Std.Usize StateTag)}
    (hR : RawOf lts n off labs tos)
    (hinvlen : inverse.val.length = n) (hplen : perm.val.length = n)
    (hlt : ∀ p ∈ perm.val, p.index.val < n)
    (hinj : (perm.val.map (fun p => p.index.val)).Nodup)
    (hpost : ∀ q (hq : q < n),
      ∃ h : (perm.val[q]'(by omega)).index.val < inverse.val.length,
        (inverse.val[(perm.val[q]'(by omega)).index.val]'h).index.val = q) :
    ∀ (m : Nat) (iter : core.ops.range.Range Std.Usize)
      (states : ByteCompressedVec Std.Usize)
      (TL : ByteCompressedVec (TagIndex Std.Usize LabelTag))
      (TT : ByteCompressedVec (TagIndex Std.Usize StateTag)),
      iter.«end».val - iter.start.val = m →
      iter.«end».val ≤ n →
      iter.start.val ≤ iter.«end».val →
      NfpInv inverse off labs tos perm iter.start.val states TL TT →
      ∃ lts' states' TL' TT',
        verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0
          iter lts perm inverse states TL TT = ok (lts', states', TL', TT') ∧
        lts' = lts ∧
        NfpInv inverse off labs tos perm iter.«end».val states' TL' TT' := by
  intro m
  induction m with
  | zero =>
    intro iter states TL TT hm hend hle hinv
    have hge : iter.start.val ≥ iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, _⟩ := next_range_none iter hge
    refine ⟨lts, states, TL, TT, ?_, rfl, ?_⟩
    · unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0
      apply loop_done'
      show verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0.body
        lts perm inverse iter states TL TT = _
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0.body
      rw [hnext, ho]
      simp
    · have heq : iter.start.val = iter.«end».val := by omega
      rw [← heq]; exact hinv
  | succ m ih =>
    intro iter states TL TT hm hend hle hinv
    have hiterlt : iter.start.val < iter.«end».val := by omega
    obtain ⟨o, iter1, hnext, ho, hstart', hend'⟩ := next_range_some iter hiterlt
    obtain ⟨hst, htl, htt⟩ := hinv
    have hcend : iter.start.val < n := by omega
    have hc_le : iter.start.val ≤ n := Nat.le_of_lt hcend
    have hmaxR : n + 1 ≤ Std.Usize.max := RawOf.off_le hR
    have hsurj : ∀ j < n, ∃ b < n, (perm.val.getD b default).index.val = j :=
      perm_surj hplen hlt hinj
    have hperm : ∀ t ∈ ByteCompressedVec.toList lts.transition_to, t.index.val < perm.val.length := by
      intro t ht; rw [hR.tl] at ht; rw [hplen]; exact hR.tlt t ht
    have hTLlen : (ByteCompressedVec.toList TL).length =
        (blocksList inverse off labs tos perm iter.start.val).flatten.length := by rw [htl, List.length_map]
    have hTTlen : (ByteCompressedVec.toList TT).length =
        (blocksList inverse off labs tos perm iter.start.val).flatten.length := by rw [htt, List.length_map]
    have hstateslen : (ByteCompressedVec.toList states).length = iter.start.val := by
      have := congrArg List.length hst; simpa [offs] using this
    have hboundTL1 : (blocksList inverse off labs tos perm (iter.start.val + 1)).flatten.length ≤
        labs.length :=
      blocksList_flatten_length_le inverse off labs tos perm hR.mono hR.last hR.len_eq hR.offlen
        hinvlen hplen hpost hsurj (iter.start.val + 1) (by omega)
    have hinvlt : invAt inverse iter.start.val < n :=
      invAt_lt hinvlen hplen hpost hsurj hcend
    obtain ⟨i0, hlen, hlenv⟩ := ByteCompressedVec.len_spec LIdx TL (by
      rw [hTLlen]
      exact le_of_lt (lt_of_le_of_lt
        (blocksList_flatten_length_le inverse off labs tos perm hR.mono hR.last hR.len_eq hR.offlen
          hinvlen hplen hpost hsurj iter.start.val hc_le) hR.tmax))
    obtain ⟨states1, hpush, hpushv⟩ := ByteCompressedVec.push_spec UIdx states i0 (by
      rw [hstateslen]; omega)
    have hvc : iter.start.val < inverse.val.length := by omega
    let ti : TagIndex Std.Usize StateTag := inverse.val[iter.start.val]'hvc
    have hveci : alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice (TagIndex Std.Usize StateTag)) inverse iter.start
        = ok ti := vec_index_ok' inverse iter.start hvc
    have htival : ti.index.val = invAt inverse iter.start.val := by
      change (inverse.val[iter.start.val]'hvc).index.val =
        (inverse.val.getD iter.start.val default).index.val
      rw [List.getD_eq_getElem inverse.val default hvc]
    have h1 : (1#usize : Std.Usize).val = 1 := by simp
    have htag : verified.merc_utilities.tagged_index.TagIndex.value core.marker.CopyUsize ti =
        ok ti.index := tag_value_id core.marker.CopyUsize ti
    have holdlt : ti.index.val < (ByteCompressedVec.toList lts.states).length := by
      rw [hR.st_length, htival]; exact Nat.lt_succ_of_lt hinvlt
    let sv : Std.Usize := (ByteCompressedVec.toList lts.states)[ti.index.val]'holdlt
    have hstarti : ByteCompressedVec.index UIdx lts.states ti.index = ok sv :=
      ByteCompressedVec.index_spec UIdx lts.states ti.index holdlt
    have hsv : sv.val = off.getD ti.index.val 0 := RawOf.st_get hR ti.index.val holdlt
    obtain ⟨i1, hadde, hi1v⟩ : ∃ r, _ = r ∧ Std.WP.spec r _ :=
      ⟨_, rfl, Usize.add_spec (x := ti.index) (y := 1#usize) (by
        rw [htival, h1]
        omega)⟩
    cases i1 <;> simp only [Std.WP.spec_ok, Std.WP.spec_vis, Std.WP.spec_div] at hi1v
    rename_i i1
    have hi1lt : i1.val < (ByteCompressedVec.toList lts.states).length := by
      rw [hR.st_length, hi1v, h1, htival]; omega
    let ev : Std.Usize := (ByteCompressedVec.toList lts.states)[i1.val]'hi1lt
    have hendi : ByteCompressedVec.index UIdx lts.states i1 = ok ev :=
      ByteCompressedVec.index_spec UIdx lts.states i1 hi1lt
    have hev : ev.val = off.getD i1.val 0 := RawOf.st_get hR i1.val hi1lt
    have hm0 : ev.val - sv.val =
        off.getD (invAt inverse iter.start.val + 1) 0 - off.getD (invAt inverse iter.start.val) 0 := by
      rw [hev, hsv, hi1v, h1, htival]
    have hend_le : ev.val ≤ labs.length := by
      rw [hev, hi1v, h1, htival]
      exact off_getD_le_last hR.mono hR.last
        (by rw [hR.offlen]; omega)
    have hcapTL : (ByteCompressedVec.toList TL).length + (ev.val - sv.val) < Std.Usize.max := by
      rw [hTLlen, hm0, ← renamedBlock_length inverse off labs tos perm hR.mono hR.last hR.len_eq
        hR.offlen hinvlt, ← blocksList_flatten_length_succ]
      exact lt_of_le_of_lt hboundTL1 hR.tmax
    have hcapTT : (ByteCompressedVec.toList TT).length + (ev.val - sv.val) < Std.Usize.max := by
      rw [hTTlen, hm0, ← renamedBlock_length inverse off labs tos perm hR.mono hR.last hR.len_eq
        hR.offlen hinvlt, ← blocksList_flatten_length_succ]
      exact lt_of_le_of_lt hboundTL1 hR.tmax
    obtain ⟨TL2, TT2, hinner, hTL2inner, hTT2inner⟩ :=
      nfp_inner_spec lts.transition_labels lts.transition_to perm hperm
        (ev.val - sv.val) { start := sv, «end» := ev } TL TT rfl
        (by rw [hR.lab]; exact hend_le)
        (by rw [hR.tl, ← hR.len_eq]; exact hend_le)
        hcapTL hcapTT
    have hseg : ((ByteCompressedVec.toList lts.transition_labels).drop sv.val).take (ev.val - sv.val) =
        (labs.drop (off.getD (invAt inverse iter.start.val) 0)).take
          (off.getD (invAt inverse iter.start.val + 1) 0 -
            off.getD (invAt inverse iter.start.val) 0) := by
      rw [hR.lab, hm0, hsv, htival]
    have hsegT : (((ByteCompressedVec.toList lts.transition_to).drop sv.val).take
          (ev.val - sv.val)).map (prename perm) =
        ((tos.drop (off.getD (invAt inverse iter.start.val) 0)).take
          (off.getD (invAt inverse iter.start.val + 1) 0 -
            off.getD (invAt inverse iter.start.val) 0)).map (prename perm) := by
      rw [hR.tl, hm0, hsv, htival]
    have hstates2 : (ByteCompressedVec.toList states1).map (fun u => u.val) =
        offs (blocksList inverse off labs tos perm (iter.start.val + 1)) (iter.start.val + 1) := by
      rw [hpushv, List.map_append, List.map_cons, List.map_nil, hst, hlenv, hTLlen,
        ← offs_blocksList_succ]
    have hoff1 : off.getD (invAt inverse iter.start.val + 1) 0 ≤ labs.length := by
      have := hend_le; rw [hev, hi1v, h1, htival] at this; exact this
    have hoff0 : off.getD (invAt inverse iter.start.val) 0 ≤
        off.getD (invAt inverse iter.start.val + 1) 0 := by
      refine off_getD_mono hR.mono ?_ ?_ (by omega)
      · rw [hR.offlen]; omega
      · rw [hR.offlen]; omega
    have hoff1' : off.getD (invAt inverse iter.start.val + 1) 0 ≤ tos.length := by
      rw [← hR.len_eq]; exact hoff1
    have hTL2' : ByteCompressedVec.toList TL2 =
        (blocksList inverse off labs tos perm (iter.start.val + 1)).flatten.map Prod.fst := by
      rw [hTL2inner, hseg, htl,
        ← renamedBlock_fst inverse off labs tos perm iter.start.val hoff1 hoff0 hoff1',
        ← blocksList_flatten_fst_succ]
    have hTT2' : ByteCompressedVec.toList TT2 =
        (blocksList inverse off labs tos perm (iter.start.val + 1)).flatten.map Prod.snd := by
      rw [hTT2inner, hsegT, htt,
        ← renamedBlock_snd inverse off labs tos perm iter.start.val hoff1 hoff0 hoff1',
        ← blocksList_flatten_snd_succ]
    have hbody : verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0.body
        lts perm inverse iter states TL TT = ok (cont (iter1, states1, TL2, TT2)) := by
      unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0.body
      rw [hnext, ho, hlen]
      simp [hpush]
      rw [alloc.vec.Vec.index_slice_index] at hveci
      simp [hveci, hstarti, hadde, hendi, hinner]
    have hn1 : iter1.«end».val - iter1.start.val = m := by rw [hend']; omega
    have hinv1 : NfpInv inverse off labs tos perm iter1.start.val states1 TL2 TT2 := by
      rw [hstart']; exact ⟨hstates2, hTL2', hTT2'⟩
    obtain ⟨lts', states', TL', TT', hloop, hlts', hinv'⟩ :=
      ih iter1 states1 TL2 TT2 hn1 (by rw [hend']; exact hend)
        (by rw [hstart', hend']; omega) hinv1
    refine ⟨lts', states', TL', TT', ?_, hlts', ?_⟩
    · unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0 at hloop ⊢
      rw [loop_cont' _ _ _ hbody]
      exact hloop
    · rw [← hend']; exact hinv'

theorem segPairs_length (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (b : Nat)
    (h1 : off.getD (b + 1) 0 ≤ labs.length) (hle : labs.length = tos.length) :
    (segPairs off labs tos b).length = off.getD (b + 1) 0 - off.getD b 0 := by
  unfold segPairs
  simp only [List.length_zip, List.length_take, List.length_drop]
  omega

theorem segPairs_getElem (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (b i : Nat)
    (hi : i < (segPairs off labs tos b).length) :
    ∃ (h1 : off.getD b 0 + i < labs.length) (h2 : off.getD b 0 + i < tos.length),
      (segPairs off labs tos b)[i] = (labs[off.getD b 0 + i], tos[off.getD b 0 + i]) := by
  unfold segPairs at hi ⊢
  simp only [List.length_zip, List.length_take, List.length_drop] at hi
  refine ⟨by omega, by omega, ?_⟩
  simp [List.getElem_zip]

theorem mem_segPairs (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (b : Nat) (x : QElem)
    (hx : x ∈ segPairs off labs tos b) : x.1 ∈ labs ∧ x.2 ∈ tos := by
  unfold segPairs at hx
  have h := List.of_mem_zip hx
  exact ⟨List.mem_of_mem_drop (List.mem_of_mem_take h.1),
    List.mem_of_mem_drop (List.mem_of_mem_take h.2)⟩

/-- The `nodup` side condition of `RawGood` says exactly that every block is duplicate-free. -/
theorem rawGood_nodup_iff {n : Nat} {off : List Nat} {labs : List (TagIndex Std.Usize LabelTag)}
    {tos : List (TagIndex Std.Usize StateTag)} (hmono : off.Pairwise (· ≤ ·))
    (hlast : off.getLast? = some labs.length) (hle : labs.length = tos.length)
    (hoff : off.length = n + 1) :
    (∀ s, s < n → ∀ i j, off.getD s 0 ≤ i → i < j → j < off.getD (s + 1) 0 →
      ∀ (hi : i < labs.length) (hj : j < labs.length) (hi' : i < tos.length) (hj' : j < tos.length),
        labs[i] = labs[j] → tos[i] = tos[j] → False) ↔
    ∀ s, s < n → (segPairs off labs tos s).Nodup := by
  constructor
  · intro H s hs
    have h1 : off.getD (s + 1) 0 ≤ labs.length := off_getD_le_last hmono hlast (by omega)
    have hlen := segPairs_length off labs tos s h1 hle
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    obtain ⟨a1, a2, ha⟩ := segPairs_getElem off labs tos s i hi
    obtain ⟨b1, b2, hb⟩ := segPairs_getElem off labs tos s j hj
    rw [ha, hb, Prod.mk.injEq] at heq
    exact H s hs _ _ (by omega) (by omega) (by omega) a1 b1 a2 b2 heq.1 heq.2
  · intro H s hs i j hsi hij hjs hi hj hi' hj' hl ht
    have h1 : off.getD (s + 1) 0 ≤ labs.length := off_getD_le_last hmono hlast (by omega)
    have hlen := segPairs_length off labs tos s h1 hle
    have hnd := H s hs
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hnd
    have hi2 : i - off.getD s 0 < (segPairs off labs tos s).length := by omega
    have hj2 : j - off.getD s 0 < (segPairs off labs tos s).length := by omega
    apply hnd _ _ hi2 hj2 (by omega)
    obtain ⟨a1, a2, ha⟩ := segPairs_getElem off labs tos s _ hi2
    obtain ⟨b1, b2, hb⟩ := segPairs_getElem off labs tos s _ hj2
    rw [ha, hb]
    have e1 : off.getD s 0 + (i - off.getD s 0) = i := by omega
    have e2 : off.getD s 0 + (j - off.getD s 0) = j := by omega
    simp only [e1, e2, hl, ht]

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
  have hn := hR.n_pos
  have hmax := hR.off_le
  have hsurj := perm_surj hlen hlt hinj
  obtain ⟨inv, hinvE, hinvlen, hpost⟩ := invert_permutation_spec perm n hlen hlt hinj
  obtain ⟨st0, hst_new, hst0⟩ := merc_collections.compressed_vec.ByteCompressedVec.new_spec UIdx
  obtain ⟨lb0, hlb_new, hlb0⟩ := merc_collections.compressed_vec.ByteCompressedVec.new_spec LIdx
  obtain ⟨tb0, htb_new, htb0⟩ := merc_collections.compressed_vec.ByteCompressedVec.new_spec SIdx
  have hlenv : (alloc.vec.Vec.len inv).val = n := by rw [vec_len_val']; exact hinvlen
  have hinv0 : NfpInv inv off labs tos perm 0 st0 lb0 tb0 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [hst0, hlb0, htb0, blocksList, offs]
  obtain ⟨lts', st, TL, TT, hloop, hlts', hinvN⟩ :=
    nfp_outer_spec Q perm inv hR hinvlen hlen hlt hinj hpost n
      { start := 0#usize, «end» := alloc.vec.Vec.len inv } st0 lb0 tb0
      (by simp [hlenv]) (by simp [hlenv]) (by simp) hinv0
  subst hlts'
  obtain ⟨hstN, hTLN, hTTN⟩ := hinvN
  simp only [hlenv] at hstN hTLN hTTN
  set Ls := blocksList inv off labs tos perm n with hLsdef
  have hLlen : Ls.length = n := blocksList_length inv off labs tos perm n
  have hflen : Ls.flatten.length ≤ labs.length :=
    blocksList_flatten_length_le inv off labs tos perm hR.mono hR.last hR.len_eq hR.offlen hinvlen
      hlen hpost hsurj n le_rfl
  have hTLlen : (ByteCompressedVec.toList TL).length ≤ Std.Usize.max := by
    rw [hTLN, List.length_map]; have := hR.tmax; omega
  obtain ⟨i1, hlen_TL, hi1v⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec LIdx TL hTLlen
  have hi1v' : i1.val = Ls.flatten.length := by rw [hi1v, hTLN, List.length_map]
  have hstlen : (ByteCompressedVec.toList st).length = n := by
    have h := congrArg List.length hstN
    simpa [List.length_map, offs_length] using h
  obtain ⟨st2, hpst, hst2⟩ :=
    merc_collections.compressed_vec.ByteCompressedVec.push_spec UIdx st i1 (by rw [hstlen]; omega)
  have hst2v : (ByteCompressedVec.toList st2).map (fun u : Std.Usize => u.val) =
      offs Ls n ++ [Ls.flatten.length] := by
    rw [hst2, List.map_append, hstN]; simp [hi1v']
  have hinitlt : lts'.initial_state.index.val < perm.val.length := by rw [hlen]; exact hR.init
  set ti := perm.val[lts'.initial_state.index.val]'hinitlt with htidef
  have hti : Slice.index_usize perm lts'.initial_state.index = ok ti :=
    slice_index_ok' perm _ hinitlt
  set R : LabelledTransitionSystem Label :=
    { states := st2, transition_labels := TL, transition_to := TT, labels := lts'.labels,
      initial_state := ti } with hRdef
  have hgetLs : ∀ j (hj : j < Ls.length), Ls[j] = renamedBlock inv off labs tos perm j := by
    intro j hj; simp [hLsdef, blocksList]
  have hmem : ∀ y ∈ Ls.flatten, ∃ x : QElem, x.1 ∈ labs ∧ x.2 ∈ tos ∧ y = (x.1, prename perm x.2) := by
    intro y hy
    obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    rw [hgetLs j hj] at hyl
    unfold renamedBlock at hyl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hyl
    exact ⟨x, (mem_segPairs _ _ _ _ x hx).1, (mem_segPairs _ _ _ _ x hx).2, rfl⟩
  have hprename_lt : ∀ t ∈ tos, (prename perm t).index.val < n := by
    intro t ht
    have htn := hR.tlt t ht
    unfold prename
    rw [List.getD_eq_getElem perm.val default (by omega)]
    exact hlt _ (List.getElem_mem _)
  have hRawOf : RawOf R n (offs Ls n ++ [Ls.flatten.length]) (Ls.flatten.map Prod.fst)
      (Ls.flatten.map Prod.snd) :=
    { st := hst2v
      lab := hTLN
      tl := hTTN
      offlen := by rw [List.length_append, offs_length]; simp
      mono := offs_pairwise Ls n
      last := by
        rw [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
          List.length_map]
      len_eq := by rw [List.length_map, List.length_map]
      tlt := by
        intro t ht
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, -, hx2, rfl⟩ := hmem y hy
        exact hprename_lt x.2 hx2
      init := by
        show ti.index.val < n
        exact hlt _ (List.getElem_mem _)
      small := hR.small
      tmax := by rw [List.length_map]; have := hR.tmax; omega }
  have hseg : ∀ s (hs : s < n), segPairs (offs Ls n ++ [Ls.flatten.length]) (Ls.flatten.map Prod.fst)
      (Ls.flatten.map Prod.snd) s = renamedBlock inv off labs tos perm s := by
    intro s hs
    rw [segPairs_of_offs Ls hLlen hs, hgetLs]
  have hRawGood : RawGood R n (offs Ls n ++ [Ls.flatten.length]) (Ls.flatten.map Prod.fst)
      (Ls.flatten.map Prod.snd) :=
    { labs_lt := by
        intro l hl
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hl
        obtain ⟨x, hx1, -, rfl⟩ := hmem y hy
        exact hG.labs_lt x.1 hx1
      nodup := by
        rw [rawGood_nodup_iff hRawOf.mono hRawOf.last hRawOf.len_eq hRawOf.offlen]
        intro s hs
        rw [hseg s hs]
        unfold renamedBlock
        have hj := invAt_lt hinvlen hlen hpost hsurj hs
        have hnd := (rawGood_nodup_iff hR.mono hR.last hR.len_eq hR.offlen).mp hG.nodup _ hj
        refine hnd.map_on ?_
        intro x hx y hy hxy
        rw [Prod.mk.injEq] at hxy
        have hx2 := hR.tlt _ (mem_segPairs _ _ _ _ x hx).2
        have hy2 := hR.tlt _ (mem_segPairs _ _ _ _ y hy).2
        have hidx : x.2.index.val = y.2.index.val := by
          have h2 := congrArg (fun t : TagIndex Std.Usize StateTag => t.index.val) hxy.2
          simp only [prename, List.getD_eq_getElem perm.val default (show x.2.index.val < perm.val.length by omega),
            List.getD_eq_getElem perm.val default (show y.2.index.val < perm.val.length by omega)] at h2
          have := (List.Nodup.getElem_inj_iff hinj
            (i := x.2.index.val) (j := y.2.index.val) (hi := by simp; omega) (hj := by simp; omega)).mp
            (by simpa using h2)
          exact this
        exact qelem_ext (by rw [hxy.1]) hidx }
  refine ⟨R, offs Ls n ++ [Ls.flatten.length], Ls.flatten.map Prod.fst, Ls.flatten.map Prod.snd,
    ?_, hRawOf, hRawGood, rfl, ?_, ?_⟩
  · have hav := assert_valid_ok TLInst hRawOf hRawGood hlab htau
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec
    rw [hinvE]
    simp only [bind_ok]
    have hlb_tb : lb0 = tb0 := by
      have h2 : (merc_collections.compressed_vec.ByteCompressedVec.new LIdx) =
          (merc_collections.compressed_vec.ByteCompressedVec.new SIdx) := rfl
      have h3 : (ok lb0 : Result (merc_collections.compressed_vec.ByteCompressedVec
          (verified.merc_utilities.tagged_index.TagIndex Std.Usize verified.merc_lts.lts.LabelTag))) = ok tb0 :=
        hlb_new.symm.trans (h2.trans htb_new)
      exact Result.ok.injEq.mp h3
    rw [hst_new, hlb_new]
    rw [← hlb_tb] at hloop
    simp only [bind_ok, hloop, tag_value_id]
    show (do
      let i1 ← ByteCompressedVec.len LIdx TL
      let states2 ← ByteCompressedVec.push UIdx st i1
      let ti ← Slice.index_usize perm lts'.initial_state.index
      verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.from_raw_parts
        TLInst ti states2 TL TT lts'.labels) = ok R
    rw [hlen_TL, bind_ok, hpst, bind_ok, hti, bind_ok]
    unfold verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.from_raw_parts
    show (do verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_valid TLInst R
             ok R) = ok R
    rw [hav, bind_ok]
  · show ti.index.val = _
    rw [List.getD_eq_getElem perm.val default hinitlt]
  · intro b hb
    have hpb : (perm.val.getD b default).index.val < n := by
      rw [List.getD_eq_getElem perm.val default (by omega)]
      exact hlt _ (List.getElem_mem _)
    rw [hseg _ hpb]
    unfold renamedBlock
    rw [invAt_perm hinvlen hlen hpost hb]
    rfl

end Permute

section Raw

variable {Label : Type} (TLInst : TransitionLabel Label)

theorem raw_num_of_states {X : LabelledTransitionSystem Label} {m : Nat} {off labs tos}
    (h : RawOf X m off labs tos) :
    ∃ mU : Std.Usize,
      (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).num_of_states X = ok mU ∧ mU.val = m := by
  have hmax := h.off_le
  obtain ⟨ls, hls, hlsv⟩ := merc_collections.compressed_vec.ByteCompressedVec.len_spec UIdx X.states
    (by rw [h.st_length]; omega)
  rw [h.st_length] at hlsv
  obtain ⟨mU, hmU, hmUv⟩ : ∃ r, _ = r ∧ Std.WP.spec r _ :=
    ⟨_, rfl, Usize.sub_spec (x := ls) (y := 1#usize) (by simp; omega)⟩
  cases mU <;> simp only [Std.WP.spec_ok, Std.WP.spec_vis, Std.WP.spec_div] at hmUv
  rename_i mU
  refine ⟨mU, ?_, by have := hmUv.1; simp at this; omega⟩
  show (do
    let i ← merc_collections.compressed_vec.ByteCompressedVec.len UIdx X.states
    i - 1#usize) = ok mU
  rw [hls, bind_ok, hmU]

theorem lts_is_hidden (X : LabelledTransitionSystem Label) (l : TagIndex Std.Usize LabelTag) :
    (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst).is_hidden_label X l =
      ok (decide (l.index.val = 0)) := by
  show (do
    let i ← verified.merc_utilities.tagged_index.TagIndex.value core.marker.CopyUsize l
    ok (i = 0#usize)) = ok (decide (l.index.val = 0))
  simp only [tag_value_id, bind_ok]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact UScalar.eq_of_val_eq (by simpa using h)

theorem segment_eq_map_segPairs (off : List Nat) (labs : List (TagIndex Std.Usize LabelTag))
    (tos : List (TagIndex Std.Usize StateTag)) (b : Nat) :
    segment labs tos (off.getD b 0) (off.getD (b + 1) 0 - off.getD b 0) =
      (segPairs off labs tos b).map (fun x => ({ label := x.1, «to» := x.2 } : Transition)) := by
  unfold segment segPairs
  simp [List.zip, List.map_zipWith]

theorem raw_tr_iff {X : LabelledTransitionSystem Label} {m : Nat} {off labs tos}
    (h : RawOf X m off labs tos) (s : TagIndex Std.Usize StateTag) (hs : s.index.val < m)
    (μ : TagIndex Std.Usize LabelTag) (t : TagIndex Std.Usize StateTag) :
    MercVerified.Lts.tr (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) X s μ t ↔
      (μ, t) ∈ segPairs off labs tos s.index.val := by
  obtain ⟨ts, hts, htsv⟩ := raw_outgoing TLInst h s hs
  rw [tr_iff_mem hts, htsv, segment_eq_map_segPairs, List.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    simp only [Transition.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hx
  · intro hx
    exact ⟨_, hx, rfl⟩

theorem raw_Eout_le {X : LabelledTransitionSystem Label} {m : Nat} {off labs tos}
    (h : RawOf X m off labs tos) :
    Eout (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) X m ≤ labs.length := by
  have hmax := h.off_le
  have hoff := h.offlen
  have hlen : ∀ u : Fin m, outLen (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst) X u =
      off.getD (u.val + 1) 0 - off.getD u.val 0 := by
    intro u
    have hu : (stOf u).index.val < m := stOf_lt u (by omega)
    obtain ⟨ts, hts, htsv⟩ := raw_outgoing TLInst h (stOf u) hu
    unfold outLen
    rw [outVec_of_ok _ _ _ ts hts, htsv, segment_eq_map_segPairs, List.length_map,
      segPairs_length _ _ _ _ (h.off_le_labs (by omega)) h.len_eq, stOf_index u (by omega)]
  unfold Eout
  simp only [hlen]
  rw [Fin.sum_univ_eq_sum_range (fun i => off.getD (i + 1) 0 - off.getD i 0)]
  have key : ∀ N, N ≤ m → ∑ i ∈ Finset.range N, (off.getD (i + 1) 0 - off.getD i 0) =
      off.getD N 0 - off.getD 0 0 := by
    intro N
    induction N with
    | zero => intro _; simp
    | succ N ih =>
      intro hN
      rw [Finset.sum_range_succ, ih (by omega)]
      have h1 := h.off_mono (i := 0) (j := N) (by omega) (by omega)
      have h2 := h.off_mono (i := N) (j := N + 1) (by omega) (by omega)
      omega
  rw [key m le_rfl]
  have := h.off_le_labs (i := m) (by omega)
  omega

end Raw

section Graph

variable {L Label : Type} (LTSInst : LTS L Label) (sys : L)

theorem stOf_mk {n : Nat} (t : TagIndex Std.Usize StateTag) (ht : t.index.val < n) (hn : n ≤ Usize.max) :
    stOf (⟨t.index.val, ht⟩ : Fin n) = t := by
  apply merc_utilities.tagged_index.TagIndex.ext
  apply UScalar.eq_of_val_eq
  rw [stOf_index _ hn]

/-- The hidden edges of the SCC graph are the τ-steps of the `Fin n` view. -/
theorem edge_gOf_iff (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val) (hnlt : n0.val < Usize.max)
    (u v : Fin n0.val) :
    MercLib.Tarjan.Edge (gOf LTSInst sys hn0 hnlt) u v ↔
      (aLTS LTSInst sys n0.val).Tr u Cslib.HasTau.τ v := by
  have hn : n0.val ≤ Usize.max := by omega
  obtain ⟨ts, hts, htlt⟩ := hwf.2.1 n0 hns (stOf u) (stOf_lt u hn)
  show (true, v) ∈ (outVec LTSInst sys (stOf u)).val.map _ ↔ MercVerified.Lts.tr LTSInst sys (stOf u) _ (stOf v)
  rw [outVec_of_ok _ _ _ ts hts, tr_iff_mem hts, List.mem_map]
  constructor
  · rintro ⟨t, ht, he⟩
    simp only [Prod.mk.injEq, decide_eq_true_eq] at he
    obtain ⟨h0, hv⟩ := he
    have htl : t.to.index.val < n0.val := htlt t ht
    have hto : t.to = stOf v := by
      rw [← hv, show toFin hn0 t.to = ⟨t.to.index.val, htl⟩ from Fin.ext (toFin_val hn0 _ htl),
        stOf_mk _ htl hn]
    have hlab : t.label = Cslib.HasTau.τ := (label_eq_tau_iff _).2 h0
    rw [← hto, ← hlab]; exact ht
  · intro hmem
    refine ⟨_, hmem, ?_⟩
    simp only [Prod.mk.injEq, decide_eq_true_eq]
    refine ⟨(label_eq_tau_iff _).1 rfl, ?_⟩
    apply Fin.ext
    rw [toFin_val hn0 _ (stOf_lt v hn), stOf_index v hn]

/-- A successor in the topological-sort graph is a τ-step to a different state. -/
theorem mem_tsucc {n : Nat} (hn0 : 0 < n) (hn : n ≤ Usize.max)
    (htlt : ∀ u : Fin n, ∀ t ∈ (outVec LTSInst sys (stOf u)).val, t.to.index.val < n)
    (a b : Fin n) (h : b ∈ tsucc LTSInst sys hn0 a) :
    a ≠ b ∧ ({ label := Cslib.HasTau.τ, «to» := stOf b } : Transition) ∈ (outVec LTSInst sys (stOf a)).val := by
  unfold tsucc hsucc at h
  rw [List.mem_filterMap] at h
  obtain ⟨t, ht, he⟩ := h
  split_ifs at he with hc
  cases he
  have htl := htlt a t ht
  have hto : t.to = stOf (toFin hn0 t.to) := by
    rw [show toFin hn0 t.to = ⟨t.to.index.val, htl⟩ from Fin.ext (toFin_val hn0 _ htl), stOf_mk _ htl hn]
  refine ⟨?_, ?_⟩
  · intro hab
    apply hc.1
    rw [hab, toFin_val hn0 _ htl]
  · have hlab : t.label = Cslib.HasTau.τ := (label_eq_tau_iff _).2 hc.2
    rw [← hto, ← hlab]; exact ht

theorem view_bk (ip : IndexedPartition) {n : Nat} (i : Nat) (hi : i < n)
    (hl : ip.partition.val.length = n) :
    view n (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val ⟨i, hi⟩ =
      (bk ip i).index.val := by
  unfold view bk
  rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
  rfl

theorem tr_target_lt (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) {s : TagIndex Std.Usize StateTag}
    {μ : TagIndex Std.Usize LabelTag} {t : TagIndex Std.Usize StateTag}
    (h : MercVerified.Lts.tr LTSInst sys s μ t) (hs : s.index.val < n0.val) : t.index.val < n0.val := by
  obtain ⟨ts, hts, htlt⟩ := hwf.2.1 n0 hns s hs
  exact htlt _ ((tr_iff_mem hts μ t).1 h)

theorem tsucc_of_tr {n : Nat} (hn0 : 0 < n) (a : Fin n) (t : TagIndex Std.Usize StateTag)
    (htr : MercVerified.Lts.tr LTSInst sys (stOf a) Cslib.HasTau.τ t) (htl : t.index.val < n)
    (hne : t.index.val ≠ a.val) :
    (⟨t.index.val, htl⟩ : Fin n) ∈ tsucc LTSInst sys hn0 a := by
  obtain ⟨ts, hts, hmem⟩ := htr
  unfold tsucc hsucc
  rw [outVec_of_ok _ _ _ ts hts, List.mem_filterMap]
  refine ⟨_, hmem, ?_⟩
  split_ifs with hc
  · congr 1
    exact Fin.ext (toFin_val hn0 _ htl)
  · exact absurd ⟨hne, (label_eq_tau_iff _).1 rfl⟩ hc

/-- States in the same τ-SCC block reach each other by τ-steps. -/
theorem sameBlock_tauSTr (hwf : MercVerified.Lts.WellFormed LTSInst sys) (n0 : Std.Usize)
    (hns : LTSInst.num_of_states sys = ok n0) (hn0 : 0 < n0.val) (hnlt : n0.val < Usize.max)
    (ip : IndexedPartition) (k : Nat) (hlen : ip.partition.val.length = n0.val)
    (hscc : MercLib.Tarjan.IsSccPartition (gOf LTSInst sys hn0 hnlt)
      (view n0.val (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val) k)
    (s t : TagIndex Std.Usize StateTag) (hs : s.index.val < n0.val) (ht : t.index.val < n0.val)
    (h : (bk ip s.index.val).index.val = (bk ip t.index.val).index.val) :
    (MercVerified.Lts.toLTS LTSInst sys).τSTr s t := by
  have hn : n0.val ≤ Usize.max := by omega
  have hP := MercLib.Sigref.isTauSccPartition_of_scc (aLTS LTSInst sys n0.val)
    (gOf LTSInst sys hn0 hnlt) (edge_gOf_iff LTSInst sys hwf n0 hns hn0 hnlt) hscc
  have hab := ((hP.2.2 ⟨s.index.val, hs⟩ ⟨t.index.val, ht⟩).1
    (by rw [view_bk ip _ hs hlen, view_bk ip _ ht hlen]; exact h)).1
  have hlift : ∀ a b : Fin n0.val, (aLTS LTSInst sys n0.val).τSTr a b →
      (MercVerified.Lts.toLTS LTSInst sys).τSTr (stOf a) (stOf b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail hbc
  have hl := hlift _ _ hab
  rw [stOf_mk s hs hn, stOf_mk t ht hn] at hl
  exact hl

end Graph

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
      MercLib.Sigref.IsCrossBB (MercVerified.Lts.toLTS LTSInst sys)
        (MercVerified.Lts.toLTS
          (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS LTSInst.TransitionLabelInst) R)
        (fun s s' => s.index.val < n0.val ∧ s'.index.val = f s.index.val) ∧
      (let I := LabelledTransitionSystem.Insts.Merc_ltsLtsLTS LTSInst.TransitionLabelInst
       MercVerified.Lts.WellFormed I R ∧ StateCountFits I R ∧ BranchingLtsAssumptions I R) := by
  have hass' := hass
  obtain ⟨hhid, -, -, hfit, -⟩ := hass'
  have hn0 : 0 < n0.val := by
    obtain ⟨n1, hn1, hn1pos⟩ := hwf.1
    have e : n0 = n1 := by have h := hns.symm.trans hn1; simpa using h
    rw [e]; exact hn1pos
  have hnlt : n0.val < Usize.max := by have := hfit n0 hns; nlinarith
  have hnmax : n0.val ≤ Usize.max := by omega
  obtain ⟨ip, k, hip, hlen, hnb, hscc⟩ := tau_scc_spec LTSInst sys hwf n0 hns hn0 hhid hnlt
  obtain ⟨Q, off, labs, tos, hQ, hRQ, hGQ, hlabQ, hinitQ, hsegQ⟩ :=
    quotient_lts_naive_spec LTSInst sys hwf hass n0 hns hn0 hnlt ip k hlen hnb hscc
  set I := LabelledTransitionSystem.Insts.Merc_ltsLtsLTS LTSInst.TransitionLabelInst with hIdef
  obtain ⟨kU, hkU, hkUv⟩ := raw_num_of_states LTSInst.TransitionLabelInst hRQ
  have hk0 : 0 < k := hRQ.n_pos
  have hkpos : 0 < kU.val := by omega
  have hkmax : k + 1 ≤ Usize.max := hRQ.off_le
  have hknlt : kU.val < Usize.max := by omega
  have hwfQ : MercVerified.Lts.WellFormed I Q := lts_wellFormed _ Q (raw_valid hRQ)
  have hEout : Eout I Q kU.val + 1 ≤ Usize.max := by
    have h1 : Eout I Q k ≤ labs.length := raw_Eout_le LTSInst.TransitionLabelInst hRQ
    rw [hkUv]; have := hRQ.tmax; omega
  -- block of a state, as a number
  have hblk_lt : ∀ i, i < n0.val → (bk ip i).index.val < k := by
    intro i hi
    rw [← view_bk ip i hi hlen]
    exact hscc.1 _
  have hknmax : kU.val ≤ Usize.max := by omega
  have htltQ : ∀ u : Fin kU.val, ∀ t ∈ (outVec I Q (stOf u)).val, t.to.index.val < kU.val := by
    intro u t ht
    obtain ⟨ts, hts, htlt⟩ := hwfQ.2.1 kU hkU (stOf u) (stOf_lt u hknmax)
    rw [outVec_of_ok _ _ _ ts hts] at ht
    exact htlt t ht
  have hA : MercLib.Sigref.Topo.Acyclic (tsucc I Q hkpos) := by
    intro v hcyc
    have hP := MercLib.Sigref.isTauSccPartition_of_scc (aLTS LTSInst sys n0.val)
      (gOf LTSInst sys hn0 hnlt) (edge_gOf_iff LTSInst sys hwf n0 hns hn0 hnlt) hscc
    have hacyc := MercLib.Sigref.quotientTauAcyclic (aLTS LTSInst sys n0.val)
      (view n0.val (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val) k hP
    have hstep : ∀ a b : Fin kU.val, b ∈ tsucc I Q hkpos a →
        (MercLib.Sigref.quotientTau (aLTS LTSInst sys n0.val)
          (view n0.val (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val)).Tr
          a.val Cslib.HasTau.τ b.val := by
      intro a b hab
      obtain ⟨hne, hmem⟩ := mem_tsucc I Q hkpos hknmax htltQ a b hab
      have hex : ∃ ts : alloc.vec.Vec Transition, I.outgoing_transitions Q (stOf a) = ok ts := by
        obtain ⟨ts, hts, -⟩ := hwfQ.2.1 kU hkU (stOf a) (stOf_lt a hknmax)
        exact ⟨ts, hts⟩
      have htr : MercVerified.Lts.tr I Q (stOf a) Cslib.HasTau.τ (stOf b) :=
        (mem_outVec_iff_tr I Q (stOf a) hex _ _).1 hmem
      have ha : (stOf a).index.val < k := by rw [stOf_index a hknmax]; omega
      have hseg := (raw_tr_iff LTSInst.TransitionLabelInst hRQ (stOf a) ha _ _).1 htr
      rw [stOf_index a hknmax] at hseg
      obtain ⟨s0, t0, hs0, ht0, hs0lt, htr0, -⟩ :=
        (hsegQ a.val (by omega) Cslib.HasTau.τ (stOf b).index).1 hseg
      have ht0lt := tr_target_lt LTSInst sys hwf n0 hns htr0 hs0lt
      refine ⟨⟨s0.index.val, hs0lt⟩, ⟨t0.index.val, ht0lt⟩, ?_, ?_, ?_, ?_⟩
      · rw [view_bk ip _ hs0lt hlen, hs0]
      · rw [view_bk ip _ ht0lt hlen, ht0, stOf_index b hknmax]
      · show MercVerified.Lts.tr LTSInst sys (stOf _) _ (stOf _)
        rw [stOf_mk s0 hs0lt hnmax, stOf_mk t0 ht0lt hnmax]; exact htr0
      · rintro ⟨-, hab'⟩; exact hne (Fin.ext hab')
    have hlift : ∀ a b, Relation.TransGen (fun a b => b ∈ tsucc I Q hkpos a) a b →
        Relation.TransGen (fun b c => (MercLib.Sigref.quotientTau (aLTS LTSInst sys n0.val)
          (view n0.val (fun t : TagIndex Std.Usize BlockTag => t.index.val) 0 ip.partition.val)).Tr
          b Cslib.HasTau.τ c) a.val b.val := by
      intro a b h
      induction h with
      | single h => exact .single (hstep _ _ h)
      | tail _ h ih => exact ih.tail (hstep _ _ h)
    exact hacyc v.val (hlift v v hcyc)
  obtain ⟨perm, hperm, hplen, hplt, hpinj, hpord⟩ :=
    sort_topological_hidden_spec I Q hwfQ kU hkU hkpos (lts_is_hidden _ Q) hknlt hEout hA
  rw [hkUv] at hplen
  have hdv : (alloc.vec.Vec.deref perm).val = perm.val := by simp [alloc.vec.Vec.deref]
  have hpl : (alloc.vec.Vec.deref perm).val.length = k := by rw [hdv]; exact hplen
  have hpltd : ∀ p ∈ (alloc.vec.Vec.deref perm).val, p.index.val < k := by
    rw [hdv]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have := hplt i hi; omega
  have hpinjd : ((alloc.vec.Vec.deref perm).val.map (fun p => p.index.val)).Nodup := by
    rw [hdv, List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    simp only [List.getElem_map] at heq
    simp only [List.length_map] at hi hj
    exact absurd (hpinj i j hi hj heq) (Nat.ne_of_lt hij)
  obtain ⟨sl, hsl, hsl1, ⟨t0, ht0, ht0tau⟩, -⟩ := hass.2.1
  obtain ⟨sl', hsl', hQl⟩ := hlabQ
  have hsl_eq : sl' = sl := by have h := hsl'.symm.trans hsl; simpa using h
  subst hsl_eq
  have hlabQ1 : 1 ≤ Q.labels.val.length := by rw [hQl]; exact hsl1
  have htauQ : ∃ t, Q.labels.val[0]? = some t ∧ LTSInst.TransitionLabelInst.is_tau_label t = ok true :=
    ⟨t0, by rw [hQl]; exact ht0, ht0tau⟩
  obtain ⟨R, off', labs', tos', hRrun, hRR, hGR, hRlab, hRinit, hRseg⟩ :=
    new_from_permutation_vec_spec LTSInst.TransitionLabelInst hRQ hGQ hlabQ1 htauQ
      (alloc.vec.Vec.deref perm) hpl hpltd hpinjd
  have hsp : state.index.val < ip.partition.val.length := by rw [hlen]; exact hstate
  have hti := ip_block_number ip state hsp
  set ti := ip.partition.val[state.index.val]'hsp with htidef
  have hbk_state : bk ip state.index.val = ti := by
    simp only [bk, List.getD_eq_getElem _ _ hsp, ti]
  have htilt : ti.index.val < perm.val.length := by
    rw [hplen, ← hbk_state]; exact hblk_lt _ hstate
  let f : ℕ → ℕ := fun i => (perm.val.getD (bk ip i).index.val default).index.val
  refine ⟨R, perm.val[ti.index.val]'htilt, f, ?_, ?_, ?_, ?_⟩
  · unfold verified.merc_reduction.signatures.tau_cycle_elimination_and_reorder
    rw [hip, bind_ok, hQ, bind_ok, hti, bind_ok]
    have hderef : verified.merc_utilities.tagged_index.TagIndex.Insts.CoreOpsDerefDeref.deref ti =
        ok ti.index := rfl
    simp only [hderef, vec_tagged_index_eq, bind_ok, merc_utilities.tagged_index.TagIndex.new_eq]
    have hperm' : verified.merc_reduction.sort_topological.sort_topological_hidden
        (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS LTSInst.TransitionLabelInst) Q = ok (some perm) :=
      hperm
    have hunw : core.option.Option.unwrap (some perm) = ok perm := rfl
    have hsl : ti.index.val < perm.slice.val.length := htilt
    rw [hperm', bind_ok, hunw, bind_ok, slice_index_ok' _ _ hsl, bind_ok, hRrun, bind_ok]
    rfl
  · show _ = (perm.val.getD (bk ip state.index.val).index.val default).index.val
    rw [hbk_state, List.getD_eq_getElem _ _ htilt]
  · have hpermlt : ∀ b, b < k → (perm.val.getD b default).index.val < k := by
      intro b hb
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hpltd _ (by rw [hdv]; exact List.getElem_mem _)
    simp only [hdv] at hRseg
    intro s t hr μ
    obtain ⟨hs, ht⟩ := hr
    have hbs := hblk_lt _ hs
    have htk : t.index.val < k := by rw [ht]; exact hpermlt _ hbs
    constructor
    · intro s' hstep
      have hs' := tr_target_lt LTSInst sys hwf n0 hns hstep hs
      by_cases hc : μ.index.val = 0 ∧
          (bk ip s.index.val).index.val = (bk ip s'.index.val).index.val
      · left
        refine ⟨(label_eq_tau_iff μ).2 hc.1, hs', ?_⟩
        rw [ht]
        show (perm.val.getD (bk ip s.index.val).index.val default).index.val =
          (perm.val.getD (bk ip s'.index.val).index.val default).index.val
        rw [hc.2]
      · right
        have hmemQ : (μ, ({ index := (bk ip s'.index.val).index, marker := () } :
            TagIndex Std.Usize StateTag)) ∈ segPairs off labs tos (bk ip s.index.val).index.val :=
          (hsegQ _ hbs μ (bk ip s'.index.val).index).2 ⟨s, s', rfl, rfl, hs, hstep, hc⟩
        have hmemR : (μ, ({ index := (perm.val.getD (bk ip s'.index.val).index.val default).index, marker := () } : TagIndex Std.Usize StateTag)) ∈
            segPairs off' labs' tos' t.index.val := by
          rw [ht]
          show _ ∈ segPairs off' labs' tos'
            (perm.val.getD (bk ip s.index.val).index.val default).index.val
          rw [hRseg _ hbs]
          exact List.mem_map.2 ⟨_, hmemQ, rfl⟩
        exact ⟨t, _, Cslib.LTS.STr.refl, (raw_tr_iff _ hRR t htk _ _).2 hmemR, ⟨hs, ht⟩, hs', rfl⟩
    · intro t' hstep
      have hmemR := (raw_tr_iff _ hRR t htk _ _).1 hstep
      rw [ht] at hmemR
      change (μ, t') ∈ segPairs off' labs' tos'
        (perm.val.getD (bk ip s.index.val).index.val default).index.val at hmemR
      rw [hRseg _ hbs] at hmemR
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hmemR
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨hx1, hx2⟩ := hxe
      have hx' : (μ, ({ index := x.2.index, marker := () } : TagIndex Std.Usize StateTag)) ∈
          segPairs off labs tos (bk ip s.index.val).index.val := by
        rw [← hx1]; exact hx
      obtain ⟨s0, t0, hs0, ht0, hs0lt, htr0, -⟩ := (hsegQ _ hbs μ x.2.index).1 hx'
      have ht0lt := tr_target_lt LTSInst sys hwf n0 hns htr0 hs0lt
      right
      refine ⟨s0, t0, (Cslib.LTS.sTr_τSTr_iff _).2
        (sameBlock_tauSTr LTSInst sys hwf n0 hns hn0 hnlt ip k hlen hscc s s0 hs hs0lt hs0.symm),
        htr0, ⟨hs0lt, ?_⟩, ⟨ht0lt, ?_⟩⟩
      · rw [ht]
        show (perm.val.getD (bk ip s.index.val).index.val default).index.val =
          (perm.val.getD (bk ip s0.index.val).index.val default).index.val
        rw [hs0]
      · rw [← hx2]
        show (perm.val.getD x.2.index.val default).index.val =
          (perm.val.getD (bk ip t0.index.val).index.val default).index.val
        rw [ht0]
  · obtain ⟨mU, hmU, hmUv⟩ := raw_num_of_states LTSInst.TransitionLabelInst hRR
    have hmeq : ∀ m, (LabelledTransitionSystem.Insts.Merc_ltsLtsLTS LTSInst.TransitionLabelInst).num_of_states R = ok m → m.val = k := by
      intro m hm
      have e : m = mU := by have h := hm.symm.trans hmU; simpa using h
      rw [e, hmUv]
    simp only [hdv] at hRseg
    refine ⟨lts_wellFormed _ R (raw_valid hRR), ?_, ?_⟩
    · intro m hm
      rw [hmeq m hm]; exact hRR.small
    · refine ⟨⟨alloc.vec.Vec.len R.labels, rfl, lts_is_hidden _ R, ?_⟩, ?_⟩
      · intro m hm s μ s' hs htr
        rw [hmeq m hm] at hs
        have hmem := (raw_tr_iff _ hRR s hs μ s').1 htr
        rw [vec_len_val']
        exact hGR.labs_lt μ (mem_segPairs _ _ _ _ _ hmem).1
      · intro m hm s μ t hs htr hμ
        rw [hmeq m hm] at hs
        obtain ⟨b, hb, hbs⟩ := perm_surj hpl hpltd hpinjd s.index.val hs
        rw [hdv] at hbs
        have hmem := (raw_tr_iff _ hRR s hs μ t).1 htr
        rw [← hbs, hRseg b hb] at hmem
        obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hmem
        simp only [Prod.mk.injEq] at hxe
        obtain ⟨hx1, hx2⟩ := hxe
        have hx2lt : x.2.index.val < k := hRQ.tlt _ (mem_segPairs _ _ _ _ _ hx).2
        have hx' : (μ, ({ index := x.2.index, marker := () } : TagIndex Std.Usize StateTag)) ∈
            segPairs off labs tos b := by
          rw [← hx1]; exact hx
        obtain ⟨-, -, -, -, -, -, hnot⟩ := (hsegQ b hb μ x.2.index).1 hx'
        have hne : x.2.index.val ≠ b := fun h => hnot ⟨hμ, h.symm⟩
        have hμτ : μ = Cslib.HasTau.τ := (label_eq_tau_iff μ).2 hμ
        have hbk : b < kU.val := by omega
        have hsb : (stOf (⟨b, hbk⟩ : Fin kU.val)).index.val = b := stOf_index _ hknmax
        have htrQ : MercVerified.Lts.tr I Q (stOf (⟨b, hbk⟩ : Fin kU.val)) Cslib.HasTau.τ x.2 := by
          apply (raw_tr_iff _ hRQ _ (by rw [hsb]; exact hb) _ _).2
          rw [hsb, ← hμτ, ← hx1]
          exact hx
        have hsucc := tsucc_of_tr I Q hkpos ⟨b, hbk⟩ x.2 htrQ (by omega) hne
        obtain ⟨ha, hb', hlt⟩ := hpord _ _ hsucc
        rw [← hx2, ← hbs]
        show (perm.val.getD x.2.index.val default).index.val <
          (perm.val.getD b default).index.val
        rw [List.getD_eq_getElem _ _ hb', List.getD_eq_getElem _ _ ha]
        exact hlt

/-- **`branching_bisim_sigref` for `divergence_preserving = false`.** -/
theorem branching_bisim_sigref_correct {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys) (hass : PreprocessAssumptions LTSInst sys)
    (state : TagIndex Std.Usize StateTag)
    (hstate : ∀ n, LTSInst.num_of_states sys = ok n → state.index.val < n.val)
    (timing : merc_utilities.timing.Timing) :
    BranchingBisimSigrefCorrectSpec LTSInst sys hwf hass state hstate timing := by
  obtain ⟨n0, hns, -⟩ := hwf.1
  obtain ⟨R, state', f, hrun, hst, hcross, hwfR, hfitR, hasmR⟩ :=
    tau_cycle_spec LTSInst sys hwf hass state n0 hns (hstate n0 hns)
  obtain ⟨partition, blockOf, himpl, hpwf, hcov, hiff⟩ :=
    branching_bisim_sigref_impl_correct _ R hwfR hfitR hasmR timing
  have hrel : (fun (s s' : TagIndex Std.Usize StateTag) =>
      (∃ n, LTSInst.num_of_states sys = ok n ∧ s.index.val < n.val) ∧ s'.index.val = f s.index.val) =
      (fun s s' => s.index.val < n0.val ∧ s'.index.val = f s.index.val) := by
    funext s s'
    apply propext
    constructor
    · rintro ⟨⟨n, hn, hs⟩, h⟩
      have e : n = n0 := by have h := hn.symm.trans hns; simpa using h
      exact ⟨e ▸ hs, h⟩
    · rintro ⟨hs, h⟩
      exact ⟨⟨n0, hns, hs⟩, h⟩
  refine ⟨R, state', partition, f, blockOf, ?_, fun _ _ _ => hst, ?_,
    hwfR, hfitR, hasmR, hpwf, hcov, hiff⟩
  · unfold verified.merc_reduction.signature_refinement.branching_bisim_sigref
    simp [hrun, himpl]
  · rw [hrel]; exact hcross

end Top

end MercVerified.Refinement.Proofs
