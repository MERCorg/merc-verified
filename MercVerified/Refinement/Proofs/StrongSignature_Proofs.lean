import MercVerified.Basic
import MercVerified.Refinement.Proofs.Partition_Proofs
import MercVerified.Refinement.Proofs.SigKey_Proofs
import Aeneas.Std.WP

/-!
# Proofs for the `strong_bisim_signature` correctness contract

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).

`strong_bisim_signature_spec_general` proves the `StrongBisimSignatureSpec`
contract (defined below - an internal lemma of the refinement proof, not a
pinned contract), generically for any `LTS` trait implementor, using the
private helper lemmas below it. `strong_bisim_signature_spec` specializes it to
`LabelledTransitionSystem`.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag TransitionLabel Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.signatures (strong_bisim_signature strong_bisim_signature_loop)
open verified.merc_reduction.partition (Partition)
open verified.merc_lts.labelled_transition_system (LabelledTransitionSystem)
open MercVerified.Lts (toLTS toLTS_Tr tr)

open MercVerified.Lts.Proofs

namespace MercVerified.Refinement

/-- Contract: the translated `strong_bisim_signature` computes `StrongSignature`. -/
def StrongBisimSignatureSpec
    {L Label P : Type}
    (LTSInst : LTS L Label)
    (PInst : Partition P)
    (sys : L)
    (partition : P)
    (s : TagIndex Std.Usize StateTag)
    (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (_hblock : ∀ t, PInst.block_number partition t = ok (blockNumber t))
    (ts : alloc.vec.Vec Transition)
    (_houtgoing : LTSInst.outgoing_transitions sys s = ok ts) : Prop :=
  ∃ result,
    verified.merc_reduction.signatures.strong_bisim_signature
        LTSInst PInst s sys partition builder0 = ok result
    ∧ ∀ μ β, (μ, β) ∈ result.val ↔
        (μ, β) ∈ StrongSignature (toLTS LTSInst sys) s blockNumber

end MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 800000

/-- The `(label, block)` pair that `strong_bisim_signature`'s loop pushes for a
    transition, assuming the `block_number` lookup succeeds. -/
private abbrev sigEntry (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (t : Transition) : (TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag) :=
  (t.label, blockNumber t.to)

@[simp]
private theorem sigEntry_mk {blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag}
    (μ : TagIndex Std.Usize LabelTag) (s' : TagIndex Std.Usize StateTag) :
    sigEntry blockNumber { label := μ, «to» := s' } = (μ, blockNumber s') := by
  simp [sigEntry]

/-- The loop state: the remaining transitions to consume and the accumulator.
    The first component is written as a `Vec` (rather than the definitionally equal
    `alloc.vec.into_iter.IntoIter`) so that `x.1.val` is well-typed at `instances`
    transparency. -/
private abbrev State := alloc.vec.Vec Transition ×
  alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag))

set_option allowUnsafeReducibility true
attribute [local reducible] alloc.vec.into_iter.IntoIter
attribute [local reducible] Aeneas.Std.WP.Post

/-- The `strong_bisim_signature` loop computes, for each transition it consumes,
    the `(label, block)` pair given by the `blockNumber` lookup, appending it to
    the accumulator. -/
private theorem strong_bisim_signature_loop_spec
    {P : Type} (PInst : Partition P) (partition : P)
    (iter : alloc.vec.into_iter.IntoIter Transition)
    (builder : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (l : List Transition)
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (hblock : ∀ t ∈ l, PInst.block_number partition t.to = ok (blockNumber t.to))
    (hlen : (builder.val ++ List.map (sigEntry blockNumber) l).length ≤ Usize.max)
    (hiter : iter.val = l) :
    ∃ builder', strong_bisim_signature_loop PInst iter partition builder = ok builder'
      ∧ builder'.val = builder.val ++ List.map (sigEntry blockNumber) l := by
  rw [strong_bisim_signature_loop]
  apply (spec_imp_exists _)
  have hspec :
      loop (fun x : State =>
            strong_bisim_signature_loop.body PInst partition x.1 x.2)
        (iter, builder)
      ⦃ builder' => builder'.val = builder.val ++ List.map (sigEntry blockNumber) l ⦄ := by
    apply loop.spec_decr_nat
      (measure := fun x : State => x.1.val.length)
      (inv := fun x : State =>
        ∃ pref rest : List Transition, l = pref ++ rest ∧ x.1.val = rest
          ∧ x.2.val = builder.val ++ List.map (sigEntry blockNumber) pref)
      (post := fun b : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)) =>
        b.val = builder.val ++ List.map (sigEntry blockNumber) l)
      (body := fun x : State =>
        strong_bisim_signature_loop.body PInst partition x.1 x.2)
      (x := (iter, builder))
    · intro x hx
      rcases hx with ⟨pref, rest, hl, hiter1, hbuilder1⟩
      cases rest with
      | nil =>
        unfold strong_bisim_signature_loop.body
        have hh : x.1.val = [] := by simpa using hiter1
        have hnext : alloc.vec.into_iter.IteratorIntoIter.next x.1
            ⦃ o iter1' => o = none ∧ iter1'.val = [] ⦄ := by
          unfold alloc.vec.into_iter.IteratorIntoIter.next
          split <;> simp_all
        apply spec_bind hnext
        intro y hy
        rcases y with ⟨o, iter1⟩
        simp at hy
        rcases hy with ⟨ho, hitl⟩
        subst o
        simp [spec_ok]
        rw [hbuilder1, hl]
        simp
      | cons hd tl =>
        unfold strong_bisim_signature_loop.body
        have hh2 : x.1.val = hd :: tl := by simpa using hiter1
        have hnext : alloc.vec.into_iter.IteratorIntoIter.next x.1
            ⦃ o iter1' => o = some hd ∧ iter1'.val = tl ⦄ := by
          unfold alloc.vec.into_iter.IteratorIntoIter.next
          split <;> simp_all
        have hti : PInst.block_number partition hd.to ⦃ ti => ti = blockNumber hd.to ⦄ := by
          rw [hblock hd (by rw [hl]; simp)]
          simp
        have hlen' : (builder.val ++ List.map (sigEntry blockNumber) (pref ++ [hd])).length ≤ Usize.max := by
          have hld : (pref ++ [hd]) ++ tl = l := by
            rw [List.append_assoc]
            simp
            rw [hl]
          have hmiddle : List.map (sigEntry blockNumber) (pref ++ [hd]) ++
                List.map (sigEntry blockNumber) tl =
              List.map (sigEntry blockNumber) l := by
            rw [← List.map_append, hld]
          have hmid2 : builder.val ++ (List.map (sigEntry blockNumber) (pref ++ [hd]) ++
                List.map (sigEntry blockNumber) tl) =
              builder.val ++ List.map (sigEntry blockNumber) l := by
            rw [hmiddle]
          calc
            (builder.val ++ List.map (sigEntry blockNumber) (pref ++ [hd])).length
                ≤ (builder.val ++ (List.map (sigEntry blockNumber) (pref ++ [hd]) ++
                    List.map (sigEntry blockNumber) tl)).length := by
                  simp [List.length_append]
            _ = (builder.val ++ List.map (sigEntry blockNumber) l).length := by rw [hmid2]
            _ ≤ Usize.max := hlen
        have hlen'' : x.2.val.length < Usize.max := by
          have hx2 : x.2.val.length + 1 ≤
              (builder.val ++ List.map (sigEntry blockNumber) (pref ++ [hd])).length := by
            rw [hbuilder1]
            simp [List.length_append, List.map_append]
          omega
        have hpush : x.2.push (sigEntry blockNumber hd)
            ⦃ builder1 => builder1.val = x.2.val ++ [sigEntry blockNumber hd] ⦄ :=
          alloc.vec.Vec.push_spec x.2 (sigEntry blockNumber hd) hlen''
        apply spec_bind hnext
        intro y hy
        rcases y with ⟨o, iter1'⟩
        simp at hy
        rcases hy with ⟨ho, hitl⟩
        subst o
        apply spec_bind hti
        intro ti hti2
        subst ti
        apply spec_bind hpush
        intro builder1 hb
        simp [spec_ok]
        constructor
        · refine ⟨pref ++ [hd], ?_, ?_⟩
          · simpa [List.append_assoc, hitl] using hl
          · rw [hb, hbuilder1]
            simp [List.append_assoc, List.map_append]
        · simp [hh2, hitl]
    · exact ⟨[], l, by simp, by simpa using hiter, by simp⟩
  simpa using hspec

/-- The accumulator element type of `strong_bisim_signature`: a label index
    paired with a block index. -/
private abbrev Entry := (TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)

/-- Bridge: a `(label, block)` pair belongs to the translated accumulator
    `map (sigEntry blockNumber) ts.val` exactly when it belongs to the
    mathematical `StrongSignature`, given that `ts` is the transition list of
    `s` (i.e. `outgoing_transitions sys s` succeeds with `ts`). -/
private theorem sigEntry_mem_iff
    {L Label : Type}
    (LTSInst : LTS L Label)
    (sys : L)
    (s : TagIndex Std.Usize StateTag)
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (ts : alloc.vec.Vec Transition)
    (houtgoing : LTSInst.outgoing_transitions sys s = ok ts) :
    ∀ μ β, (μ, β) ∈ List.map (sigEntry blockNumber) ts.val ↔
      (μ, β) ∈ StrongSignature (toLTS LTSInst sys) s blockNumber := by
  intro μ β
  have htr : ∀ s', tr LTSInst sys s μ s' ↔ { label := μ, «to» := s' } ∈ ts.val := by
    intro s'
    constructor
    · intro h
      rcases h with ⟨ts', hts', hmem⟩
      have htseq : ts' = ts := by simpa [Result.ok.injEq] using hts'.symm.trans houtgoing
      subst ts'
      exact hmem
    · intro hmem
      exact ⟨ts, houtgoing, hmem⟩
  calc
    (μ, β) ∈ List.map (sigEntry blockNumber) ts.val
        ↔ ∃ t : Transition, t ∈ ts.val ∧ t.label = μ ∧ blockNumber t.to = β := by
          simp [List.mem_map, sigEntry]
    _ ↔ ∃ s', { label := μ, «to» := s' } ∈ ts.val ∧ blockNumber s' = β := by
          constructor
          · rintro ⟨t, htmem, htl, htb⟩
            refine ⟨t.to, ?_, htb⟩
            have ht' : { label := μ, «to» := t.to } = t := by
              rw [← htl]
            simpa [ht'] using htmem
          · rintro ⟨s', hmem, hsb⟩
            refine ⟨{ label := μ, «to» := s' }, hmem, ?_, ?_⟩
            · rfl
            · simpa using hsb
    _ ↔ ∃ s', tr LTSInst sys s μ s' ∧ blockNumber s' = β := by
          apply exists_congr
          intro s'
          constructor
          · rintro ⟨hmem, hsb⟩
            exact ⟨(htr s').mpr hmem, hsb⟩
          · rintro ⟨htm, hsb⟩
            exact ⟨(htr s').mp htm, hsb⟩
    _ ↔ ∃ s', (toLTS LTSInst sys).Tr s μ s' ∧ blockNumber s' = β := by
          apply exists_congr
          intro s'
          constructor
          · rintro ⟨htm, hsb⟩
            exact ⟨(toLTS_Tr LTSInst sys s μ s').mp htm, hsb⟩
          · rintro ⟨htm, hsb⟩
            exact ⟨(toLTS_Tr LTSInst sys s μ s').mpr htm, hsb⟩
    _ ↔ (μ, β) ∈ StrongSignature (toLTS LTSInst sys) s blockNumber := by
          simp [StrongSignature]

/-- Contract pin theorem: for any `LTS` trait implementor `L`/`LTSInst`,
    `strong_bisim_signature` computes exactly the mathematical
    `StrongSignature`, given that `outgoing_transitions s` and every
    `block_number` lookup it needs succeed. -/
theorem strong_bisim_signature_spec_general
    {L Label P : Type}
    (LTSInst : LTS L Label)
    (PInst : Partition P)
    (sys : L)
    (partition : P)
    (s : TagIndex Std.Usize StateTag)
    (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (hblock : ∀ t, PInst.block_number partition t = ok (blockNumber t))
    (ts : alloc.vec.Vec Transition)
    (houtgoing : LTSInst.outgoing_transitions sys s = ok ts) :
    StrongBisimSignatureSpec LTSInst PInst sys partition s builder0 blockNumber hblock ts houtgoing := by
  unfold StrongBisimSignatureSpec
  rw [strong_bisim_signature]
  rcases (alloc.vec.Vec.clear_spec (T := Entry) Global builder0) with ⟨builder1, hb1, hb1val⟩
  let iter : alloc.vec.into_iter.IntoIter Transition := ts
  have hlen : (builder1.val ++ List.map (sigEntry blockNumber) ts.val).length ≤ Usize.max := by
    simp [hb1val]
  rcases (strong_bisim_signature_loop_spec PInst partition iter builder1 ts.val blockNumber
      (fun t _ => hblock t.to) hlen (by rfl)) with ⟨builder2, hb2, hb2val⟩
  rcases (core.slice.Slice.sort_unstable_spec (T := Entry)
      (verified.Pair.Insts.CoreCmpOrd
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd BlockTag core.cmp.OrdUsize))
      builder2.slice) with ⟨s1, hs1, hs1perm, -⟩
  let builder3 : alloc.vec.Vec Entry := { slice := s1 }
  rcases (alloc.vec.Vec.dedup_spec (T := Entry) Global
      (verified.Pair.Insts.CoreCmpPartialEqPair
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag core.cmp.PartialEqUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag core.cmp.PartialEqUsize))
      builder3) with ⟨result, hdedup, hdedupspec⟩
  have hdedupmem := (hdedupspec entry_partialEq_lawful).1
  refine ⟨result, ?_, ?_⟩
  · rw [hb1]
    simp
    rw [houtgoing]
    simp
    simp [alloc.vec.IntoIteratorVec.into_iter]
    rw [hb2]
    simp [Aeneas.Std.lift, alloc.vec.Vec.deref_mut]
    rw [hs1]
    simp
    rw [hdedup]
  · intro μ β
    have hperm : List.Perm s1.val builder2.val := by simpa [alloc.vec.Vec.val] using hs1perm
    calc
      (μ, β) ∈ result.val ↔ (μ, β) ∈ builder3.val := hdedupmem (μ, β)
      _ ↔ (μ, β) ∈ builder2.val := by
            have hb3 : builder3.val = s1.val := by simp [builder3, alloc.vec.Vec.val]
            rw [hb3]
            exact List.Perm.mem_iff hperm
      _ ↔ (μ, β) ∈ List.map (sigEntry blockNumber) ts.val := by
            rw [hb2val, hb1val]
            simp
      _ ↔ (μ, β) ∈ StrongSignature (toLTS LTSInst sys) s blockNumber :=
            sigEntry_mem_iff LTSInst sys s blockNumber ts houtgoing μ β

/-- `strong_bisim_signature` succeeds as soon as `outgoing_transitions s` does and the
    `block_number` lookups of the actual transition targets do (no assumption about other states). -/
theorem strong_bisim_signature_total
    {L Label P : Type}
    (LTSInst : LTS L Label)
    (PInst : Partition P)
    (sys : L)
    (partition : P)
    (s : TagIndex Std.Usize StateTag)
    (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (ts : alloc.vec.Vec Transition)
    (houtgoing : LTSInst.outgoing_transitions sys s = ok ts)
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (hblock : ∀ t ∈ ts.val, PInst.block_number partition t.to = ok (blockNumber t.to)) :
    ∃ result, strong_bisim_signature LTSInst PInst s sys partition builder0 = ok result := by
  rw [strong_bisim_signature]
  rcases (alloc.vec.Vec.clear_spec (T := Entry) Global builder0) with ⟨builder1, hb1, hb1val⟩
  let iter : alloc.vec.into_iter.IntoIter Transition := ts
  have hlen : (builder1.val ++ List.map (sigEntry blockNumber) ts.val).length ≤ Usize.max := by
    simp [hb1val]
  rcases (strong_bisim_signature_loop_spec PInst partition iter builder1 ts.val blockNumber
      hblock hlen (by rfl)) with ⟨builder2, hb2, hb2val⟩
  rcases (core.slice.Slice.sort_unstable_spec (T := Entry)
      (verified.Pair.Insts.CoreCmpOrd
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd BlockTag core.cmp.OrdUsize))
      builder2.slice) with ⟨s1, hs1, hs1perm, -⟩
  let builder3 : alloc.vec.Vec Entry := { slice := s1 }
  rcases (alloc.vec.Vec.dedup_spec (T := Entry) Global
      (verified.Pair.Insts.CoreCmpPartialEqPair
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag core.cmp.PartialEqUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag core.cmp.PartialEqUsize))
      builder3) with ⟨result, hdedup, -⟩
  refine ⟨result, ?_⟩
  rw [hb1]
  simp
  rw [houtgoing]
  simp
  simp [alloc.vec.IntoIteratorVec.into_iter]
  rw [hb2]
  simp [Aeneas.Std.lift, alloc.vec.Vec.deref_mut]
  rw [hs1]
  simp
  rw [hdedup]

/-- The signature key that `strong_bisim_signature` computes: it succeeds as soon as
    `outgoing_transitions s` and the `block_number` lookups of the actual targets do, its members are
    exactly the `StrongSignature` of `s` under `blockNumber`, and it is strictly sorted. Hence the
    key is a canonical form of the signature set (`sigKey_unique`). -/
theorem strong_bisim_signature_key
    {L Label P : Type}
    (LTSInst : LTS L Label)
    (PInst : Partition P)
    (sys : L)
    (partition : P)
    (s : TagIndex Std.Usize StateTag)
    (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (ts : alloc.vec.Vec Transition)
    (houtgoing : LTSInst.outgoing_transitions sys s = ok ts)
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (hblock : ∀ t ∈ ts.val, PInst.block_number partition t.to = ok (blockNumber t.to)) :
    ∃ result, strong_bisim_signature LTSInst PInst s sys partition builder0 = ok result ∧
      (∀ μ β, (μ, β) ∈ result.val ↔ (μ, β) ∈ StrongSignature (toLTS LTSInst sys) s blockNumber) ∧
      List.Pairwise entLt result.val := by
  rw [strong_bisim_signature]
  rcases (alloc.vec.Vec.clear_spec (T := Entry) Global builder0) with ⟨builder1, hb1, hb1val⟩
  let iter : alloc.vec.into_iter.IntoIter Transition := ts
  have hlen : (builder1.val ++ List.map (sigEntry blockNumber) ts.val).length ≤ Usize.max := by
    simp [hb1val]
  rcases (strong_bisim_signature_loop_spec PInst partition iter builder1 ts.val blockNumber
      hblock hlen (by rfl)) with ⟨builder2, hb2, hb2val⟩
  rcases (core.slice.Slice.sort_unstable_spec (T := Entry)
      (verified.Pair.Insts.CoreCmpOrd
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd LabelTag core.cmp.OrdUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd BlockTag core.cmp.OrdUsize))
      builder2.slice) with ⟨s1, hs1, hs1perm, hs1sorted⟩
  let builder3 : alloc.vec.Vec Entry := { slice := s1 }
  rcases (alloc.vec.Vec.dedup_spec (T := Entry) Global
      (verified.Pair.Insts.CoreCmpPartialEqPair
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex LabelTag core.cmp.PartialEqUsize)
        (verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex BlockTag core.cmp.PartialEqUsize))
      builder3) with ⟨result, hdedup, hdedupspec⟩
  obtain ⟨hdmem, hdsub, hdchain⟩ := hdedupspec entry_partialEq_lawful
  refine ⟨result, ?_, ?_, ?_⟩
  · rw [hb1]
    simp
    rw [houtgoing]
    simp
    simp [alloc.vec.IntoIteratorVec.into_iter]
    rw [hb2]
    simp [Aeneas.Std.lift, alloc.vec.Vec.deref_mut]
    rw [hs1]
    simp
    rw [hdedup]
  · intro μ β
    have hperm : List.Perm s1.val builder2.val := by simpa [alloc.vec.Vec.val] using hs1perm
    calc
      (μ, β) ∈ result.val ↔ (μ, β) ∈ builder3.val := hdmem (μ, β)
      _ ↔ (μ, β) ∈ builder2.val := by
            have hb3 : builder3.val = s1.val := by simp [builder3, alloc.vec.Vec.val]
            rw [hb3]
            exact List.Perm.mem_iff hperm
      _ ↔ (μ, β) ∈ List.map (sigEntry blockNumber) ts.val := by
            rw [hb2val, hb1val]
            simp
      _ ↔ (μ, β) ∈ StrongSignature (toLTS LTSInst sys) s blockNumber :=
            sigEntry_mem_iff LTSInst sys s blockNumber ts houtgoing μ β
  · have hb3 : builder3.val = s1.val := by simp [builder3, alloc.vec.Vec.val]
    have hsorted : List.Pairwise (fun a b => entryOrd.cmp a b ≠ ok Ordering.gt) result.val :=
      List.Pairwise.sublist hdsub (by rw [hb3]; exact hs1sorted entry_ord_total)
    exact sorted_chain_strict hsorted hdchain

/-- `LabelledTransitionSystem`'s `LTS` instance is a specific `LTS`
    implementor, so its correctness result is a corollary of the generic
    `strong_bisim_signature_spec_general`. -/
theorem strong_bisim_signature_spec
    {Label P : Type}
    (TLInst : TransitionLabel Label)
    (PInst : Partition P)
    (sys : LabelledTransitionSystem Label)
    (partition : P)
    (s : TagIndex Std.Usize StateTag)
    (builder0 : alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × (TagIndex Std.Usize BlockTag)))
    (blockNumber : TagIndex Std.Usize StateTag → TagIndex Std.Usize BlockTag)
    (hblock : ∀ t, PInst.block_number partition t = ok (blockNumber t))
    (ts : alloc.vec.Vec Transition)
    (houtgoing :
      (verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS
          TLInst).outgoing_transitions sys s = ok ts) :
    StrongBisimSignatureSpec
      (verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
      PInst sys partition s builder0 blockNumber hblock ts houtgoing :=
  strong_bisim_signature_spec_general
    (verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS TLInst)
    PInst sys partition s builder0 blockNumber hblock ts houtgoing

end MercVerified.Refinement.Proofs
