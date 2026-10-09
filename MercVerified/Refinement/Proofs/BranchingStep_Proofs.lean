import MercVerified.Refinement.Proofs.BranchingClosure_Proofs
import MercVerified.Refinement.Proofs.BranchingPartition_Proofs
import MercVerified.Refinement.Proofs.WorklistStep_Proofs
import Sigref.Proofs.Branching_Proofs
import Aeneas.Std.WP

/-!
# One iteration of `branching_run_worklist_loop`

One call of `branching_process_worklist_block` is a step of the abstract algorithm
(`Sigref.BranchingStep`) on the configuration `(partition, marked states)` of the partition.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_lts.incoming_transitions (IncomingTransitions FromTransition)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder Block)
open verified.merc_reduction.signature_refinement (WorklistContextBranching)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

open verified.merc_reduction.signature_refinement in
/-- `branching_process_worklist_block` with the leaf contracts rewritten in. -/
theorem branching_process_worklist_block_contract {L : Type} {Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (incoming : verified.merc_lts.incoming_transitions.IncomingTransitions)
    (ctx : WorklistContextBranching) (b : BT)
    (hIdx : b.index.val < ctx.partition.blocks.val.length)
    (b0 : Block) (hb0 : ctx.partition.blocks.slice.val[b.index.val] = b0)
    (hb0wf : merc_reduction.block_partition.Block.WellFormed b0)
    (hMark : (b0.marked_split : Nat) < (b0.«end» : Nat)) :
    branching_process_worklist_block LTSInst sys incoming ctx b =
      (do
        let id ←
          std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault.default
            (VecTy ((TagIndex Std.Usize LabelTag) × BT)) (TagIndex Std.Usize BlockTag)
            verified.rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault
        let _bk ← ok b0
        let b1 ← ok (decide ((b0.marked_split : Nat) < (b0.«end» : Nat)))
        massert b1
        let bp ← maybe_mark_backward_closure true ctx.partition b incoming
        let num_blocks ← ok (alloc.vec.Vec.len bp.blocks)
        let (nbi, bp1, _, _, v, bpb, v1) ←
          branching_partition_marked LTSInst sys bp b id
            (alloc.vec.Vec.new (VecTy ((TagIndex Std.Usize LabelTag) × BT)))
            ctx.builder ctx.split_builder ctx.state_to_key
        let (bp2, v2, v3) ←
          mark_dirty_new_blocks true LTSInst sys bp1 incoming ctx.worklist ctx.states b nbi
            num_blocks
        ok { partition := bp2, worklist := v2, states := v3, builder := v,
             split_builder := bpb, state_to_key := v1 }) := by
  unfold branching_process_worklist_block
  rw [block_partition_block_val ctx.partition b hIdx]
  rw [hb0]
  simp [block_has_marked_contract b0 hb0wf, num_of_blocks_contract, hMark, bind_ok]

/-- The abstract configuration of a concrete partition: block equivalence and marked states. -/
def cfgOf (p : BlockPartition) (n : Nat) : Sigref.Config (Fin n) :=
  ⟨(bdOf p n).setoid, {x | IsMarked p x.val}⟩

theorem bdOf_setoid_eq {n : Nat} {p q : BlockPartition} (h : ∀ s, e2bAt q s = e2bAt p s) :
    (bdOf q n).setoid = (bdOf p n).setoid :=
  Setoid.ext fun x y => by
    show e2bAt q x.val = e2bAt q y.val ↔ e2bAt p x.val = e2bAt p y.val
    rw [h, h]

/-- The termination measure of the branching worklist loop. -/
def bworklistMeasure (n : Nat) (ctx : WorklistContextBranching) : Nat :=
  (n - ctx.partition.blocks.val.length) * (n + 1) + ctx.worklist.val.length

/-- The abstract invariant of the loop. -/
structure BrLoopInv {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Nat)
    (ctx : WorklistContextBranching) : Prop where
  dirty : DirtyInv n ctx.partition ctx.worklist
  stk : ctx.state_to_key.val.length = n
  queued : ∀ t : ST, t.index.val < n → IsMarked ctx.partition t.index.val →
    ∃ x ∈ ctx.worklist.val, x.index.val = e2bAt ctx.partition t.index.val
  sem : Sigref.BranchingInv (aLTS LTSInst sys n) (cfgOf ctx.partition n)

/-- The block data after the backward closure satisfies the hypotheses of the key computation. -/
theorem blockInv_of_closure {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    (_hn : n ≤ Usize.max) {p q : BlockPartition} {b : Nat}
    (he2b : ∀ s, e2bAt q s = e2bAt p s)
    (_hout : ∀ x : Fin n, e2bAt p x.val ≠ b → (IsMarked q x.val ↔ IsMarked p x.val))
    (hin : ∀ x : Fin n, e2bAt p x.val = b → (IsMarked q x.val ↔ x ∈ Sigref.inertClosure
      (aLTS LTSInst sys n) (bdOf p n).setoid {d : Fin n | e2bAt p d.val = b ∧ IsMarked p d.val}))
    (hinv : Sigref.BranchingInv (aLTS LTSInst sys n) (cfgOf p n)) :
    Sigref.RP.BlockInv (aLTS LTSInst sys n) (bdOf q n) b := by
  have hset : (bdOf q n).setoid = (bdOf p n).setoid := bdOf_setoid_eq he2b
  -- membership in the inert closure of the whole marked set, for states of block `b`
  have hIC : ∀ x : Fin n, e2bAt p x.val = b → (x ∈ Sigref.inertClosure (aLTS LTSInst sys n)
      (bdOf p n).setoid {d : Fin n | IsMarked p d.val} ↔ x ∈ Sigref.inertClosure (aLTS LTSInst sys n)
      (bdOf p n).setoid {d : Fin n | e2bAt p d.val = b ∧ IsMarked p d.val}) := by
    intro x hx
    constructor
    · rintro ⟨d, hd, hreach⟩
      have hdb : e2bAt p d.val = b := by
        have := Sigref.InertReach.rel (aLTS LTSInst sys n) (bdOf p n).setoid hreach
        have h2 : e2bAt p x.val = e2bAt p d.val := this
        rw [← h2]; exact hx
      exact ⟨d, ⟨hdb, hd⟩, hreach⟩
    · rintro ⟨d, ⟨-, hd⟩, hreach⟩
      exact ⟨d, hd, hreach⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s t hTr hsb htb hdt
    show IsMarked q s.val
    have hsb' : e2bAt p s.val = b := by rw [← he2b]; exact hsb
    have htb' : e2bAt p t.val = b := by rw [← he2b]; exact htb
    have hdt' := (hin t htb').1 hdt
    have hstep : Sigref.InertTr (aLTS LTSInst sys n) (bdOf p n).setoid s t :=
      ⟨hTr, by show e2bAt p s.val = e2bAt p t.val; rw [hsb', htb']⟩
    obtain ⟨d, hd, hreach⟩ := hdt'
    exact (hin s hsb').2 ⟨d, hd, Relation.ReflTransGen.head hstep hreach⟩
  · intro s t hsb htb hds hdt
    have hsb' : e2bAt p s.val = b := by rw [← he2b]; exact hsb
    have htb' : e2bAt p t.val = b := by rw [← he2b]; exact htb
    show Sigref.E (aLTS LTSInst sys n) (bdOf q n).setoid s t
    rw [hset]
    exact hinv.U s t (show e2bAt p s.val = e2bAt p t.val by rw [hsb', htb'])
      (fun h => hds ((hin s hsb').2 ((hIC s hsb').1 h)))
      (fun h => hdt ((hin t htb').2 ((hIC t htb').1 h)))
  · intro s t hsb htb hds hdt
    have hsb' : e2bAt p s.val = b := by rw [← he2b]; exact hsb
    have htb' : e2bAt p t.val = b := by rw [← he2b]; exact htb
    show ¬ Sigref.E (aLTS LTSInst sys n) (bdOf q n).setoid s t
    rw [hset]
    exact hinv.S s t (show e2bAt p s.val = e2bAt p t.val by rw [hsb', htb'])
      (fun h => hds ((hin s hsb').2 ((hIC s hsb').1 h)))
      ((hIC t htb').2 ((hin t htb').1 hdt))

/-- **The set-level effect of one iteration is a step of the abstract algorithm.** All the facts
about the partitions before (`p`), after the closure (`bp`), after the split (`p1`) and after the
marking (`p2`) that the concrete proofs establish. -/
theorem branching_step_sem {L Label : Type} {LTSInst : LTS L Label} {sys : L} {n : Nat}
    (hn : n ≤ Usize.max) {X : Type} (sg : ST → X) {incoming : IncomingTransitions}
    (hmemc : ∀ s : ST, s.index.val < n → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
      ∀ i : FromTransition, i ∈ res.val ↔ ∃ (μ : TagIndex Std.Usize LabelTag) (s' : ST),
        s'.index.val < n ∧ MercVerified.Lts.tr LTSInst sys s' μ s ∧ (i.label, i.«from») = (μ, s'))
    {p bp p1 p2 : BlockPartition} {b : Nat} (_hp : PartInv n p) (hbp : PartInv n bp)
    (hp1 : PartInv n p1) (hbpe : ∀ s, e2bAt bp s = e2bAt p s)
    (hout : ∀ x : Fin n, e2bAt p x.val ≠ b → (IsMarked bp x.val ↔ IsMarked p x.val))
    (hin : ∀ x : Fin n, e2bAt p x.val = b → (IsMarked bp x.val ↔ x ∈ Sigref.inertClosure
      (aLTS LTSInst sys n) (bdOf p n).setoid {d : Fin n | e2bAt p d.val = b ∧ IsMarked p d.val}))
    {k : Nat} (hb : b < bp.blocks.val.length)
    (hother : ∀ j, j < bp.blocks.val.length → j ≠ b → blkAt p1 j = blkAt bp j)
    (hms : ∀ j, (j = b ∨ (bp.blocks.val.length ≤ j ∧ j < bp.blocks.val.length + k)) →
      (blkAt p1 j).marked_split.val = (blkAt p1 j).«end».val)
    (hs1 : ∀ s : ST, s.index.val < n → e2bAt bp s.index.val ≠ b →
      e2bAt p1 s.index.val = e2bAt bp s.index.val ∧ offAt p1 s.index.val = offAt bp s.index.val)
    (hs2 : ∀ s : ST, s.index.val < n → e2bAt bp s.index.val = b →
      e2bAt p1 s.index.val = b ∨ (bp.blocks.val.length ≤ e2bAt p1 s.index.val ∧
        e2bAt p1 s.index.val < bp.blocks.val.length + k))
    (hs3 : ∀ s s' : ST, s.index.val < n → s'.index.val < n → e2bAt bp s.index.val = b →
      e2bAt bp s'.index.val = b →
      (e2bAt p1 s.index.val = e2bAt p1 s'.index.val ↔
        ((¬ IsMarked bp s.index.val ∧ ¬ IsMarked bp s'.index.val) ∨
          (IsMarked bp s.index.val ∧ IsMarked bp s'.index.val ∧ sg s = sg s'))))
    (hsg : ∀ s t : Fin n, e2bAt p s.val = b → e2bAt p t.val = b → IsMarked bp s.val →
      IsMarked bp t.val → (sg (stOf s) = sg (stOf t) ↔
        Sigref.E (aLTS LTSInst sys n) (bdOf p n).setoid s t))
    (hmarkp0 : ∃ x : Fin n, e2bAt p x.val = b ∧ IsMarked p x.val)
    (hkeep : ∃ x : Fin n, e2bAt p1 x.val = b)
    (hlen : p1.blocks.val.length = bp.blocks.val.length + k)
    (numB : Sz) (hnumB : numB.val = bp.blocks.val.length)
    (hp2e : ∀ s, e2bAt p2 s = e2bAt p1 s)
    (hD : ∀ t : ST, t.index.val < n → (IsMarked p2 t.index.val ↔ IsMarked p1 t.index.val ∨
      ∃ f, bp.blocks.val.length ≤ f ∧ f < bp.blocks.val.length + k ∧
        PredBlkG p1 numB incoming n f t)) :
    Sigref.BranchingStep (aLTS LTSInst sys n) (cfgOf p n) (cfgOf p2 n) := by
  classical
  have hstv : ∀ y : Fin n, (stOf y).index.val = y.val := fun y => stOf_index y hn
  have hfin : ∀ y : ST, ∀ hy : y.index.val < n, stOf (⟨y.index.val, hy⟩ : Fin n) = y := by
    intro y hy
    apply merc_utilities.tagged_index.TagIndex.ext
    apply UScalar.eq_of_val_eq
    rw [stOf_index _ hn]
  have hlt : ∀ y : Fin n, (stOf y).index.val < n := fun y => stOf_lt y hn
  have hs1' : ∀ x : Fin n, e2bAt p x.val ≠ b →
      e2bAt p1 x.val = e2bAt p x.val ∧ offAt p1 x.val = offAt bp x.val := by
    intro x hx
    have := hs1 (stOf x) (hlt x) (by rw [hstv, hbpe]; exact hx)
    rw [hstv, hbpe] at this
    exact this
  have hs2' : ∀ x : Fin n, e2bAt p x.val = b → e2bAt p1 x.val = b ∨
      (bp.blocks.val.length ≤ e2bAt p1 x.val ∧ e2bAt p1 x.val < bp.blocks.val.length + k) := by
    intro x hx
    have := hs2 (stOf x) (hlt x) (by rw [hstv, hbpe]; exact hx)
    rw [hstv] at this
    exact this
  have hs3' : ∀ x y : Fin n, e2bAt p x.val = b → e2bAt p y.val = b →
      (e2bAt p1 x.val = e2bAt p1 y.val ↔ ((¬ IsMarked bp x.val ∧ ¬ IsMarked bp y.val) ∨
        (IsMarked bp x.val ∧ IsMarked bp y.val ∧ sg (stOf x) = sg (stOf y)))) := by
    intro x y hx hy
    have := hs3 (stOf x) (stOf y) (hlt x) (hlt y) (by rw [hstv, hbpe]; exact hx)
      (by rw [hstv, hbpe]; exact hy)
    rw [hstv, hstv] at this
    exact this
  have hown1 := hp1.own
  have hownb := hbp.own
  -- marking after the split
  have hm1 : ∀ x : Fin n, IsMarked p1 x.val ↔ (e2bAt p x.val ≠ b ∧ IsMarked p x.val) := by
    intro x
    by_cases h : e2bAt p x.val = b
    · have hown := (hown1 x.val x.2).2
      have hnm : ¬ IsMarked p1 x.val := by
        have hj : (blkAt p1 (e2bAt p1 x.val)).marked_split.val =
            (blkAt p1 (e2bAt p1 x.val)).«end».val := by
          rcases hs2' x h with h1 | h1
          · rw [h1]; exact hms b (Or.inl rfl)
          · exact hms _ (Or.inr h1)
        unfold IsMarked; omega
      simp [hnm, h]
    · obtain ⟨he, ho⟩ := hs1' x h
      have hj := (hownb x.val x.2).1
      rw [hbpe] at hj
      have hbl := hother _ hj h
      have : IsMarked p1 x.val ↔ IsMarked bp x.val := by
        unfold IsMarked
        rw [he, hbl, ho, hbpe]
      rw [this]
      exact ⟨fun hm => ⟨h, (hout x h).1 hm⟩, fun hm => (hout x h).2 hm.2⟩
  have hIC : ∀ x : Fin n, x ∈ Sigref.inertClosure (aLTS LTSInst sys n) (bdOf p n).setoid
      {d : Fin n | e2bAt p d.val = b ∧ IsMarked p d.val} ↔ (e2bAt p x.val = b ∧ IsMarked bp x.val) := by
    intro x
    by_cases h : e2bAt p x.val = b
    · rw [← hin x h]; simp [h]
    · constructor
      · rintro ⟨d, hd, hr⟩
        have := Sigref.InertReach.rel (aLTS LTSInst sys n) (bdOf p n).setoid hr
        exact absurd (this.trans hd.1) h
      · intro h'; exact absurd h'.1 h
  obtain ⟨x0, hx0b, hx0m⟩ := hmarkp0
  obtain ⟨x1, hx1⟩ := hkeep
  have hx1p : e2bAt p x1.val = b := by
    by_cases h : e2bAt p x1.val = b
    · exact h
    · exfalso; have := (hs1' x1 h).1; omega
  have hlenp : ∀ x : Fin n, e2bAt p x.val < bp.blocks.val.length := fun x => by
    have := (hownb x.val x.2).1; rwa [hbpe] at this
  have hneq : ∀ s t : Fin n, e2bAt p s.val = b → e2bAt p t.val ≠ b →
      e2bAt p1 s.val ≠ e2bAt p1 t.val := by
    intro s t hs ht heq
    rw [(hs1' t ht).1] at heq
    have := hlenp t
    rcases hs2' s hs with h | h <;> omega
  have hcls : ∀ t : Fin n, t ∈ Sigref.cls (bdOf p n).setoid x0 ↔ e2bAt p t.val = b := by
    intro t
    show e2bAt p x0.val = e2bAt p t.val ↔ _
    rw [hx0b]; exact eq_comm
  have hcls' : ∀ t : Fin n, t ∈ Sigref.cls (bdOf p2 n).setoid x1 ↔ e2bAt p1 t.val = b := by
    intro t
    show e2bAt p2 x1.val = e2bAt p2 t.val ↔ _
    rw [hp2e, hp2e, hx1]; exact eq_comm
  have hU : ∀ x : Fin n, (e2bAt p x.val = b ∧ ¬ e2bAt p1 x.val = b) ↔
      (bp.blocks.val.length ≤ e2bAt p1 x.val ∧ e2bAt p1 x.val < bp.blocks.val.length + k) := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩
      rcases hs2' x h1 with h | h
      · exact absurd h h2
      · exact h
    · intro h
      by_cases h1 : e2bAt p x.val = b
      · refine ⟨h1, ?_⟩; omega
      · exfalso; have := (hs1' x h1).1; have := hlenp x; omega
  refine ⟨x0, x1, ?_, ?_, ?_, ?_⟩
  · exact ⟨x0, (hcls x0).2 hx0b, hx0m⟩
  · exact (hcls x1).2 hx1p
  · intro s t
    show e2bAt p2 s.val = e2bAt p2 t.val ↔ Sigref.branchRel (aLTS LTSInst sys n)
      (bdOf p n).setoid {x : Fin n | IsMarked p x.val} x0 s t
    unfold Sigref.branchRel
    rw [hp2e, hp2e]
    have hIs := hIC s
    have hIt := hIC t
    have hset : {d : Fin n | e2bAt p d.val = b ∧ IsMarked p d.val} =
        Sigref.cls (bdOf p n).setoid x0 ∩ {x : Fin n | IsMarked p x.val} := by
      ext d; exact and_congr (hcls d).symm Iff.rfl
    rw [hset] at hIs hIt
    by_cases hs : e2bAt p s.val = b
    · have hsc := (hcls s).2 hs
      by_cases ht : e2bAt p t.val = b
      · have h3 := hs3' s t hs ht
        have hsgst := hsg s t hs ht
        have hr : (bdOf p n).setoid.r s t := show e2bAt p s.val = e2bAt p t.val by rw [hs, ht]
        have hIs' := (hIs.trans ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩ : _ ↔ IsMarked bp s.val)
        have hIt' := (hIt.trans ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩ : _ ↔ IsMarked bp t.val)
        rw [h3]
        constructor
        · intro h
          refine ⟨hr, fun _ => ⟨?_, ?_⟩⟩
          · rw [hIs', hIt']; tauto
          · intro hsI
            have hms' := hIs'.1 hsI
            have hmt : IsMarked bp t.val := by tauto
            exact (hsgst hms' hmt).1 (by tauto)
        · rintro ⟨_, h⟩
          obtain ⟨h1, h2⟩ := h hsc
          rw [hIs', hIt'] at h1
          by_cases hm : IsMarked bp s.val
          · right
            have hmt := h1.1 hm
            exact ⟨hm, hmt, (hsgst hm hmt).2 (h2 (hIs'.2 hm))⟩
          · left; exact ⟨hm, fun hmt => hm (h1.2 hmt)⟩
      · have hne := hneq s t hs ht
        constructor
        · intro h; exact absurd h hne
        · rintro ⟨h, _⟩
          exact absurd (show e2bAt p s.val = e2bAt p t.val from h) (by rw [hs]; exact fun h' => ht h'.symm)
    · have hsc : s ∉ Sigref.cls (bdOf p n).setoid x0 := fun h => hs ((hcls s).1 h)
      obtain ⟨hse, _⟩ := hs1' s hs
      by_cases ht : e2bAt p t.val = b
      · have hne := hneq t s ht hs
        constructor
        · intro h; exact absurd h.symm hne
        · rintro ⟨h, _⟩
          exact absurd (show e2bAt p s.val = e2bAt p t.val from h) (fun h' => hs (h'.trans ht))
      · rw [hse, (hs1' t ht).1]
        exact ⟨fun h => ⟨h, fun hc => absurd hc hsc⟩, fun h => h.1⟩
  · -- dirty set
    have hmem : ∀ i : FromTransition, ∀ s : ST, s.index.val < n → ∀ res,
        IncomingTransitions.incoming_transitions incoming s = ok res →
        (i ∈ res.val ↔ ∃ (μ : TagIndex Std.Usize LabelTag) (s' : ST),
          s'.index.val < n ∧ MercVerified.Lts.tr LTSInst sys s' μ s ∧ (i.label, i.«from») = (μ, s')) := by
      intro i s hsn res hres
      obtain ⟨res', hres', hiff⟩ := hmemc s hsn
      rw [hres] at hres'
      have : res' = res := by simpa using hres'.symm
      subst this
      exact hiff i
    ext x
    have hUx : ∀ y : Fin n, y ∈ Sigref.cls (bdOf p n).setoid x0 \ Sigref.cls (bdOf p2 n).setoid x1 ↔
        (bp.blocks.val.length ≤ e2bAt p1 y.val ∧ e2bAt p1 y.val < bp.blocks.val.length + k) := by
      intro y
      rw [← hU y]
      exact and_congr (hcls y) (not_congr (hcls' y))
    have hset : {d : Fin n | e2bAt p d.val = b ∧ IsMarked p d.val} =
        Sigref.cls (bdOf p n).setoid x0 ∩ {x : Fin n | IsMarked p x.val} := by
      ext d; exact and_congr (hcls d).symm Iff.rfl
    have hICs : ∀ y : Fin n, y ∈ Sigref.inertClosure (aLTS LTSInst sys n) (cfgOf p n).π
        (Sigref.cls (cfgOf p n).π x0 ∩ (cfgOf p n).X) ↔ (e2bAt p y.val = b ∧ IsMarked bp y.val) := by
      intro y; have := hIC y; rw [hset] at this; exact this
    have hmono : ∀ y : Fin n, e2bAt p y.val = b → IsMarked p y.val → IsMarked bp y.val := by
      intro y h hm
      exact (hin y h).2 ⟨y, ⟨h, hm⟩, Relation.ReflTransGen.refl⟩
    have hP : (∃ f, bp.blocks.val.length ≤ f ∧ f < bp.blocks.val.length + k ∧
        PredBlkG p1 numB incoming n f (stOf x)) ↔ x ∈ Sigref.predB (aLTS LTSInst sys n)
          (Sigref.cls (cfgOf p n).π x0 \ Sigref.cls (cfgOf p2 n).π x1) := by
      constructor
      · rintro ⟨f, hf1, hf2, s, hsn, hsf, res, hres, i, hi, hg, hfrom⟩
        obtain ⟨μ, s', hs'n, htr, hpair⟩ := (hmem i s hsn res hres).1 hi
        have hil : i.label = μ := (Prod.mk.inj hpair).1
        have hif : i.«from» = s' := (Prod.mk.inj hpair).2
        have hs'x : s' = stOf x := by
          apply merc_utilities.tagged_index.TagIndex.ext
          apply UScalar.eq_of_val_eq
          rw [← hif]; exact hfrom
        refine ⟨μ, ⟨s.index.val, hsn⟩, ?_, ?_, ?_⟩
        · exact (hUx ⟨s.index.val, hsn⟩).2 ⟨by rw [← hsf] at hf1; exact hf1,
            by rw [← hsf] at hf2; exact hf2⟩
        · show MercVerified.Lts.tr LTSInst sys (stOf x) μ (stOf ⟨s.index.val, hsn⟩)
          rw [hfin s hsn, ← hs'x]; exact htr
        · intro hμ
          have h0 : μ.index.val = 0 := (label_eq_tau_iff μ).1 hμ
          rcases hg with hg | hg
          · exact absurd (by rw [hil]; exact h0) hg
          · intro hxU
            have := (hUx x).1 hxU
            rw [hif, hs'x, hstv] at hg
            omega
      · rintro ⟨μ, u, huU, htr, hμ⟩
        have hu := (hUx u).1 huU
        refine ⟨e2bAt p1 u.val, hu.1, hu.2, stOf u, hlt u, by rw [hstv], ?_⟩
        obtain ⟨res, hres, hiff⟩ := hmemc (stOf u) (hlt u)
        refine ⟨res, hres, ⟨μ, stOf x⟩, (hiff ⟨μ, stOf x⟩).2 ⟨μ, stOf x, hlt x, htr, rfl⟩, ?_, rfl⟩
        by_cases h0 : μ.index.val = 0
        · right
          have hxn := hμ ((label_eq_tau_iff μ).2 h0)
          have h1 := (hown1 x.val x.2).1
          rw [hlen] at h1
          show e2bAt p1 (stOf x).index.val < numB.val
          rw [hstv, hnumB]
          by_contra hc
          exact hxn ((hUx x).2 ⟨by omega, h1⟩)
        · left; exact h0
    have hDx := hD (stOf x) (hlt x)
    rw [hstv] at hDx
    show IsMarked p2 x.val ↔ x ∈ ({y : Fin n | IsMarked p y.val} \ _) ∪ _
    rw [hDx, hm1 x]
    refine or_congr ?_ hP
    show _ ↔ x ∈ {y : Fin n | IsMarked p y.val} ∧ ¬ x ∈ Sigref.inertClosure (aLTS LTSInst sys n)
      (cfgOf p n).π (Sigref.cls (cfgOf p n).π x0 ∩ (cfgOf p n).X)
    rw [hICs x]
    by_cases h : e2bAt p x.val = b
    · constructor
      · rintro ⟨h', _⟩; exact absurd h h'
      · rintro ⟨hm, hn'⟩; exact absurd (hmono x h hm) (fun hb => hn' ⟨h, hb⟩)
    · simp [h]

open verified.merc_reduction.signature_refinement in
/-- **One iteration of the worklist loop** (structural part): the worklist invariant is preserved. -/
theorem branching_worklist_step_struct {L Label : Type}
    (LTSInst : verified.merc_lts.lts.LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (hfit : MercVerified.Refinement.StateCountFits LTSInst sys) (nU : Sz)
    (hns : LTSInst.num_of_states sys = ok nU) (hn0 : 0 < nU.val)
    {nl : Std.Usize} (hE : CEnv LTSInst sys nl) (htopo : ConcTopo LTSInst sys)
    (incoming : IncomingTransitions)
    (hinc : ∀ s : ST, s.index.val < nU.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
        ∀ i ∈ res.val, i.«from».index.val < nU.val)
    (hsil : IncSilent LTSInst sys nU.val incoming)
    (hmemc : ∀ s : ST, s.index.val < nU.val → ∃ res : alloc.vec.Vec FromTransition,
      IncomingTransitions.incoming_transitions incoming s = ok res ∧
      ∀ i : FromTransition, i ∈ res.val ↔ ∃ (μ : TagIndex Std.Usize LabelTag) (s' : ST),
        s'.index.val < nU.val ∧ MercVerified.Lts.tr LTSInst sys s' μ s ∧ (i.label, i.«from») = (μ, s'))
    (ctx : WorklistContextBranching) (b : BT) (w : VecTy BT) (hw : ctx.worklist.val = w.val ++ [b])
    (hI : BrLoopInv LTSInst sys nU.val ctx) :
    ∃ ctx', branching_process_worklist_block LTSInst sys incoming { ctx with worklist := w } b = ok ctx' ∧
      BrLoopInv LTSInst sys nU.val ctx' ∧
      Sigref.BranchingStep (aLTS LTSInst sys nU.val) (cfgOf ctx.partition nU.val)
        (cfgOf ctx'.partition nU.val) ∧
      bworklistMeasure nU.val ctx' < bworklistMeasure nU.val ctx := by
  obtain ⟨⟨hp, hnd, hwl⟩, hstk, hmq, hsem⟩ := hI
  rw [hw] at hnd hwl
  have hbmem : b ∈ w.val ++ [b] := by simp
  obtain ⟨hbN, hbmark⟩ := hwl b hbmem
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hn2 := hfit nU hns
  have hnbw : b ∉ w.val := by
    intro hbw
    have := (List.nodup_append.mp hnd).2.2 b hbw b (by simp)
    exact this rfl
  have hDw : DirtyInv nU.val ctx.partition w := by
    refine ⟨hp, (List.nodup_append.mp hnd).1, ?_⟩
    intro x hx
    exact hwl x (List.mem_append_left _ hx)
  have hb0 : ctx.partition.blocks.slice.val[b.index.val]'hbN = blkAt ctx.partition b.index.val :=
    (blkAt_eq_getElem hbN).symm
  have hcon := branching_process_worklist_block_contract LTSInst sys incoming
    { ctx with worklist := w } b hbN _ hb0 (partInv_blockWF hp hbN) hbmark
  have hbhid := hE.hid
  have htopoA : Sigref.RP.TopoSorted (aLTS LTSInst sys nU.val) := by
    intro s t h
    have h0 := (label_eq_tau_iff _).1 (rfl : (Cslib.HasTau.τ : TagIndex Std.Usize LabelTag) = _)
    have := htopo (stOf s) _ (stOf t) h h0
    rw [stOf_index _ hnmax, stOf_index _ hnmax] at this
    exact this
  -- the closure
  obtain ⟨bp, hbpq, hmono, hout, hin⟩ := mark_backward_closure_spec hnmax hsil hp b hbN
  have hbpe : ∀ s, e2bAt bp s = e2bAt ctx.partition s := fun s => hmono.e2bAt_eq s
  have hbpN : bp.blocks.val.length = ctx.partition.blocks.val.length := hmono.nblocks
  have hbbp : b.index.val < bp.blocks.val.length := by rw [hbpN]; exact hbN
  have hmarkbp : (blkAt bp b.index.val).marked_split.val < (blkAt bp b.index.val).«end».val := by
    have := hmono.ms_le; have := hmono.end_eq
    have h1 : (blkAt bp b.index.val).«end».val = (blkAt ctx.partition b.index.val).«end».val := by
      rw [hmono.end_eq]
    omega
  have hbinv : Sigref.RP.BlockInv (aLTS LTSInst sys nU.val) (bdOf bp nU.val) b.index.val :=
    blockInv_of_closure hnmax hbpe hout hin hsem
  obtain ⟨idm, hidm, hid⟩ := std.collections.hash.map.HashMapKVSGlobal.default_spec
    (alloc.vec.Vec ((TagIndex Std.Usize LabelTag) × BT)) BT
    verified.rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault
  have hkts : (alloc.vec.Vec.new (VecTy ((TagIndex Std.Usize LabelTag) × BT))).val = [] := rfl
  obtain ⟨nbi, p1, id1, kts1, sigb1, sb1, stk1, hspm, hstk1, hsplit⟩ :=
    branching_partition_marked_spec LTSInst sys hwf hfit nU hns hn0 hE htopo hmono.inv b hbbp
      hmarkbp idm
      (fun q => hid _ _ _ internHash_total internBuildHasher_total q) (alloc.vec.Vec.new _) hkts
      ctx.builder ctx.split_builder ctx.state_to_key hstk
  obtain ⟨hp1, k, hN1, hnbi, hother, hmk, hs1, hs2, hs3⟩ := hsplit
  have hND : DirtyInv nU.val p1 w := by
    refine ⟨hp1, hDw.2.1, fun x hx => ?_⟩
    obtain ⟨hx1, hx2⟩ := hwl x (List.mem_append_left _ hx)
    have hxb : x.index.val ≠ b.index.val := fun h =>
      hnbw (by
        have : x = b := merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq h)
        rw [← this]; exact hx)
    refine ⟨by omega, ?_⟩
    rw [hother _ (by omega) hxb, hmono.other _ hxb]; exact hx2
  have hbase : DirtySem nU.val p1 p1 w (fun _ => False) := by
    refine ⟨rfl, fun t _ => by simp, fun t ht hm => ?_⟩
    by_cases hjb : e2bAt p1 t.index.val = b.index.val
    · exfalso
      have hme := hmk (e2bAt p1 t.index.val) (Or.inl hjb)
      have hlt := (hp1.own t.index.val ht).2.2
      unfold IsMarked at hm
      omega
    · by_cases hjnew : bp.blocks.val.length ≤ e2bAt p1 t.index.val ∧
          e2bAt p1 t.index.val < bp.blocks.val.length + k
      · exfalso
        have hme := hmk (e2bAt p1 t.index.val) (Or.inr hjnew)
        have hlt := (hp1.own t.index.val ht).2.2
        unfold IsMarked at hm
        omega
      · have hjlt : e2bAt p1 t.index.val < bp.blocks.val.length := by
          have hown := (hp1.own t.index.val ht).1
          rw [hN1] at hown
          omega
        have hne : e2bAt bp t.index.val ≠ b.index.val := by
          intro heq
          rcases hs2 t ht heq with h | h
          · exact hjb h
          · exact hjnew h
        have hpres := hs1 t ht hne
        have hblk : blkAt p1 (e2bAt p1 t.index.val) = blkAt bp (e2bAt bp t.index.val) := by
          rw [hother _ hjlt hjb, hpres.1]
        have hm' : IsMarked bp t.index.val := by
          unfold IsMarked at hm ⊢
          rw [hblk, hpres.2] at hm
          exact hm
        have hne' : e2bAt ctx.partition t.index.val ≠ b.index.val := by rwa [hbpe] at hne
        have hm'' : IsMarked ctx.partition t.index.val := by
          have := hout ⟨t.index.val, ht⟩ hne'
          exact this.1 hm'
        obtain ⟨x, hx, hxe⟩ := hmq t ht hm''
        rw [hw] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, hx, by rw [hpres.1, hbpe]; exact hxe⟩
        · simp at hx
          subst hx
          exact absurd hxe.symm hne'
  have hnumB : (alloc.vec.Vec.len bp.blocks).val = bp.blocks.val.length := by
    simp [alloc.vec.Vec.len]
  have hNn : (ctx.partition.blocks.val.length) ≤ nU.val := hp.blocks_le_n
  have hN1n : p1.blocks.val.length ≤ nU.val := hp1.blocks_le_n
  have hlt2 : nU.val < 2 ^ UScalarTy.Usize.numBits := by
    have := usize_max_succ; omega
  obtain ⟨p2, w2, s2, hrun, hI2, hlen2, hsem2⟩ := bmarkDirtyAcc_spec LTSInst sys incoming b
    (alloc.vec.Vec.len bp.blocks) hnmax (hbhid) hinc nbi.val ctx.states (p := p1) (w := w) (by
      intro x hx
      rw [hnbi] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have hj' := List.mem_range'_1.mp hj
        show (uTag j : BT).index.val < _
        simp only [uTag]
        rw [uTotal_val_of_lt (by omega)]
        omega) hND hbase
  rw [hcon]
  simp only [hidm, massert, hbmark, decide_true, maybe_mark_backward_closure, hbpq,
    if_true, bind_ok]
  rw [hspm]
  simp only [bind_ok, mark_dirty_new_blocks_contract]
  have hstv : ∀ y : Fin nU.val, (stOf y).index.val = y.val := fun y => stOf_index y hnmax
  have htoFin : ∀ y : Fin nU.val, toFin hn0 (stOf y) = y := fun y =>
    Fin.ext (by show (stOf y).index.val % nU.val = y.val; rw [hstv]; exact Nat.mod_eq_of_lt y.2)
  have hu : ∀ j, j < nU.val → (uTag j : BT).index.val = j := fun j hj => by
    simp only [uTag]; rw [uTotal_val_of_lt (by omega)]
  have hsg : ∀ s t : Fin nU.val, e2bAt ctx.partition s.val = b.index.val →
      e2bAt ctx.partition t.val = b.index.val → IsMarked bp s.val → IsMarked bp t.val →
      ((fun s : ST => Sigref.RP.keysOf (aLTS LTSInst sys nU.val) (bdOf bp nU.val) b.index.val
          (keyOf ctx.state_to_key) (toFin hn0 s)) (stOf s) =
        (fun s : ST => Sigref.RP.keysOf (aLTS LTSInst sys nU.val) (bdOf bp nU.val) b.index.val
          (keyOf ctx.state_to_key) (toFin hn0 s)) (stOf t) ↔
        Sigref.E (aLTS LTSInst sys nU.val) (bdOf ctx.partition nU.val).setoid s t) := by
    intro s t hs ht hms hmt
    have := Sigref.RP.keyCompCorrect (aLTS LTSInst sys nU.val) (bdOf bp nU.val) b.index.val
      (keyOf ctx.state_to_key) htopoA hbinv s t (by show e2bAt bp s.val = _; rw [hbpe]; exact hs)
      (by show e2bAt bp t.val = _; rw [hbpe]; exact ht) hms hmt
    show Sigref.RP.keysOf _ _ _ _ (toFin hn0 (stOf s)) = Sigref.RP.keysOf _ _ _ _ (toFin hn0 (stOf t)) ↔ _
    rw [htoFin, htoFin, this, bdOf_setoid_eq hbpe]
  have hmarkp0 : ∃ x : Fin nU.val, e2bAt ctx.partition x.val = b.index.val ∧
      IsMarked ctx.partition x.val := by
    have hbk := hp.blk b.index.val hbN
    obtain ⟨hxn, hxb, hxoff⟩ := pos_in_block hp hbN
      (pos := (blkAt ctx.partition b.index.val).marked_split.val) hbk.2.2.1 hbmark
    exact ⟨⟨_, hxn⟩, hxb, (isMarked_iff_ms hxb).2 (le_of_eq hxoff.symm)⟩
  have hkeep : ∃ x : Fin nU.val, e2bAt p1 x.val = b.index.val := by
    have hbk := hp1.blk b.index.val (by omega)
    obtain ⟨hxn, hxb, _⟩ := pos_in_block hp1 (b := b.index.val) (by omega)
      (pos := (blkAt p1 b.index.val).begin.val) le_rfl hbk.1
    exact ⟨⟨_, hxn⟩, hxb⟩
  have hp2e : ∀ s, e2bAt p2 s = e2bAt p1 s := fun s => by
    unfold e2bAt; rw [hsem2.1]
  have hD : ∀ t : ST, t.index.val < nU.val → (IsMarked p2 t.index.val ↔ IsMarked p1 t.index.val ∨
      ∃ f, bp.blocks.val.length ≤ f ∧ f < bp.blocks.val.length + k ∧
        PredBlkG p1 bp.blocks.len incoming nU.val f t) := by
    intro t ht
    rw [hsem2.2.1 t ht]
    refine or_congr_right ?_
    constructor
    · rintro (h | ⟨nb, hnb, hne, hP⟩)
      · exact h.elim
      · rw [hnbi] at hnb
        rcases List.mem_cons.mp hnb with rfl | hnb
        · exact absurd rfl hne
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hnb
          have hj' := List.mem_range'_1.mp hj
          rw [hu j (by omega)] at hP
          exact ⟨j, by omega, by omega, hP⟩
    · rintro ⟨f, hf1, hf2, hP⟩
      refine Or.inr ⟨uTag f, ?_, ?_, ?_⟩
      · rw [hnbi]
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨f, List.mem_range'_1.2 ⟨hf1, by omega⟩, rfl⟩)
      · intro h
        have := congrArg (fun x : BT => x.index.val) h
        simp only [hu f (by omega)] at this
        omega
      · rw [hu f (by omega)]; exact hP
  have hstep := branching_step_sem hnmax _ hmemc hp hmono.inv hp1 hbpe hout hin hbbp hother hmk
    hs1 hs2 hs3 hsg hmarkp0 hkeep hN1 bp.blocks.len hnumB hp2e hD
  have hlenw : w.val.length + 1 = ctx.worklist.val.length := by rw [hw]; simp
  have hmeas : (nU.val - p2.blocks.val.length) * (nU.val + 1) + w2.val.length <
      (nU.val - ctx.partition.blocks.val.length) * (nU.val + 1) + ctx.worklist.val.length := by
    by_cases hk : k = 0
    · subst hk
      have hnbi' : nbi.val = [b] := by rw [hnbi]; simp
      rw [hnbi', markDirtyAcc_cons, markDirtyStep_pos true LTSInst sys incoming b _ b p1 w
        ctx.states rfl] at hrun
      simp only [bind_ok, markDirtyAcc, ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨h1, h2, -⟩ := hrun
      rw [← h1, ← h2, hN1, hbpN, Nat.add_zero]
      omega
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hN2n : p2.blocks.val.length ≤ nU.val := hI2.1.blocks_le_n
      have hw2 : w2.val.length ≤ p2.blocks.val.length :=
        nodup_bounded_length_le _ _ hI2.2.1 (fun x hx => (hI2.2.2 x hx).1)
      rw [hlen2, hN1, hbpN] at hN2n hw2 ⊢
      obtain ⟨a, ha⟩ : ∃ a, a = nU.val - (ctx.partition.blocks.val.length + k) := ⟨_, rfl⟩
      have hsub : nU.val - ctx.partition.blocks.val.length = a + k := by omega
      rw [← ha, hsub]
      have : (a + k) * (nU.val + 1) = a * (nU.val + 1) + k * (nU.val + 1) := by ring
      have hk1 : nU.val + 1 ≤ k * (nU.val + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
  show ∃ ctx', (do
      let r ← markDirtyAcc true LTSInst sys incoming b bp.blocks.len p1 w ctx.states nbi.val
      ok ({ partition := r.1, worklist := r.2.1, states := r.2.2, builder := sigb1,
            split_builder := sb1, state_to_key := stk1 } : WorklistContextBranching)) = ok ctx' ∧
    BrLoopInv LTSInst sys nU.val ctx' ∧
    Sigref.BranchingStep (aLTS LTSInst sys nU.val) (cfgOf ctx.partition nU.val)
      (cfgOf ctx'.partition nU.val) ∧ bworklistMeasure nU.val ctx' < bworklistMeasure nU.val ctx
  rw [hrun]
  simp only [bind_ok]
  refine ⟨_, rfl, ⟨hI2, hstk1, hsem2.2.2, ?_⟩, hstep, ?_⟩
  · exact Sigref.branchingInv_step _ (Sigref.RP.tauLoopFree_of_topo _ htopoA) hsem hstep
  · unfold bworklistMeasure; exact hmeas

end MercVerified.Refinement.Proofs
