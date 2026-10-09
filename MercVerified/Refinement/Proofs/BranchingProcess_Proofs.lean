import MercVerified.Refinement.Proofs.BranchingRenumber_Proofs
import Sigref.Proofs.KeyComp_Proofs
import Aeneas.Std.WP

/-!
# `branching_process_marked_elements`: the concrete key computation is `Sigref.RP.kcRun`

The abstract view of the concrete data (`stOf`, `aLTS`, `bdOf`, `absOf`) and the translation of the
flat signature built by `branching_bisim_signature_inductive` to `Sigref.RP.flatSig`.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md).
-/

open Aeneas Aeneas.Std WP Result ControlFlow
open verified.merc_utilities.tagged_index (TagIndex)
open verified.merc_lts.lts (StateTag LabelTag Transition LTS)
open verified.merc_collections.indexed_partition (BlockTag)
open verified.merc_reduction.block_partition (BlockPartition BlockPartitionBuilder)

open MercVerified.Lts.Proofs
open MercVerified.Refinement

namespace MercVerified.Refinement.Proofs

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

open Classical

/-- The state with index `a`. -/
def stOf {n : Nat} (a : Fin n) : ST := uTag a.val

theorem stOf_index {n : Nat} (a : Fin n) (hn : n ≤ Usize.max) : (stOf a).index.val = a.val := by
  unfold stOf uTag
  show (uTotal a.val).val = _
  exact uTotal_val_of_lt (by have := usize_max_succ; have := a.2; omega)

/-- The abstract LTS on the states `Fin n` of an `LTS` implementor. -/
def aLTS {L Label : Type} (LTSInst : LTS L Label) (sys : L) (n : Nat) :
    Cslib.LTS (Fin n) (TagIndex Std.Usize LabelTag) where
  Tr a μ b := MercVerified.Lts.tr LTSInst sys (stOf a) μ (stOf b)

/-- The block data of a concrete partition. -/
def bdOf (p : BlockPartition) (n : Nat) : Sigref.BD n :=
  ⟨fun a => e2bAt p a.val, fun a => IsMarked p a.val⟩

/-- The `state_to_key` array read as a function on `Fin n`. -/
def keyOf {n : Nat} (stk : VecTy BT) : Fin n → Nat := fun a => (stk.val.getD a.val zBT).index.val

/-- The abstract flat signature represented by a sorted entry list: the entries whose label is not
the hat label are visible entries, the others hat entries carrying keys. -/
def decodeSig (nl : Nat) (l : List SigEntry) : Sigref.KSig (TagIndex Std.Usize LabelTag) where
  vis := {e | ∃ x ∈ l, x.1.index.val ≠ nl ∧ e = (x.1, x.2.index.val)}
  hat := {k | ∃ x ∈ l, x.1.index.val = nl ∧ k = x.2.index.val}

/-- The abstract key-computation state of the concrete `state_to_key` and `key_to_signature`. -/
def absOf {n : Nat} (nl : Nat) (stk : VecTy BT) (kts : VecTy SigKey) :
    Sigref.KC n (TagIndex Std.Usize LabelTag) :=
  ⟨keyOf stk, kts.val.map (fun v => decodeSig nl v.val)⟩

/-- What the key computation needs of the `LTS` implementor and its labels. -/
structure CEnv {L Label : Type} (LTSInst : LTS L Label) (sys : L) (nl : Std.Usize) : Prop where
  num : LTSInst.num_of_labels sys = ok nl
  hid : ∀ l : TagIndex Std.Usize LabelTag,
    LTSInst.is_hidden_label sys l = ok (decide (l.index.val = 0))
  lab : ∀ s μ s', MercVerified.Lts.tr LTSInst sys s μ s' → μ.index.val < nl.val

theorem tr_iff_mem {L Label : Type} {LTSInst : LTS L Label} {sys : L} {s : ST}
    {ts : alloc.vec.Vec Transition} (h : LTSInst.outgoing_transitions sys s = ok ts)
    (μ : TagIndex Std.Usize LabelTag) (s' : ST) :
    MercVerified.Lts.tr LTSInst sys s μ s' ↔ ({ label := μ, «to» := s' } : Transition) ∈ ts.val := by
  constructor
  · rintro ⟨ts', hts', hmem⟩
    have : ts' = ts := by simpa [Result.ok.injEq] using hts'.symm.trans h
    subst this; exact hmem
  · intro hmem; exact ⟨ts, h, hmem⟩

theorem label_eq_tau_iff (l : TagIndex Std.Usize LabelTag) :
    l = (Cslib.HasTau.τ : TagIndex Std.Usize LabelTag) ↔ l.index.val = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply merc_utilities.tagged_index.TagIndex.ext
    exact UScalar.eq_of_val_eq h

theorem bt_eq_iff (a b : BT) : a = b ↔ a.index.val = b.index.val :=
  ⟨fun h => by rw [h], fun h => merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq h)⟩

/-- **The concrete flat signature is `Sigref.RP.flatSig`.** -/
theorem decode_brEntries {L Label : Type} (LTSInst : LTS L Label) (sys : L) {nl : Std.Usize}
    (hE : CEnv LTSInst sys nl) {n : Nat} (hn : n ≤ Usize.max) (s : Fin n)
    (ts : alloc.vec.Vec Transition) (hout : LTSInst.outgoing_transitions sys (stOf s) = ok ts)
    (htgt : ∀ t ∈ ts.val, t.to.index.val < n) (p : BlockPartition) (stk : VecTy BT) :
    decodeSig nl.val (ts.val.map (brEntry ({ index := nl, marker := () } : TagIndex Std.Usize LabelTag)
        (fun t => p.element_to_block.val.getD t.index.val zBT)
        (fun l => decide (l.index.val = 0)) (fun t => decide (IsMarked p t.index.val))
        (fun t => stk.val.getD t.index.val zBT) (stOf s)))
      = Sigref.RP.flatSig (aLTS LTSInst sys n) (bdOf p n).blk (bdOf p n).Dirty (keyOf stk) s := by
  have hlabt : ∀ t ∈ ts.val, t.label.index.val < nl.val := fun t ht =>
    hE.lab _ _ _ ((tr_iff_mem hout t.label t.to).2 (by cases t; exact ht))
  -- targets as `Fin n`
  let tf : ∀ t ∈ ts.val, Fin n := fun t ht => ⟨t.to.index.val, htgt t ht⟩
  have hst : ∀ (t : Transition) (ht : t ∈ ts.val), stOf (tf t ht) = t.to := by
    intro t ht
    apply merc_utilities.tagged_index.TagIndex.ext
    apply UScalar.eq_of_val_eq
    rw [stOf_index _ hn]
  have hbn : ∀ (a : Fin n), (p.element_to_block.val.getD (stOf a).index.val zBT).index.val = e2bAt p a.val := by
    intro a; rw [stOf_index _ hn]; rfl
  have hcond : ∀ (t : Transition) (ht : t ∈ ts.val),
      (p.element_to_block.val.getD (stOf s).index.val zBT = p.element_to_block.val.getD t.to.index.val zBT ∧
        decide (t.label.index.val = 0) = true ∧ decide (IsMarked p t.to.index.val) = true) ↔
      (t.label = Cslib.HasTau.τ ∧ (bdOf p n).blk (tf t ht) = (bdOf p n).blk s ∧ (bdOf p n).Dirty (tf t ht)) := by
    intro t ht
    rw [bt_eq_iff, label_eq_tau_iff]
    simp only [decide_eq_true_eq, bdOf]
    rw [hbn s]
    have : e2bAt p (tf t ht).val = (p.element_to_block.val.getD t.to.index.val zBT).index.val := rfl
    rw [this]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1.symm, h3⟩
    · rintro ⟨h2, h1, h3⟩; exact ⟨h1.symm, h2, h3⟩
  have hTr : ∀ (a : TagIndex Std.Usize LabelTag) (t' : Fin n),
      (aLTS LTSInst sys n).Tr s a t' ↔ ∃ t ∈ ts.val, t.label = a ∧ t.to = stOf t' := by
    intro a t'
    show MercVerified.Lts.tr LTSInst sys (stOf s) a (stOf t') ↔ _
    rw [tr_iff_mem hout]
    constructor
    · intro h; exact ⟨_, h, rfl, rfl⟩
    · rintro ⟨t, ht, h1, h2⟩
      have : t = { label := a, «to» := stOf t' } := by cases t; simp_all
      rw [← this]; exact ht
  have hFin : ∀ (t : Transition) (ht : t ∈ ts.val) (t' : Fin n), t.to = stOf t' → tf t ht = t' := by
    intro t ht t' h
    apply Fin.ext
    show t.to.index.val = t'.val
    rw [h, stOf_index _ hn]
  unfold decodeSig Sigref.RP.flatSig
  congr 1
  · ext ⟨a, β⟩
    constructor
    · rintro ⟨x, hx, hx1, hx2⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      by_cases hc : (p.element_to_block.val.getD (stOf s).index.val zBT =
          p.element_to_block.val.getD t.to.index.val zBT ∧
          decide (t.label.index.val = 0) = true ∧ decide (IsMarked p t.to.index.val) = true)
      · exfalso; apply hx1; simp only [brEntry, if_pos hc]
      · simp only [brEntry, if_neg hc] at hx1 hx2
        refine ⟨t.label, tf t ht, (hTr _ _).2 ⟨t, ht, rfl, (hst t ht).symm⟩,
          fun h => hc ((hcond t ht).2 h), ?_⟩
        rw [hx2]; rfl
    · rintro ⟨a', t', hTr', hnc, he⟩
      obtain ⟨t, ht, h1, h2⟩ := (hTr _ _).1 hTr'
      have hf := hFin t ht t' h2
      have hc : ¬ (p.element_to_block.val.getD (stOf s).index.val zBT =
          p.element_to_block.val.getD t.to.index.val zBT ∧
          decide (t.label.index.val = 0) = true ∧ decide (IsMarked p t.to.index.val) = true) := by
        intro hc
        apply hnc
        rw [← h1, ← hf]
        exact (hcond t ht).1 hc
      refine ⟨_, List.mem_map.2 ⟨t, ht, rfl⟩, ?_, ?_⟩
      · simp only [brEntry, if_neg hc]; exact ne_of_lt (hlabt t ht)
      · simp only [brEntry, if_neg hc]
        rw [he, ← h1, ← hf]; rfl
  · ext k
    constructor
    · rintro ⟨x, hx, hx1, hx2⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      by_cases hc : (p.element_to_block.val.getD (stOf s).index.val zBT =
          p.element_to_block.val.getD t.to.index.val zBT ∧
          decide (t.label.index.val = 0) = true ∧ decide (IsMarked p t.to.index.val) = true)
      · simp only [brEntry, if_pos hc] at hx2
        have hc' := (hcond t ht).1 hc
        refine ⟨tf t ht, ?_, hc'.2.1, hc'.2.2, hx2⟩
        refine (hTr _ _).2 ⟨t, ht, ?_, (hst t ht).symm⟩
        exact hc'.1
      · simp only [brEntry, if_neg hc] at hx1
        exact absurd hx1 (ne_of_lt (hlabt t ht))
    · rintro ⟨t', hTr', hb, hd, hk⟩
      obtain ⟨t, ht, h1, h2⟩ := (hTr _ _).1 hTr'
      have hf := hFin t ht t' h2
      have hc : (p.element_to_block.val.getD (stOf s).index.val zBT =
          p.element_to_block.val.getD t.to.index.val zBT ∧
          decide (t.label.index.val = 0) = true ∧ decide (IsMarked p t.to.index.val) = true) := by
        apply (hcond t ht).2
        rw [hf]
        exact ⟨by rw [h1], hb, hd⟩
      refine ⟨_, List.mem_map.2 ⟨t, ht, rfl⟩, ?_, ?_⟩
      · simp only [brEntry, if_pos hc]
      · simp only [brEntry, if_pos hc]
        rw [hk, ← hf]; rfl

/-- The acceptance test of `renumber_branching` on the hat entry `e`. -/
def RnTest (_nl : Nat) (kts : List (List SigEntry)) (L : List SigEntry) (e : SigEntry) : Prop :=
  ∀ x ∈ L, x ≠ e → x ∈ kts.getD e.2.index.val []

/-- The scan returns the key of the hat entry with the largest key passing the test, and none if
no hat entry passes. -/
theorem rnScan_char (nl : Nat) (kts : List (List SigEntry)) (L : List SigEntry) :
    ∀ R : List SigEntry, (∀ e ∈ R, e.1.index.val ≤ nl) → (R.Pairwise (fun a b => entLt b a)) →
      (∀ c, rnScan nl kts L R = some c →
        (∃ e ∈ R, e.2 = c ∧ e.1.index.val = nl ∧ RnTest nl kts L e) ∧
          ∀ e ∈ R, e.1.index.val = nl → RnTest nl kts L e → e.2.index.val ≤ c.index.val) ∧
      (rnScan nl kts L R = none →
        ∀ e ∈ R, e.1.index.val = nl → ¬ RnTest nl kts L e) := by
  intro R
  induction R with
  | nil => intro _ _; exact ⟨fun c h => by simp [rnScan] at h, fun _ e he => absurd he (by simp)⟩
  | cons e rest ih =>
    intro hle hpw
    obtain ⟨hlt, hpw'⟩ := List.pairwise_cons.1 hpw
    have hle' : ∀ x ∈ rest, x.1.index.val ≤ nl := fun x hx => hle x (List.mem_cons_of_mem _ hx)
    obtain ⟨ih1, ih2⟩ := ih hle' hpw'
    by_cases hhat : e.1.index.val = nl
    · by_cases htest : RnTest nl kts L e
      · have htest' : ∀ x ∈ L, x ≠ e → x ∈ kts.getD e.2.index.val [] := htest
        have hscan : rnScan nl kts L (e :: rest) = some e.2 := by
          simp only [rnScan, if_pos hhat]
          rw [if_pos htest']
        refine ⟨fun c h => ?_, fun h => by rw [hscan] at h; simp at h⟩
        rw [hscan] at h
        obtain rfl := Option.some.inj h
        refine ⟨⟨e, List.mem_cons_self, rfl, hhat, htest⟩, fun x hx hxh _ => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_refl _
        · have := hlt x hx
          unfold entLt at this
          omega
      · have htest' : ¬ ∀ x ∈ L, x ≠ e → x ∈ kts.getD e.2.index.val [] := htest
        have hscan : rnScan nl kts L (e :: rest) = rnScan nl kts L rest := by
          simp only [rnScan, if_pos hhat]
          rw [if_neg htest']
        rw [hscan]
        refine ⟨fun c h => ?_, fun h x hx hxh => ?_⟩
        · obtain ⟨⟨e1, he1, he2, he3, he4⟩, d⟩ := ih1 c h
          refine ⟨⟨e1, List.mem_cons_of_mem _ he1, he2, he3, he4⟩, fun x hx hxh hxt => ?_⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact absurd hxt htest
          · exact d x hx hxh hxt
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact htest
          · exact ih2 h x hx hxh
    · have hscan : rnScan nl kts L (e :: rest) = none := by simp [rnScan, hhat]
      rw [hscan]
      refine ⟨fun c h => by simp at h, fun _ x hx hxh => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd hxh hhat
      · have := hlt x hx
        have h2 := hle e List.mem_cons_self
        unfold entLt at this
        omega

theorem entry_ext' {a b : SigEntry} (h1 : a.1 = b.1) (h2 : a.2.index.val = b.2.index.val) : a = b :=
  entry_ext (by rw [h1]) h2

/-- The acceptance test of the scan is `is_subset_excluding` of the abstract signatures. -/
theorem rnTest_iff (nl : Nat) (kts : List (List SigEntry)) (L : List SigEntry) (e : SigEntry)
    (_heL : e ∈ L) (hhat : e.1.index.val = nl) (hk : e.2.index.val < kts.length) :
    RnTest nl kts L e ↔
      Sigref.RP.SubsetExcl ((kts.map (decodeSig nl))[e.2.index.val]'(by simpa using hk))
        (decodeSig nl L) e.2.index.val := by
  have hget : (kts.map (decodeSig nl))[e.2.index.val]'(by simpa using hk) =
      decodeSig nl (kts[e.2.index.val]'hk) := by simp
  have hgd : kts.getD e.2.index.val [] = kts[e.2.index.val]'hk := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rw [hget]
  unfold RnTest Sigref.RP.SubsetExcl
  rw [hgd]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨l, β⟩ ⟨x, hx, hx1, hx2⟩
      have hne : x ≠ e := fun h' => hx1 (by rw [h', hhat])
      exact ⟨x, h x hx hne, hx1, hx2⟩
    · rintro k ⟨hk1, hk2⟩
      obtain ⟨x, hx, hx1, rfl⟩ := hk1
      have hne : x ≠ e := fun h' => hk2 (by rw [h']; rfl)
      exact ⟨x, h x hx hne, hx1, rfl⟩
  · rintro ⟨h1, h2⟩ x hx hne
    by_cases hxl : x.1.index.val = nl
    · have hx1e : x.1 = e.1 :=
        merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (hxl.trans hhat.symm))
      have hk' : x.2.index.val ≠ e.2.index.val := fun h' => hne (entry_ext' hx1e h')
      obtain ⟨y, hy, hy1, hy2⟩ := h2 ⟨⟨x, hx, hxl, rfl⟩, hk'⟩
      have hy1e : y.1 = x.1 :=
        merc_utilities.tagged_index.TagIndex.ext (UScalar.eq_of_val_eq (hy1.trans hxl.symm))
      have : y = x := entry_ext' hy1e hy2.symm
      rwa [this] at hy
    · obtain ⟨y, hy, hy1, hy2⟩ := h1 ⟨x, hx, hxl, rfl⟩
      obtain ⟨hyx1, hyx2⟩ := Prod.mk.inj hy2
      have : y = x := entry_ext' hyx1.symm hyx2.symm
      rwa [this] at hy

/-- **The backwards scan is the abstract `renumber`.** -/
theorem rnScan_renumber (nl : Nat) (kts : List (List SigEntry)) (L : List SigEntry)
    (hL : List.Pairwise entLt L) (hle : ∀ e ∈ L, e.1.index.val ≤ nl)
    (hkeys : ∀ e ∈ L, e.1.index.val = nl → e.2.index.val < kts.length) :
    (rnScan nl kts L L.reverse).map (fun c => c.index.val) =
      Sigref.RP.renumber (kts.map (decodeSig nl)) (decodeSig nl L) := by
  have hR : L.reverse.Pairwise (fun a b => entLt b a) := by
    rw [List.pairwise_reverse]; exact hL
  have hRle : ∀ e ∈ L.reverse, e.1.index.val ≤ nl := fun e he => hle e (List.mem_reverse.1 he)
  obtain ⟨hc1, hc2⟩ := rnScan_char nl kts L L.reverse hRle hR
  have hmem_hat : ∀ k, k ∈ (decodeSig nl L).hat ↔ ∃ x ∈ L, x.1.index.val = nl ∧ k = x.2.index.val :=
    fun k => Iff.rfl
  unfold Sigref.RP.renumber
  cases hscan : rnScan nl kts L L.reverse with
  | none =>
    rw [dif_neg]
    · rfl
    · rintro ⟨k, hk, hkh, hsub⟩
      obtain ⟨x, hx, hx1, rfl⟩ := (hmem_hat k).1 hkh
      have hxk := hkeys x hx hx1
      have := (rnTest_iff nl kts L x hx hx1 hxk).2 hsub
      exact hc2 hscan x (List.mem_reverse.2 hx) hx1 this
  | some c =>
    obtain ⟨⟨e, he, hec, he1, het⟩, hmax⟩ := hc1 c hscan
    have heL := List.mem_reverse.1 he
    have hek := hkeys e heL he1
    let P : Nat → Prop := fun k => ∃ hk : k < (kts.map (decodeSig nl)).length,
      k ∈ (decodeSig nl L).hat ∧ Sigref.RP.SubsetExcl ((kts.map (decodeSig nl))[k]) (decodeSig nl L) k
    have hk0 : e.2.index.val < (kts.map (decodeSig nl)).length := by simpa using hek
    have hPk0 : P e.2.index.val :=
      ⟨hk0, (hmem_hat _).2 ⟨e, heL, he1, rfl⟩, (rnTest_iff nl kts L e heL he1 hek).1 het⟩
    have hex : ∃ k, ∃ hk : k < (kts.map (decodeSig nl)).length, k ∈ (decodeSig nl L).hat ∧
        Sigref.RP.SubsetExcl ((kts.map (decodeSig nl))[k]) (decodeSig nl L) k := ⟨_, hPk0⟩
    rw [dif_pos hex]
    simp only [Option.map_some]
    congr 1
    have hspec := Nat.findGreatest_spec (P := P) (m := e.2.index.val)
      (n := (kts.map (decodeSig nl)).length) hk0.le hPk0
    have h2 : e.2.index.val ≤ Nat.findGreatest P (kts.map (decodeSig nl)).length :=
      Nat.le_findGreatest hk0.le hPk0
    generalize Nat.findGreatest P (kts.map (decodeSig nl)).length = fg at hspec h2 ⊢
    obtain ⟨hkf, hhf, hsf⟩ := hspec
    obtain ⟨x, hx, hx1, hxk⟩ := (hmem_hat _).1 hhf
    subst hxk
    have hxk' := hkeys x hx hx1
    have htest := (rnTest_iff nl kts L x hx hx1 hxk').2 hsf
    have h1 := hmax x (List.mem_reverse.2 hx) hx1 htest
    have hc' : c.index.val = e.2.index.val := by rw [← hec]
    omega

open verified.merc_reduction.signature_refinement in
/-- **`branching_signature_index`**: the backwards scan, falling back to interning. -/
theorem bsi_eq {L Label : Type} (LTSInst : LTS L Label) (sys : L) {nl : Std.Usize}
    (hnl : LTSInst.num_of_labels sys = ok nl) (id : InternMap) (kts : VecTy SigKey)
    (sigb : SigKey) (hsig : List.Pairwise entLt sigb.val)
    (hkts : ∀ v ∈ kts.val, List.Pairwise entLt v.val)
    (hkeys : ∀ e ∈ sigb.val, e.1.index.val = nl.val → e.2.index.val < kts.val.length) :
    branching_signature_index LTSInst sys id kts sigb =
      (match rnScan nl.val (kts.val.map (·.val)) sigb.val sigb.val.reverse with
        | none => strong_intern_signature id kts sigb
        | some key => ok (key, id, kts)) := by
  unfold branching_signature_index
  obtain ⟨r, hr, hreq⟩ := renumber_branching_spec LTSInst sys nl hnl (alloc.vec.Vec.deref sigb) kts
    (by simpa [alloc.vec.Vec.deref] using hsig) hkts
    (by simpa [alloc.vec.Vec.deref] using hkeys)
  show (do
    let o ← renumber_branching LTSInst sys (alloc.vec.Vec.deref sigb) kts
    match o with
      | none => strong_intern_signature id kts sigb
      | some key => ok (key, id, kts)) = _
  rw [hr]
  have hd : (alloc.vec.Vec.deref sigb).val = sigb.val := by simp [alloc.vec.Vec.deref]
  have hr2 : r = rnScan nl.val (kts.val.map (·.val)) sigb.val sigb.val.reverse := by
    rw [hreq, hd]
  rw [← hr2]
  cases r <;> simp

theorem kcRun_snoc {n : Nat} {Label : Type} [Cslib.HasTau Label] (lts : Cslib.LTS (Fin n) Label)
    (blk : Fin n → ℕ) (dirty : Fin n → Prop) (l : List (Fin n)) (z : Fin n) (st : Sigref.KC n Label) :
    Sigref.RP.kcRun lts blk dirty (l ++ [z]) st =
      Sigref.RP.kcStep lts blk dirty (Sigref.RP.kcRun lts blk dirty l st) z := by
  unfold Sigref.RP.kcRun
  rw [List.foldl_append]; rfl

/-- Writing `idx` into `state_to_key[i]` updates `keyOf` at `z = i`. -/
theorem keyOf_set {n : Nat} (stk : VecTy BT) (z : Fin n) (i : Std.Usize) (idx : BT)
    (hzi : z.val = i.val) (hz : i.val < stk.val.length) :
    keyOf (n := n) ({ slice := stk.slice.set i idx } : VecTy BT) =
      Function.update (keyOf stk) z idx.index.val := by
  have hval : ({ slice := stk.slice.set i idx } : VecTy BT).val = stk.val.set i.val idx := by
    show (stk.slice.set i idx).val = _
    rw [Slice.set_val_eq]; rfl
  funext a
  unfold keyOf
  rw [hval]
  by_cases haz : a = z
  · subst haz
    rw [Function.update_self, List.getD_eq_getElem?_getD, hzi, List.getElem?_set_self hz]
    rfl
  · rw [Function.update_of_ne haz, List.getD_eq_getElem?_getD, List.getElem?_set_ne,
      ← List.getD_eq_getElem?_getD]
    intro h
    exact haz (Fin.ext (by rw [← h, hzi]))

/-- Indexing a slice by a tagged `usize`. -/
theorem slice_tagged_index_ok {U Tag : Type} (s : Slice U) (t : TagIndex Std.Usize Tag)
    (h : t.index.val < s.val.length) :
    verified.Slice.Insts.CoreOpsIndexIndexTagIndexU.index core.marker.CopyUsize
      (core.slice.index.SliceIndexUsizeSlice U) s t = ok (s.val[t.index.val]'h) := by
  unfold verified.Slice.Insts.CoreOpsIndexIndexTagIndexU.index
  simp only [tag_value_id, bind_ok]
  have := slice_index_ok s t.index h
  simpa [core.slice.index.Slice.index, core.slice.index.Usize.index] using this

open verified.merc_reduction.signature_refinement in
theorem bpme_body_done {L Label : Type} (LTSInst : LTS L Label) (sys : L) (partition : BlockPartition)
    (id : InternMap) (kts : VecTy SigKey) (sigb : SigKey) (spb : BlockPartitionBuilder)
    (stk : VecTy BT) (ei : Sz) (hge : spb.old_elements.val.length ≤ ei.val) :
    branching_process_marked_elements_loop.body LTSInst sys partition id kts sigb spb stk ei
      = ok (done (id, kts, sigb, spb.index_to_block, spb.block_sizes, spb.old_elements, stk)) := by
  unfold branching_process_marked_elements_loop.body
  simp [hge]

open verified.merc_reduction.signature_refinement in
theorem bpme_body_some {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (partition : BlockPartition) (id : InternMap) (kts : VecTy SigKey) (sigb : SigKey)
    (spb : BlockPartitionBuilder) (stk : VecTy BT) (ei : Sz)
    (hlt : ei.val < spb.old_elements.val.length) (state_index : ST)
    (hsid : spb.old_elements.index_usize ei = ok state_index)
    (sigb1 : SigKey)
    (hsig : verified.merc_reduction.signatures.branching_bisim_signature_inductive LTSInst
      state_index sys partition (alloc.vec.Vec.deref stk) sigb = ok sigb1)
    (index : BT) (id1 : InternMap) (kts1 : VecTy SigKey)
    (hidx : branching_signature_index LTSInst sys id kts sigb1 = ok (index, id1, kts1))
    (hmut1 : BT → VecTy BT)
    (hmut1ok : ∃ x : BT, spb.index_to_block.index_mut_usize ei = ok (x, hmut1))
    (v : VecTy Sz) (hcount : count_block_occurrence spb.block_sizes index = ok v)
    (hmut2 : BT → VecTy BT)
    (hmut2ok : ∃ x : BT, verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut
      core.marker.CopyUsize (core.slice.index.SliceIndexUsizeSlice BT) stk state_index
      = ok (x, hmut2))
    (ei1 : Sz) (hadd : ei + 1#usize = ok ei1) :
    branching_process_marked_elements_loop.body LTSInst sys partition id kts sigb spb stk ei
      = ok (cont (id1, kts1, sigb1,
          { spb with index_to_block := hmut1 index, block_sizes := v }, hmut2 index, ei1)) := by
  unfold branching_process_marked_elements_loop.body
  simp [hlt]
  rw [hsid]
  simp
  rw [hsig]
  simp
  rw [hidx]
  simp
  rcases hmut1ok with ⟨_, hmut1ok'⟩
  rw [hmut1ok']
  simp
  rw [hcount]
  simp
  rcases hmut2ok with ⟨_, hmut2ok'⟩
  rw [hmut2ok']
  simp
  rw [hadd]
  simp

theorem decodeSig_congr (nl : Nat) {l l' : List SigEntry} (h : ∀ e, e ∈ l ↔ e ∈ l') :
    decodeSig nl l = decodeSig nl l' := by
  unfold decodeSig
  congr 1
  · ext e
    constructor
    · rintro ⟨x, hx, h1, h2⟩; exact ⟨x, (h x).1 hx, h1, h2⟩
    · rintro ⟨x, hx, h1, h2⟩; exact ⟨x, (h x).2 hx, h1, h2⟩
  · ext k
    constructor
    · rintro ⟨x, hx, h1, h2⟩; exact ⟨x, (h x).1 hx, h1, h2⟩
    · rintro ⟨x, hx, h1, h2⟩; exact ⟨x, (h x).2 hx, h1, h2⟩

theorem mem_of_decode_eq (nl : Nat) {l l' : List SigEntry} (h : decodeSig nl l = decodeSig nl l') :
    ∀ e ∈ l, e ∈ l' := by
  intro e he
  by_cases hl : e.1.index.val = nl
  · have : e.2.index.val ∈ (decodeSig nl l).hat := ⟨e, he, hl, rfl⟩
    rw [h] at this
    obtain ⟨y, hy, hy1, hy2⟩ := this
    have : y = e := entry_ext' (merc_utilities.tagged_index.TagIndex.ext
      (UScalar.eq_of_val_eq (hy1.trans hl.symm))) hy2.symm
    rwa [this] at hy
  · have : (e.1, e.2.index.val) ∈ (decodeSig nl l).vis := ⟨e, he, hl, rfl⟩
    rw [h] at this
    obtain ⟨y, hy, hy1, hy2⟩ := this
    obtain ⟨h1, h2⟩ := Prod.mk.inj hy2
    have : y = e := entry_ext' h1.symm h2.symm
    rwa [this] at hy

/-- The abstract signature determines a sorted entry list. -/
theorem decodeSig_inj (nl : Nat) {l l' : List SigEntry} (hl : List.Pairwise entLt l)
    (hl' : List.Pairwise entLt l') (h : decodeSig nl l = decodeSig nl l') : l = l' :=
  sigKey_unique hl hl' (fun e => ⟨mem_of_decode_eq nl h e, mem_of_decode_eq nl h.symm e⟩)

/-- Interning a signature that is stored at `i` in a duplicate-free table returns `i`. -/
theorem intern_found {Label : Type} (tbl : List (Sigref.KSig Label)) (sg : Sigref.KSig Label)
    (hnd : tbl.Nodup) (i : Nat) (hi : i < tbl.length) (hs : tbl[i] = sg) :
    Sigref.RP.intern tbl sg = (i, tbl) := by
  unfold Sigref.RP.intern
  have hex : ∃ k, ∃ hk : k < tbl.length, tbl[k] = sg := ⟨i, hi, hs⟩
  rw [dif_pos hex]
  have hk := hex.choose_spec.choose_spec
  have hkl := hex.choose_spec.choose
  have : hex.choose = i := by
    have := (List.Nodup.getElem_inj_iff hnd).1 (hk.trans hs.symm)
    exact this
  rw [this]

theorem intern_new {Label : Type} (tbl : List (Sigref.KSig Label)) (sg : Sigref.KSig Label)
    (hnew : ∀ i, ∀ hi : i < tbl.length, tbl[i] ≠ sg) :
    Sigref.RP.intern tbl sg = (tbl.length, tbl ++ [sg]) := by
  unfold Sigref.RP.intern
  have hex : ¬ ∃ k, ∃ hk : k < tbl.length, tbl[k] = sg := fun ⟨k, hk, h⟩ => hnew k hk h
  rw [dif_neg hex]

/-- In a strictly sorted list, an element smaller than `l[m]` occurs before position `m`. -/
theorem before_of_lt {α : Type} (f : α → Nat) {l : List α} (hl : List.Pairwise (fun a c => f a < f c) l)
    {m : Nat} (hm : m < l.length) {x : α} (hx : x ∈ l) (hlt : f x < f (l[m]'hm)) :
    ∃ j, ∃ hj : j < m, l[j]'(by omega) = x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  by_cases hjm : j < m
  · exact ⟨j, hjm, rfl⟩
  · exfalso
    rcases Nat.eq_or_lt_of_le (not_lt.1 hjm) with h | h
    · subst h; exact lt_irrefl _ hlt
    · have := (List.pairwise_iff_getElem.1 hl) m j hm hj h
      omega

theorem stk_set_getD (stk : VecTy BT) (i : Std.Usize) (idx : BT) (hi : i.val < stk.val.length) (a : Nat) :
    (({ slice := stk.slice.set i idx } : VecTy BT).val.getD a zBT) =
      if a = i.val then idx else stk.val.getD a zBT := by
  have hval : ({ slice := stk.slice.set i idx } : VecTy BT).val = stk.val.set i.val idx := by
    show (stk.slice.set i idx).val = _
    rw [Slice.set_val_eq]; rfl
  rw [hval]
  by_cases ha : a = i.val
  · subst ha
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self hi]; rfl
  · rw [if_neg ha, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm ha),
      ← List.getD_eq_getElem?_getD]

/-- Concrete topological order: inert τ-steps go to a state with a smaller index. -/
def ConcTopo {L Label : Type} (LTSInst : LTS L Label) (sys : L) : Prop :=
  ∀ s μ t, MercVerified.Lts.tr LTSInst sys s μ t → μ.index.val = 0 → t.index.val < s.index.val

/-- The state with index `s mod n`. -/
def toFin {n : Nat} (hn0 : 0 < n) (s : ST) : Fin n := ⟨s.index.val % n, Nat.mod_lt _ hn0⟩

/-- The abstract initial key-computation state. -/
def absInit {n : Nat} (stk0 : VecTy BT) : Sigref.KC n (TagIndex Std.Usize LabelTag) :=
  ⟨keyOf stk0, []⟩

/-- The semantic loop invariant of `branching_process_marked_elements` after `m` elements. -/
structure BrSem {L Label : Type} (LTSInst : LTS L Label) (sys : L) (nl : Std.Usize) {n : Nat}
    (hn0 : 0 < n) (p : BlockPartition) (olds : VecTy ST) (m : Nat) (stk0 stk : VecTy BT)
    (id : InternMap) (kts : VecTy SigKey) (spb : BlockPartitionBuilder) : Prop where
  idinv : IdInv id kts
  sorted : ∀ v ∈ kts.val, List.Pairwise entLt v.val ∧ ∀ e ∈ v.val, e.1.index.val ≤ nl.val
  abs : absOf nl.val stk kts =
    Sigref.RP.kcRun (aLTS LTSInst sys n) (bdOf p n).blk (bdOf p n).Dirty
      ((olds.val.take m).map (toFin hn0)) (absInit stk0)
  keysLt : ∀ t, t < m →
    (stk.val.getD (olds.val.getD t zST).index.val zBT).index.val < kts.val.length
  cls : ∀ t, t < m → clsAt spb t = (stk.val.getD (olds.val.getD t zST).index.val zBT).index.val

open verified.merc_reduction.signature_refinement in
/-- One iteration of the key-computation loop. -/
theorem bpme_step {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (nU : Sz) (hns : LTSInst.num_of_states sys = ok nU) (hn0 : 0 < nU.val)
    {nl : Std.Usize} (hE : CEnv LTSInst sys nl) (htopo : ConcTopo LTSInst sys)
    {p : BlockPartition} (hp : PartInv nU.val p) (b : Nat) {olds : VecTy ST} {m : Nat}
    {id : InternMap} {kts : VecTy SigKey} {sigb : SigKey} {spb : BlockPartitionBuilder}
    {stk0 stk : VecTy BT} {ei : Sz}
    (hold : ∀ x ∈ olds.val, x.index.val < nU.val)
    (hsorted : List.Pairwise (fun a c => a.index.val < c.index.val) olds.val)
    (hmem : ∀ x : ST, x.index.val < nU.val →
      ((e2bAt p x.index.val = b ∧ IsMarked p x.index.val) ↔ x ∈ olds.val))
    (hinv : SpmeInv nU.val olds m id kts spb stk ei) (hsem : BrSem LTSInst sys nl hn0 p olds m stk0 stk id kts spb)
    (hm : m < olds.val.length) :
    ∃ id1 kts1 sigb1 spb1 stk1 ei1,
      branching_process_marked_elements_loop.body LTSInst sys p id kts sigb spb stk ei
        = ok (cont (id1, kts1, sigb1, spb1, stk1, ei1)) ∧
      SpmeInv nU.val olds (m + 1) id1 kts1 spb1 stk1 ei1 ∧
      BrSem LTSInst sys nl hn0 p olds (m + 1) stk0 stk1 id1 kts1 spb1 := by
  have hnmax : nU.val ≤ Usize.max := by scalar_tac
  have hold' := hinv.old
  have hlt : ei.val < spb.old_elements.val.length := by rw [hold', hinv.ei_eq]; exact hm
  obtain ⟨state_index, hsid, hsval⟩ := spec_imp_exists
    (alloc.vec.Vec.index_usize_spec spb.old_elements ei hlt)
  have hsi : state_index ∈ olds.val := by
    rw [hsval, ← hold']; exact List.getElem_mem _
  have hsi_lt := hold _ hsi
  have holdsm : state_index = olds.val[m]'hm := by
    rw [hsval]
    subst hold'
    simp [hinv.ei_eq]
  obtain ⟨ts, hout, htgt⟩ := hwf.2.1 nU hns state_index hsi_lt
  -- the abstract view of the current state
  set z : Fin nU.val := toFin hn0 state_index with hz
  have hzval : z.val = state_index.index.val := by
    show state_index.index.val % nU.val = _
    exact Nat.mod_eq_of_lt hsi_lt
  have hstz : stOf z = state_index := by
    apply merc_utilities.tagged_index.TagIndex.ext
    apply UScalar.eq_of_val_eq
    rw [stOf_index _ hnmax, hzval]
  -- the calls of the signature function succeed
  have hlenstk : stk.val.length = nU.val := hinv.len_stk
  have hbrok : BrOk LTSInst sys p (alloc.vec.Vec.deref stk) state_index
      (fun t => p.element_to_block.val.getD t.index.val zBT)
      (fun l => decide (l.index.val = 0)) (fun t => decide (IsMarked p t.index.val))
      (fun t => stk.val.getD t.index.val zBT)
      ({ index := nl, marker := () } : TagIndex Std.Usize LabelTag) ts.val := by
    refine ⟨block_number_ok hp state_index hsi_lt, fun t ht => block_number_ok hp t.to (htgt t ht),
      fun t _ => hE.hid t.label, fun t ht => is_element_marked_ok hp t.to (htgt t ht), ?_,
      tau_hat_ok LTSInst sys nl hE.num⟩
    intro t ht
    have h1 : t.to.index.val < (alloc.vec.Vec.deref stk).val.length := by
      simp [alloc.vec.Vec.deref, hlenstk]; exact htgt t ht
    have h2 : t.to.index.val < stk.val.length := by rw [hlenstk]; exact htgt t ht
    rw [slice_tagged_index_ok _ _ h1]
    congr 1
    simp [alloc.vec.Vec.deref, List.getElem?_eq_getElem h2]
  obtain ⟨sigb1, hsig, hkmem, hksort⟩ := branching_signature_key LTSInst sys p
    (alloc.vec.Vec.deref stk) state_index ts hout hbrok sigb
  obtain ⟨sigb1, hsig, hkmem, hksort⟩ := branching_signature_key LTSInst sys p
    (alloc.vec.Vec.deref stk) state_index ts hout hbrok sigb
  have hoz : olds.val[m]'hm = state_index := holdsm.symm
  have hbz : e2bAt p state_index.index.val = b := ((hmem state_index hsi_lt).2 hsi).1
  have hlabt : ∀ t ∈ ts.val, t.label.index.val < nl.val := fun t ht =>
    hE.lab _ _ _ ((tr_iff_mem hout t.label t.to).2 (by cases t; exact ht))
  -- classification of the entries
  have hcls : ∀ e ∈ sigb1.val, (e.1.index.val < nl.val ∨ e.1.index.val = nl.val) ∧
      (e.1.index.val = nl.val → ∃ t ∈ ts.val, e.2 = stk.val.getD t.to.index.val zBT ∧
        p.element_to_block.val.getD state_index.index.val zBT =
          p.element_to_block.val.getD t.to.index.val zBT ∧
        decide (t.label.index.val = 0) = true ∧ decide (IsMarked p t.to.index.val) = true) := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ((hkmem e).1 he)
    by_cases hc : (p.element_to_block.val.getD state_index.index.val zBT =
        p.element_to_block.val.getD t.to.index.val zBT ∧
        decide (t.label.index.val = 0) = true ∧ decide (IsMarked p t.to.index.val) = true)
    · simp only [brEntry, if_pos hc]
      exact ⟨Or.inr (by simp), fun _ => ⟨t, ht, rfl, hc.1, hc.2.1, hc.2.2⟩⟩
    · simp only [brEntry, if_neg hc]
      refine ⟨Or.inl (hlabt t ht), fun h => absurd h (ne_of_lt (hlabt t ht))⟩
  have hle : ∀ e ∈ sigb1.val, e.1.index.val ≤ nl.val := fun e he => by
    rcases (hcls e he).1 with h | h <;> omega
  have hkeys : ∀ e ∈ sigb1.val, e.1.index.val = nl.val → e.2.index.val < kts.val.length := by
    intro e he hl
    obtain ⟨t, ht, he2, hbeq, hhid, hmk⟩ := (hcls e he).2 hl
    rw [he2]
    have hmk' : IsMarked p t.to.index.val := by simpa using hmk
    have hlab0 : t.label.index.val = 0 := by simpa using hhid
    have hbt : e2bAt p t.to.index.val = b := by
      have : (p.element_to_block.val.getD t.to.index.val zBT).index.val = e2bAt p t.to.index.val := rfl
      rw [← this, ← hbeq]; exact hbz
    have hto : t.to ∈ olds.val := (hmem t.to (htgt t ht)).1 ⟨hbt, hmk'⟩
    have hlt0 : t.to.index.val < (olds.val[m]'hm).index.val := by
      rw [hoz]
      exact htopo _ _ _ ((tr_iff_mem hout t.label t.to).2 (by cases t; exact ht)) hlab0
    obtain ⟨j, hj, hjv⟩ := before_of_lt (fun x : ST => x.index.val) hsorted hm hto hlt0
    have := hsem.keysLt j hj
    have hjl : j < olds.val.length := by omega
    rw [List.getD_eq_getElem _ _ hjl, hjv] at this
    exact this
  -- the abstract signature of the current state
  have hout' : LTSInst.outgoing_transitions sys (stOf z) = ok ts := by rw [hstz]; exact hout
  have hdec : decodeSig nl.val sigb1.val =
      Sigref.RP.flatSig (aLTS LTSInst sys nU.val) (bdOf p nU.val).blk (bdOf p nU.val).Dirty
        (keyOf stk) z := by
    rw [decodeSig_congr nl.val hkmem]
    have := decode_brEntries LTSInst sys hE hnmax z ts hout' htgt p stk
    rw [hstz] at this
    exact this
  have hbsi := bsi_eq LTSInst sys hE.num id kts sigb1 hksort
    (fun v hv => (hsem.sorted v hv).1) hkeys
  have hren := rnScan_renumber nl.val (kts.val.map (·.val)) sigb1.val hksort hle
    (by intro e he hl; simpa using hkeys e he hl)
  have hmapmap : (kts.val.map (·.val)).map (decodeSig nl.val) = (absOf (n := nU.val) nl.val stk kts).tbl := by
    simp [absOf, List.map_map, Function.comp_def]
  rw [hmapmap] at hren
  -- the abstract run
  have hrun : Sigref.RP.kcRun (aLTS LTSInst sys nU.val) (bdOf p nU.val).blk (bdOf p nU.val).Dirty
      ((olds.val.take (m + 1)).map (toFin hn0)) (absInit stk0) =
      Sigref.RP.kcStep (aLTS LTSInst sys nU.val) (bdOf p nU.val).blk (bdOf p nU.val).Dirty
        (absOf (n := nU.val) nl.val stk kts) z := by
    have htake : (olds.val.take (m + 1)).map (toFin hn0) = (olds.val.take m).map (toFin hn0) ++ [z] := by
      have hzo : z = toFin hn0 (olds.val[m]'hm) := by rw [hz, holdsm]
      rw [List.take_add_one, List.getElem?_eq_getElem hm, hzo]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    rw [htake, kcRun_snoc, ← hsem.abs]
  have hcasesA := Sigref.RP.kcStep_cases (lts := aLTS LTSInst sys nU.val) (rp := bdOf p nU.val)
    (absOf (n := nU.val) nl.val stk kts) z
  have hsg : Sigref.RP.fsig (aLTS LTSInst sys nU.val) (bdOf p nU.val)
      (absOf (n := nU.val) nl.val stk kts).key z = decodeSig nl.val sigb1.val := hdec.symm
  rw [hsg] at hcasesA
  -- structural facts about the mutations (as for the strong loop)
  have hm_i2b : ei.val < spb.index_to_block.val.length := by rw [hinv.len_i2b, hinv.ei_eq]; exact hm
  have hm_i2b' : m < spb.index_to_block.val.length := by rw [hinv.len_i2b]; exact hm
  have hstk_b : state_index.index.val < stk.val.length := by rw [hinv.len_stk]; exact hsi_lt
  have hmut1 := vec_index_mut_usize_ok spb.index_to_block ei hm_i2b
  have hmut2 := vec_tagged_index_mut_ok stk state_index hstk_b
  have hstk1 : ∀ u : BT, ({ slice := stk.slice.set state_index.index u } : VecTy BT).val.length
      = nU.val := by
    intro u
    show (stk.slice.set state_index.index u).val.length = _
    rw [Slice.set_val_eq]; simp only [List.length_set]; exact hinv.len_stk
  have hei1 : ∃ ei1 : Sz, ei + 1#usize = ok ei1 ∧ ei1.val = m + 1 := by
    obtain ⟨ei1, h1⟩ := add1_ok_of_lt_max ei (by rw [hinv.ei_eq]; have := hinv.olds_le; omega)
    exact ⟨ei1, h1, by rw [usize_add_one_val ei ei1 h1, hinv.ei_eq]⟩
  obtain ⟨ei1, hadd, hei1v⟩ := hei1
  have hlen_tbl : (absOf (n := nU.val) nl.val stk kts).tbl.length = kts.val.length := by
    simp [absOf]
  cases hscan : rnScan nl.val (kts.val.map (·.val)) sigb1.val sigb1.val.reverse with
  | some key0 =>
    have hren' : Sigref.RP.renumber (absOf (n := nU.val) nl.val stk kts).tbl (decodeSig nl.val sigb1.val)
        = some key0.index.val := by rw [← hren, hscan]; rfl
    have hbsi' : branching_signature_index LTSInst sys id kts sigb1 = ok (key0, id, kts) := by
      rw [hbsi, hscan]
    obtain ⟨hklt, -, -⟩ := Sigref.RP.renumber_some hren'
    have hidxlt : key0.index.val < kts.val.length := by omega
    obtain ⟨v, hcount, hinv'⟩ := spme_commit_old
      (stk1 := ({ slice := stk.slice.set state_index.index key0 } : VecTy BT)) (ei1 := ei1)
      hinv hm hnmax key0 hidxlt (hstk1 _) hei1v
    refine ⟨id, kts, sigb1, _, _, ei1, ?_, hinv', ?_⟩
    · exact bpme_body_some LTSInst sys p id kts sigb spb stk ei hlt state_index hsid sigb1 hsig
        key0 id kts hbsi' _ ⟨_, hmut1⟩ v hcount _ ⟨_, hmut2⟩ ei1 hadd
    · refine ⟨hsem.idinv, hsem.sorted, ?_, ?_, ?_⟩
      · rw [hrun]
        rcases hcasesA with ⟨k, hk, hst⟩ | ⟨hnone, -⟩
        · have hk' : k = key0.index.val := by
            rw [hren'] at hk; exact (Option.some.inj hk).symm
          rw [hst, hk']
          show absOf (n := nU.val) nl.val ({ slice := stk.slice.set state_index.index key0 } : VecTy BT) kts = _
          unfold absOf
          congr 1
          exact keyOf_set stk z state_index.index key0 hzval hstk_b
        · rw [hren'] at hnone; simp at hnone
      · intro t ht
        rw [stk_set_getD stk state_index.index key0 hstk_b]
        by_cases htm : t = m
        · subst htm
          rw [List.getD_eq_getElem _ _ hm, ← holdsm, if_pos rfl]
          exact hidxlt
        · have htm' : t < m := by omega
          have htl : t < olds.val.length := by omega
          have hne : (olds.val.getD t zST).index.val ≠ state_index.index.val := by
            rw [List.getD_eq_getElem _ _ htl, holdsm]
            have := (List.pairwise_iff_getElem.1 hsorted) t m htl hm htm'
            omega
          rw [if_neg hne]
          exact hsem.keysLt t htm'
      · intro t ht
        rw [clsAt_set spb ei m hinv.ei_eq key0 hm_i2b' v _ rfl t,
          stk_set_getD stk state_index.index key0 hstk_b]
        by_cases htm : t = m
        · subst htm
          rw [if_pos rfl, List.getD_eq_getElem _ _ hm, ← holdsm, if_pos rfl]
        · have htm' : t < m := by omega
          have htl : t < olds.val.length := by omega
          have hne : (olds.val.getD t zST).index.val ≠ state_index.index.val := by
            rw [List.getD_eq_getElem _ _ htl, holdsm]
            have := (List.pairwise_iff_getElem.1 hsorted) t m htl hm htm'
            omega
          rw [if_neg htm, if_neg hne]
          exact hsem.cls t htm'
  | none =>
    have hren' : Sigref.RP.renumber (absOf (n := nU.val) nl.val stk kts).tbl (decodeSig nl.val sigb1.val)
        = none := by rw [← hren, hscan]; rfl
    have hbsi' : branching_signature_index LTSInst sys id kts sigb1 =
        strong_intern_signature id kts sigb1 := by rw [hbsi, hscan]
    obtain ⟨o, ho⟩ := std.collections.hash.map.HashMap.get_key_value_ok internEqInst internHashInst
      internBuildHasher internEq_lawful internHash_total internBuildHasher_total id sigb1
    have hlt2 : kts.val.length < 2 ^ UScalarTy.Usize.numBits := by
      have := usize_max_succ; have := hinv.kts_le; have := hinv.m_le; have := hinv.olds_le; omega
    have hsortedE : ∀ v ∈ kts.val, List.Pairwise entLt v.val := fun v hv => (hsem.sorted v hv).1
    rcases o with _ | ⟨k, idx⟩
    · -- a new signature: it is interned at the end of the table
      have hlenK : kts.val.length < Usize.max := by
        have := hinv.kts_le; have := hinv.m_le; have := hinv.olds_le; omega
      obtain ⟨id1, kts1, hint, hk1, hlook, hall, hother⟩ :=
        strong_intern_signature_absent id kts sigb1 ho hlenK
      have hidx : ({ index := alloc.vec.Vec.len kts, marker := () } : BT).index.val = kts.val.length := by
        simp [alloc.vec.Vec.len]
      have hkts1 : kts1.val.length = kts.val.length + 1 := by rw [hk1]; simp
      have hids1 := hall (fun v => v.index.val < kts1.val.length)
        (fun q k v h => by have := hinv.ids q k v h; simp only []; omega)
        (by simp only []; rw [hidx]; omega)
      obtain ⟨idx0, hidx0⟩ : ∃ idx0 : BT, idx0 = { index := alloc.vec.Vec.len kts, marker := () } :=
        ⟨_, rfl⟩
      have hidx0t : idx0 = uTag kts.val.length := by rw [hidx0]; exact len_tag_eq kts
      rw [← hidx0] at hidx hint hlook
      obtain ⟨v, hcount, hinv'⟩ := spme_commit_new
        (stk1 := ({ slice := stk.slice.set state_index.index idx0 } : VecTy BT)) (ei1 := ei1)
        (kts1 := kts1) (id1 := id1) hinv hm hnmax _ hidx hkts1 hids1 (hstk1 _) hei1v
      have hbsi'' : branching_signature_index LTSInst sys id kts sigb1 = ok (idx0, id1, kts1) := by
        rw [hbsi', hint]
      refine ⟨id1, kts1, sigb1, _, _, ei1, ?_, hinv', ?_⟩
      · exact bpme_body_some LTSInst sys p id kts sigb spb stk ei hlt state_index hsid sigb1 hsig
          idx0 id1 kts1 hbsi'' _ ⟨_, hmut1⟩ v hcount _ ⟨_, hmut2⟩ ei1 hadd
      · have hlook' : internGet id1 sigb1 = ok (some (sigb1, uTag kts.val.length)) := by
          rw [← hidx0t]; exact hlook
        have hidinv := IdInv.new hsem.idinv ho hk1 hlook' hother hlt2
        -- no stored signature has the same abstract signature
        have hnew : ∀ i, ∀ hi : i < (absOf (n := nU.val) nl.val stk kts).tbl.length,
            (absOf (n := nU.val) nl.val stk kts).tbl[i] ≠ decodeSig nl.val sigb1.val := by
          intro i hi heq
          have hi' : i < kts.val.length := by omega
          have hget : (absOf (n := nU.val) nl.val stk kts).tbl[i] = decodeSig nl.val (kts.val[i]'hi').val := by
            simp [absOf]
          rw [hget] at heq
          have hveq := decodeSig_inj nl.val (hsortedE _ (List.getElem_mem hi')) hksort heq
          have hkeq : kts.val[i]'hi' = sigb1 := alloc.vec.Vec.ext _ _ hveq
          have := hsem.idinv.2 i hi'
          have ho' : internGet id sigb1 = ok none := ho
          rw [hkeq, ho'] at this
          simp at this
        refine ⟨hidinv, ?_, ?_, ?_, ?_⟩
        · intro w hw
          rw [hk1] at hw
          rcases List.mem_append.1 hw with h | h
          · exact hsem.sorted w h
          · rw [List.mem_singleton.1 h]; exact ⟨hksort, hle⟩
        · rw [hrun]
          rcases hcasesA with ⟨k, hk, -⟩ | ⟨-, hst⟩
          · rw [hren'] at hk; simp at hk
          · rw [hst, intern_new _ _ hnew]
            show absOf (n := nU.val) nl.val ({ slice := stk.slice.set state_index.index idx0 } : VecTy BT) kts1 = _
            unfold absOf
            congr 1
            · rw [keyOf_set stk z state_index.index idx0 hzval hstk_b]
              simp [hidx0, alloc.vec.Vec.len]
            · rw [hk1]; simp
        · intro t ht
          rw [stk_set_getD stk state_index.index idx0 hstk_b, hkts1]
          by_cases htm : t = m
          · subst htm
            rw [List.getD_eq_getElem _ _ hm, ← holdsm, if_pos rfl, hidx]; omega
          · have htm' : t < m := by omega
            have htl : t < olds.val.length := by omega
            have hne : (olds.val.getD t zST).index.val ≠ state_index.index.val := by
              rw [List.getD_eq_getElem _ _ htl, holdsm]
              have := (List.pairwise_iff_getElem.1 hsorted) t m htl hm htm'
              omega
            rw [if_neg hne]
            have := hsem.keysLt t htm'
            omega
        · intro t ht
          rw [clsAt_set spb ei m hinv.ei_eq idx0 hm_i2b' v _ rfl t,
            stk_set_getD stk state_index.index idx0 hstk_b]
          by_cases htm : t = m
          · subst htm
            rw [if_pos rfl, List.getD_eq_getElem _ _ hm, ← holdsm, if_pos rfl]
          · have htm' : t < m := by omega
            have htl : t < olds.val.length := by omega
            have hne : (olds.val.getD t zST).index.val ≠ state_index.index.val := by
              rw [List.getD_eq_getElem _ _ htl, holdsm]
              have := (List.pairwise_iff_getElem.1 hsorted) t m htl hm htm'
              omega
            rw [if_neg htm, if_neg hne]
            exact hsem.cls t htm'
    · -- a known signature: it was interned before
      obtain ⟨hkk, hv, hkv⟩ := hsem.idinv.1 sigb1 k idx ho
      have hidxlt := hinv.ids sigb1 k idx ho
      have hint := strong_intern_signature_found' id kts sigb1 k idx ho
      have hbsi'' : branching_signature_index LTSInst sys id kts sigb1 = ok (idx, id, kts) := by
        rw [hbsi', hint]
      have hlenkts : kts.val.length ≤ Usize.max := kts.property
      have hnd : (absOf (n := nU.val) nl.val stk kts).tbl.Nodup := by
        have hkn := hsem.idinv.nodup hlenkts
        simp only [absOf]
        refine List.Nodup.map_on ?_ hkn
        intro x hx y hy hxy
        exact alloc.vec.Vec.ext _ _ (decodeSig_inj nl.val (hsortedE x hx) (hsortedE y hy) hxy)
      have hget : (absOf (n := nU.val) nl.val stk kts).tbl[idx.index.val]'(by omega) =
          decodeSig nl.val sigb1.val := by
        have : (absOf (n := nU.val) nl.val stk kts).tbl[idx.index.val]'(by omega) =
            decodeSig nl.val (kts.val[idx.index.val]'hv).val := by simp [absOf]
        rw [this, hkv]
      have hintA := intern_found _ _ hnd idx.index.val (by omega) hget
      obtain ⟨v, hcount, hinv'⟩ := spme_commit_old
        (stk1 := ({ slice := stk.slice.set state_index.index idx } : VecTy BT)) (ei1 := ei1)
        hinv hm hnmax idx hidxlt (hstk1 _) hei1v
      refine ⟨id, kts, sigb1, _, _, ei1, ?_, hinv', ?_⟩
      · exact bpme_body_some LTSInst sys p id kts sigb spb stk ei hlt state_index hsid sigb1 hsig
          idx id kts hbsi'' _ ⟨_, hmut1⟩ v hcount _ ⟨_, hmut2⟩ ei1 hadd
      · refine ⟨hsem.idinv, hsem.sorted, ?_, ?_, ?_⟩
        · rw [hrun]
          rcases hcasesA with ⟨k', hk, -⟩ | ⟨-, hst⟩
          · rw [hren'] at hk; simp at hk
          · rw [hst, hintA]
            show absOf (n := nU.val) nl.val ({ slice := stk.slice.set state_index.index idx } : VecTy BT) kts = _
            unfold absOf
            congr 1
            exact keyOf_set stk z state_index.index idx hzval hstk_b
        · intro t ht
          rw [stk_set_getD stk state_index.index idx hstk_b]
          by_cases htm : t = m
          · subst htm
            rw [List.getD_eq_getElem _ _ hm, ← holdsm, if_pos rfl]
            exact hidxlt
          · have htm' : t < m := by omega
            have htl : t < olds.val.length := by omega
            have hne : (olds.val.getD t zST).index.val ≠ state_index.index.val := by
              rw [List.getD_eq_getElem _ _ htl, holdsm]
              have := (List.pairwise_iff_getElem.1 hsorted) t m htl hm htm'
              omega
            rw [if_neg hne]
            exact hsem.keysLt t htm'
        · intro t ht
          rw [clsAt_set spb ei m hinv.ei_eq idx hm_i2b' v _ rfl t,
            stk_set_getD stk state_index.index idx hstk_b]
          by_cases htm : t = m
          · subst htm
            rw [if_pos rfl, List.getD_eq_getElem _ _ hm, ← holdsm, if_pos rfl]
          · have htm' : t < m := by omega
            have htl : t < olds.val.length := by omega
            have hne : (olds.val.getD t zST).index.val ≠ state_index.index.val := by
              rw [List.getD_eq_getElem _ _ htl, holdsm]
              have := (List.pairwise_iff_getElem.1 hsorted) t m htl hm htm'
              omega
            rw [if_neg htm, if_neg hne]
            exact hsem.cls t htm'

open verified.merc_reduction.signature_refinement in
/-- `branching_process_marked_elements` on the builder left by `marked_elements_sorted` succeeds,
leaves dense classes, and computes the abstract key computation `kcRun` on `old_elements`. -/
theorem branching_process_marked_elements_dense {L Label : Type} (LTSInst : LTS L Label) (sys : L)
    (hwf : MercVerified.Lts.WellFormed LTSInst sys)
    (nU : Sz) (hns : LTSInst.num_of_states sys = ok nU) (hn0 : 0 < nU.val)
    {nl : Std.Usize} (hE : CEnv LTSInst sys nl) (htopo : ConcTopo LTSInst sys)
    {p : BlockPartition} (hp : PartInv nU.val p) (b : Nat) {olds : VecTy ST}
    (hold : ∀ x ∈ olds.val, x.index.val < nU.val) (holdn : olds.val.length ≤ nU.val)
    (hsorted : List.Pairwise (fun a c => a.index.val < c.index.val) olds.val)
    (hmem : ∀ x : ST, x.index.val < nU.val →
      ((e2bAt p x.index.val = b ∧ IsMarked p x.index.val) ↔ x ∈ olds.val))
    (id : InternMap)
    (hid : ∀ q, std.collections.hash.map.HashMap.get_key_value internEqInst internHashInst
      internBuildHasher (verified.core.borrow.Borrow.Blanket SigKey) internHashInst internEqInst id q
        = ok none)
    (kts : VecTy SigKey) (hkts : kts.val = []) (sigb : SigKey) (spb : BlockPartitionBuilder)
    (stk : VecTy BT) (hstk : stk.val.length = nU.val)
    (hspb : spb.old_elements = olds) (hi2b : ∀ x ∈ spb.index_to_block.val, x.index.val = 0)
    (hlen : spb.index_to_block.val.length = olds.val.length) (hbs : spb.block_sizes.val = []) :
    ∃ id1 kts1 sigb1 spb1 stk1,
      branching_process_marked_elements LTSInst sys p id kts sigb spb stk
        = ok (id1, kts1, sigb1, spb1, stk1) ∧
      spb1.old_elements = olds ∧ spb1.index_to_block.val.length = olds.val.length ∧
      stk1.val.length = nU.val ∧
      (∀ x ∈ spb1.index_to_block.val.map (fun x => x.index.val),
        x < (spb1.block_sizes.val.map (fun z => z.val)).length) ∧
      (∀ j, j < (spb1.block_sizes.val.map (fun z => z.val)).length →
        (spb1.block_sizes.val.map (fun z => z.val)).getD j 0
          = (spb1.index_to_block.val.map (fun x => x.index.val)).count j) ∧
      (∀ j, j < (spb1.block_sizes.val.map (fun z => z.val)).length →
        0 < (spb1.block_sizes.val.map (fun z => z.val)).getD j 0) ∧
      BrSem LTSInst sys nl hn0 p olds olds.val.length stk stk1 id1 kts1 spb1 := by
  unfold branching_process_marked_elements
  have hinv0 : SpmeInv nU.val olds 0 id kts spb stk 0#usize := by
    refine ⟨rfl, by omega, holdn, hspb, hlen, hstk, by simp [hkts], by simp [hkts, hbs], ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; simp at hx
    · intro x hx
      simp only [List.drop_zero, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hi2b y hy
    · intro j hj; simp [hkts] at hj
    · intro j hj; simp [hkts] at hj
    · intro q k v h; rw [hid q] at h; simp at h
  have hsem0 : BrSem LTSInst sys nl hn0 p olds 0 stk stk id kts spb := by
    refine ⟨IdInv.of_empty hid hkts, by simp [hkts], ?_, fun t ht => absurd ht (Nat.not_lt_zero _),
      fun t ht => absurd ht (Nat.not_lt_zero _)⟩
    simp [absOf, absInit, Sigref.RP.kcRun, hkts]
  obtain ⟨y, hy, hQ⟩ := loop_nat_spec
    (fun (x : SpmeState) =>
      branching_process_marked_elements_loop.body LTSInst sys p x.1 x.2.1 x.2.2.1 x.2.2.2.1
        x.2.2.2.2.1 x.2.2.2.2.2)
    (fun x => x.2.2.2.2.2.val)
    (fun m x => SpmeInv nU.val olds m x.1 x.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧
      BrSem LTSInst sys nl hn0 p olds m stk x.2.2.2.2.1 x.1 x.2.1 x.2.2.2.1)
    (fun (y : SpmeFinal) =>
      y.2.2.2.2.2.1 = olds ∧ y.2.2.2.1.val.length = olds.val.length ∧
      y.2.2.2.2.2.2.val.length = nU.val ∧
      (∀ x ∈ y.2.2.2.1.val.map (fun x => x.index.val),
        x < (y.2.2.2.2.1.val.map (fun z => z.val)).length) ∧
      (∀ j, j < (y.2.2.2.2.1.val.map (fun z => z.val)).length →
        (y.2.2.2.2.1.val.map (fun z => z.val)).getD j 0
          = (y.2.2.2.1.val.map (fun x => x.index.val)).count j) ∧
      (∀ j, j < (y.2.2.2.2.1.val.map (fun z => z.val)).length →
        0 < (y.2.2.2.2.1.val.map (fun z => z.val)).getD j 0) ∧
      BrSem LTSInst sys nl hn0 p olds olds.val.length stk y.2.2.2.2.2.2 y.1 y.2.1
        { index_to_block := y.2.2.2.1, block_sizes := y.2.2.2.2.1, old_elements := y.2.2.2.2.2.1 })
    olds.val.length
    (fun m x hx => hx.1.ei_eq) (fun m x hx => hx.1.m_le)
    (by
      intro m x hm hx
      obtain ⟨id1, kts1, sigb1, spb1, stk1, ei1, hb, hinv', hsem'⟩ :=
        bpme_step LTSInst sys hwf nU hns hn0 hE htopo hp b hold hsorted hmem hx.1 hx.2 hm
      exact ⟨(id1, kts1, sigb1, spb1, stk1, ei1), hb, hinv', hsem'⟩)
    (by
      intro x hxx
      obtain ⟨hx, hxs⟩ := hxx
      refine ⟨_, bpme_body_done LTSInst sys p _ _ _ _ _ _ ?_, ?_⟩
      · rw [hx.old, hx.ei_eq]
      · have hcl : (x.2.2.2.1.index_to_block.val.map (fun x => x.index.val)).length = olds.val.length := by
          simp [hx.len_i2b]
        have htk : (x.2.2.2.1.index_to_block.val.map (fun x => x.index.val)).take olds.val.length
            = x.2.2.2.1.index_to_block.val.map (fun x => x.index.val) :=
          List.take_of_length_le (by omega)
        have hbl : (x.2.2.2.1.block_sizes.val.map (fun z => z.val)).length = x.2.1.val.length := by
          simp [hx.len_bs]
        refine ⟨hx.old, hx.len_i2b, hx.len_stk, ?_, ?_, ?_, ?_⟩
        · intro c hc
          have := hx.taken c (by rw [htk]; exact hc)
          rw [hbl]; exact this
        · intro j hj
          rw [hbl] at hj
          have := hx.sizes j hj
          rw [htk] at this
          exact this
        · intro j hj
          rw [hbl] at hj
          exact hx.pos j hj
        · exact hxs)
    (id, kts, sigb, spb, stk, 0#usize) ⟨hinv0, hsem0⟩
  obtain ⟨id1, kts1, sigb1, i2b, bs, ol, stk1⟩ := y
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hQ
  refine ⟨id1, kts1, sigb1, { index_to_block := i2b, block_sizes := bs, old_elements := ol }, stk1, ?_,
    h1, h2, h3, h4, h5, h6, h7⟩
  unfold branching_process_marked_elements_loop
  rw [hy]
  simp

end MercVerified.Refinement.Proofs
