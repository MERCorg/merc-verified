import Sigref.KeyComp
import Sigref.Proofs.Absorb_Proofs
import Sigref.Proofs.SigData_Proofs

/-!
# Proofs: the key computation

The keys computed by the implementation (`kcRun`) induce, on the dirty states of a block, the
partition by `E π`. The proof compares the implementation's flat signatures with the paper's
inductive signature `Sig_π` of a coherent fixed point `d : SigData lts π`:
the key of a state equals the key of an interned *representative* whose flat signature is stored in
the table and whose `Sig_π` is its local signature, and states have the same key iff their `Sig_π`
agree (`KInv`).

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorem is
pinned in `Sigref/Pins/KeyComp_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

namespace RP

open Classical

variable {n : ℕ} {Label : Type} [HasTau Label]

/-- Everything the key computation of block `b` is compared against: a coherent signature
fixed point `d` for the partition of `rp`, and the facts `U`/`S` of the algorithm's invariant
(clean states of a block are `E`-equivalent, and never equivalent to a dirty one). -/
structure Env (lts : LTS (Fin n) Label) (rp : BD n) (b : ℕ) where
  d : SigData lts rp.setoid
  hWF : TauLoopFree lts
  hU : ∀ s t, rp.blk s = b → rp.blk t = b → ¬ rp.Dirty s → ¬ rp.Dirty t → E lts rp.setoid s t
  hS : ∀ s t, rp.blk s = b → rp.blk t = b → ¬ rp.Dirty s → rp.Dirty t → ¬ E lts rp.setoid s t

variable {lts : LTS (Fin n) Label} {rp : BD n} {b : ℕ}

/-- The flat signature of the implementation, with the dirty predicate of `rp` fixed. -/
noncomputable abbrev fsig (lts : LTS (Fin n) Label) (rp : BD n) (K : Fin n → ℕ) (x : Fin n) :
    KSig Label :=
  flatSig lts rp.blk (fun y => rp.Dirty y) K x

theorem mem_vis {K : Fin n → ℕ} {x : Fin n} {e : Label × ℕ} :
    e ∈ (fsig lts rp K x).vis ↔
      ∃ t, lts.Tr x e.1 t ∧ ¬ (e.1 = HasTau.τ ∧ rp.blk t = rp.blk x ∧ rp.Dirty t) ∧
        e.2 = rp.blk t := by
  obtain ⟨a, β⟩ := e
  constructor
  · rintro ⟨a', t, h1, h2, h3⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact ⟨t, h1, h2, rfl⟩
  · rintro ⟨t, h1, h2, h3⟩
    exact ⟨a, t, h1, h2, Prod.ext rfl h3⟩

theorem mem_hat {K : Fin n → ℕ} {x : Fin n} {k : ℕ} :
    k ∈ (fsig lts rp K x).hat ↔
      ∃ t, lts.Tr x HasTau.τ t ∧ rp.blk t = rp.blk x ∧ rp.Dirty t ∧ k = K t := Iff.rfl

theorem fsig_congr {K K' : Fin n → ℕ} {x : Fin n}
    (h : ∀ t, lts.Tr x HasTau.τ t → rp.blk t = rp.blk x → rp.Dirty t → K t = K' t) :
    fsig lts rp K x = fsig lts rp K' x := by
  have : (fsig lts rp K x).hat = (fsig lts rp K' x).hat := by
    ext k
    rw [mem_hat, mem_hat]
    constructor
    · rintro ⟨t, h1, h2, h3, h4⟩; exact ⟨t, h1, h2, h3, by rw [h4, h t h1 h2 h3]⟩
    · rintro ⟨t, h1, h2, h3, h4⟩; exact ⟨t, h1, h2, h3, by rw [h4, h t h1 h2 h3]⟩
  show (⟨_, _⟩ : KSig Label) = ⟨_, _⟩
  simp only [fsig, flatSig] at this ⊢
  rw [this]

namespace Env

variable (e : Env lts rp b)

/-- Signature hashes of two states of the block are equal iff both are clean, or both are dirty
with equal keys. -/
theorem hash_class {K : Fin n → ℕ} {t u : Fin n} (ht : rp.blk t = b) (hu : rp.blk u = b)
    (hK : rp.Dirty t → rp.Dirty u → (K t = K u ↔ e.d.sigFn t = e.d.sigFn u)) :
    e.d.sigHash t = e.d.sigHash u ↔
      ((rp.Dirty t ↔ rp.Dirty u) ∧ (rp.Dirty t → K t = K u)) := by
  have hπ : rp.setoid.r t u := show rp.blk t = rp.blk u from ht.trans hu.symm
  rw [e.d.hCoh, e.d.sig_iff_E e.hWF hπ]
  by_cases h1 : rp.Dirty t <;> by_cases h2 : rp.Dirty u
  · rw [← e.d.sig_iff_E e.hWF hπ]
    exact ⟨fun h => ⟨iff_of_true h1 h2, fun _ => (hK h1 h2).2 h⟩, fun h => (hK h1 h2).1 (h.2 h1)⟩
  · have := e.hS u t hu ht h2 h1
    exact ⟨fun h => absurd (E.symm lts _ h) this, fun h => absurd (h.1.1 h1) h2⟩
  · have := e.hS t u ht hu h1 h2
    exact ⟨fun h => absurd h this, fun h => absurd (h.1.2 h2) h1⟩
  · exact ⟨fun _ => ⟨iff_of_false h1 h2, fun h => absurd h h1⟩,
      fun _ => e.hU t u ht hu h1 h2⟩

/-- Membership in the local signature, `inl` entries. -/
theorem mem_PS_inl {x : Fin n} {a : Label} {α : Quotient rp.setoid} :
    (a, Sum.inl α) ∈ e.d.PS x ↔
      ∃ t, lts.Tr x a t ∧ (a ≠ HasTau.τ ∨ rp.blk x ≠ rp.blk t) ∧ α = Quotient.mk rp.setoid t := by
  constructor
  · intro h
    obtain ⟨t, h1, h2, h3⟩ := e.d.ps_inl_elim h
    exact ⟨t, h1, h2, h3⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact e.d.ps_inl h1 h2

/-- Membership in the local signature, `inr` entries. -/
theorem mem_PS_inr {x : Fin n} {a : Label} {c : e.d.Tag} :
    (a, Sum.inr c) ∈ e.d.PS x ↔
      a = HasTau.τ ∧ ∃ t, lts.Tr x HasTau.τ t ∧ rp.blk x = rp.blk t ∧ c = e.d.sigHash t := by
  constructor
  · intro h
    obtain ⟨h1, t, h2, h3, h4⟩ := e.d.ps_inr_elim h
    exact ⟨h1, t, h2, h3, h4⟩
  · rintro ⟨rfl, t, h2, h3, rfl⟩
    exact e.d.ps_inr h2 h3

section Flat

variable {K : Fin n → ℕ} {P : Fin n → Prop}

/-- `K` is consistent with `Sig`-equality on the dirty states of `P`. -/
def KeyOK (K : Fin n → ℕ) (P : Fin n → Prop) : Prop :=
  ∀ t u, P t → P u → rp.Dirty t → rp.Dirty u → (K t = K u ↔ e.d.sigFn t = e.d.sigFn u)

/-- The dirty inert targets of `x` satisfy `P`. -/
def TargetsIn (lts : LTS (Fin n) Label) (rp : BD n) (P : Fin n → Prop) (x : Fin n) : Prop :=
  ∀ t, lts.Tr x HasTau.τ t → rp.blk t = rp.blk x → rp.Dirty t → P t

theorem hash_class' (hK : e.KeyOK K P) {x y t u : Fin n} (hx : rp.blk x = b) (hy : rp.blk y = b)
    (hPx : TargetsIn lts rp P x) (hPy : TargetsIn lts rp P y)
    (ht : lts.Tr x HasTau.τ t) (htb : rp.blk t = rp.blk x)
    (hu : lts.Tr y HasTau.τ u) (hub : rp.blk u = rp.blk y) :
    e.d.sigHash t = e.d.sigHash u ↔ ((rp.Dirty t ↔ rp.Dirty u) ∧ (rp.Dirty t → K t = K u)) :=
  e.hash_class (htb.trans hx) (hub.trans hy) fun h1 h2 =>
    hK t u (hPx t ht htb h1) (hPy u hu hub h2) h1 h2

/-- If the local signature of `x` is contained in that of `y`, so is the flat signature. -/
theorem flat_sub (hK : e.KeyOK K P) {x y : Fin n} (hx : rp.blk x = b) (hy : rp.blk y = b)
    (hPx : TargetsIn lts rp P x) (hPy : TargetsIn lts rp P y) (h : e.d.PS x ⊆ e.d.PS y) :
    (fsig lts rp K x).vis ⊆ (fsig lts rp K y).vis ∧ (fsig lts rp K x).hat ⊆ (fsig lts rp K y).hat := by
  have hxy : rp.blk x = rp.blk y := hx.trans hy.symm
  constructor
  · intro ⟨a, β⟩ hv
    obtain ⟨t, h1, h2, h3⟩ := mem_vis.1 hv
    simp only at h1 h2 h3
    by_cases hni : a ≠ HasTau.τ ∨ rp.blk x ≠ rp.blk t
    · have := h ((mem_PS_inl e).2 ⟨t, h1, hni, rfl⟩)
      obtain ⟨t', h1', h2', h3'⟩ := (mem_PS_inl e).1 this
      have hb : rp.blk t = rp.blk t' := Quotient.exact h3'
      refine mem_vis.2 ⟨t', h1', ?_, by simp only; rw [h3, hb]⟩
      rintro ⟨ha, hb', _⟩
      rcases h2' with h2' | h2'
      · exact h2' ha
      · exact h2' (hb'.symm)
    · push Not at hni
      obtain ⟨ha, hbt⟩ := hni
      subst ha
      have hcl : ¬ rp.Dirty t := fun hd => h2 ⟨rfl, hbt.symm, hd⟩
      have := h ((mem_PS_inr e).2 ⟨rfl, t, h1, hbt, rfl⟩)
      obtain ⟨_, t', h1', h2', h3'⟩ := (mem_PS_inr e).1 this
      have hcls := (e.hash_class' hK hx hy hPx hPy h1 hbt.symm h1' h2'.symm).1 h3'
      have hcl' : ¬ rp.Dirty t' := fun hd => hcl (hcls.1.2 hd)
      refine mem_vis.2 ⟨t', h1', ?_, ?_⟩
      · rintro ⟨_, _, hd⟩; exact hcl' hd
      · simp only; rw [h3]; exact (hbt.symm.trans (hxy.trans h2'))
  · intro k hk
    obtain ⟨t, h1, h2, h3, h4⟩ := mem_hat.1 hk
    have := h ((mem_PS_inr e).2 ⟨rfl, t, h1, h2.symm, rfl⟩)
    obtain ⟨_, t', h1', h2', h3'⟩ := (mem_PS_inr e).1 this
    have hcls := (e.hash_class' hK hx hy hPx hPy h1 h2 h1' h2'.symm).1 h3'
    exact mem_hat.2 ⟨t', h1', h2'.symm, hcls.1.1 h3, by rw [h4]; exact hcls.2 h3⟩

/-- If the flat signature of `x` is contained in that of `y`, so is the local signature. -/
theorem ps_sub (hK : e.KeyOK K P) {x y : Fin n} (hx : rp.blk x = b) (hy : rp.blk y = b)
    (hPx : TargetsIn lts rp P x) (hPy : TargetsIn lts rp P y)
    (hv : (fsig lts rp K x).vis ⊆ (fsig lts rp K y).vis)
    (hh : (fsig lts rp K x).hat ⊆ (fsig lts rp K y).hat) : e.d.PS x ⊆ e.d.PS y := by
  have hxy : rp.blk x = rp.blk y := hx.trans hy.symm
  rintro ⟨a, α | c⟩ hm
  · obtain ⟨t, h1, h2, h3⟩ := (mem_PS_inl e).1 hm
    have hmem : (a, rp.blk t) ∈ (fsig lts rp K x).vis := by
      refine mem_vis.2 ⟨t, h1, ?_, rfl⟩
      rintro ⟨ha, hb', _⟩
      rcases h2 with h2 | h2
      · exact h2 ha
      · exact h2 hb'.symm
    obtain ⟨t', h1', h2', h3'⟩ := mem_vis.1 (hv hmem)
    simp only at h1' h2' h3'
    refine (mem_PS_inl e).2 ⟨t', h1', ?_, ?_⟩
    · by_cases ha : a = HasTau.τ
      · right
        intro hb'
        rcases h2 with h2 | h2
        · exact h2 ha
        · exact h2 (by rw [hxy, hb', ← h3'])
      · exact Or.inl ha
    · rw [h3]; exact Quotient.sound (show rp.blk t = rp.blk t' from h3')
  · obtain ⟨ha, t, h1, h2, h3⟩ := (mem_PS_inr e).1 hm
    subst ha
    by_cases hd : rp.Dirty t
    · have hk : K t ∈ (fsig lts rp K x).hat := mem_hat.2 ⟨t, h1, h2.symm, hd, rfl⟩
      obtain ⟨t', h1', h2', h3', h4'⟩ := mem_hat.1 (hh hk)
      have hcls := (e.hash_class' hK hx hy hPx hPy h1 h2.symm h1' h2').2 ⟨iff_of_true hd h3', fun _ => h4'⟩
      exact (mem_PS_inr e).2 ⟨rfl, t', h1', h2'.symm, by rw [h3, hcls]⟩
    · have hmem : (HasTau.τ, rp.blk t) ∈ (fsig lts rp K x).vis :=
        mem_vis.2 ⟨t, h1, fun ⟨_, _, hd'⟩ => hd hd', rfl⟩
      obtain ⟨t', h1', h2', h3'⟩ := mem_vis.1 (hv hmem)
      simp only at h1' h2' h3'
      have hbt' : rp.blk t' = rp.blk y := by rw [← h3', ← h2, hxy]
      have hd' : ¬ rp.Dirty t' := fun hd'' => h2' ⟨by trivial, hbt', hd''⟩
      have hcls := (e.hash_class' hK hx hy hPx hPy h1 h2.symm h1' hbt').2 ⟨iff_of_false hd hd', fun h => absurd h hd⟩
      exact (mem_PS_inr e).2 ⟨rfl, t', h1', hbt'.symm, by rw [h3, hcls]⟩

/-- **Flat signatures compare like local signatures** (for states whose dirty inert targets carry
consistent keys). -/
theorem flat_eq_iff (hK : e.KeyOK K P) {x y : Fin n} (hx : rp.blk x = b) (hy : rp.blk y = b)
    (hPx : TargetsIn lts rp P x) (hPy : TargetsIn lts rp P y) :
    fsig lts rp K x = fsig lts rp K y ↔ e.d.PS x = e.d.PS y := by
  constructor
  · intro h
    have h1 := e.flat_sub hK hx hy hPx hPy
    apply Set.Subset.antisymm
    · exact e.ps_sub hK hx hy hPx hPy (h ▸ subset_rfl) (h ▸ subset_rfl)
    · exact e.ps_sub hK hy hx hPy hPx (h ▸ subset_rfl) (h ▸ subset_rfl)
  · intro h
    have h1 := e.flat_sub hK hx hy hPx hPy h.subset
    have h2 := e.flat_sub hK hy hx hPy hPx h.symm.subset
    show (⟨_, _⟩ : KSig Label) = ⟨_, _⟩
    simp only [fsig, flatSig] at h1 h2 ⊢
    rw [Set.Subset.antisymm h1.1 h2.1, Set.Subset.antisymm h1.2 h2.2]

/-- **The implementation's absorption test is the paper's.** For a dirty inert successor `a` of
`z`, `is_subset_excluding` of the flat signature of `z` against the flat signature of `r` (excluding
the hat entry of `a`) holds iff the local signature of `z` is absorbed by the local signature of `r`
up to the entry `(τ̇, h(a))`. -/
theorem subsetExcl_iff (hK : e.KeyOK K P) {z r a : Fin n} (hz : rp.blk z = b) (hr : rp.blk r = b)
    (hPz : TargetsIn lts rp P z) (hPr : TargetsIn lts rp P r)
    (ha : lts.Tr z HasTau.τ a) (hab : rp.blk a = rp.blk z) (hda : rp.Dirty a) :
    SubsetExcl (fsig lts rp K r) (fsig lts rp K z) (K a) ↔
      ∀ x ∈ e.d.PS z, x ∈ e.d.PS r ∨ x = (HasTau.τ, Sum.inr (e.d.sigHash a)) := by
  have hzr : rp.blk z = rp.blk r := hz.trans hr.symm
  constructor
  · rintro ⟨hv, hh⟩ ⟨c, α | c'⟩ hm
    · obtain ⟨t, h1, h2, h3⟩ := (mem_PS_inl e).1 hm
      have hmem : (c, rp.blk t) ∈ (fsig lts rp K z).vis := by
        refine mem_vis.2 ⟨t, h1, ?_, rfl⟩
        rintro ⟨hc, hb', _⟩
        rcases h2 with h2 | h2
        · exact h2 hc
        · exact h2 hb'.symm
      obtain ⟨t', h1', h2', h3'⟩ := mem_vis.1 (hv hmem)
      simp only at h1' h2' h3'
      refine Or.inl ((mem_PS_inl e).2 ⟨t', h1', ?_, ?_⟩)
      · by_cases hc : c = HasTau.τ
        · right
          intro hb'
          rcases h2 with h2 | h2
          · exact h2 hc
          · exact h2 (by rw [hzr, hb', ← h3'])
        · exact Or.inl hc
      · rw [h3]; exact Quotient.sound (show rp.blk t = rp.blk t' from h3')
    · obtain ⟨hc, t, h1, h2, h3⟩ := (mem_PS_inr e).1 hm
      subst hc
      by_cases hd : rp.Dirty t
      · by_cases hkt : K t = K a
        · right
          have := (e.hash_class' hK hz hz hPz hPz h1 h2.symm ha hab).2
            ⟨iff_of_true hd hda, fun _ => hkt⟩
          rw [h3, this]
        · have hk : K t ∈ (fsig lts rp K z).hat \ {K a} :=
            ⟨mem_hat.2 ⟨t, h1, h2.symm, hd, rfl⟩, hkt⟩
          obtain ⟨t', h1', h2', h3', h4'⟩ := mem_hat.1 (hh hk)
          have hcls := (e.hash_class' hK hz hr hPz hPr h1 h2.symm h1' h2').2
            ⟨iff_of_true hd h3', fun _ => h4'⟩
          exact Or.inl ((mem_PS_inr e).2 ⟨rfl, t', h1', h2'.symm, by rw [h3, hcls]⟩)
      · have hmem : (HasTau.τ, rp.blk t) ∈ (fsig lts rp K z).vis :=
          mem_vis.2 ⟨t, h1, fun ⟨_, _, hd'⟩ => hd hd', rfl⟩
        obtain ⟨t', h1', h2', h3'⟩ := mem_vis.1 (hv hmem)
        simp only at h1' h2' h3'
        have hbt' : rp.blk t' = rp.blk r := by rw [← h3', ← h2, hzr]
        have hd' : ¬ rp.Dirty t' := fun hd'' => h2' ⟨by trivial, hbt', hd''⟩
        have hcls := (e.hash_class' hK hz hr hPz hPr h1 h2.symm h1' hbt').2
          ⟨iff_of_false hd hd', fun h => absurd h hd⟩
        exact Or.inl ((mem_PS_inr e).2 ⟨rfl, t', h1', hbt'.symm, by rw [h3, hcls]⟩)
  · intro hsub
    have hne : ∀ t, lts.Tr z HasTau.τ t → rp.blk t = rp.blk z →
        e.d.sigHash t = e.d.sigHash a → (rp.Dirty t ∧ K t = K a) := by
      intro t h1 h2 h3
      have := (e.hash_class' hK hz hz hPz hPz h1 h2 ha hab).1 h3
      have hdt : rp.Dirty t := this.1.2 hda
      exact ⟨hdt, this.2 hdt⟩
    refine ⟨?_, ?_⟩
    · intro ⟨c, β⟩ hv
      obtain ⟨t, h1, h2, h3⟩ := mem_vis.1 hv
      simp only at h1 h2 h3
      by_cases hni : c ≠ HasTau.τ ∨ rp.blk z ≠ rp.blk t
      · have hm := hsub _ ((mem_PS_inl e).2 ⟨t, h1, hni, rfl⟩)
        rcases hm with hm | hm
        · obtain ⟨t', h1', h2', h3'⟩ := (mem_PS_inl e).1 hm
          have hb : rp.blk t = rp.blk t' := Quotient.exact h3'
          refine mem_vis.2 ⟨t', h1', ?_, by simp only; rw [h3, hb]⟩
          rintro ⟨hc, hb', _⟩
          rcases h2' with h2' | h2'
          · exact h2' hc
          · exact h2' hb'.symm
        · exact absurd (congrArg Prod.snd hm) (by simp)
      · push Not at hni
        obtain ⟨hc, hbt⟩ := hni
        subst hc
        have hcl : ¬ rp.Dirty t := fun hd => h2 ⟨rfl, hbt.symm, hd⟩
        rcases hsub _ ((mem_PS_inr e).2 ⟨rfl, t, h1, hbt, rfl⟩) with hm | hm
        · obtain ⟨_, t', h1', h2', h3'⟩ := (mem_PS_inr e).1 hm
          have hcls := (e.hash_class' hK hz hr hPz hPr h1 hbt.symm h1' h2'.symm).1 h3'
          have hcl' : ¬ rp.Dirty t' := fun hd => hcl (hcls.1.2 hd)
          refine mem_vis.2 ⟨t', h1', ?_, ?_⟩
          · rintro ⟨_, _, hd⟩; exact hcl' hd
          · simp only; rw [h3]; exact (hbt.symm.trans (hzr.trans h2'))
        · exfalso
          have := hne t h1 hbt.symm (Sum.inr.inj (congrArg Prod.snd hm))
          exact hcl this.1
    · intro k ⟨hk, hka⟩
      obtain ⟨t, h1, h2, h3, h4⟩ := mem_hat.1 hk
      rcases hsub _ ((mem_PS_inr e).2 ⟨rfl, t, h1, h2.symm, rfl⟩) with hm | hm
      · obtain ⟨_, t', h1', h2', h3'⟩ := (mem_PS_inr e).1 hm
        have hcls := (e.hash_class' hK hz hr hPz hPr h1 h2 h1' h2'.symm).1 h3'
        exact mem_hat.2 ⟨t', h1', h2'.symm, hcls.1.1 h3, by rw [h4]; exact hcls.2 h3⟩
      · exfalso
        have := hne t h1 h2 (Sum.inr.inj (congrArg Prod.snd hm))
        exact hka (by show k = K a; rw [h4]; exact this.2)

end Flat

end Env

/-! ### The table operations -/

omit [HasTau Label] in
theorem renumber_some {tbl : List (KSig Label)} {sg : KSig Label} {k : ℕ}
    (h : renumber tbl sg = some k) :
    ∃ hk : k < tbl.length, k ∈ sg.hat ∧ SubsetExcl tbl[k] sg k := by
  unfold renumber at h
  split at h
  · rename_i hex
    obtain ⟨k0, hk0, hk0h, hk0s⟩ := hex
    have hspec := Nat.findGreatest_spec (P := fun k => ∃ hk : k < tbl.length, k ∈ sg.hat ∧
      SubsetExcl tbl[k] sg k) (m := k0) (n := tbl.length) hk0.le ⟨hk0, hk0h, hk0s⟩
    obtain rfl := Option.some.inj h
    exact hspec
  · exact absurd h (by simp)

omit [HasTau Label] in
theorem renumber_none {tbl : List (KSig Label)} {sg : KSig Label}
    (h : renumber tbl sg = none) :
    ∀ k, ∀ hk : k < tbl.length, k ∈ sg.hat → ¬ SubsetExcl tbl[k] sg k := by
  unfold renumber at h
  split at h
  · exact absurd h (by simp)
  · rename_i hex
    intro k hk hh hs
    exact hex ⟨k, hk, hh, hs⟩

omit [HasTau Label] in
theorem intern_cases (tbl : List (KSig Label)) (sg : KSig Label) :
    (∃ hk : (intern tbl sg).1 < tbl.length, tbl[(intern tbl sg).1] = sg ∧
        (intern tbl sg).2 = tbl) ∨
    ((intern tbl sg).1 = tbl.length ∧ (intern tbl sg).2 = tbl ++ [sg] ∧
      ∀ i, ∀ hi : i < tbl.length, tbl[i] ≠ sg) := by
  unfold intern
  split
  · rename_i h
    exact Or.inl ⟨h.choose_spec.choose, h.choose_spec.choose_spec, rfl⟩
  · rename_i h
    refine Or.inr ⟨rfl, rfl, fun i hi hh => h ⟨i, hi, hh⟩⟩

/-! ### The loop invariant -/

/-- The invariant of the key computation after the states of `pre` were processed. -/
structure KInv (e : Env lts rp b) (pre : List (Fin n)) (st : KC n Label) : Prop where
  nodup : pre.Nodup
  mem : ∀ z ∈ pre, rp.blk z = b ∧ rp.Dirty z
  down : ∀ t r, r ∈ pre → rp.blk t = b → rp.Dirty t → t < r → t ∈ pre
  tbl_nodup : st.tbl.Nodup
  key_lt : ∀ z ∈ pre, st.key z < st.tbl.length
  tblrep : ∀ i, ∀ hi : i < st.tbl.length, ∃ r ∈ pre, st.key r = i ∧
    e.d.sigFn r = e.d.PS r ∧ st.tbl[i] = fsig lts rp st.key r
  equiv : ∀ x ∈ pre, ∀ y ∈ pre, (st.key x = st.key y ↔ e.d.sigFn x = e.d.sigFn y)

theorem KInv.init (e : Env lts rp b) (key0 : Fin n → ℕ) : KInv e [] ⟨key0, []⟩ where
  nodup := List.nodup_nil
  mem := by simp
  down := by simp
  tbl_nodup := List.nodup_nil
  key_lt := by simp
  tblrep := by simp
  equiv := by simp

/-- The dirty inert targets of a processed state are processed. -/
theorem KInv.targets {e : Env lts rp b} {pre : List (Fin n)} {st : KC n Label}
    (hI : KInv e pre st) (hTopo : TopoSorted lts) {r : Fin n} (hr : r ∈ pre) :
    Env.TargetsIn lts rp (· ∈ pre) r := by
  intro t ht htb hd
  have hrb := (hI.mem r hr).1
  exact hI.down t r hr (htb.trans hrb) hd (hTopo r t ht)

theorem KInv.keyOK {e : Env lts rp b} {pre : List (Fin n)} {st : KC n Label}
    (hI : KInv e pre st) : e.KeyOK st.key (· ∈ pre) :=
  fun t u ht hu _ _ => hI.equiv t ht u hu

section Step

variable {e : Env lts rp b} {pre : List (Fin n)} {st : KC n Label}

theorem kcStep_cases (st : KC n Label) (z : Fin n) :
    (∃ k, renumber st.tbl (fsig lts rp st.key z) = some k ∧
      kcStep lts rp.blk (fun x => rp.Dirty x) st z = { st with key := Function.update st.key z k }) ∨
    (renumber st.tbl (fsig lts rp st.key z) = none ∧
      kcStep lts rp.blk (fun x => rp.Dirty x) st z =
        ⟨Function.update st.key z (intern st.tbl (fsig lts rp st.key z)).1,
          (intern st.tbl (fsig lts rp st.key z)).2⟩) := by
  unfold kcStep
  cases h : renumber st.tbl (fsig lts rp st.key z) with
  | some k => exact Or.inl ⟨k, rfl, by simp only [fsig] at h ⊢; rw [h]⟩
  | none => exact Or.inr ⟨rfl, by simp only [fsig] at h ⊢; rw [h]⟩

/-- No absorber when the implementation interns. -/
theorem no_absorb (hI : KInv e pre st) (hTopo : TopoSorted lts) {z : Fin n} (hz : rp.blk z = b)
    (hdz : rp.Dirty z) (hzpre : ∀ t, rp.blk t = b → rp.Dirty t → t < z → t ∈ pre)
    (hnone : renumber st.tbl (fsig lts rp st.key z) = none) :
    ∀ a, ¬ e.d.Absorbs z a := by
  intro a ⟨ha, hπ, hsub⟩
  have hab : rp.blk a = rp.blk z := hπ.symm
  by_cases hda : rp.Dirty a
  · have hapre : a ∈ pre := hzpre a (hab.trans hz) hda (hTopo z a ha)
    have hPz : Env.TargetsIn lts rp (· ∈ pre) z := fun t ht htb hd =>
      hzpre t (htb.trans hz) hd (hTopo z t ht)
    obtain ⟨r, hrpre, hkr, hσr, htr⟩ := hI.tblrep (st.key a) (hI.key_lt a hapre)
    have hσar : e.d.sigFn r = e.d.sigFn a := (hI.equiv r hrpre a hapre).1 hkr
    refine renumber_none hnone (st.key a) (hI.key_lt a hapre)
      (mem_hat.2 ⟨a, ha, hab, hda, rfl⟩) ?_
    rw [htr]
    refine (e.subsetExcl_iff hI.keyOK hz (hI.mem r hrpre).1 hPz (hI.targets hTopo hrpre) ha hab
      hda).2 ?_
    intro x hx
    rcases hsub hx with h | h
    · have hh : e.d.sigFn a = e.d.PS r := hσar.symm.trans hσr
      rw [hh] at h
      exact Or.inl h
    · exact Or.inr (by rw [h])
  · have hE := e.d.absorbs_E e.hWF ⟨ha, hπ, hsub⟩
    exact e.hS a z (hab.trans hz) hz hda hdz (E.symm lts _ hE)

theorem fsig_update (hI : KInv e pre st) (hTopo : TopoSorted lts) {z r : Fin n} (hz : z ∉ pre)
    (hr : r ∈ pre) (k : ℕ) :
    fsig lts rp (Function.update st.key z k) r = fsig lts rp st.key r := by
  refine fsig_congr fun t ht htb hd => ?_
  have htpre := hI.targets hTopo hr t ht htb hd
  exact Function.update_of_ne (fun h => hz (by rw [← h]; exact htpre)) _ _

/-- The structural part of the invariant, common to all three cases of a step. -/
theorem kInv_struct (hI : KInv e pre st) {z : Fin n} (hz : rp.blk z = b) (hdz : rp.Dirty z)
    (hznot : z ∉ pre) (hzpre : ∀ t, rp.blk t = b → rp.Dirty t → t < z → t ∈ pre) :
    (pre ++ [z]).Nodup ∧ (∀ w ∈ pre ++ [z], rp.blk w = b ∧ rp.Dirty w) ∧
      (∀ t r, r ∈ pre ++ [z] → rp.blk t = b → rp.Dirty t → t < r → t ∈ pre ++ [z]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hI.nodup, List.nodup_singleton z, fun a ha c hc hac =>
      hznot (by rw [List.mem_singleton.1 hc] at hac; rw [← hac]; exact ha)⟩
  · intro w hw
    rcases List.mem_append.1 hw with h | h
    · exact hI.mem w h
    · rw [List.mem_singleton.1 h]; exact ⟨hz, hdz⟩
  · intro t r hr htb htd hlt
    rcases List.mem_append.1 hr with h | h
    · exact List.mem_append_left _ (hI.down t r h htb htd hlt)
    · rw [List.mem_singleton.1 h] at hlt
      exact List.mem_append_left _ (hzpre t htb htd hlt)

/-- **One step of the key computation preserves the invariant.** -/
theorem kInv_step (hI : KInv e pre st) (hTopo : TopoSorted lts) {z : Fin n}
    (hz : rp.blk z = b) (hdz : rp.Dirty z) (hznot : z ∉ pre)
    (hzpre : ∀ t, rp.blk t = b → rp.Dirty t → t < z → t ∈ pre) :
    KInv e (pre ++ [z]) (kcStep lts rp.blk (fun x => rp.Dirty x) st z) := by
  obtain ⟨hnd, hmem, hdown⟩ := kInv_struct hI hz hdz hznot hzpre
  have hPz : Env.TargetsIn lts rp (· ∈ pre) z := fun t ht htb hd =>
    hzpre t (htb.trans hz) hd (hTopo z t ht)
  have hne : ∀ w ∈ pre, w ≠ z := fun w hw h => hznot (by rw [← h]; exact hw)
  rcases kcStep_cases (lts := lts) (rp := rp) st z with ⟨k, hk, hst⟩ | ⟨hnone, hst⟩
  · -- the signature is absorbed by a processed state
    rw [hst]
    obtain ⟨hklt, hkh, hsub⟩ := renumber_some hk
    obtain ⟨a, ha, hab, hda, hka⟩ := mem_hat.1 hkh
    subst hka
    have hapre : a ∈ pre := hzpre a (hab.trans hz) hda (hTopo z a ha)
    obtain ⟨r, hrpre, hkr, hσr, htr⟩ := hI.tblrep (st.key a) hklt
    have hσar : e.d.sigFn r = e.d.sigFn a := (hI.equiv r hrpre a hapre).1 hkr
    rw [htr] at hsub
    have habs := (e.subsetExcl_iff hI.keyOK hz (hI.mem r hrpre).1 hPz (hI.targets hTopo hrpre)
      ha hab hda).1 hsub
    have hE : E lts rp.setoid z a := e.d.absorbs_E e.hWF ⟨ha, hab.symm, fun x hx => by
      rcases habs x hx with h | h
      · exact Or.inl (by rw [← hσar, hσr]; exact h)
      · exact Or.inr h⟩
    have hσza : e.d.sigFn z = e.d.sigFn a :=
      (e.d.sig_iff_E e.hWF (show rp.blk z = rp.blk a from hab.symm)).2 hE
    have hup : ∀ w ∈ pre, Function.update st.key z (st.key a) w = st.key w :=
      fun w hw => Function.update_of_ne (hne w hw) _ _
    have hupz : Function.update st.key z (st.key a) z = st.key a := Function.update_self _ _ _
    refine ⟨hnd, hmem, hdown, hI.tbl_nodup, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.1 hw with h | h
      · show Function.update st.key z (st.key a) w < st.tbl.length
        rw [hup w h]; exact hI.key_lt w h
      · rw [List.mem_singleton.1 h]; show Function.update st.key z (st.key a) z < st.tbl.length
        rw [hupz]; exact hklt
    · intro i hi
      obtain ⟨r', hr', hkr', hσr', htr'⟩ := hI.tblrep i hi
      refine ⟨r', List.mem_append_left _ hr', ?_, hσr', ?_⟩
      · show Function.update st.key z (st.key a) r' = i
        rw [hup r' hr']; exact hkr'
      · show st.tbl[i] = fsig lts rp (Function.update st.key z (st.key a)) r'
        rw [fsig_update hI hTopo hznot hr']; exact htr'
    · have hzy : ∀ y ∈ pre, (Function.update st.key z (st.key a) z =
          Function.update st.key z (st.key a) y ↔ e.d.sigFn z = e.d.sigFn y) := by
        intro y hy
        rw [hupz, hup y hy, hσza]
        exact hI.equiv a hapre y hy
      intro x hx y hy
      rcases List.mem_append.1 hx with hx | hx <;> rcases List.mem_append.1 hy with hy | hy
      · show Function.update st.key z (st.key a) x = Function.update st.key z (st.key a) y ↔ _
        rw [hup x hx, hup y hy]; exact hI.equiv x hx y hy
      · rw [List.mem_singleton.1 hy]
        exact ⟨fun h => ((hzy x hx).1 h.symm).symm, fun h => ((hzy x hx).2 h.symm).symm⟩
      · rw [List.mem_singleton.1 hx]; exact hzy y hy
      · rw [List.mem_singleton.1 hx, List.mem_singleton.1 hy]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
  · -- the signature is not absorbed: it is interned
    rw [hst]
    have hnoabs := no_absorb hI hTopo hz hdz hzpre hnone
    have hσz : e.d.sigFn z = e.d.PS z := e.d.sig_eq_PS (hnoabs)
    have hup : ∀ (k : ℕ), ∀ w ∈ pre, Function.update st.key z k w = st.key w :=
      fun k w hw => Function.update_of_ne (hne w hw) _ _
    have hcases := intern_cases st.tbl (fsig lts rp st.key z)
    generalize intern st.tbl (fsig lts rp st.key z) = p at hcases ⊢
    obtain ⟨k0, tbl'⟩ := p
    simp only at hcases ⊢
    rcases hcases with ⟨hk0, htk, rfl⟩ | ⟨rfl, rfl, hnew⟩
    · -- an equal signature is already interned
      obtain ⟨r, hrpre, hkr, hσr, htr⟩ := hI.tblrep k0 hk0
      have hPS : e.d.PS z = e.d.PS r :=
        (e.flat_eq_iff hI.keyOK hz (hI.mem r hrpre).1 hPz (hI.targets hTopo hrpre)).1
          (htk.symm.trans htr)
      have hσzr : e.d.sigFn z = e.d.sigFn r := by rw [hσz, hσr, hPS]
      refine ⟨hnd, hmem, hdown, hI.tbl_nodup, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_append.1 hw with h | h
        · show Function.update st.key z k0 w < st.tbl.length
          rw [hup k0 w h]; exact hI.key_lt w h
        · rw [List.mem_singleton.1 h]
          show Function.update st.key z k0 z < st.tbl.length
          rw [Function.update_self]; exact hk0
      · intro i hi
        obtain ⟨r', hr', hkr', hσr', htr'⟩ := hI.tblrep i hi
        refine ⟨r', List.mem_append_left _ hr', ?_, hσr', ?_⟩
        · show Function.update st.key z k0 r' = i
          rw [hup k0 r' hr']; exact hkr'
        · show st.tbl[i] = fsig lts rp (Function.update st.key z k0) r'
          rw [fsig_update hI hTopo hznot hr']; exact htr'
      · have hzy : ∀ y ∈ pre, (Function.update st.key z k0 z = Function.update st.key z k0 y ↔
            e.d.sigFn z = e.d.sigFn y) := by
          intro y hy
          rw [Function.update_self, hup k0 y hy, hσzr, ← hkr]
          exact hI.equiv r hrpre y hy
        intro x hx y hy
        rcases List.mem_append.1 hx with hx | hx <;> rcases List.mem_append.1 hy with hy | hy
        · show Function.update st.key z k0 x = Function.update st.key z k0 y ↔ _
          rw [hup k0 x hx, hup k0 y hy]; exact hI.equiv x hx y hy
        · rw [List.mem_singleton.1 hy]
          exact ⟨fun h => ((hzy x hx).1 h.symm).symm, fun h => ((hzy x hx).2 h.symm).symm⟩
        · rw [List.mem_singleton.1 hx]; exact hzy y hy
        · rw [List.mem_singleton.1 hx, List.mem_singleton.1 hy]
          exact ⟨fun _ => rfl, fun _ => rfl⟩
    · -- a new signature is appended
      have hzy : ∀ y ∈ pre, ¬ (e.d.sigFn z = e.d.sigFn y) := by
        intro y hy hσ
        obtain ⟨r', hr', hkr', hσr', htr'⟩ := hI.tblrep (st.key y) (hI.key_lt y hy)
        have hσr'y : e.d.sigFn r' = e.d.sigFn y := (hI.equiv r' hr' y hy).1 hkr'
        have hPS : e.d.PS z = e.d.PS r' := by rw [← hσz, ← hσr', hσ, hσr'y]
        have hflat := (e.flat_eq_iff hI.keyOK hz (hI.mem r' hr').1 hPz
          (hI.targets hTopo hr')).2 hPS
        exact hnew (st.key y) (hI.key_lt y hy) (htr'.trans hflat.symm)
      refine ⟨hnd, hmem, hdown, ?_, ?_, ?_, ?_⟩
      · show (st.tbl ++ [fsig lts rp st.key z]).Nodup
        rw [List.nodup_append]
        refine ⟨hI.tbl_nodup, List.nodup_singleton _, fun a ha c hc hac => ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
        rw [List.mem_singleton.1 hc] at hac
        exact hnew i hi hac
      · intro w hw
        show Function.update st.key z st.tbl.length w < (st.tbl ++ [fsig lts rp st.key z]).length
        rw [List.length_append]
        rcases List.mem_append.1 hw with h | h
        · rw [hup _ w h]; have := hI.key_lt w h; simp; omega
        · rw [List.mem_singleton.1 h, Function.update_self]; simp
      · intro i hi
        have hi' : i < st.tbl.length + 1 := by simpa using hi
        by_cases hlt : i < st.tbl.length
        · obtain ⟨r', hr', hkr', hσr', htr'⟩ := hI.tblrep i hlt
          refine ⟨r', List.mem_append_left _ hr', ?_, hσr', ?_⟩
          · show Function.update st.key z st.tbl.length r' = i
            rw [hup _ r' hr']; exact hkr'
          · show (st.tbl ++ [fsig lts rp st.key z])[i] =
              fsig lts rp (Function.update st.key z st.tbl.length) r'
            rw [List.getElem_append_left hlt, fsig_update hI hTopo hznot hr']; exact htr'
        · have hieq : i = st.tbl.length := by omega
          subst hieq
          refine ⟨z, List.mem_append_right _ (List.mem_singleton_self z), ?_, hσz, ?_⟩
          · show Function.update st.key z st.tbl.length z = st.tbl.length
            rw [Function.update_self]
          · show (st.tbl ++ [fsig lts rp st.key z])[st.tbl.length] =
              fsig lts rp (Function.update st.key z st.tbl.length) z
            rw [List.getElem_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            exact fsig_congr fun t ht htb hd => (Function.update_of_ne
              (fun h => by
                have := hTopo z t ht
                rw [h] at this; exact lt_irrefl _ this) _ _).symm
      · have hzy' : ∀ y ∈ pre, (Function.update st.key z st.tbl.length z =
            Function.update st.key z st.tbl.length y ↔ e.d.sigFn z = e.d.sigFn y) := by
          intro y hy
          rw [Function.update_self, hup _ y hy]
          exact ⟨fun h => absurd h (ne_of_gt (hI.key_lt y hy)), fun h => absurd h (hzy y hy)⟩
        intro x hx y hy
        rcases List.mem_append.1 hx with hx | hx <;> rcases List.mem_append.1 hy with hy | hy
        · show Function.update st.key z _ x = Function.update st.key z _ y ↔ _
          rw [hup _ x hx, hup _ y hy]; exact hI.equiv x hx y hy
        · rw [List.mem_singleton.1 hy]
          exact ⟨fun h => ((hzy' x hx).1 h.symm).symm, fun h => ((hzy' x hx).2 h.symm).symm⟩
        · rw [List.mem_singleton.1 hx]; exact hzy' y hy
        · rw [List.mem_singleton.1 hx, List.mem_singleton.1 hy]
          exact ⟨fun _ => rfl, fun _ => rfl⟩

end Step

section Run

variable {e : Env lts rp b}

theorem kInv_foldl (hTopo : TopoSorted lts) (L : List (Fin n)) (hL : L.Pairwise (· < ·))
    (hmemL : ∀ x, x ∈ L ↔ rp.blk x = b ∧ rp.Dirty x) :
    ∀ (l pre : List (Fin n)) (st : KC n Label), pre ++ l = L → KInv e pre st →
      KInv e L (l.foldl (kcStep lts rp.blk (fun x => rp.Dirty x)) st) := by
  intro l
  induction l with
  | nil => intro pre st h hI; simpa [← h] using hI
  | cons z l ih =>
    intro pre st h hI
    have hzL : z ∈ L := by rw [← h]; simp
    obtain ⟨hz, hdz⟩ := (hmemL z).1 hzL
    have hLs : (pre ++ z :: l).Pairwise (· < ·) := h ▸ hL
    rw [List.pairwise_append] at hLs
    have hznot : z ∉ pre := fun hzp => lt_irrefl z (hLs.2.2 z hzp z (List.mem_cons_self))
    have hzpre : ∀ t, rp.blk t = b → rp.Dirty t → t < z → t ∈ pre := by
      intro t htb htd htz
      have htL : t ∈ pre ++ z :: l := h ▸ (hmemL t).2 ⟨htb, htd⟩
      rcases List.mem_append.1 htL with h1 | h1
      · exact h1
      · rcases List.mem_cons.1 h1 with h2 | h2
        · rw [h2] at htz; exact absurd htz (lt_irrefl _)
        · exact absurd htz (not_lt.2 (le_of_lt ((List.pairwise_cons.1 hLs.2.1).1 t h2)))
    refine ih (pre ++ [z]) _ (by rw [List.append_assoc]; exact h) ?_
    exact kInv_step hI hTopo hz hdz hznot hzpre

end Run

theorem sortedDirty_facts (rp : BD n) (b : ℕ) :
    (sortedDirty rp b).Pairwise (· < ·) ∧
      ∀ x, x ∈ sortedDirty rp b ↔ rp.blk x = b ∧ rp.Dirty x := by
  refine ⟨?_, ?_⟩
  · unfold sortedDirty
    exact List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  · intro x
    unfold sortedDirty
    simp [List.mem_filter, List.mem_finRange]


theorem tauLoopFree_of_topo (lts : LTS (Fin n) Label) (hTopo : TopoSorted lts) :
    TauLoopFree lts :=
  Subrelation.wf (fun {s' s} h => hTopo s s' h) (wellFounded_lt (α := Fin n))

/-- **The key computation computes `E π`** (headline). -/
theorem keyCompCorrect (lts : LTS (Fin n) Label) (rp : BD n) (b : ℕ) (key0 : Fin n → ℕ) :
    KeyCompCorrect lts rp b key0 := by
  intro hTopo hinv x y hx hy hdx hdy
  have hWF := tauLoopFree_of_topo lts hTopo
  obtain ⟨d⟩ := sigDataExists lts rp.setoid hWF
  let e : Env lts rp b := { d := d, hWF := hWF, hU := hinv.U, hS := hinv.S }
  obtain ⟨hpw, hmemL⟩ := sortedDirty_facts rp b
  have hI := kInv_foldl (e := e) hTopo (sortedDirty rp b) hpw hmemL (sortedDirty rp b) [] ⟨key0, []⟩
    (by simp) (KInv.init e key0)
  have hxL : x ∈ sortedDirty rp b := (hmemL x).2 ⟨hx, hdx⟩
  have hyL : y ∈ sortedDirty rp b := (hmemL y).2 ⟨hy, hdy⟩
  have := hI.equiv x hxL y hyL
  unfold keysOf kcRun
  rw [this]
  exact e.d.sig_iff_E hWF (show rp.blk x = rp.blk y from hx.trans hy.symm)

end RP

end Sigref
