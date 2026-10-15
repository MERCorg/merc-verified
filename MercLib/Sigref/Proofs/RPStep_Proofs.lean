module

public import MercLib.Sigref.Refinable
public import MercLib.Sigref.Branching
public import MercLib.Sigref.Proofs.Refinable_Proofs

@[expose] public section

/-!
# Proofs: RPStep

The backwards closure computes `inertClosure` of the dirty states of the block.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). -/

namespace MercLib.Sigref

open MercLib.LTS MercLib.Signatures

open Cslib

namespace RP

variable {n : ℕ} {Label : Type} [HasTau Label]

theorem inertReach_iff (lts : LTS (Fin n) Label) (rp : RP n) (x d : Fin n) :
    InertReach lts rp.setoid x d ↔
      Relation.ReflTransGen (fun u v => lts.Tr u HasTau.τ v ∧ rp.blk u = rp.blk v) x d :=
  Iff.rfl

/-- The backwards closure computes `inertClosure` of the dirty states of the block. -/
theorem closure_view (lts : LTS (Fin n) Label) {preds : Fin n → List (Fin n)}
    (hpreds : ∀ x y, y ∈ preds x ↔ lts.Tr y HasTau.τ x) {rp : RP n} {b : ℕ}
    (hwf : rp.WF) (hb : b < rp.nb) (x : Fin n) (hx : rp.blk x = b) :
    (closure b preds rp).Dirty x ↔
      x ∈ inertClosure lts rp.setoid {d | rp.blk d = b ∧ rp.Dirty d} := by
  rw [(closure_spec hpreds hwf hb).2.2.2.1 x hx]
  constructor
  · rintro ⟨d, hd1, hd2, hp⟩; exact ⟨d, ⟨hd1, hd2⟩, hp⟩
  · rintro ⟨d, ⟨hd1, hd2⟩, hp⟩; exact ⟨d, hd1, hd2, hp⟩

end RP

end MercLib.Sigref
