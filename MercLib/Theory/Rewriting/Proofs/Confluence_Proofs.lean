module

public import MercLib.Theory.Rewriting.Confluence

@[expose] public section

/-!
# Proofs: Confluence

Newman's lemma for rewrite systems, and unique normal forms of convergent systems.

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/Rewriting.lean` (human-vetted).
-/

namespace MercLib.Rewriting

variable {S : Signature} {V W : VarSet S} {ι : Type} {R : TRS S V ι}

/-- **Newman's lemma.** A terminating, locally confluent rewrite system is confluent. -/
theorem confluent_of_locallyConfluent (ht : Terminating R W) (hl : LocallyConfluent R W) :
    Confluent R W :=
  fun s => Relation.LocallyConfluent.terminating_toConfluent (hl s) (ht s)

/-- In a terminating, confluent rewrite system every term has exactly one normal form. -/
theorem existsUnique_normalForm (ht : Terminating R W) (hc : Confluent R W) {s : S.Srt}
    (t : Term S W s) : ∃! u, Steps R s t u ∧ Normal R u :=
  (ht s).confluent_iff_forall_unique_normal.mp (hc s) t

end MercLib.Rewriting
