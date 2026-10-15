module

public import MercLib.Graph.Tarjan
public import MercLib.Graph.Proofs.Scc_Proofs

@[expose] public section

/-!
# Proofs: the blocks of an SCC partition of the Tarjan model are SCCs

Machine-generated; may be freely edited or regenerated (see AGENTS.md). Relates the numbering
`IsSccPartition` of `Graph/Tarjan.lean` to the set-based `MercLib.Graph.IsSCC` of `Graph/Scc.lean`.
-/

namespace MercLib.Tarjan

open Relation

variable {n : ℕ}

/-- Reachability inside the whole vertex set is plain reachability. -/
theorem reach_univ_iff (g : Graph n) (u v : Fin n) :
    MercLib.Graph.Reach (Edge g) Set.univ u v ↔ ReflTransGen (Edge g) u v := by
  constructor
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ he ih => exact ih.tail he.2.2
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ he ih => exact ih.tail ⟨trivial, trivial, he⟩

/-- Every block of an SCC numbering is an SCC of the graph. -/
theorem IsSccPartition.isSCC {g : Graph n} {blk : Fin n → ℕ} {k : ℕ} (h : IsSccPartition g blk k)
    (s : Fin n) : MercLib.Graph.IsSCC (Edge g) Set.univ {t | blk t = blk s} := by
  refine ⟨⟨s, rfl⟩, Set.subset_univ _, fun u hu v hv => ?_, fun u hu w _ huw hwu => ?_⟩
  · rw [reach_univ_iff]
    exact ((h.2.2 u v).1 (hu.trans hv.symm)).1
  · rw [reach_univ_iff] at huw hwu
    exact ((h.2.2 w u).2 ⟨hwu, huw⟩).trans hu

end MercLib.Tarjan
