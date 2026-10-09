import Sigref.Proofs.TopoSort_Proofs

open Sigref.Topo

-- Contract pin: fails to compile if `topoSortCorrect`'s signature drifts.
example : ∀ {n : ℕ} (succ : Fin n → List (Fin n)),
    (∀ v, ¬ Relation.TransGen (fun a b => b ∈ succ a) v v) →
    ∀ c : Cfg n, Relation.ReflTransGen (fun a b => step succ a = some b) (init n) c →
      step succ c = none →
        c.acyc = true ∧ c.order.Nodup ∧ (∀ v, v ∈ c.order) ∧
        ∀ (l1 : List (Fin n)) (a : Fin n) (l2 : List (Fin n)), c.order = l1 ++ a :: l2 → ∀ b ∈ succ a, b ∈ l1 :=
  fun succ => topoSortCorrect succ

-- Contract pin: fails to compile if `topoSortTerminates`'s signature drifts.
example : ∀ {n : ℕ} (succ : Fin n → List (Fin n)) (c c' : Cfg n),
    step succ c = some c' → measure succ c' < measure succ c :=
  fun succ => topoSortTerminates succ
