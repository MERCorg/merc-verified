import MercLib.Algorithms.ParityGame.HybridSI.Algorithm

/-!
# Tests for `MercLib.Algorithms.ParityGame.HybridSI.Algorithm`

Solves small parity games with H-B and compares the winners with a hand analysis. Vertices are
`Fin n` in relevance order, and every game below has `prio v = v`, so the games are relabelled
(`Game.Relabelled`) as the valuation requires.
-/

namespace MercLibTest.HybridSI

open MercLib.ParityGame MercLib.HybridSI

/-- A game on `Fin n` from owners and adjacency lists, with `prio v = v`. -/
def mk (n : ℕ) (own : Fin n → Player) (adj : Fin n → List (Fin n))
    (h : ∀ v, ∃ w, w ∈ adj v) : Game (Fin n) :=
  ⟨own, fun v w => w ∈ adj v, fun v => v, h⟩

/-- The edges of `mk` are decidable: they are list membership. -/
@[instance_reducible]
def mkDec (n : ℕ) (own : Fin n → Player) (adj : Fin n → List (Fin n)) (h : ∀ v, ∃ w, w ∈ adj v) :
    DecidableRel (mk n own adj h).edge := fun v w => decidable_of_iff (w ∈ adj v) Iff.rfl

/-- Every vertex reaches the even self-loop at `0`; Odd at `2` avoids its own self-loop
(priority 2, even) and moves to `1`, and Even at `1` moves to `0`. Even wins everywhere. -/
def gA : Game (Fin 3) :=
  mk 3 (fun | 0 => .one | 1 => .zero | 2 => .one)
    (fun | 0 => [0] | 1 => [0, 1] | 2 => [1, 2]) (by decide)

/-- `gA` plus an odd self-loop at `3`: Odd at `2` now escapes to `3` and wins `2` and `3`;
Even still wins `0` and `1`. -/
def gB : Game (Fin 4) :=
  mk 4 (fun | 0 => .one | 1 => .zero | 2 => .one | 3 => .one)
    (fun | 0 => [0] | 1 => [0, 1] | 2 => [1, 2, 3] | 3 => [3]) (by decide)

/-- An Even vertex choosing between the odd self-loop at `1` and the even self-loop at `2`:
Even wins `0` and `2`, Odd wins `1`. -/
def gC : Game (Fin 3) :=
  mk 3 (fun | 0 => .zero | 1 => .one | 2 => .zero)
    (fun | 0 => [1, 2] | 1 => [1] | 2 => [2]) (by decide)

instance : DecidableRel gA.edge := mkDec _ _ _ _
instance : DecidableRel gB.edge := mkDec _ _ _ _
instance : DecidableRel gC.edge := mkDec _ _ _ _

#guard hbSolve gA 100 100 = some [Player.zero, Player.zero, Player.zero]
#guard hbSolve gB 100 100 = some [Player.zero, Player.zero, Player.one, Player.one]
#guard hbSolve gC 100 100 = some [Player.zero, Player.one, Player.zero]

end MercLibTest.HybridSI
