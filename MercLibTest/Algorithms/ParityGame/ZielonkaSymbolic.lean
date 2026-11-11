import MercLib.Algorithms.ParityGame.ZielonkaSymbolic

/-!
# Tests for `MercLib.Algorithms.ParityGame.ZielonkaSymbolic`

Runs the set-based Zielonka algorithm and the attractor iteration on small games whose winning
regions are known by hand.
-/

namespace MercLibTest.ZielonkaSymbolic

open MercLib.ParityGame

/-- A game on `Fin n` from an owner table, a Boolean edge table and a priority table. -/
def mk {n : ℕ} (owner : Fin n → Player) (E : Fin n → Fin n → Bool) (prio : Fin n → ℕ)
    (total : ∀ v, ∃ w, E v w = true) : Game (Fin n) :=
  ⟨owner, fun v w => E v w = true, prio, total⟩

instance {n : ℕ} {owner : Fin n → Player} {E : Fin n → Fin n → Bool} {prio : Fin n → ℕ}
    {total : ∀ v, ∃ w, E v w = true} : DecidableRel (mk owner E prio total).edge :=
  fun v w => inferInstanceAs (Decidable (E v w = true))

/-- `0 → 1 → 2 → 0` and a loop on `2`; Even owns `0` and `2` and loops on priority `2`. Even wins
everywhere, since Odd's vertex `1` can only move to `2`. -/
abbrev g₁ : Game (Fin 3) :=
  mk (fun v => if v = 1 then .one else .zero)
    (fun v w => w = v + 1 || (v = 2 && w = 2)) (fun v => v.val) (by decide)

#guard g₁.zielonkaSym .zero = Finset.univ
#guard g₁.zielonkaSym .one = ∅

/-- A two-cycle through priorities `0` and `1`: Odd wins everywhere. -/
abbrev g₂ : Game (Fin 2) :=
  mk (fun _ => .zero) (fun v w => w = v + 1) (fun v => v.val) (by decide)

#guard g₂.zielonkaSym .zero = ∅
#guard g₂.zielonkaSym .one = Finset.univ

/-- Even loops on `0` (priority `2`) and Odd on `1` (priority `3`); vertex `2` of Even and vertex
`3` of Odd can each move to `0` or `1`, and each owner picks its own loop. -/
abbrev g₃ : Game (Fin 4) :=
  mk (fun v => if v = 1 ∨ v = 3 then .one else .zero)
    (fun v w => (v = 0 && w = 0) || (v = 1 && w = 1) || (v ≥ 2 && w ≤ 1))
    (fun v => if v = 0 then 2 else if v = 1 then 3 else 0) (by decide)

#guard g₃.zielonkaSym .zero = {0, 2}
#guard g₃.zielonkaSym .one = {1, 3}

-- Even attracts `2` to `{0}`, but not Odd's vertex `3`, which can escape to `1`.
#guard g₃.attrSym Finset.univ .zero {0} = {0, 2}
-- Odd attracts both `3` and Odd's own vertex `1` to `{1}`; vertex `2` escapes to `0`.
#guard g₃.attrSym Finset.univ .one {1} = {1, 3}

end MercLibTest.ZielonkaSymbolic
