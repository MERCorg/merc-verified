import MercLib.Algorithms.ParityGame.Incomplete

/-!
# Tests for `MercLib.Algorithms.ParityGame.Incomplete`

Runs the safe-set and (safe) attractor computations on the incomplete parity game of Figure 2 and
Examples 6 and 7 of [Laveaux2022].
-/

namespace MercLibTest.Incomplete

open MercLib.ParityGame

/-- An incomplete game on all of `Fin n` from an owner table, a Boolean edge table, a priority
table and a Boolean table of incomplete vertices. -/
def mk {n : ℕ} (owner : Fin n → Player) (E : Fin n → Fin n → Bool) (prio : Fin n → ℕ)
    (inc : Fin n → Bool) : IncompleteGame (Fin n) where
  vs := Set.univ
  owner := owner
  edge v w := E v w = true
  prio := prio
  edge_mem _ _ _ := ⟨trivial, trivial⟩
  I := {v | inc v = true}
  I_sub _ _ := trivial

section
variable {n : ℕ} {owner : Fin n → Player} {E : Fin n → Fin n → Bool} {prio : Fin n → ℕ}
  {inc : Fin n → Bool}

instance : DecidablePred (· ∈ (mk owner E prio inc).vs) := fun _ => isTrue trivial

instance : DecidablePred (· ∈ (mk owner E prio inc).I) :=
  fun v => inferInstanceAs (Decidable (inc v = true))

instance : DecidableRel (mk owner E prio inc).edge :=
  fun v w => inferInstanceAs (Decidable (E v w = true))
end

/-- Figure 2 of [Laveaux2022] with the solid edges only, and `I = {u₃, u₅}` (Example 6). Even (`♦`)
owns `u₀ u₂ u₃`, Odd (`□`) owns `u₁ u₄ u₅`; `u₁` and `u₅` are sinks. -/
abbrev fig2 : IncompleteGame (Fin 6) :=
  mk (fun v => if v = 1 ∨ v = 4 ∨ v = 5 then .one else .zero)
    (fun v w => (v, w) ∈ [(0, 1), (0, 2), (2, 0), (3, 2), (4, 2), (4, 3), (4, 5)])
    (fun v => [2, 3, 0, 2, 1, 2][v]!) (fun v => v = 3 || v = 5)

#guard Incomplete.sinks fig2 = {1, 5}

/-! Example 7: `safe♦(a) = {u₀, u₁, u₂, u₃}` and `safe□(a) = {u₀, u₁, u₂, u₄, u₅}`. -/
#guard Incomplete.attr fig2 .one (Incomplete.own fig2 .one ∩ Incomplete.I fig2) = {4, 5}
#guard Incomplete.safe fig2 .zero = {0, 1, 2, 3}
#guard Incomplete.safe fig2 .one = {0, 1, 2, 4, 5}

/-! The safe attractor does not attract through the incomplete vertex `u₃` of `♦`, which may get
a successor outside the target later. -/
#guard Incomplete.attr fig2 .one {2} = {2, 3, 4}
#guard Incomplete.sattr fig2 .one {2} = {2, 4}

/-! Corollary 3: `♦` safely attracts to the complete sink `u₁` of `□`; the sink `u₅` is
incomplete and is left out. -/
#guard (Incomplete.own fig2 .one ∩ Incomplete.sinks fig2) \ Incomplete.I fig2 = {1}
#guard Incomplete.sattr fig2 .zero {1} = {0, 1, 2, 3}

/-! `cpre` leaves out the sinks: the sinks `u₁, u₅` of `□` have all their (no) successors in `∅`,
but are not in `cpre♦(a, ∅)`. -/
#guard Incomplete.cpre fig2 .zero ∅ = ∅

end MercLibTest.Incomplete
