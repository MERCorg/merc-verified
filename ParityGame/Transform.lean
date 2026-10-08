module

public import ParityGame.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.Find

open Cslib (ωSequence)

@[expose] public section Transform

namespace ParityGame

/-!
# Priority compression and propagation

Sections 3.3 and 3.4 of O. Friedmann and M. Lange, *Solving Parity Games in Practice*, ATVA 2009.

Both transformations only change the priority function, so a transformed game has exactly the same
nodes, edges, owners, plays and strategies. They are *sound* when every play (inside the subgame
of interest) is won by the same player before and after (`Game.PrioPreserves`); the winning
regions and strategies of the transformed game are then those of the original game
(`Game.Solves.of_withPrio`).
-/

variable {V : Type*}

/-- The game with the priority function replaced by `f`. -/
def Game.withPrio (G : Game V) (f : V → ℕ) : Game V := { G with prio := f }

/-- Replacing the priorities by `f` does not change the winner of any play inside `X`. -/
def Game.PrioPreserves (G : Game V) (X : Set V) (f : V → ℕ) : Prop :=
  ∀ p : ωSequence V, (∀ n, p n ∈ X ∧ G.edge (p n) (p (n + 1))) →
    ∀ i, (G.withPrio f).PlayWonBy i p ↔ G.PlayWonBy i p

/-- Solutions of the game with preserved priorities are solutions of the original game. -/
def Game.SolvesOfWithPrio (G : Game V) (X : Set V) (f : V → ℕ) : Prop :=
  G.PrioPreserves X f → ∀ r : Solution V, (G.withPrio f).Solves X r → G.Solves X r

/-! ### Priority compression (Section 3.3) -/

/-- `ω` is *a compression* of the priority set `S` (Section 3.3): monotone, decreasing,
    parity-preserving, dense and minimal on `S`. -/
def IsCompression (S : Set ℕ) (ω : ℕ → ℕ) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, x ≤ y → ω x ≤ ω y) ∧
  (∀ x ∈ S, ω x ≤ x) ∧
  (∀ x ∈ S, ω x % 2 = x % 2) ∧
  (∀ x ∈ S, ∀ y ∈ S, ω x + 1 < ω y → ∃ z ∈ S, ω x < ω z ∧ ω z < ω y) ∧
  (∃ x ∈ S, ω x < 2)

open scoped Classical in
/-- The compression of the priority set `S`, computed by a sweep through `S` in ascending order:
    the least priority is mapped to its parity, and each larger priority `x` is mapped to the
    image of its predecessor in `S`, plus one if the parities differ. -/
noncomputable def compress (S : Set ℕ) (x : ℕ) : ℕ :=
  if h : ∃ y ∈ S, y < x then
    (if sSup {y | y ∈ S ∧ y < x} % 2 = x % 2 then compress S (sSup {y | y ∈ S ∧ y < x})
      else compress S (sSup {y | y ∈ S ∧ y < x}) + 1)
  else x % 2
termination_by x
decreasing_by
  all_goals
    obtain ⟨y, hy, hyx⟩ := h
    have hmem : sSup {y | y ∈ S ∧ y < x} ∈ {y | y ∈ S ∧ y < x} :=
      Nat.sSup_mem ⟨y, hy, hyx⟩ ⟨x, fun z hz => hz.2.le⟩
    exact hmem.2

/-- Compressing the priorities occurring in `X` preserves the winner of every play in `X`. -/
def Game.CompressionSound (G : Game V) [Finite V] (X : Set V) : Prop :=
  G.PrioPreserves X (compress (G.prio '' X) ∘ G.prio)

/-- The sweep is a compression in the sense of Section 3.3. -/
def CompressIsCompression (S : Set ℕ) : Prop :=
  S.Nonempty → IsCompression S (compress S)

/-! ### Priority propagation (Section 3.4) -/

/-- Backward propagation: `Ω'(v) = max {Ω(v), min {Ω(w) | vEw}}` (successors inside `X`). -/
noncomputable def Game.propagateBwd (G : Game V) (X : Set V) (v : V) : ℕ :=
  max (G.prio v) (sInf (G.prio '' {w | w ∈ X ∧ G.edge v w}))

/-- Forward propagation: `Ω'(v) = max {Ω(v), min {Ω(u) | uEv}}` (predecessors inside `X`). -/
noncomputable def Game.propagateFwd (G : Game V) (X : Set V) (v : V) : ℕ :=
  max (G.prio v) (sInf (G.prio '' {u | u ∈ X ∧ G.edge u v}))

/-- Both propagations preserve the winner of every play inside `X` (Section 3.4). -/
def Game.PropagationSound (G : Game V) [Finite V] (X : Set V) : Prop :=
  G.PrioPreserves X (G.propagateBwd X) ∧ G.PrioPreserves X (G.propagateFwd X)

end ParityGame

end Transform
