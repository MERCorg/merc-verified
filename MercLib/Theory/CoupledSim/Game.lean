module

public import MercLib.Theory.CoupledSim.CoupledSimilarity
public import Mathlib.Order.FixedPoints

open Cslib (LTS HasTau)

@[expose] public section

namespace MercLib.CoupledSim

/-!
# The coupled simulation game

This module formalises the game characterisation of the coupled simulation preorder
(Section 4 of [B. Bisping and U. Nestmann, *Computing Coupled Similarity*][Bisping2019],
Definitions 7–10). We do not model plays and strategies explicitly: since all infinite plays are
won by the attacker in a bounded game (the game graph is finite whenever the LTS is), the
defender's winning region is the greatest fixed point of the monotone `defenderStep` operator
below, i.e. the standard coinductive (greatest-fixed-point) winning-region semantics of the
game. Theorem 3 of [Bisping2019] — the defender wins the game at `att p q` iff
`p ≼cs[lts] q` — is proved against this characterisation.

## Main definitions

- `CSGameNode`: game positions `att p q`, `sim a p' q`, `cpl p q` (Definition 7).
- `CSGameMoves`: the game graph (Definition 8).
- `defenderStep` / `defenderHom`: the monotone one-step operator on defender-winning regions
  (Definition 9 in coinductive form).
- `DefenderWinning`: the defender's winning region (greatest fixed point of `defenderHom`).

## Main statements

See the `Proofs/` files next to this module; the headline theorems are restated in
`Challenges/CoupledSim.lean`.

## References

- [B. Bisping and U. Nestmann, *Computing Coupled Similarity*][Bisping2019]
-/

/-! ## Game nodes and moves -/

/-- Game positions (Definition 7 of [Bisping2019]): `att p q` challenges with a transition of
`p`, `sim a p' q` lets the defender answer a `μ`-challenge with a delay step of `q`, and
`cpl p q` lets the defender answer the coupling challenge with `τ`-steps of `q`. -/
inductive CSGameNode [HasTau Label] (lts : LTS State Label) where
  | att (p q : State)
  | sim (a : Label) (p' q : State)
  | cpl (p q : State)

/-- The game graph (Definition 8 of [Bisping2019]):
- attacker: challenge a visible step of `p`, or follow a `τ`-step of `p` without changing `q`;
- defender (sim): answer with a delay step of `q`;
- attacker: challenge the coupling;
- defender (cpl): catch up by `τ`-steps of `q` and turn the position around. -/
def CSGameMoves [HasTau Label] (lts : LTS State Label) :
    CSGameNode lts → CSGameNode lts → Prop :=
  fun n n' =>
    match n, n' with
    | .att p q, .sim a p' q' => lts.Tr p a p' ∧ a ≠ HasTau.τ ∧ q = q'
    | .att p q, .att p' q' => lts.Tr p HasTau.τ p' ∧ q = q'
    | .sim a p' q, .att p'' q' => p' = p'' ∧ DTr lts q a q'
    | .att p q, .cpl p' q' => p = p' ∧ q = q'
    | .cpl p q, .att q' p' => p = p' ∧ lts.τSTr q q'
    | _, _ => False

/-! ## The defender's winning region -/

/-- One step of the winning-region computation (Definition 9 of [Bisping2019] in coinductive
form): at an attacker node the defender must cope with every attacker move; at defender nodes
one suitable move must lead back into the winning region. (All infinite plays are won by the
attacker, so defender nodes must be able to keep the play going.) -/
def defenderStep [HasTau Label] (lts : LTS State Label)
    (d : CSGameNode lts → Prop) : CSGameNode lts → Prop :=
  fun n =>
    match n with
    | .att _ _ => ∀ n', CSGameMoves lts n n' → d n'
    | .sim _ _ _ => ∃ n', CSGameMoves lts n n' ∧ d n'
    | .cpl p q => ∃ q', lts.τSTr q q' ∧ d (.att q' p)

/-- `defenderStep` as a bundled monotone operator, to take the greatest fixed point of. -/
def defenderHom [HasTau Label] (lts : LTS State Label) :
    (CSGameNode lts → Prop) →o (CSGameNode lts → Prop) where
  toFun := defenderStep lts
  monotone' := by
    intro x y hxy n
    match n with
    | .att _ _ => intro h n' hn'; exact hxy _ (h n' hn')
    | .sim _ _ _ =>
      rintro ⟨n', hn', hd⟩
      exact ⟨n', hn', hxy _ hd⟩
    | .cpl _ _ => rintro ⟨q', hτ, hd⟩; exact ⟨q', hτ, hxy _ hd⟩

/-- The defender's winning region (Definition 10 of [Bisping2019]): the greatest fixed point of
`defenderHom`, i.e. the largest set of positions from which the defender can keep every play
alive forever — the coinductive winning-region semantics of the game. -/
def DefenderWinning [HasTau Label] (lts : LTS State Label) : CSGameNode lts → Prop :=
  OrderHom.gfp (defenderHom lts)

end MercLib.CoupledSim
