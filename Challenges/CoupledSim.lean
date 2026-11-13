import MercLib.Theory.CoupledSim.CoupledSimilarity
import MercLib.Theory.CoupledSim.FixedPoint
import MercLib.Theory.CoupledSim.Game

/-!
# Comparator challenge: coupled similarity (human-vetted)

The headline theorems of `MercLib/Theory/CoupledSim/` — the theory of coupled similarity
([B. Bisping and U. Nestmann, *Computing Coupled Similarity*][Bisping2019], Theorems 1–3 and
Lemmas 1–5, 7, 8, Corollary 1) — stated with `sorry` against the human-vetted spec files only;
`lake comparator` checks them against the solution module `MercLib`.

Every statement must be written exactly as in the proof files (binder names and binder kinds
included): the comparison is syntactic, not up to definitional unfolding.
-/

open Cslib (LTS HasTau)

namespace MercLib.CoupledSim

/-! ## Order properties of the coupled simulation preorder -/

/-- **Lemma 2 of [Bisping2019]** (reflexivity): the coupled simulation preorder is reflexive. -/
theorem CoupledSimulationPreorder.refl [HasTau Label] (lts : LTS State Label) (s : State) :
    s ≼cs[lts] s := sorry

/-- **Lemma 2 of [Bisping2019]** (transitivity): the coupled simulation preorder is transitive. -/
theorem CoupledSimulationPreorder.trans [HasTau Label] {lts : LTS State Label} {p q r : State}
    (h1 : p ≼cs[lts] q) (h2 : q ≼cs[lts] r) : p ≼cs[lts] r := sorry

/-- **Lemma 4 of [Bisping2019]**: if `q ⇒ p`, then `p ≼cs[lts] q`. -/
theorem preorder_of_tauReach [HasTau Label] {lts : LTS State Label} {p q : State}
    (h : lts.τSTr q p) : p ≼cs[lts] q := sorry

/-! ## Coupled delay simulations and the coinductive characterization -/

/-- **Lemma 1 of [Bisping2019]**: the coupled simulation preorder is exactly the greatest
relation that is a coupled delay simulation. -/
theorem cds_iff_preorder [HasTau Label] {lts : LTS State Label} {p q : State} :
    p ≼cs[lts] q ↔ ∃ r, IsCoupledDelaySimulation lts r ∧ r p q := sorry

/-- **Corollary 1 of [Bisping2019]**: states on a `τ`-cycle are coupled similar. -/
theorem tauCycle_coupledSimilarity [HasTau Label] {lts : LTS State Label} {p q : State}
    (h1 : lts.τSTr p q) (h2 : lts.τSTr q p) : p ≡cs[lts] q := sorry

/-- **Lemma 3 of [Bisping2019]**: the coupled simulation preorder can be characterized
coinductively: `p ≼cs[lts] q` iff every strong step of `p` can be answered by a delay step of
`q` into a related pair, and `q` can catch up to `p` by `τ`-steps into a related pair. -/
theorem preorder_coinductive_iff [HasTau Label] {lts : LTS State Label} {p q : State} :
    p ≼cs[lts] q ↔
      ((∀ μ p', lts.Tr p μ p' → ∃ q', DTr lts q μ q' ∧ p' ≼cs[lts] q') ∧
        ∃ q', lts.τSTr q q' ∧ q' ≼cs[lts] p) := sorry

/-- **Lemma 5 of [Bisping2019]**: if `p` and `q` have exactly the same outgoing transitions,
except that `p` has an additional `τ`-loop, then `p ≡cs[lts] q`. -/
theorem tauLoopIgnorance [HasTau Label] {lts : LTS State Label} {p q : State}
    (h : ∀ ⦃α p'⦄, lts.Tr p α p' ↔ (lts.Tr q α p' ∨ (α = HasTau.τ ∧ p' = p))) :
    p ≡cs[lts] q := sorry

/-! ## Reduction of weak similarity to coupled similarity (Theorem 1) -/

/-- **Theorem 1 of [Bisping2019]** (first part): on the sink-extended LTS, the weak simulation
preorder and the coupled simulation preorder coincide. -/
theorem extendSink_ws_iff_cs [HasTau Label] (lts : LTS State Label) (p q : Option State) :
    p ≼ws[extendSink lts] q ↔ p ≼cs[extendSink lts] q := sorry

/-- **Theorem 1 of [Bisping2019]** (second part): weak similarity in the original LTS agrees
with weak similarity between the corresponding `some`-states of the sink-extended LTS. -/
theorem extendSink_ws_some_iff [HasTau Label] (lts : LTS State Label) (s t : State) :
    s ≼ws[lts] t ↔ (some s) ≼ws[extendSink lts] (some t) := sorry

/-! ## The fixed-point algorithm (Lemmas 7, 8 and Theorem 2) -/

/-- **Lemma 7 of [Bisping2019]**: the greatest fixed points of `fpStep` are exactly the relations
equivalent to the coupled simulation preorder. -/
theorem gfp_iff_preorder [HasTau Label] (lts : LTS State Label) (r : State → State → Prop) :
    IsGreatestFixedPt lts r ↔ ∀ p q, r p q ↔ p ≼cs[lts] q := sorry

/-- **Theorem 2 of [Bisping2019]**: on finite state spaces, the fixed-point iteration returns the
coupled simulation preorder. -/
theorem exists_fpIter_eq_preorder [HasTau Label] [Finite State] (lts : LTS State Label) :
    ∃ n, ∀ p q, fpIter lts n p q ↔ p ≼cs[lts] q := sorry

/-! ## The coupled simulation game (Theorem 3) -/

/-- **Theorem 3 of [Bisping2019]**: the defender wins the coupled simulation game at `att p q`
precisely if `p ≼cs[lts] q`. -/
theorem defenderWinning_iff_preorder [HasTau Label] (lts : LTS State Label) (p q : State) :
    DefenderWinning lts (.att p q) ↔ p ≼cs[lts] q := sorry

end MercLib.CoupledSim
