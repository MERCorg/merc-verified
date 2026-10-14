module

public import ParityGame.Certificate
public import ParityGame.Proofs.Lifting_Proofs
public import ParityGame.Proofs.TwoSidedAlgorithm_Proofs
public import ParityGame.Proofs.Region_Proofs

@[expose] public section CertificateProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorems live in `ParityGame/Pins/Certificate_Pins.lean`.

* Soundness: a certificate labelling is, word for word, a progress measure on the whole game for
  the truncated lexicographic codomain (`Game.certPM_iff`), so `Game.progressMeasureSound` makes
  the first domain player `0`'s and, through `Game.dualWinsFrom` in the dual game, the second
  player `1`'s; exclusivity is `Game.not_wins_both` and covering is part of validity.
* Completeness: Zielonka's regions are dominions (winning with a strategy, closed under its
  moves); `Game.chainTreeComplete_truncLex` turns each into chain-tree labels, for player `1`
  in the dual game. The label bound needs that a region has at most `|V|` components
  (`Game.card_lowComps_le`: components are non-empty and disjoint) and `Game.chainBound_le`. -/

variable {V : Type*}

/-! ### Small labels -/

/-- A region has at most as many weakly connected components as the game has nodes. -/
theorem Game.card_lowComps_le [Finite V] (G : Game V) (R : Set V) (q : ℕ) :
    Nat.card (G.lowComps R q) ≤ Nat.card V := by
  classical
  have hrep : ∀ K : G.lowComps R q, ∃ v, (K : Set V) = G.lowComp R q v := fun K => by
    obtain ⟨v, -, -, hK⟩ := K.2
    exact ⟨v, hK⟩
  choose f hf using hrep
  refine Nat.card_le_card_of_injective f fun K K' h => Subtype.ext ?_
  rw [hf K, hf K', h]

/-- Every coordinate of a chain-tree leaf is at most the number of nodes. -/
theorem Game.chainLeaf_le_card [Finite V] (G : Game V) (X : Set V) {a : ℕ → ℕ}
    (ha : G.IsChainLeaf X a) (i : ℕ) : a i ≤ Nat.card V := by
  obtain ⟨h0, hk, hc, hz⟩ := ha
  by_cases hi : 2 * G.height X ≤ i
  · rw [hz i hi]; exact Nat.zero_le _
  · rcases Nat.even_or_odd' i with ⟨l, rfl | rfl⟩
    · rcases l with _ | l
      · rw [h0]; exact Nat.zero_le _
      · have h1 := hk l (by omega)
        have h2 := G.card_lowComps_le (G.leafRegion X a l) (G.level X l)
        omega
    · have := (hc l (by omega)).trans (G.chainBound_le _ _)
      omega

/-- The number of odd levels is at most the number of nodes. -/
theorem Game.height_le_card [Finite V] (G : Game V) (X : Set V) :
    G.height X ≤ Nat.card V := by
  classical
  unfold Game.height Game.oddPrios
  rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  calc (G.prio '' X ∩ {p | p % 2 = 1}).ncard ≤ (G.prio '' X).ncard :=
        Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
    _ ≤ X.ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ Nat.card V := Set.ncard_le_card X

/-! ### Certificate labellings are progress measures -/

/-- A certificate labelling is a progress measure of the whole game for the truncated
    lexicographic codomain. -/
theorem Game.certPM_iff [Finite V] (G : Game V) (D : Set V) (μ : V → ℕ → ℕ) (σ : Strategy V) :
    G.CertPM D μ σ ↔
      G.IsProgressMeasure Set.univ
        (truncLexCodomain (G.chainDepth Set.univ) (G.chainDepth_antitone Set.univ)) D μ σ := by
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨Set.subset_univ _, h0, fun v hv ho w _ he => h1 v hv ho w he⟩
  · rintro ⟨-, h0, h1⟩
    exact ⟨h0, fun v hv ho w he => h1 v hv ho w (Set.mem_univ _) he⟩

theorem Game.isSubgame_univ (G : Game V) : G.IsSubgame Set.univ := fun v _ => by
  obtain ⟨w, hw⟩ := G.total v
  exact ⟨w, Set.mem_univ _, hw⟩

/-! ### Soundness -/

/-- A valid certificate determines the winning regions (headline). -/
theorem Game.certSound [Finite V] (G : Game V) (c : Game.Cert V) : G.CertSound c := by
  rintro ⟨h0, h1, hcov⟩ v
  have hw0 : ∀ v ∈ c.D₀, G.Wins Set.univ .zero v := fun v hv =>
    ⟨c.σ₀, G.progressMeasureSound Set.univ _ c.D₀ c.μ₀ c.σ₀ G.isSubgame_univ
      ((G.certPM_iff _ _ _).1 h0) v hv⟩
  have hw1 : ∀ v ∈ c.D₁, G.Wins Set.univ .one v := fun v hv =>
    ⟨c.σ₁, (G.dualWinsFrom Set.univ .zero c.σ₁ v).1
      (G.dual.progressMeasureSound Set.univ _ c.D₁ c.μ₁ c.σ₁ G.dual.isSubgame_univ
        ((G.dual.certPM_iff _ _ _).1 h1) v hv)⟩
  have hv : v ∈ c.D₀ ∨ v ∈ c.D₁ := by
    have : v ∈ c.D₀ ∪ c.D₁ := hcov ▸ Set.mem_univ v
    exact this
  refine ⟨⟨hw0 v, fun hw => ?_⟩, ⟨hw1 v, fun hw => ?_⟩⟩
  · rcases hv with h | h
    · exact h
    · exact (G.not_wins_both (i := .zero) hw (hw1 v h)).elim
  · rcases hv with h | h
    · exact (G.not_wins_both (i := .one) hw (hw0 v h)).elim
    · exact h

/-! ### Completeness -/

/-- Zielonka's region of player `j` is a dominion: `j` wins from it with the returned strategy and
    its moves stay inside. -/
theorem Game.zielonka_dominion [Finite V] (G : Game V) (j : Player) :
    (∀ v ∈ G.zielonka.win j, G.WinsFrom Set.univ j (G.zielonka.strat j) v) ∧
    (∀ v ∈ G.zielonka.win j, ∀ w, G.Step Set.univ j (G.zielonka.strat j) v w →
      w ∈ G.zielonka.win j) := by
  have hs : G.Solves Set.univ G.zielonka := G.zielonka_correct
  refine ⟨hs.2.2 j, fun v hv w hstep => ?_⟩
  have hr := hs.strong.region j
  by_cases ho : G.owner v = j
  · rw [hstep.2.2.2 ho]
    exact (hr.mine v hv ho).1
  · exact hr.theirs v hv ho w hstep.2.1 hstep.2.2.1

/-- Every finite game has a valid certificate with small labels (headline). -/
theorem Game.certComplete [Finite V] (G : Game V) : G.CertComplete := by
  classical
  have hs : G.Strong Set.univ G.zielonka := (G.zielonka_correct : G.Solves _ _).strong
  obtain ⟨hwin0, hcl0⟩ := G.zielonka_dominion .zero
  obtain ⟨hwin1, hcl1⟩ := G.zielonka_dominion .one
  obtain ⟨μ₀, hpm0, hleaf0⟩ := G.chainTreeComplete_truncLex Set.univ (fun _ _ _ => Iff.rfl)
    (G.zielonka.win .zero) (G.zielonka.strat .zero) hwin0 hcl0
  obtain ⟨μ₁, hpm1, hleaf1⟩ := G.dual.chainTreeComplete_truncLex Set.univ (fun _ _ _ => Iff.rfl)
    (G.zielonka.win .one) (G.zielonka.strat .one)
    (fun v hv => (G.dualWinsFrom Set.univ .zero _ v).2 (hwin1 v hv))
    (fun v hv w hstep => hcl1 v hv w ((G.dual_step Set.univ .zero _ v w).1 hstep))
  refine ⟨G.height_le_card _, G.dual.height_le_card _,
    ⟨μ₀, G.zielonka.strat .zero, G.zielonka.win .zero, μ₁, G.zielonka.strat .one,
      G.zielonka.win .one⟩,
    ⟨(G.certPM_iff _ _ _).2 hpm0, (G.dual.certPM_iff _ _ _).2 hpm1, hs.cover⟩, ?_, ?_⟩
  · intro v hv i
    exact ⟨G.chainLeaf_le_card _ (hleaf0 v hv) i, (hleaf0 v hv).2.2.2 i⟩
  · intro v hv i
    exact ⟨G.dual.chainLeaf_le_card _ (hleaf1 v hv) i, (hleaf1 v hv).2.2.2 i⟩

end ParityGame

end CertificateProofs
