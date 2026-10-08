module

public import ParityGame.Transform
public import ParityGame.Proofs.Defs_Proofs
public import ParityGame.Proofs.Region_Proofs

open Cslib (ωSequence)

@[expose] public section TransformProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). -/

variable {V : Type*}

/-! ### Transferring solutions along priority changes -/

theorem Game.solves_of_withPrio (G : Game V) (X : Set V) (f : V → ℕ) : G.SolvesOfWithPrio X f := by
  intro hf r hr
  obtain ⟨hcov, hdisj, hwin⟩ := hr
  refine ⟨hcov, hdisj, fun i v hv => ?_⟩
  obtain ⟨h1, h2⟩ := hwin i v hv
  refine ⟨h1, fun p hp0 hconf => ?_⟩
  have hconf' : ∀ n, p n ∈ X ∧ G.edge (p n) (p (n + 1)) := fun n =>
    ⟨(hconf n).1, (hconf n).2.2.1⟩
  exact (hf p hconf' i).mp (h2 p hp0 hconf)

/-! ### Priority compression -/

section Compress
variable (S : Set ℕ)

theorem compress_pred {x : ℕ} (h : ∃ y ∈ S, y < x) :
    sSup {y | y ∈ S ∧ y < x} ∈ S ∧ sSup {y | y ∈ S ∧ y < x} < x ∧
      ∀ z ∈ S, z < x → z ≤ sSup {y | y ∈ S ∧ y < x} := by
  obtain ⟨y, hy, hyx⟩ := h
  have hb : BddAbove {y | y ∈ S ∧ y < x} := ⟨x, fun z hz => hz.2.le⟩
  have hmem : sSup {y | y ∈ S ∧ y < x} ∈ {y | y ∈ S ∧ y < x} := Nat.sSup_mem ⟨y, hy, hyx⟩ hb
  exact ⟨hmem.1, hmem.2, fun z hz hzx => le_csSup hb ⟨hz, hzx⟩⟩

theorem compress_of_exists {x : ℕ} (h : ∃ y ∈ S, y < x) :
    compress S x = if sSup {y | y ∈ S ∧ y < x} % 2 = x % 2
      then compress S (sSup {y | y ∈ S ∧ y < x})
      else compress S (sSup {y | y ∈ S ∧ y < x}) + 1 := by
  rw [compress, dif_pos h]

theorem compress_of_not {x : ℕ} (h : ¬ ∃ y ∈ S, y < x) : compress S x = x % 2 := by
  rw [compress, dif_neg h]

theorem compress_parity (x : ℕ) : compress S x % 2 = x % 2 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases h : ∃ y ∈ S, y < x
    · obtain ⟨-, hlt, -⟩ := compress_pred S h
      have := ih _ hlt
      rw [compress_of_exists S h]
      split_ifs with hp <;> omega
    · rw [compress_of_not S h]; omega

theorem compress_le_self (x : ℕ) : compress S x ≤ x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases h : ∃ y ∈ S, y < x
    · obtain ⟨-, hlt, -⟩ := compress_pred S h
      have := ih _ hlt
      rw [compress_of_exists S h]
      split_ifs <;> omega
    · rw [compress_of_not S h]; omega

theorem compress_pred_le {x : ℕ} (h : ∃ y ∈ S, y < x) :
    compress S (sSup {y | y ∈ S ∧ y < x}) ≤ compress S x ∧
      compress S x ≤ compress S (sSup {y | y ∈ S ∧ y < x}) + 1 := by
  rw [compress_of_exists S h]
  split_ifs <;> omega

theorem compress_mono {x x' : ℕ} (hx : x ∈ S) (hx' : x' ∈ S) (hle : x ≤ x') :
    compress S x ≤ compress S x' := by
  induction x' using Nat.strong_induction_on with
  | _ x' ih =>
    rcases hle.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have h : ∃ y ∈ S, y < x' := ⟨x, hx, hlt⟩
      obtain ⟨hyS, hylt, hmax⟩ := compress_pred S h
      have h1 := hmax x hx hlt
      exact (ih _ hylt hyS h1).trans (compress_pred_le S h).1

theorem compress_dense {x y : ℕ} (_hx : x ∈ S) (hy : y ∈ S)
    (hlt : compress S x + 1 < compress S y) :
    ∃ z ∈ S, compress S x < compress S z ∧ compress S z < compress S y := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    have h : ∃ z ∈ S, z < y := by
      by_contra hn
      have := compress_of_not S hn
      omega
    obtain ⟨hyS, hylt, -⟩ := compress_pred S h
    obtain ⟨h1, h2⟩ := compress_pred_le S h
    by_cases heq : compress S (sSup {z | z ∈ S ∧ z < y}) = compress S y
    · obtain ⟨z, hz, a, b⟩ := ih (sSup {z | z ∈ S ∧ z < y}) hylt hyS (by omega)
      exact ⟨z, hz, a, heq ▸ b⟩
    · exact ⟨_, hyS, by omega, by omega⟩

theorem compress_isCompression : CompressIsCompression S := by
  intro hne
  refine ⟨fun x hx y hy hxy => compress_mono S hx hy hxy, fun x _ => compress_le_self S x,
    fun x _ => compress_parity S x, fun x hx y hy h => compress_dense S hx hy h, ?_⟩
  refine ⟨sInf S, Nat.sInf_mem hne, ?_⟩
  have : ¬ ∃ y ∈ S, y < sInf S := fun ⟨y, hy, hlt⟩ => absurd (Nat.sInf_le hy) (by omega)
  rw [compress_of_not S this]
  omega

end Compress

/-- Compression preserves the winner of every play in `X`. -/
theorem Game.compressionSound (G : Game V) [Finite V] (X : Set V) : G.CompressionSound X := by
  intro p hp i
  set S := G.prio '' X with hS
  obtain ⟨M, hM⟩ := G.exists_maxInfPrio p
  rw [Game.maxInfPrio_iff] at hM
  obtain ⟨⟨v₀, hv₀, hv₀M⟩, hbound⟩ := hM
  have hmemS : ∀ v ∈ nodeInf p, G.prio v ∈ S := by
    intro v hv
    obtain ⟨k, -, hk⟩ := (Filter.frequently_atTop.mp hv) 0
    exact ⟨v, hk ▸ (hp k).1, rfl⟩
  have hM' : (G.withPrio (compress S ∘ G.prio)).MaxInfPrio p (compress S M) := by
    rw [Game.maxInfPrio_iff]
    refine ⟨⟨v₀, hv₀, by simp [Game.withPrio, hv₀M]⟩, fun v hv => ?_⟩
    show compress S (G.prio v) ≤ compress S M
    exact compress_mono S (hmemS v hv) (hv₀M ▸ hmemS v₀ hv₀) (hbound v hv)
  have hM0 : G.MaxInfPrio p M := by
    rw [Game.maxInfPrio_iff]; exact ⟨⟨v₀, hv₀, hv₀M⟩, hbound⟩
  refine G.playWonBy_iff_of_maxInfPrio hM0 hM' ?_ i
  simp only [Player.ofPrio, compress_parity]

/-! ### Priority propagation -/

theorem Game.prioPreserves_of_bound (G : Game V) [Finite V] (X : Set V) (f : V → ℕ)
    (hf : ∀ p : ωSequence V, (∀ n, p n ∈ X ∧ G.edge (p n) (p (n + 1))) → ∀ M,
      G.MaxInfPrio p M → ∀ v ∈ nodeInf p, G.prio v ≤ f v ∧ f v ≤ M) : G.PrioPreserves X f := by
  intro p hp i
  obtain ⟨M, hM⟩ := G.exists_maxInfPrio p
  have hb := hf p hp M hM
  rw [Game.maxInfPrio_iff] at hM
  obtain ⟨⟨v₀, hv₀, hv₀M⟩, hbound⟩ := hM
  have hM' : (G.withPrio f).MaxInfPrio p M := by
    rw [Game.maxInfPrio_iff]
    refine ⟨⟨v₀, hv₀, le_antisymm (hb v₀ hv₀).2 (hv₀M ▸ (hb v₀ hv₀).1)⟩, fun v hv => (hb v hv).2⟩
  have hM0 : G.MaxInfPrio p M := by
    rw [Game.maxInfPrio_iff]; exact ⟨⟨v₀, hv₀, hv₀M⟩, hbound⟩
  exact G.playWonBy_iff_of_maxInfPrio hM0 hM' rfl i

theorem Game.propagationSound (G : Game V) [Finite V] (X : Set V) : G.PropagationSound X := by
  constructor
  · refine G.prioPreserves_of_bound X _ fun p hp M hM v hv => ?_
    rw [Game.maxInfPrio_iff] at hM
    refine ⟨le_max_left _ _, max_le (hM.2 v hv) ?_⟩
    obtain ⟨u, hu, he⟩ := exists_succ_nodeInf G (fun n => (hp n).2) hv
    have huX : u ∈ X := by
      obtain ⟨k, -, hk⟩ := (Filter.frequently_atTop.mp hu) 0
      exact hk ▸ (hp k).1
    exact (Nat.sInf_le (show G.prio u ∈ G.prio '' {w | w ∈ X ∧ G.edge v w} from
      ⟨u, ⟨huX, he⟩, rfl⟩)).trans (hM.2 u hu)
  · refine G.prioPreserves_of_bound X _ fun p hp M hM v hv => ?_
    rw [Game.maxInfPrio_iff] at hM
    refine ⟨le_max_left _ _, max_le (hM.2 v hv) ?_⟩
    obtain ⟨u, hu, he⟩ := exists_pred_nodeInf G (fun n => (hp n).2) hv
    have huX : u ∈ X := by
      obtain ⟨k, -, hk⟩ := (Filter.frequently_atTop.mp hu) 0
      exact hk ▸ (hp k).1
    exact (Nat.sInf_le (show G.prio u ∈ G.prio '' {w | w ∈ X ∧ G.edge w v} from
      ⟨u, ⟨huX, he⟩, rfl⟩)).trans (hM.2 u hu)

end ParityGame

end TransformProofs
