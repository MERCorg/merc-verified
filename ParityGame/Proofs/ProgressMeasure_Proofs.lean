module

public import ParityGame.ProgressMeasure
public import ParityGame.Proofs.Defs_Proofs

open Cslib (ωSequence)

@[expose] public section ProgressMeasureProofs

namespace ParityGame

/-! Machine-generated; may be freely edited or regenerated (see CLAUDE.md). Contract pins for the
"headline" theorem below live in `ParityGame/Pins/ProgressMeasure_Pins.lean`.

Proof: a conforming play from `D` stays in `D`. If the greatest recurring priority `P` were odd,
then from some point on every priority is `≤ P`, so (by monotonicity) the labels never increase at
level `P`, and they strictly decrease at level `P` at each of the infinitely many visits to
priority `P` — an infinite descent in the well-founded strict part of `C.le P`. -/

variable {V M : Type*}

/-- One conforming step from a node of the domain stays in the domain and progresses. -/
theorem Game.step_prog (G : Game V) {X : Set V} {C : Codomain M} {D : Set V} {μ : V → M}
    {σ : Strategy V} (hμ : G.IsProgressMeasure X C D μ σ) {v w : V} (hv : v ∈ D)
    (hs : G.Step X .zero σ v w) : w ∈ D ∧ G.Prog C μ v w := by
  obtain ⟨-, h0, h1⟩ := hμ
  obtain ⟨-, hwX, hE, hσ⟩ := hs
  cases ho : G.owner v with
  | zero =>
    obtain rfl := hσ ho
    exact ⟨(h0 v hv ho).1, (h0 v hv ho).2.2⟩
  | one => exact h1 v hv ho w hwX hE

/-- A conforming play from the domain stays in the domain. -/
theorem Game.play_mem_domain (G : Game V) {X : Set V} {C : Codomain M} {D : Set V} {μ : V → M}
    {σ : Strategy V} (hμ : G.IsProgressMeasure X C D μ σ) {p : ωSequence V} (h0 : p 0 ∈ D)
    (hp : G.ConformingPlay X .zero σ p) : ∀ n, p n ∈ D := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact (G.step_prog hμ ih (hp n)).1

/-- No sequence can be non-increasing at a well-founded level forever while strictly decreasing
    infinitely often. -/
theorem Codomain.not_descent (C : Codomain M) {P : ℕ} (hP : P % 2 = 1) (f : ℕ → M) (N : ℕ)
    (hle : ∀ i ≥ N, C.le P (f (i + 1)) (f i))
    (hlt : ∀ i ≥ N, ∃ j ≥ i, ¬ C.le P (f j) (f (j + 1))) : False := by
  have hchain : ∀ i ≥ N, ∀ k, C.le P (f (i + k)) (f i) := by
    intro i hi k
    induction k with
    | zero => exact C.refl _ _
    | succ k ih => exact C.trans _ _ _ _ (hle (i + k) (by omega)) ih
  suffices ∀ a, ∀ i ≥ N, ¬ C.le P (f i) a from this (f N) N le_rfl (C.refl _ _)
  intro a
  induction a using (C.wf P hP).induction with
  | _ a ih =>
    intro i hi hia
    obtain ⟨j, hj, hstrict⟩ := hlt i hi
    have hji : C.le P (f j) (f i) := by
      simpa [show i + (j - i) = j by omega] using hchain i hi (j - i)
    have hja : C.le P (f j) a := C.trans _ _ _ _ hji hia
    have hj1 : C.le P (f (j + 1)) (f j) := hle j (by omega)
    refine ih (f (j + 1)) ⟨C.trans _ _ _ _ hj1 hja, fun hc => hstrict ?_⟩ (j + 1) (by omega)
      (C.refl _ _)
    exact C.trans _ _ _ _ hja hc

/-- Soundness of progress measures (headline). -/
theorem Game.progressMeasureSound [Finite V] (G : Game V) (X : Set V) (C : Codomain M)
    (D : Set V) (μ : V → M) (σ : Strategy V) : G.ProgressMeasureSound X C D μ σ := by
  intro hX hμ v hv
  refine ⟨?_, ?_⟩
  · -- conforming play never gets stuck
    intro w hw
    have hwD : w ∈ D := by
      induction hw with
      | refl => exact hv
      | tail _ hs ih => exact (G.step_prog hμ ih hs).1
    have hwX : w ∈ X := hμ.1 hwD
    cases ho : G.owner w with
    | zero =>
      obtain ⟨h1, h2, -⟩ := hμ.2.1 w hwD ho
      exact ⟨σ w, hwX, hμ.1 h1, h2, fun _ => rfl⟩
    | one =>
      obtain ⟨u, huX, hu⟩ := hX w hwX
      exact ⟨u, hwX, huX, hu, fun h => by rw [ho] at h; cases h⟩
  · intro p hp0 hp
    have hD := G.play_mem_domain hμ (hp0 ▸ hv) hp
    obtain ⟨P, hP⟩ := G.exists_maxInfPrio p
    refine ⟨P, hP, ?_⟩
    by_contra hne
    have hodd : P % 2 = 1 := by
      unfold Player.ofPrio at hne
      split_ifs at hne with h
      · exact absurd rfl hne
      · omega
    obtain ⟨⟨u, hu, huP⟩, hmax⟩ := (G.maxInfPrio_iff p P).mp hP
    -- eventually only recurring nodes are visited
    have hev : ∀ᶠ k in Filter.atTop, p k ∈ nodeInf p := by
      have : ∀ᶠ k in Filter.atTop, ∀ x : {x : V // x ∉ nodeInf p}, p k ≠ x.1 :=
        Filter.eventually_all.mpr fun x => Filter.not_frequently.mp x.2
      exact this.mono fun k hk => by
        by_contra hc
        exact hk ⟨p k, hc⟩ rfl
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hprog : ∀ i, G.Prog C μ (p i) (p (i + 1)) := fun i => (G.step_prog hμ (hD i) (hp i)).2
    apply C.not_descent hodd (fun i => μ (p i)) N
    · intro i hi
      exact C.mono _ _ _ _ (hmax _ (hN i hi)) (hprog i).1
    · intro i hi
      obtain ⟨j, hj, hju⟩ := Filter.frequently_atTop.mp hu i
      refine ⟨j, hj, ?_⟩
      have := (hprog j).2
      rw [hju, huP] at this
      rw [hju]
      exact this hodd

/-- Progress cycles are even (headline). -/
theorem Game.progCycleEven (G : Game V) (C : Codomain M) (μ : V → M) : G.ProgCycleEven C μ := by
  intro k c _ hck hprog i hi hmax
  by_contra hodd
  have hodd : G.prio (c i) % 2 = 1 := by omega
  -- labels never increase at level `P = prio (c i)` along the cycle
  have hchain : ∀ a n, a + n ≤ k → C.le (G.prio (c i)) (μ (c (a + n))) (μ (c a)) := by
    intro a n
    induction n with
    | zero => intro _; exact C.refl _ _
    | succ n ih =>
      intro h
      have hstep := C.mono _ _ _ _ (hmax (a + n) (by omega)) (hprog (a + n) (by omega)).1
      exact C.trans _ _ _ _ hstep (ih (by omega))
  have h1 : C.le (G.prio (c i)) (μ (c k)) (μ (c (i + 1))) := by
    simpa [show i + 1 + (k - (i + 1)) = k by omega] using hchain (i + 1) (k - (i + 1)) (by omega)
  have h2 : C.le (G.prio (c i)) (μ (c i)) (μ (c 0)) := by
    simpa using hchain 0 i (by omega)
  rw [hck] at h1
  exact (hprog i hi).2 hodd (C.trans _ _ _ _ h2 h1)
