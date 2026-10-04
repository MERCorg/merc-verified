import Sigref.SigData
import Signatures.Proofs.InductiveSignatures_Proofs
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Encodable.Basic

/-!
# Proofs: SigData

Existence of hash-coherent signature data by well-founded recursion along a total order extending the τ-order.

Machine-generated; may be freely edited or regenerated (see CLAUDE.md). The "headline" theorems
are pinned in `Sigref/Pins/SigData_Pins.lean` (human-vetted).
-/

namespace Sigref

open Cslib

variable {State Label : Type} [HasTau Label]

section Existence

variable (lts : LTS State Label) {Block : Type} (part : State → Block) {Tag : Type}

theorem choose_congr {α : Sort _} {P Q : α → Prop} (h : P = Q) (hp : ∃ a, P a) (hq : ∃ a, Q a) :
    hp.choose = hq.choose := by
  subst h; rfl

/-- `Sig` at `s` only depends on `sigHash`/`sigFn` at the τ-successors of `s`. -/
theorem Sig_congr (s : State) {h₁ h₂ : State → Tag} {f₁ f₂ : State → Set (Label × (Block ⊕ Tag))}
    (hh : ∀ u, lts.Tr s HasTau.τ u → h₁ u = h₂ u) (hf : ∀ u, lts.Tr s HasTau.τ u → f₁ u = f₂ u) :
    Sig lts part h₁ f₁ s = Sig lts part h₂ f₂ s := by
  have hpre : PreSig lts part h₁ s = PreSig lts part h₂ s := by
    ext ⟨a, x⟩
    simp only [PreSig, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨u, hu, hp, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, hp, by rw [he, hh u hu]⟩
    · rintro (h | ⟨u, hu, hp, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, hp, by rw [he, hh u hu]⟩
  have hP : (fun s' => lts.Tr s HasTau.τ s' ∧ part s = part s' ∧
        PreSig lts part h₁ s ⊆ f₁ s' ∪ {(HasTau.τ, Sum.inr (h₁ s'))}) =
      (fun s' => lts.Tr s HasTau.τ s' ∧ part s = part s' ∧
        PreSig lts part h₂ s ⊆ f₂ s' ∪ {(HasTau.τ, Sum.inr (h₂ s'))}) := by
    funext s'
    apply propext
    constructor
    · rintro ⟨hu, hp, hs⟩
      refine ⟨hu, hp, ?_⟩
      rw [← hpre, ← hf s' hu, ← hh s' hu]; exact hs
    · rintro ⟨hu, hp, hs⟩
      refine ⟨hu, hp, ?_⟩
      rw [hpre, hf s' hu, hh s' hu]; exact hs
  unfold Sig
  by_cases hc : ∃ s', lts.Tr s HasTau.τ s' ∧ part s = part s' ∧
        PreSig lts part h₁ s ⊆ f₁ s' ∪ {(HasTau.τ, Sum.inr (h₁ s'))}
  · have hc2 : ∃ s', lts.Tr s HasTau.τ s' ∧ part s = part s' ∧
        PreSig lts part h₂ s ⊆ f₂ s' ∪ {(HasTau.τ, Sum.inr (h₂ s'))} := by
      obtain ⟨s', h⟩ := hc
      exact ⟨s', Eq.mp (congrFun hP s') h⟩
    rw [dif_pos hc, dif_pos hc2, ← choose_congr hP hc hc2]
    exact hf _ hc.choose_spec.1
  · have hc2 : ¬ ∃ s', lts.Tr s HasTau.τ s' ∧ part s = part s' ∧
        PreSig lts part h₂ s ⊆ f₂ s' ∪ {(HasTau.τ, Sum.inr (h₂ s'))} := by
      rintro ⟨s', h⟩
      exact hc ⟨s', Eq.mpr (congrFun hP s') h⟩
    rw [dif_neg hc, dif_neg hc2, hpre]

end Existence

variable [Finite State]

/-- A well-founded strict total order on states in which every τ-successor is smaller. -/
theorem exists_tau_order (lts : LTS State Label) (hWF : TauLoopFree lts) :
    ∃ lt : State → State → Prop, WellFounded lt ∧ (∀ a b, a ≠ b → lt a b ∨ lt b a) ∧
      (∀ s u, lts.Tr s HasTau.τ u → lt u s) ∧ (∀ a b c, lt a b → lt b c → lt a c) := by
  obtain ⟨e, he⟩ := exists_injective_nat State
  haveI : IsWellFounded State (fun s' s => lts.Tr s HasTau.τ s') := ⟨hWF⟩
  let key : State → Lex (Ordinal.{0} × ℕ) := fun s =>
    toLex (IsWellFounded.rank (fun s' s => lts.Tr s HasTau.τ s') s, e s)
  refine ⟨fun a b => key a < key b, InvImage.wf key wellFounded_lt, ?_, ?_, fun a b c => lt_trans⟩
  · intro a b hab
    rcases lt_trichotomy (key a) (key b) with h | h | h
    · exact Or.inl h
    · exfalso
      have h2 := h
      exact hab (he (Prod.ext_iff.1 h2).2)
    · exact Or.inr h
  · intro s u hu
    exact Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel (r := fun s' s => lts.Tr s HasTau.τ s') hu)

theorem sigData_exists (lts : LTS State Label) (hWF : TauLoopFree lts) (π : Setoid State) :
    Nonempty (SigData lts π) := by
  classical
  obtain ⟨lt, hlt, htot, hmono, htrans⟩ := exists_tau_order lts hWF
  let P := Set (Label × (Quotient π ⊕ State)) × State
  let F : (s : State) → ((t : State) → lt t s → P) → P := fun s ih =>
    let f : State → Set (Label × (Quotient π ⊕ State)) := fun u => if h : lt u s then (ih u h).1 else ∅
    let hs : State → State := fun u => if h : lt u s then (ih u h).2 else u
    let sg := Sig lts (Quotient.mk π) hs f s
    (sg, if h : ∃ t : {t // lt t s}, (ih t.1 t.2).1 = sg then (ih h.choose.1 h.choose.2).2 else s)
  let G : State → P := hlt.fix F
  have hG : ∀ s, G s = F s (fun t _ => G t) := fun s => hlt.fix_eq F s
  let sigFn : State → Set (Label × (Quotient π ⊕ State)) := fun s => (G s).1
  let sigHash : State → State := fun s => (G s).2
  have hFix : ∀ s, sigFn s = Sig lts (Quotient.mk π) sigHash sigFn s := by
    intro s
    show (G s).1 = _
    rw [hG s]
    apply Sig_congr
    · intro u hu; simp [hmono s u hu, sigHash]
    · intro u hu; simp [hmono s u hu, sigFn]
  have hHash : ∀ s, (∃ t, lt t s ∧ sigFn t = sigFn s ∧ sigHash s = sigHash t) ∨
      ((∀ t, lt t s → sigFn t ≠ sigFn s) ∧ sigHash s = s) := by
    intro s
    have h1 := congrArg Prod.fst (hG s)
    have h2 := congrArg Prod.snd (hG s)
    simp only [F] at h1 h2
    split at h2
    · rename_i hc
      left
      refine ⟨hc.choose.1, hc.choose.2, ?_, h2⟩
      show (G _).1 = (G s).1
      rw [hc.choose_spec, h1]
    · rename_i hc
      right
      refine ⟨fun t ht heq => hc ⟨⟨t, ht⟩, ?_⟩, h2⟩
      show (G t).1 = _
      rw [← h1]; exact heq
  have H1 : ∀ s, sigFn (sigHash s) = sigFn s := by
    intro s
    induction s using hlt.induction with
    | _ s ih =>
      rcases hHash s with ⟨t, hts, hsig, hh⟩ | ⟨_, hh⟩
      · rw [hh, ih t hts, hsig]
      · rw [hh]
  have H2 : ∀ s a b, (a = s ∨ lt a s) → (b = s ∨ lt b s) → sigFn a = sigFn b →
      sigHash a = sigHash b := by
    intro s
    induction s using hlt.induction with
    | _ s ih =>
      have below : ∀ a b, lt a s → lt b s → sigFn a = sigFn b → sigHash a = sigHash b := by
        intro a b has hbs hab
        by_cases hne : a = b
        · rw [hne]
        rcases htot a b hne with h | h
        · exact ih b hbs a b (Or.inr h) (Or.inl rfl) hab
        · exact ih a has a b (Or.inl rfl) (Or.inr h) hab
      have key : ∀ b, lt b s → sigFn b = sigFn s → sigHash s = sigHash b := by
        intro b hbs hb
        rcases hHash s with ⟨t, hts, hsig, hh⟩ | ⟨hno, _⟩
        · rw [hh]; exact below t b hts hbs (hsig.trans hb.symm)
        · exact absurd hb (hno b hbs)
      intro a b ha hb hab
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact key b hb hab.symm
      · exact (key a ha hab).symm
      · exact below a b ha hb hab
  refine ⟨⟨State, sigHash, sigFn, hFix, fun a b => ⟨fun h => ?_, fun h => ?_⟩⟩⟩
  · rw [← H1 a, ← H1 b, h]
  · by_cases hne : a = b
    · rw [hne]
    rcases htot a b hne with h' | h'
    · exact H2 b a b (Or.inr h') (Or.inl rfl) h
    · exact H2 a a b (Or.inl rfl) (Or.inr h') h
/-- Headline: hash-coherent signature data exists. -/
theorem sigDataExists [Finite State] (lts : LTS State Label) (π : Setoid State) :
    SigDataExists lts π :=
  fun hWF => sigData_exists lts hWF π


end Sigref
