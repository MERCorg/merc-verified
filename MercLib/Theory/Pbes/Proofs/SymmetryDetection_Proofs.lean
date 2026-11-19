module

public import MercLib.Theory.Pbes.SymmetryDetection
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Proofs: symmetry detection graphs

Machine-generated; may be freely edited or regenerated (see AGENTS.md). The headline theorems are
stated in `Challenges/Pbes.lean` (human-vetted).
-/

namespace MercLib.Symmetry

open Expr Vertex

variable {F P : Type} {n : ℕ}

/-! ## Subformulas -/

private theorem sub_eq (φ : Expr F P n) : φ.sub = φ :: φ.subD.flatMap sub := by
  cases φ <;> simp [sub, subD]

private theorem mem_sub_self (φ : Expr F P n) : φ ∈ φ.sub := by
  rw [sub_eq]; exact List.mem_cons_self

private theorem size_pos : ∀ φ : Expr F P n, 0 < φ.size
  | par _ | var _ => by simp [size]
  | app _ _ | pvi _ _ => by simp [size]; omega
  | Expr.and a _ | Expr.or a _ => by have := size_pos a; simp [size]; omega
  | all _ _ | ex _ _ => by simp [size]; omega

private theorem le_sum_map {α : Type} (f : α → ℕ) : ∀ {l : List α} {c : α}, c ∈ l →
    f c ≤ (l.map f).sum
  | [], _, h => by simp at h
  | a :: l, c, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_map f h; simp; omega

private theorem size_lt {φ c : Expr F P n} (h : c ∈ φ.subD) : c.size < φ.size := by
  cases φ with
  | par _ => simp [subD] at h
  | var _ => simp [subD] at h
  | app f ts =>
    simp only [subD] at h
    have := le_sum_map size h
    simp [size]; omega
  | pvi X ts =>
    simp only [subD] at h
    have := le_sum_map size h
    simp [size]; omega
  | and a b =>
    simp [subD] at h; have := size_pos a; have := size_pos b
    rcases h with rfl | rfl <;> simp [size] <;> omega
  | or a b =>
    simp [subD] at h; have := size_pos a; have := size_pos b
    rcases h with rfl | rfl <;> simp [size] <;> omega
  | all x a => simp [subD] at h; subst h; simp [size]
  | ex x a => simp [subD] at h; subst h; simp [size]

private theorem sub_trans : ∀ (φ : Expr F P n) {ψ χ : Expr F P n}, ψ ∈ φ.sub → χ ∈ ψ.sub →
    χ ∈ φ.sub
  | φ, ψ, χ, hψ, hχ => by
    rw [sub_eq] at hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hχ
    · obtain ⟨c, hc, hψc⟩ := List.mem_flatMap.1 hψ
      have := size_lt hc
      have := sub_trans c hψc hχ
      rw [sub_eq]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨c, hc, this⟩)
termination_by φ => φ.size

private theorem subD_mem_sub {φ c : Expr F P n} (h : c ∈ φ.subD) : c ∈ φ.sub := by
  rw [sub_eq]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨c, h, mem_sub_self c⟩)

private theorem mem_subE {E : Pbes F P n} {φ : Expr F P n} :
    φ ∈ subE E ↔ ∃ e ∈ E, φ ∈ e.φ.sub := by
  simp [subE]

private theorem subE_closed {E : Pbes F P n} {φ c : Expr F P n} (hφ : φ ∈ subE E)
    (hc : c ∈ φ.subD) : c ∈ subE E := by
  obtain ⟨e, he, hφ⟩ := mem_subE.1 hφ
  exact mem_subE.2 ⟨e, he, sub_trans _ hφ (subD_mem_sub hc)⟩

private theorem rhs_mem_subE {E : Pbes F P n} {e : Equation F P n} (he : e ∈ E) :
    e.φ ∈ subE E :=
  mem_subE.2 ⟨e, he, mem_sub_self _⟩

private theorem pvi_of_isPviAt {e : Equation F P n} {i : ℕ} {p : Expr F P n}
    (h : IsPviAt e i p) : p ∈ e.φ.sub ∧ p.isPvi = true := by
  have hm := List.mem_of_getElem? h
  simp only [pvis, List.mem_filter] at hm
  exact hm

private theorem isPviAt_of_pvi {E : Pbes F P n} {X : P} {ts : List (Expr F P n)}
    (h : pvi X ts ∈ subE E) : ∃ e ∈ E, ∃ i, IsPviAt e i (pvi X ts) := by
  obtain ⟨e, he, hs⟩ := mem_subE.1 h
  have hm : pvi X ts ∈ e.φ.pvis := by simp [pvis, List.mem_filter, hs, isPvi]
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hm
  exact ⟨e, he, i, by simp [IsPviAt, List.getElem?_eq_getElem hi, hget]⟩

private theorem eq_of_X {E : Pbes F P n} (hwf : WellFormed E) {e e' : Equation F P n}
    (he : e ∈ E) (he' : e' ∈ E) (hX : e.X = e'.X) : e = e' :=
  List.inj_on_of_nodup_map hwf.1 he he' hX

/-! ## The vertex set is finite -/

private def vertexList (E : Pbes F P n) : List (Vertex F P n) :=
  (subE E).map expr ++ (List.finRange n).map (fun k => expr (par k)) ++
    E.flatMap fun e => (List.range e.φ.pvis.length).flatMap fun i =>
      (List.finRange n).map (upd e.X i)

private theorem vertices_finite (E : Pbes F P n) : (vertices E).Finite := by
  refine (List.finite_toSet (vertexList E)).subset ?_
  rintro v (⟨φ, hφ, rfl⟩ | ⟨k, rfl⟩ | ⟨e, he, i, hi, k, rfl⟩)
  · simp [vertexList, hφ]
  · simp [vertexList]
  · simp only [vertexList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
      List.mem_finRange, true_and]
    exact Or.inr ⟨e, he, i, hi, k, rfl⟩

private theorem expr_mem_vertices {E : Pbes F P n} {φ : Expr F P n} :
    expr φ ∈ vertices E ↔ φ ∈ subE E ∨ ∃ k, φ = par k := by
  simp [vertices]

private theorem upd_mem_vertices {E : Pbes F P n} {X : P} {i : ℕ} {k : Fin n} :
    upd X i k ∈ vertices E ↔ ∃ e ∈ E, e.X = X ∧ i < e.φ.pvis.length := by
  constructor
  · rintro (⟨φ, -, h⟩ | ⟨k', h⟩ | ⟨e, he, i', hi', k', h⟩)
    · simp at h
    · simp at h
    · simp only [Vertex.upd.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨e, he, rfl, hi'⟩
  · rintro ⟨e, he, rfl, hi⟩; exact Or.inr (Or.inr ⟨e, he, i, hi, k, rfl⟩)

private theorem lt_of_isPviAt {e : Equation F P n} {i : ℕ} {p : Expr F P n}
    (h : IsPviAt e i p) : i < e.φ.pvis.length := by
  unfold IsPviAt at h
  exact (List.getElem?_eq_some_iff.1 h).1

private theorem isPviAt_unique {e : Equation F P n} {i : ℕ} {p q : Expr F P n}
    (hp : IsPviAt e i p) (hq : IsPviAt e i q) : p = q := by
  unfold IsPviAt at hp hq; rw [hp] at hq; exact Option.some.inj hq

/-! ## Arcs -/

private theorem arc_expr_expr {E : Pbes F P n} {φ ψ : Expr F P n} :
    Arc E (expr φ) (expr ψ) ↔ φ ∈ subE E ∧ φ.isPvi = false ∧ ψ ∈ φ.subD := by
  constructor
  · rintro (⟨φ', hφ', hp, ψ', hψ', h1, h2⟩ | ⟨e, he, i, p, hp, k, h | h | h⟩)
    · cases h1; cases h2; exact ⟨hφ', hp, hψ'⟩
    · simp at h
    · simp at h
    · simp at h
  · rintro ⟨h1, h2, h3⟩; exact Or.inl ⟨φ, h1, h2, ψ, h3, rfl, rfl⟩

private theorem arc_expr_upd {E : Pbes F P n} {φ : Expr F P n} {X : P} {i : ℕ} {k : Fin n} :
    Arc E (expr φ) (upd X i k) ↔ ∃ e ∈ E, e.X = X ∧ IsPviAt e i φ := by
  constructor
  · rintro (⟨φ', hφ', hp, ψ', hψ', h1, h2⟩ | ⟨e, he, i', p, hp, k', h | h | h⟩)
    · simp at h2
    · simp only [Vertex.expr.injEq, Vertex.upd.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨e, he, rfl, hp⟩
    · simp at h
    · simp at h
  · rintro ⟨e, he, rfl, hp⟩; exact Or.inr ⟨e, he, i, φ, hp, k, Or.inl ⟨rfl, rfl⟩⟩

private theorem arc_upd {E : Pbes F P n} {X : P} {i : ℕ} {k : Fin n} {v : Vertex F P n} :
    Arc E (upd X i k) v ↔ ∃ e ∈ E, e.X = X ∧ ∃ p, IsPviAt e i p ∧
      ((∃ t, p.subD[(k : ℕ)]? = some t ∧ v = expr t) ∨ v = expr (par k)) := by
  constructor
  · rintro (⟨φ', hφ', hp, ψ', hψ', h1, h2⟩ | ⟨e, he, i', p, hp, k', h | h | h⟩)
    · simp at h1
    · simp at h
    · obtain ⟨h1, t, ht, rfl⟩ := h
      simp only [Vertex.upd.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨e, he, rfl, p, hp, Or.inl ⟨t, ht, rfl⟩⟩
    · obtain ⟨h1, rfl⟩ := h
      simp only [Vertex.upd.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨e, he, rfl, p, hp, Or.inr rfl⟩
  · rintro ⟨e, he, rfl, p, hp, ⟨t, ht, rfl⟩ | rfl⟩
    · exact Or.inr ⟨e, he, i, p, hp, k, Or.inr (Or.inl ⟨rfl, t, ht, rfl⟩)⟩
    · exact Or.inr ⟨e, he, i, p, hp, k, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

private theorem arc_mem {E : Pbes F P n} {u v : Vertex F P n} (h : Arc E u v) :
    u ∈ vertices E ∧ v ∈ vertices E := by
  rcases h with ⟨φ, hφ, -, ψ, hψ, rfl, rfl⟩ | ⟨e, he, i, p, hp, k, h | h | h⟩
  · exact ⟨expr_mem_vertices.2 (Or.inl hφ), expr_mem_vertices.2 (Or.inl (subE_closed hφ hψ))⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨expr_mem_vertices.2 (Or.inl (mem_subE.2 ⟨e, he, (pvi_of_isPviAt hp).1⟩)),
      upd_mem_vertices.2 ⟨e, he, rfl, lt_of_isPviAt hp⟩⟩
  · obtain ⟨rfl, t, ht, rfl⟩ := h
    have hpE : p ∈ subE E := mem_subE.2 ⟨e, he, (pvi_of_isPviAt hp).1⟩
    exact ⟨upd_mem_vertices.2 ⟨e, he, rfl, lt_of_isPviAt hp⟩,
      expr_mem_vertices.2 (Or.inl (subE_closed hpE (List.mem_of_getElem? ht)))⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨upd_mem_vertices.2 ⟨e, he, rfl, lt_of_isPviAt hp⟩, expr_mem_vertices.2 (Or.inr ⟨k, rfl⟩)⟩

/-- An automorphism of a finite graph also maps the arcs out of `h u` back to arcs out of `u`:
it maps the finite set of arcs injectively into itself. -/
private theorem arc_back {E : Pbes F P n} {col : Vertex F P n → Vertex F P n → ArcColour}
    {h : Vertex F P n → Vertex F P n} (hA : IsAut E (Arc E) col h) {u w : Vertex F P n}
    (hu : u ∈ vertices E) (hw : Arc E (h u) w) : ∃ v, Arc E u v ∧ h v = w := by
  let A : Set (Vertex F P n × Vertex F P n) := {p | Arc E p.1 p.2}
  have hfin : A.Finite :=
    ((vertices_finite E).prod (vertices_finite E)).subset fun p hp => arc_mem hp
  have hmaps : Set.MapsTo (Prod.map h h) A A := fun p hp => (hA.2.2 _ _ hp).1
  have hinj : Set.InjOn (Prod.map h h) A := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
    simp only [Prod.map, Prod.mk.injEq] at heq
    have h1 := arc_mem (E := E) hab; have h2 := arc_mem (E := E) hcd
    exact Prod.ext (hA.1.injOn h1.1 h2.1 heq.1) (hA.1.injOn h1.2 h2.2 heq.2)
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
  obtain ⟨⟨a, b⟩, hab, heq⟩ := hbij.surjOn (show (h u, w) ∈ A from hw)
  simp only [Prod.map, Prod.mk.injEq] at heq
  have ha : a = u := hA.1.injOn (arc_mem (E := E) hab).1 hu heq.1
  subst ha
  exact ⟨b, hab, heq.2⟩

/-! ## Colours -/

private theorem shape_eq {E : Pbes F P n} {R : Vertex F P n → Vertex F P n → Prop}
    {col : Vertex F P n → Vertex F P n → ArcColour} {h : Vertex F P n → Vertex F P n}
    (hA : IsAut E R col h) {v : Vertex F P n} (hv : v ∈ vertices E) :
    shapeColour (h v) = shapeColour v :=
  congrArg Prod.fst (hA.2.1 v hv)

private theorem rhs_eq {E : Pbes F P n} {R : Vertex F P n → Vertex F P n → Prop}
    {col : Vertex F P n → Vertex F P n → ArcColour} {h : Vertex F P n → Vertex F P n}
    (hA : IsAut E R col h) {v : Vertex F P n} (hv : v ∈ vertices E) :
    {X | ∃ e ∈ E, e.X = X ∧ h v = expr e.φ} = {X | ∃ e ∈ E, e.X = X ∧ v = expr e.φ} :=
  congrArg Prod.snd (hA.2.1 v hv)

private theorem shape_upd {v : Vertex F P n} (h : shapeColour v = .upd) :
    ∃ X i k, v = upd X i k := by
  rcases v with φ | ⟨X, i, k⟩
  · cases φ <;> simp [shapeColour] at h
  · exact ⟨X, i, k, rfl⟩

private theorem shape_expr_ne_upd (φ : Expr F P n) : shapeColour (expr φ) ≠ .upd := by
  cases φ <;> simp [shapeColour]

/-- The formula that `h` maps the vertex of `φ` to. -/
private def hE (h : Vertex F P n → Vertex F P n) (φ : Expr F P n) : Expr F P n :=
  match h (expr φ) with
  | expr ψ => ψ
  | upd _ _ _ => φ

private theorem h_expr {E : Pbes F P n} {R : Vertex F P n → Vertex F P n → Prop}
    {col : Vertex F P n → Vertex F P n → ArcColour} {h : Vertex F P n → Vertex F P n}
    (hA : IsAut E R col h) {φ : Expr F P n} (hφ : expr φ ∈ vertices E) :
    h (expr φ) = expr (hE h φ) := by
  have hs := shape_eq hA hφ
  unfold hE
  split
  · assumption
  · rename_i heq; rw [heq] at hs; exact absurd hs.symm (shape_expr_ne_upd φ)

private theorem hE_mem {E : Pbes F P n} {R : Vertex F P n → Vertex F P n → Prop}
    {col : Vertex F P n → Vertex F P n → ArcColour} {h : Vertex F P n → Vertex F P n}
    (hA : IsAut E R col h) {φ : Expr F P n} (hφ : expr φ ∈ vertices E) :
    expr (hE h φ) ∈ vertices E := by
  rw [← h_expr hA hφ]; exact hA.1.mapsTo hφ

private theorem hE_shape {E : Pbes F P n} {R : Vertex F P n → Vertex F P n → Prop}
    {col : Vertex F P n → Vertex F P n → ArcColour} {h : Vertex F P n → Vertex F P n}
    (hA : IsAut E R col h) {φ : Expr F P n} (hφ : expr φ ∈ vertices E) :
    shapeColour (expr (hE h φ)) = shapeColour (expr φ) := by
  rw [← h_expr hA hφ]; exact shape_eq hA hφ

private theorem hE_inj {E : Pbes F P n} {R : Vertex F P n → Vertex F P n → Prop}
    {col : Vertex F P n → Vertex F P n → ArcColour} {h : Vertex F P n → Vertex F P n}
    (hA : IsAut E R col h) {φ ψ : Expr F P n} (hφ : expr φ ∈ vertices E)
    (hψ : expr ψ ∈ vertices E) (heq : hE h φ = hE h ψ) : φ = ψ := by
  have := hA.1.injOn hφ hψ (by rw [h_expr hA hφ, h_expr hA hψ, heq])
  simpa using this

/-- **Theorem 2, first part.** -/
theorem restrictionExists (comm : F → Prop) (E : Pbes F P n) : RestrictionExists comm E := by
  intro h hA
  have hk : ∀ k : Fin n, ∃ k', h (expr (par k)) = expr (par k') := by
    intro k
    have hv : expr (par k) ∈ vertices E := expr_mem_vertices.2 (Or.inr ⟨k, rfl⟩)
    have hs := hE_shape hA hv
    rw [h_expr hA hv]
    revert hs
    cases hE h (par k) <;> simp [shapeColour]
  choose g hg using hk
  have ginj : Function.Injective g := by
    intro a b hab
    have := hA.1.injOn (expr_mem_vertices.2 (Or.inr ⟨a, rfl⟩))
      (expr_mem_vertices.2 (Or.inr ⟨b, rfl⟩)) (by rw [hg a, hg b, hab])
    simpa using this
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 ginj), fun k => hg k⟩

/-! ## Children in the directed SDG -/

section Directed

variable {comm : F → Prop} {E : Pbes F P n} {h : Vertex F P n → Vertex F P n}

private theorem arcColour_expr (a b : Expr F P n) :
    arcColour comm E (expr a) (expr b) = termArcColour comm (expr a) (expr b) := by
  simp [arcColour]

private theorem arcColour_upd (X : P) (i : ℕ) (k : Fin n) (v : Vertex F P n) :
    arcColour comm E (upd X i k) v = .roles ({r | r = .par ∧ v = expr (par k)} ∪
      {r | r = .data ∧ ∃ e ∈ E, e.X = X ∧ ∃ p, IsPviAt e i p ∧ ∃ t,
        p.subD[(k : ℕ)]? = some t ∧ v = expr t}) := by
  simp [arcColour]

private theorem termArcColour_app (f : F) (ts : List (Expr F P n)) (t : Expr F P n) :
    termArcColour comm (expr (app f ts)) (expr t) =
      open Classical in if comm f ∧ ts.length = 2 then .bot else .pos {i | ts[i]? = some t} := by
  simp [termArcColour]

private theorem isPvi_eq_of_shape {a b : Expr F P n}
    (h : shapeColour (expr a) = shapeColour (expr b)) : a.isPvi = b.isPvi := by
  cases a <;> cases b <;> simp_all [shapeColour, isPvi]

private theorem children_fwd (hA : IsSdgAut comm E h) {φ c : Expr F P n} (hφ : φ ∈ subE E)
    (hnp : φ.isPvi = false) (hc : c ∈ φ.subD) :
    hE h c ∈ (hE h φ).subD ∧
      termArcColour comm (expr (hE h φ)) (expr (hE h c)) = termArcColour comm (expr φ) (expr c) := by
  have harc : Arc E (expr φ) (expr c) := arc_expr_expr.2 ⟨hφ, hnp, hc⟩
  obtain ⟨h1, h2⟩ := hA.2.2 _ _ harc
  have m1 := (arc_mem harc).1
  have m2 := (arc_mem harc).2
  rw [h_expr hA m1, h_expr hA m2] at h1 h2
  rw [arcColour_expr, arcColour_expr] at h2
  exact ⟨(arc_expr_expr.1 h1).2.2, h2⟩

private theorem children_bwd (hA : IsSdgAut comm E h) {φ c' : Expr F P n} (hφ : φ ∈ subE E)
    (hnp : φ.isPvi = false) (hc' : c' ∈ (hE h φ).subD) : ∃ c ∈ φ.subD, hE h c = c' := by
  have m1 : expr φ ∈ vertices E := expr_mem_vertices.2 (Or.inl hφ)
  have hψ : hE h φ ∈ subE E := by
    rcases expr_mem_vertices.1 (hE_mem hA m1) with h | ⟨k, hk⟩
    · exact h
    · rw [hk] at hc'; simp [subD] at hc'
  have hnp' : (hE h φ).isPvi = false := by rw [isPvi_eq_of_shape (hE_shape hA m1)]; exact hnp
  have harc : Arc E (h (expr φ)) (expr c') := by
    rw [h_expr hA m1]; exact arc_expr_expr.2 ⟨hψ, hnp', hc'⟩
  obtain ⟨v, hv, hvw⟩ := arc_back hA m1 harc
  rcases v with c | ⟨X, i, k⟩
  · obtain ⟨-, -, hc⟩ := arc_expr_expr.1 hv
    refine ⟨c, hc, ?_⟩
    rw [h_expr hA (arc_mem hv).2] at hvw
    simpa using hvw
  · obtain ⟨e, he, -, hp⟩ := arc_expr_upd.1 hv
    have := (pvi_of_isPviAt hp).2
    rw [hnp] at this
    cases this

private theorem two_cases {α β : Type} (g : α → β) {a b : α} {c d : β}
    (hinj : g a = g b → a = b) (h1 : g a ∈ [c, d]) (h2 : g b ∈ [c, d])
    (h3 : ∀ y ∈ [c, d], ∃ x ∈ [a, b], g x = y) :
    [c, d] = [g a, g b] ∨ [c, d] = [g b, g a] := by
  obtain ⟨x, hx, hxc⟩ := h3 c (by simp)
  obtain ⟨y, hy, hyd⟩ := h3 d (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2 hx hy
  simp only [List.cons.injEq, and_true]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rcases h2 with h2 | h2
    · have := hinj (hxc.trans h2.symm); subst this; exact Or.inl ⟨hxc.symm, hyd.symm⟩
    · have := hinj (hyd.trans h2.symm); subst this; exact Or.inl ⟨hxc.symm, hyd.symm⟩
  · exact Or.inl ⟨hxc.symm, hyd.symm⟩
  · exact Or.inr ⟨hxc.symm, hyd.symm⟩
  · rcases h1 with h1 | h1
    · have := hinj (h1.trans hxc.symm); subst this; exact Or.inl ⟨hxc.symm, hyd.symm⟩
    · have := hinj (h1.trans hyd.symm); subst this; exact Or.inl ⟨hxc.symm, hyd.symm⟩

private theorem mem_of_sub {φ c : Expr F P n} (hφ : φ ∈ subE E) (hc : c ∈ φ.subD) :
    expr c ∈ vertices E :=
  expr_mem_vertices.2 (Or.inl (subE_closed hφ hc))

private theorem hE_and (hA : IsSdgAut comm E h) {a b : Expr F P n}
    (hφ : Expr.and a b ∈ subE E) :
    hE h (Expr.and a b) = Expr.and (hE h a) (hE h b) ∨
      hE h (Expr.and a b) = Expr.and (hE h b) (hE h a) := by
  have m := expr_mem_vertices.2 (Or.inl hφ)
  have hs := hE_shape hA m
  obtain ⟨c, d, hcd⟩ : ∃ c d, hE h (Expr.and a b) = Expr.and c d := by
    revert hs; cases hE h (Expr.and a b) <;> simp [shapeColour]
  have hfwd : ∀ x ∈ (Expr.and a b).subD, hE h x ∈ (hE h (Expr.and a b)).subD :=
    fun x hx => (children_fwd hA hφ rfl hx).1
  have hbwd : ∀ y ∈ (hE h (Expr.and a b)).subD, ∃ x ∈ (Expr.and a b).subD, hE h x = y :=
    fun y hy => children_bwd hA hφ rfl hy
  simp only [hcd, subD] at hfwd hbwd
  have ma := mem_of_sub hφ (by simp [subD] : a ∈ (Expr.and a b).subD)
  have mb := mem_of_sub hφ (by simp [subD] : b ∈ (Expr.and a b).subD)
  rcases two_cases (hE h) (hE_inj hA ma mb) (hfwd a (by simp)) (hfwd b (by simp)) hbwd with
    h1 | h1 <;> simp only [List.cons.injEq, and_true] at h1 <;> rw [hcd, h1.1, h1.2] <;> simp

private theorem hE_or (hA : IsSdgAut comm E h) {a b : Expr F P n}
    (hφ : Expr.or a b ∈ subE E) :
    hE h (Expr.or a b) = Expr.or (hE h a) (hE h b) ∨
      hE h (Expr.or a b) = Expr.or (hE h b) (hE h a) := by
  have m := expr_mem_vertices.2 (Or.inl hφ)
  have hs := hE_shape hA m
  obtain ⟨c, d, hcd⟩ : ∃ c d, hE h (Expr.or a b) = Expr.or c d := by
    revert hs; cases hE h (Expr.or a b) <;> simp [shapeColour]
  have hfwd : ∀ x ∈ (Expr.or a b).subD, hE h x ∈ (hE h (Expr.or a b)).subD :=
    fun x hx => (children_fwd hA hφ rfl hx).1
  have hbwd : ∀ y ∈ (hE h (Expr.or a b)).subD, ∃ x ∈ (Expr.or a b).subD, hE h x = y :=
    fun y hy => children_bwd hA hφ rfl hy
  simp only [hcd, subD] at hfwd hbwd
  have ma := mem_of_sub hφ (by simp [subD] : a ∈ (Expr.or a b).subD)
  have mb := mem_of_sub hφ (by simp [subD] : b ∈ (Expr.or a b).subD)
  rcases two_cases (hE h) (hE_inj hA ma mb) (hfwd a (by simp)) (hfwd b (by simp)) hbwd with
    h1 | h1 <;> simp only [List.cons.injEq, and_true] at h1 <;> rw [hcd, h1.1, h1.2] <;> simp

private theorem hE_all (hA : IsSdgAut comm E h) {x : ℕ} {a : Expr F P n}
    (hφ : all x a ∈ subE E) : hE h (all x a) = all x (hE h a) := by
  have m := expr_mem_vertices.2 (Or.inl hφ)
  have hs := hE_shape hA m
  obtain ⟨c, hc⟩ : ∃ c, hE h (all x a) = all x c := by
    revert hs; cases hE h (all x a) <;> simp [shapeColour]
  have := (children_fwd hA hφ rfl (by simp [subD] : a ∈ (all x a).subD)).1
  rw [hc] at this ⊢; simp [subD] at this; rw [this]

private theorem hE_ex (hA : IsSdgAut comm E h) {x : ℕ} {a : Expr F P n}
    (hφ : ex x a ∈ subE E) : hE h (ex x a) = ex x (hE h a) := by
  have m := expr_mem_vertices.2 (Or.inl hφ)
  have hs := hE_shape hA m
  obtain ⟨c, hc⟩ : ∃ c, hE h (ex x a) = ex x c := by
    revert hs; cases hE h (ex x a) <;> simp [shapeColour]
  have := (children_fwd hA hφ rfl (by simp [subD] : a ∈ (ex x a).subD)).1
  rw [hc] at this ⊢; simp [subD] at this; rw [this]

private theorem hE_var (hA : IsSdgAut comm E h) {x : ℕ} (hφ : var x ∈ subE E) :
    hE h (var x) = (var x : Expr F P n) := by
  have hs := hE_shape hA (expr_mem_vertices.2 (Or.inl hφ))
  revert hs; cases hE h (var x) <;> simp [shapeColour]

private theorem hE_par (hA : IsSdgAut comm E h) {π : Equiv.Perm (Fin n)} (hπ : Restricts h π)
    (k : Fin n) : hE h (par k) = (par (π k) : Expr F P n) := by
  have := h_expr hA (expr_mem_vertices.2 (Or.inr ⟨k, rfl⟩))
  rw [hπ k] at this
  simpa using this.symm

private theorem hE_app (hA : IsSdgAut comm E h) {f : F} {ts : List (Expr F P n)}
    (hφ : app f ts ∈ subE E) :
    ∃ ts', hE h (app f ts) = app f ts' ∧
      (ts' = ts.map (hE h) ∨ (comm f ∧ ∃ a b, ts = [a, b] ∧ ts' = [hE h b, hE h a])) := by
  have m := expr_mem_vertices.2 (Or.inl hφ)
  have hs := hE_shape hA m
  obtain ⟨ts', hts'⟩ : ∃ ts', hE h (app f ts) = app f ts' := by
    revert hs; cases hE h (app f ts) <;> simp [shapeColour]
  refine ⟨ts', hts', ?_⟩
  have hfwd : ∀ x ∈ (app f ts).subD, hE h x ∈ (hE h (app f ts)).subD ∧
      termArcColour comm (expr (hE h (app f ts))) (expr (hE h x)) =
        termArcColour comm (expr (app f ts)) (expr x) :=
    fun x hx => children_fwd hA hφ rfl hx
  have hbwd : ∀ y ∈ (hE h (app f ts)).subD, ∃ x ∈ (app f ts).subD, hE h x = y :=
    fun y hy => children_bwd hA hφ rfl hy
  simp only [hts', subD, termArcColour_app] at hfwd hbwd
  by_cases hc : comm f ∧ ts.length = 2
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hc.2
    by_cases hc' : ts'.length = 2
    · obtain ⟨c, d, rfl⟩ := List.length_eq_two.1 hc'
      have ma := mem_of_sub hφ (by simp [subD] : a ∈ (app f [a, b]).subD)
      have mb := mem_of_sub hφ (by simp [subD] : b ∈ (app f [a, b]).subD)
      rcases two_cases (hE h) (hE_inj hA ma mb) (hfwd a (by simp)).1 (hfwd b (by simp)).1
        hbwd with h1 | h1
      · exact Or.inl (by simpa using h1)
      · exact Or.inr ⟨hc.1, a, b, rfl, h1⟩
    · have := (hfwd a (by simp)).2
      simp [hc, hc'] at this
  · left
    rcases eq_or_ne ts [] with rfl | hne
    · simp only [List.map_nil]
      apply List.eq_nil_iff_forall_not_mem.2
      intro y hy
      obtain ⟨x, hx, -⟩ := hbwd y hy
      simp at hx
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil ts hne
      have hnc' : ¬(comm f ∧ ts'.length = 2) := by
        intro hc'
        have := (hfwd a ha).2
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc'), ite_eq_right_of_eq_false _ _ (eq_false hc)] at this
        cases this
      have key : ∀ c ∈ ts, ∀ j : ℕ, ts'[j]? = some (hE h c) ↔ ts[j]? = some c := by
        intro c hcm j
        have := (hfwd c hcm).2
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnc'), ite_eq_right_of_eq_false _ _ (eq_false hc)] at this
        exact Set.ext_iff.1 (ArcColour.pos.inj this) j
      apply List.ext_getElem?
      intro j
      rw [List.getElem?_map]
      cases hj : ts[j]? with
      | some c => simp [(key c (List.mem_of_getElem? hj) j).2 hj]
      | none =>
        cases hj' : ts'[j]? with
        | none => rfl
        | some c' =>
          obtain ⟨c, hcm, rfl⟩ := hbwd c' (List.mem_of_getElem? hj')
          have := (key c hcm j).1 hj'
          rw [hj] at this
          cases this

private theorem hE_pvi (hwf : WellFormed E) (hA : IsSdgAut comm E h) {π : Equiv.Perm (Fin n)}
    (hπ : Restricts h π) {X : P} {ts : List (Expr F P n)} (hφ : pvi X ts ∈ subE E) :
    ∃ ts', hE h (pvi X ts) = pvi X ts' ∧ ts'.length = n ∧
      ∀ (k : Fin n) t, ts[(k : ℕ)]? = some t → ts'[(π k : ℕ)]? = some (hE h t) := by
  have m := expr_mem_vertices.2 (Or.inl hφ)
  have hs := hE_shape hA m
  obtain ⟨ts', hts'⟩ : ∃ ts', hE h (pvi X ts) = pvi X ts' := by
    revert hs; cases hE h (pvi X ts) <;> simp [shapeColour]
  have hψ : pvi X ts' ∈ subE E := by
    rcases expr_mem_vertices.1 (hE_mem hA m) with h | ⟨k, hk⟩
    · rwa [hts'] at h
    · rw [hts'] at hk; cases hk
  refine ⟨ts', hts', hwf.2 X ts' hψ, ?_⟩
  obtain ⟨e, he, i, hp⟩ := isPviAt_of_pvi hφ
  intro k t ht
  have a1 : Arc E (expr (pvi X ts)) (upd e.X i k) := arc_expr_upd.2 ⟨e, he, rfl, hp⟩
  have mu := (arc_mem a1).2
  obtain ⟨X', i', k', hu⟩ := shape_upd (by rw [shape_eq hA mu]; rfl)
  have b1 := (hA.2.2 _ _ a1).1
  rw [h_expr hA m, hts', hu] at b1
  obtain ⟨e', he', hX', hp'⟩ := arc_expr_upd.1 b1
  -- The `data` arc of `X_{i,k}` is mapped to the `data` arc of its image.
  have a2 : Arc E (upd e.X i k) (expr t) :=
    arc_upd.2 ⟨e, he, rfl, _, hp, Or.inl ⟨t, by simpa [subD] using ht, rfl⟩⟩
  have c2 := (hA.2.2 _ _ a2).2
  rw [hu, h_expr hA (arc_mem a2).2, arcColour_upd, arcColour_upd] at c2
  have hd : Role.data ∈ ({r | r = .par ∧ expr t = expr (par k)} ∪
      {r | r = .data ∧ ∃ e'' ∈ E, e''.X = e.X ∧ ∃ p, IsPviAt e'' i p ∧ ∃ t',
        p.subD[(k : ℕ)]? = some t' ∧ expr t = expr t'} : Set Role) :=
    Or.inr ⟨rfl, e, he, rfl, _, hp, t, by simpa [subD] using ht, rfl⟩
  rw [← ArcColour.roles.inj c2] at hd
  rcases hd with ⟨hd, -⟩ | ⟨-, e'', he'', hX'', p, hp'', t', ht', heq⟩
  · cases hd
  have : e'' = e' := eq_of_X hwf he'' he' (hX''.trans hX'.symm)
  subst this
  have := isPviAt_unique hp'' hp'
  subst this
  simp only [subD, Vertex.expr.injEq] at ht' heq
  subst heq
  -- The `par` arc of `X_{i,k}` is mapped to the `par` arc of its image, so `k' = π k`.
  have a3 : Arc E (upd e.X i k) (expr (par k)) := arc_upd.2 ⟨e, he, rfl, _, hp, Or.inr rfl⟩
  have c3 := (hA.2.2 _ _ a3).2
  rw [hu, hπ k, arcColour_upd, arcColour_upd] at c3
  have hpar : Role.par ∈ ({r | r = .par ∧ (expr (par k) : Vertex F P n) = expr (par k)} ∪
      {r | r = .data ∧ ∃ e'' ∈ E, e''.X = e.X ∧ ∃ p, IsPviAt e'' i p ∧ ∃ t',
        p.subD[(k : ℕ)]? = some t' ∧ (expr (par k) : Vertex F P n) = expr t'} : Set Role) :=
    by left; exact ⟨rfl, rfl⟩
  rw [← ArcColour.roles.inj c3] at hpar
  rcases hpar with ⟨-, hk⟩ | ⟨hd, -⟩
  · simp only [Vertex.expr.injEq, Expr.par.injEq] at hk
    rw [hk]; exact ht'
  · cases hd

end Directed

/-! ## Lemmas 1–3 and Theorem 2 -/

/-- **Lemma 1.** -/
theorem rhsFixed (comm : F → Prop) (E : Pbes F P n) : RhsFixed comm E := by
  intro hwf h hA e he
  have m : expr e.φ ∈ vertices E := expr_mem_vertices.2 (Or.inl (rhs_mem_subE he))
  have hX : e.X ∈ {X | ∃ e' ∈ E, e'.X = X ∧ h (expr e.φ) = expr e'.φ} := by
    rw [rhs_eq hA m]; exact ⟨e, he, rfl, rfl⟩
  obtain ⟨e', he', hX, heq⟩ := hX
  rw [heq, eq_of_X hwf he' he hX]

private theorem sum_map_fin {α : Type} (f : α → ℕ) (l : List α) (hl : l.length = n) :
    (l.map f).sum = ∑ k : Fin n, f (l[(k : ℕ)]'(by have := k.2; omega)) := by
  subst hl
  conv_lhs => rw [← List.ofFn_getElem (xs := l)]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- The arguments of `hE h (X(t₁, …, tₙ))` are the images of the `tₖ`, permuted by `π`. -/
private theorem pvi_args {h : Vertex F P n → Vertex F P n}
    {π : Equiv.Perm (Fin n)} {ts ts' : List (Expr F P n)} (hl : ts.length = n)
    (hl' : ts'.length = n)
    (hk : ∀ (k : Fin n) t, ts[(k : ℕ)]? = some t → ts'[(π k : ℕ)]? = some (hE h t))
    (k : Fin n) : ts'[(π k : ℕ)]'(by have := (π k).2; omega) = hE h (ts[(k : ℕ)]'(by have := k.2; omega)) := by
  have := hk k _ (List.getElem?_eq_getElem (by have := k.2; omega))
  rw [List.getElem?_eq_getElem (by have := (π k).2; omega)] at this
  exact Option.some.inj this

/-- **Lemma 2.** -/
theorem sizePreserved (comm : F → Prop) (E : Pbes F P n) : SizePreserved comm E := by
  intro hwf h hA
  obtain ⟨π, hπ⟩ := restrictionExists comm E h hA
  suffices H : ∀ N, ∀ φ : Expr F P n, φ.size = N → (φ ∈ subE E ∨ ∃ k, φ = par k) →
      (hE h φ).size = φ.size by
    intro φ hφ
    exact ⟨hE h φ, h_expr hA (expr_mem_vertices.2 hφ), H _ φ rfl hφ⟩
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro φ hN hφ
  rcases hφ with hφ | ⟨k, rfl⟩
  · have ihc : ∀ c ∈ φ.subD, (hE h c).size = c.size := fun c hc =>
      ih _ (hN ▸ size_lt hc) c rfl (Or.inl (subE_closed hφ hc))
    cases φ with
    | par k => rw [hE_par hA hπ]; simp [size]
    | var x => rw [hE_var hA hφ]
    | app f ts =>
      obtain ⟨ts', h1, h2 | ⟨-, a, b, rfl, rfl⟩⟩ := hE_app hA hφ
      · rw [h1, h2]
        simp only [size, List.map_map]
        congr 2
        exact List.map_congr_left fun c hc => ihc c hc
      · rw [h1]
        simp [size, ihc a (by simp [subD]), ihc b (by simp [subD])]
        omega
    | pvi X ts =>
      obtain ⟨ts', h1, hl', hk⟩ := hE_pvi hwf hA hπ hφ
      have hl : ts.length = n := hwf.2 X ts hφ
      rw [h1]
      simp only [size]
      rw [sum_map_fin size ts' hl', sum_map_fin size ts hl,
        ← Equiv.sum_comp π (fun k => size (ts'[(k : ℕ)]'(by have := k.2; omega)))]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pvi_args hl hl' hk k]
      exact ihc _ (List.getElem_mem _)
    | and a b =>
      rcases hE_and hA hφ with h1 | h1 <;> rw [h1] <;>
        simp [size, ihc a (by simp [subD]), ihc b (by simp [subD]), Nat.add_comm]
    | or a b =>
      rcases hE_or hA hφ with h1 | h1 <;> rw [h1] <;>
        simp [size, ihc a (by simp [subD]), ihc b (by simp [subD]), Nat.add_comm]
    | all x a => rw [hE_all hA hφ]; simp [size, ihc a (by simp [subD])]
    | ex x a => rw [hE_ex hA hφ]; simp [size, ihc a (by simp [subD])]
  · rw [hE_par hA hπ]; simp [size]

section Semantics

variable {D : Type} [Inhabited D] (I : F → List D → D) (T : D → Prop)

private theorem eval_act (π : Equiv.Perm (Fin n)) (σ : Fin n → D) (β : ℕ → D)
    (t : Expr F P n) : (t.act π).eval I σ β = (t.subst π).eval I σ β := by
  cases t <;> simp [act, eval, subst]

/-- **Lemma 3.** -/
theorem agreesWithAct (comm : F → Prop) (E : Pbes F P n) : AgreesWithAct I T comm E := by
  intro hcomm hwf h π hA hπ
  suffices H : ∀ N, ∀ φ : Expr F P n, φ.size = N → (φ ∈ subE E ∨ ∃ k, φ = par k) →
      ∀ η σ β, (hE h φ).eval I σ β = (φ.act π).eval I σ β ∧
        ((hE h φ).holds I T η σ β ↔ (φ.act π).holds I T η σ β) by
    intro φ hφ
    exact ⟨hE h φ, h_expr hA (expr_mem_vertices.2 hφ), H _ φ rfl hφ⟩
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro φ hN hφ
  rcases hφ with hφ | ⟨k, rfl⟩
  · have ihc : ∀ c ∈ φ.subD, ∀ η σ β, (hE h c).eval I σ β = (c.subst π).eval I σ β ∧
        ((hE h c).holds I T η σ β ↔ (c.act π).holds I T η σ β) := fun c hc η σ β => by
      have := ih _ (hN ▸ size_lt hc) c rfl (Or.inl (subE_closed hφ hc)) η σ β
      rw [eval_act] at this
      exact this
    intro η σ β
    cases φ with
    | par k => rw [hE_par hA hπ]; simp [act, subst]
    | var x => rw [hE_var hA hφ]; simp [act, subst]
    | app f ts =>
      obtain ⟨ts', h1, h2 | ⟨hcf, a, b, rfl, rfl⟩⟩ := hE_app hA hφ
      · have he : (hE h (app f ts)).eval I σ β = ((app f ts).act π).eval I σ β := by
          rw [h1, h2]
          simp only [act, subst, eval, List.map_map]
          congr 1
          exact List.map_congr_left fun c hc => (ihc c hc η σ β).1
        refine ⟨he, ?_⟩
        rw [h1] at he ⊢
        simp only [act, subst, holds] at he ⊢
        rw [he]
      · have he : (hE h (app f [a, b])).eval I σ β = ((app f [a, b]).act π).eval I σ β := by
          rw [h1]
          simp only [act, subst, eval, List.map_cons, List.map_nil]
          rw [(ihc a (by simp [subD]) η σ β).1, (ihc b (by simp [subD]) η σ β).1]
          exact hcomm f hcf _ _
        refine ⟨he, ?_⟩
        rw [h1] at he ⊢
        simp only [act, subst, holds] at he ⊢
        rw [he]
    | pvi X ts =>
      obtain ⟨ts', h1, hl', hk⟩ := hE_pvi hwf hA hπ hφ
      have hl : ts.length = n := hwf.2 X ts hφ
      rw [h1]
      refine ⟨by simp [act, eval], ?_⟩
      simp only [act, holds]
      suffices hargs : ts'.map (eval I σ β) = (List.ofFn fun m : Fin n =>
          ((ts[(π.symm m : ℕ)]?).getD (var 0)).subst π).map (eval I σ β) by rw [hargs]
      apply List.ext_getElem (by simp [hl'])
      intro m hm1 hm2
      simp only [List.length_map] at hm1
      have hm : m < n := hl' ▸ hm1
      have key := pvi_args hl hl' hk (π.symm ⟨m, hm⟩)
      simp only [Equiv.apply_symm_apply] at key
      have hi : ((π.symm ⟨m, hm⟩ : Fin n) : ℕ) < ts.length := by
        have := (π.symm ⟨m, hm⟩).2; omega
      simp only [List.getElem_map, List.getElem_ofFn, key]
      rw [List.getElem?_eq_getElem hi, Option.getD_some]
      exact (ihc _ (by simp [subD]) η σ β).1
    | and a b =>
      refine ⟨by rcases hE_and hA hφ with h1 | h1 <;> rw [h1] <;> simp [act, eval], ?_⟩
      have ha := (ihc a (by simp [subD]) η σ β).2
      have hb := (ihc b (by simp [subD]) η σ β).2
      rcases hE_and hA hφ with h1 | h1 <;> rw [h1] <;> simp only [act, holds] <;>
        rw [ha, hb]; exact And.comm
    | or a b =>
      refine ⟨by rcases hE_or hA hφ with h1 | h1 <;> rw [h1] <;> simp [act, eval], ?_⟩
      have ha := (ihc a (by simp [subD]) η σ β).2
      have hb := (ihc b (by simp [subD]) η σ β).2
      rcases hE_or hA hφ with h1 | h1 <;> rw [h1] <;> simp only [act, holds] <;>
        rw [ha, hb]; exact Or.comm
    | all x a =>
      rw [hE_all hA hφ]
      refine ⟨by simp [act, eval], ?_⟩
      simp only [act, holds]
      exact forall_congr' fun d => (ihc a (by simp [subD]) η σ _).2
    | ex x a =>
      rw [hE_ex hA hφ]
      refine ⟨by simp [act, eval], ?_⟩
      simp only [act, holds]
      exact exists_congr fun d => (ihc a (by simp [subD]) η σ _).2
  · intro η σ β; rw [hE_par hA hπ]; simp [act, subst]

/-- **Theorem 2.** -/
theorem symmetryFromAutomorphism (comm : F → Prop) (E : Pbes F P n) :
    SymmetryFromAutomorphism I T comm E := by
  intro hcomm hwf h π hA hπ e he η σ β
  obtain ⟨ψ, hψ, hsem⟩ := agreesWithAct I T comm E hcomm hwf h π hA hπ e.φ
    (Or.inl (rhs_mem_subE he))
  rw [rhsFixed comm E hwf h hA e he] at hψ
  cases hψ
  exact ((hsem η σ β).2).symm

end Semantics

/-! ## Counterexamples -/

section Counterexamples

open Classical in
/-- Swaps `a` with `b` and `c` with `d`. -/
private noncomputable def swap2 {α : Type} (a b c d : α) (x : α) : α :=
  if x = a then b else if x = b then a else if x = c then d else if x = d then c else x

private theorem swap2_cases {α : Type} (a b c d x : α) :
    (x = a ∧ swap2 a b c d x = b) ∨ (x = b ∧ swap2 a b c d x = a) ∨
    (x = c ∧ swap2 a b c d x = d) ∨ (x = d ∧ swap2 a b c d x = c) ∨ swap2 a b c d x = x := by
  unfold swap2; split_ifs <;> simp_all

private theorem swap2_invol {α : Type} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (x : α) : swap2 a b c d (swap2 a b c d x) = x := by
  rcases swap2_cases a b c d x with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | h <;> rw [h]
  · simp [swap2, Ne.symm hab]
  · simp [swap2]
  · simp [swap2, Ne.symm had, Ne.symm hbd, Ne.symm hcd]
  · simp [swap2, Ne.symm hac, Ne.symm hbc]
  · exact h

private theorem swap2_bijOn {α : Type} {a b c d : α} {s : Set α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hd : d ∈ s) : Set.BijOn (swap2 a b c d) s s := by
  have hm : Set.MapsTo (swap2 a b c d) s s := by
    intro x hx; unfold swap2; split_ifs <;> assumption
  have hi := swap2_invol hab hac had hbc hbd hcd
  exact ⟨hm, fun x _ y _ hxy => by rw [← hi x, hxy, hi y], fun y hy => ⟨_, hm hy, hi y⟩⟩

private theorem swap2_colour {α β : Type} (f : α → β) {a b c d : α} (hab : f a = f b)
    (hcd : f c = f d) (x : α) : f (swap2 a b c d x) = f x := by
  rcases swap2_cases a b c d x with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | h <;>
    rw [h] <;> simp [*]

/-! ### The undirected SDG -/

private abbrev cP : Expr BoolSym ℕ 3 := par 0
private abbrev cQ : Expr BoolSym ℕ 3 := par 1
private abbrev cR : Expr BoolSym ℕ 3 := par 2
/-- `A = (q == q)`. -/
private abbrev cA : Expr BoolSym ℕ 3 := app .eq [cQ, cQ]
/-- `B = (A == r)`. -/
private abbrev cB : Expr BoolSym ℕ 3 := app .eq [cA, cR]
/-- `C = (B == p)`. -/
private abbrev cC : Expr BoolSym ℕ 3 := app .eq [cB, cP]
/-- `D = C ∧ A`. -/
private abbrev cD : Expr BoolSym ℕ 3 := Expr.and cC cA
/-- `X(p, q, r) = B` and `Y(p, q, r) = C ∧ A`, so `Y(p, q, r) ≡ (r == p)`. -/
private abbrev cE1 : Pbes BoolSym ℕ 3 := [⟨false, 0, cB⟩, ⟨false, 1, cD⟩]
/-- Swaps `p` with `q`, and `A` with `C`. -/
private noncomputable abbrev cH1 := swap2 (expr cP) (expr cQ) (expr cA) (expr cC)

private theorem cE1_arc {u v : Vertex BoolSym ℕ 3} (h : Arc cE1 u v) :
    (u = expr cA ∧ v = expr cQ) ∨ (u = expr cB ∧ v = expr cA) ∨ (u = expr cB ∧ v = expr cR) ∨
    (u = expr cC ∧ v = expr cB) ∨ (u = expr cC ∧ v = expr cP) ∨
    (u = expr cD ∧ v = expr cC) ∨ (u = expr cD ∧ v = expr cA) := by
  rcases h with ⟨φ, hφ, -, ψ, hψ, rfl, rfl⟩ | ⟨e, he, i, p, hp, -⟩
  · have key : ∀ φ ∈ subE cE1, ∀ ψ ∈ φ.subD,
        (expr φ = expr cA ∧ expr ψ = expr cQ) ∨ (expr φ = expr cB ∧ expr ψ = expr cA) ∨
        (expr φ = expr cB ∧ expr ψ = expr cR) ∨ (expr φ = expr cC ∧ expr ψ = expr cB) ∨
        (expr φ = expr cC ∧ expr ψ = expr cP) ∨ (expr φ = expr cD ∧ expr ψ = expr cC) ∨
        (expr φ = expr cD ∧ expr ψ = expr cA) := by
      simp [subE, sub, subD]
    exact key φ hφ ψ hψ
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [IsPviAt, pvis, sub, isPvi] at hp

private theorem cE1_arcColour {u v : Vertex BoolSym ℕ 3} (h : Arc cE1 u v) :
    arcColour boolComm cE1 u v = .bot := by
  rcases cE1_arc h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [arcColour, termArcColour, boolComm]

private theorem cE1_edgeColour {u v : Vertex BoolSym ℕ 3} (h : Edge cE1 u v) :
    edgeColour cE1 (arcColour boolComm cE1) u v = .bot := by
  unfold edgeColour
  split
  · exact cE1_arcColour ‹_›
  · exact cE1_arcColour (h.resolve_left ‹_›)

private theorem cE1_arc_of {φ ψ : Expr BoolSym ℕ 3} (hφ : φ ∈ subE cE1) (hp : φ.isPvi = false)
    (hψ : ψ ∈ φ.subD) : Arc cE1 (expr φ) (expr ψ) :=
  arc_expr_expr.2 ⟨hφ, hp, hψ⟩

-- `done` makes `first` reject an orientation that leaves goals open.
set_option linter.unusedTactic false in
private theorem cE1_aut : IsAut cE1 (Edge cE1) (edgeColour cE1 (arcColour boolComm cE1)) cH1 := by
  have mem : ∀ φ ∈ subE cE1, expr φ ∈ vertices cE1 := fun φ h =>
    expr_mem_vertices.2 (Or.inl h)
  refine ⟨swap2_bijOn (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (mem _ (by simp [subE, sub])) (mem _ (by simp [subE, sub])) (mem _ (by simp [subE, sub]))
    (mem _ (by simp [subE, sub])), fun v _ => ?_, fun u v huv => ?_⟩
  · refine swap2_colour (colour cE1) ?_ ?_ v <;>
      simp only [colour, Prod.mk.injEq] <;> refine ⟨rfl, Set.ext fun X => ?_⟩ <;> simp
  · have himg : Edge cE1 (cH1 u) (cH1 v) := by
      rcases huv with huv | huv <;>
      rcases cE1_arc huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [cH1, swap2] <;>
      first
        | (left; apply cE1_arc_of <;> simp [subE, sub, subD, isPvi]; done)
        | (right; apply cE1_arc_of <;> simp [subE, sub, subD, isPvi]; done)
    exact ⟨himg, by rw [cE1_edgeColour himg, cE1_edgeColour huv]⟩

theorem undirectedUnsound : UndirectedUnsound := by
  refine ⟨cE1, cH1, Equiv.swap 0 1, ⟨by simp, fun X ts h => ?_⟩, cE1_aut, ?_, ?_⟩
  · simp [subE, sub] at h
  · intro k
    fin_cases k <;> simp [cH1, swap2, Equiv.swap_apply_of_ne_of_ne]
  · intro hs
    have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    have := hs ⟨false, 1, cD⟩ (by simp) (fun _ => ∅) ![true, false, true] fun _ => true
    simp [act, subst, holds, eval, boolI, h2] at this

/-! ### Uncoloured update arcs -/

/-- `Y(b, c, a)`, the right-hand side of `X`. -/
private abbrev cY : Expr BoolSym ℕ 3 := pvi 1 [cQ, cR, cP]
/-- `X(a, b, c) = Y(b, c, a)` and `Y(a, b, c) = c`. -/
private abbrev cE2 : Pbes BoolSym ℕ 3 := [⟨false, 0, cY⟩, ⟨false, 1, cR⟩]
/-- Swaps `a` with `b`, and `X_{1,2}` with `X_{1,3}`. -/
private noncomputable abbrev cH2 := swap2 (expr cP) (expr cQ) (upd 0 0 1) (upd 0 0 2)

private theorem cY_pvis : cY.pvis = [cY] := by
  simp [pvis, sub, List.filter, isPvi]

private theorem cR_pvis : cR.pvis = [] := by
  simp [pvis, sub, List.filter, isPvi]

private theorem cE2_isPviAt {e : Equation BoolSym ℕ 3} (he : e ∈ cE2) {i : ℕ}
    {p : Expr BoolSym ℕ 3} (hp : IsPviAt e i p) : e = ⟨false, 0, cY⟩ ∧ i = 0 ∧ p = cY := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp only [IsPviAt, cY_pvis] at hp
    rcases i with _ | i
    · simp_all
    · simp at hp
  · simp [IsPviAt, cR_pvis] at hp

/-- The arguments of `Y(b, c, a)` by position. -/
private def cData : Fin 3 → Expr BoolSym ℕ 3 := ![cQ, cR, cP]

private theorem cY_subD (k : Fin 3) : cY.subD[(k : ℕ)]? = some (cData k) := by
  fin_cases k <;> rfl

private theorem cE2_arc {u v : Vertex BoolSym ℕ 3} (h : Arc cE2 u v) :
    ∃ k : Fin 3, (u = expr cY ∧ v = upd 0 0 k) ∨ (u = upd 0 0 k ∧ v = expr (cData k)) ∨
      (u = upd 0 0 k ∧ v = expr (par k)) := by
  rcases h with ⟨φ, hφ, hnp, ψ, hψ, rfl, rfl⟩ | ⟨e, he, i, p, hp, k, h⟩
  · exfalso
    have key : ∀ φ ∈ subE cE2, φ.isPvi = false → φ.subD = [] := by
      simp [subE, sub, isPvi, subD]
    rw [key φ hφ hnp] at hψ
    cases hψ
  · obtain ⟨rfl, rfl, rfl⟩ := cE2_isPviAt he hp
    refine ⟨k, ?_⟩
    rcases h with h | ⟨rfl, t, ht, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · rw [cY_subD] at ht; cases ht; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

private theorem cE2_colour {u v : Vertex BoolSym ℕ 3} (h : Arc cE2 u v) :
    paperArcColour boolComm u v = .bot := by
  obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := cE2_arc h <;>
    simp [paperArcColour, termArcColour]

theorem uncolouredUpdatesUnsound : UncolouredUpdatesUnsound := by
  have hY : IsPviAt (⟨false, 0, cY⟩ : Equation BoolSym ℕ 3) 0 cY := by
    simp [IsPviAt, cY_pvis]
  have arcY : ∀ k : Fin 3, Arc cE2 (expr cY) (upd 0 0 k) := fun k =>
    arc_expr_upd.2 ⟨_, by simp, rfl, hY⟩
  have arcPar : ∀ k : Fin 3, Arc cE2 (upd 0 0 k) (expr (par k)) := fun k =>
    arc_upd.2 ⟨_, by simp, rfl, _, hY, Or.inr rfl⟩
  have arcData : ∀ k : Fin 3, Arc cE2 (upd 0 0 k) (expr (cData k)) := fun k =>
    arc_upd.2 ⟨_, by simp, rfl, _, hY, Or.inl ⟨_, cY_subD k, rfl⟩⟩
  have mem : ∀ φ ∈ subE cE2, expr φ ∈ vertices cE2 := fun φ h =>
    expr_mem_vertices.2 (Or.inl h)
  have memU : ∀ k : Fin 3, upd 0 0 k ∈ vertices cE2 := fun k =>
    upd_mem_vertices.2 ⟨_, by simp, rfl, lt_of_isPviAt hY⟩
  have himg : ∀ u v, Arc cE2 u v → Arc cE2 (cH2 u) (cH2 v) := by
    intro u v huv
    obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := cE2_arc huv <;>
      fin_cases k <;> simp [cH2, swap2, cData] <;>
      first
        | exact arcY _
        | exact arcPar _
        | exact arcData 0
        | exact arcData 1
        | exact arcData 2
  refine ⟨cE2, cH2, Equiv.swap 0 1, ⟨by simp, fun X ts h => ?_⟩,
    ⟨swap2_bijOn (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (mem _ (by simp [subE, sub])) (mem _ (by simp [subE, sub])) (memU 1) (memU 2),
      fun v _ => ?_, fun u v huv => ⟨himg u v huv, by
        rw [cE2_colour huv, cE2_colour (himg u v huv)]⟩⟩, ?_, ?_⟩
  · simp [subE, sub] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · refine swap2_colour (colour cE2) ?_ ?_ v <;>
      simp only [colour, Prod.mk.injEq] <;> refine ⟨rfl, Set.ext fun X => ?_⟩ <;> simp
  · intro k
    fin_cases k <;> simp [cH2, swap2, Equiv.swap_apply_of_ne_of_ne]
  · intro hs
    have := hs ⟨false, 0, cY⟩ (by simp) (fun _ => {[false, false, true]}) ![true, false, false]
      fun _ => true
    simp [act, subst, holds, eval, List.ofFn_succ, Equiv.swap_apply_of_ne_of_ne] at this

end Counterexamples

end MercLib.Symmetry
