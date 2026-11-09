module

public import MercLib.Algorithms.Graph.Tarjan
import MercLib.Algorithms.Graph.Proofs.TarjanMain_Proofs
import Std.Tactic.Do

/-! Machine-generated; may be freely edited or regenerated (see AGENTS.md).

Correctness of the do-notation `tarjan`: every iteration of its inner loop is one `step` of the
machine, and every iteration of its outer loop is a root step followed by a run of the inner loop.
So the states it passes through are reachable from `init`, the facts `tarjanCorrect` and
`tarjanTerminates` of the machine apply to them, and `measure` is a variant of both loops.

`TarjanRun_Proofs` imports this module privately, so that the lemmas `mvcgen` and `simp` generate
for the matches of `step` and `finish` are not exported. -/

namespace MercLib.Tarjan

variable {n : ℕ}

private theorem step_cons (g : Graph n) (c : Ctx n) (s : Fin n) (off : ℕ) (W : List (Fin n × ℕ))
    (hw : c.work = (s, off) :: W) :
    step g c =
      match scan g s ((g.adj s).drop off) off (initNode g s { c with work := W }) with
      | (some ch, off', c2) => Out.next { c2 with work := (ch, 0) :: (s, off') :: W }
      | (none, _, c2) =>
        match finish s c2 with
        | none => Out.fail
        | some c3 => Out.next c3 := by
  simp only [step, hw]; rfl

/-- The inner loop descends into a child. -/
private theorem step_descend {g : Graph n} {c c2 : Ctx n} {s ch : Fin n} {off off' : ℕ}
    {W : List (Fin n × ℕ)} (hw : c.work = (s, off) :: W)
    (hsc : scan g s ((g.adj s).drop off) off (initNode g s { c with work := W }) =
      (some ch, off', c2)) :
    Step g c { c2 with work := (ch, 0) :: (s, off') :: W } := by
  simp only [Step, step_cons g c s off W hw, hsc]

/-- The inner loop finishes a state. -/
private theorem step_finish {g : Graph n} {c c2 c3 : Ctx n} {s : Fin n} {off f : ℕ}
    {W : List (Fin n × ℕ)} (hw : c.work = (s, off) :: W)
    (hsc : scan g s ((g.adj s).drop off) off (initNode g s { c with work := W }) = (none, f, c2))
    (hfin : finish s c2 = some c3) : Step g c c3 := by
  simp only [Step, step_cons g c s off W hw, hsc, hfin]

/-- `finish` failing is a failing step. -/
private theorem step_fail {g : Graph n} {c c2 : Ctx n} {s : Fin n} {off f : ℕ}
    {W : List (Fin n × ℕ)} (hw : c.work = (s, off) :: W)
    (hsc : scan g s ((g.adj s).drop off) off (initNode g s { c with work := W }) = (none, f, c2))
    (hfin : finish s c2 = none) : step g c = Out.fail := by
  simp only [step_cons g c s off W hw, hsc, hfin]

/-- The outer loop starts a search from an unvisited root. -/
private theorem step_root {g : Graph n} {c : Ctx n} (hw : c.work = []) (hri : c.ri < n)
    (hlow : c.low ⟨c.ri, hri⟩ = g.unv) :
    Step g c { c with work := [(⟨c.ri, hri⟩, 0)], ri := c.ri + 1 } := by
  simp [Step, step, hw, hri, hlow]

/-- The outer loop skips a visited root. -/
private theorem step_skip {g : Graph n} {c : Ctx n} (hw : c.work = []) (hri : c.ri < n)
    (hlow : ¬ c.low ⟨c.ri, hri⟩ = g.unv) : Step g c { c with ri := c.ri + 1 } := by
  simp [Step, step, hw, hri, hlow]

/-- With no work and no roots left the machine stops. -/
private theorem step_stop {g : Graph n} {c : Ctx n} (hw : c.work = []) (hri : ¬ c.ri < n) :
    step g c = Out.stop := by
  simp [step, hw, hri]

/-- The states reachable from the initial context. -/
private abbrev Reach (g : Graph n) (c : Ctx n) : Prop := Relation.ReflTransGen (Step g) (init g) c

open Std.Do

/-- The variant of both loops evaluates to the measure of the context. -/
private theorem eval_iff (g : Graph n) (s : Ctx n × Bool) (m : ℕ) :
    (WhileVariant.eval (ps := PostShape.pure)
      (fun s : Ctx n × Bool => (⟨measure g s.1⟩ : ULift ℕ)) s m).down ↔ measure g s.1 = m := by
  simp [WhileVariant.eval, SVal.evalsTo, eq_comm]

/-- An iteration that takes one machine step preserves the inner invariant and decreases the variant. -/
private theorem inner_yield {g : Graph n} {s t : Ctx n} {f : Bool} {B : ℕ} (hr : Reach g s)
    (hlt : measure g s < B) (hf : f = false) (hst : Step g s t) :
    ∃ a, (WhileVariant.eval (ps := PostShape.pure)
        (fun s : Ctx n × Bool => (⟨measure g s.1⟩ : ULift ℕ)) (t, f) a).down ∧
      a < measure g s ∧ f = false ∧ Reach g t ∧ measure g t < B :=
  have hd := tarjanTerminates g s hr t hst
  ⟨measure g t, (eval_iff g (t, f) _).2 rfl, hd, hf, hr.tail hst, lt_trans hd hlt⟩

set_option linter.deprecated.syntax false in
/-- **`tarjan` is correct.** -/
private theorem tarjanRun_aux (g : Graph n) : TarjanRunCorrect g := by
  unfold TarjanRunCorrect
  generalize h : tarjan g = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => fun s => ⟨measure g s.1⟩
  | inv2 => ⇓ x => match x with
      | .inl s => ⌜s.2 = false ∧ Reach g s.1 ∧ s.1.work = []⌝
      | .inr s => ⌜s.2 = false ∧ Reach g s.1 ∧ s.1.work = [] ∧ ¬ s.1.ri < n⌝
  | inv3 => fun s => ⟨measure g s.1⟩
  | inv4 b _ _ _ _ _ _ _ => ⇓ x => match x with
      | .inl s => ⌜s.2 = false ∧ Reach g s.1 ∧ measure g s.1 < measure g b.1⌝
      | .inr s => ⌜s.2 = false ∧ Reach g s.1 ∧ measure g s.1 < measure g b.1 ∧ s.1.work = []⌝
  case vc1.step.isTrue.h_1 _ _ _ _ _ _ _ _ _ _ _ _ hw hnil _ =>
    exact absurd hnil hw.1
  case vc2.step.isTrue.h_2.h_1 _ _ _ _ _ _ _ _ b mb _ _ _ p off W hsw ch off' c2 hsc hi =>
    obtain ⟨hev, hf, hr, hlt⟩ := hi
    have hst := step_descend (g := g) (c := b.1) hsw hsc
    rw [(eval_iff g b mb).1 hev |>.symm]
    exact inner_yield hr hlt hf hst
  case vc3.step.isTrue.h_2.h_2.h_1 _ _ _ _ _ _ _ _ b _ _ _ _ p off W hsw _ c2 hsc hfin hi =>
    obtain ⟨_, _, hr, _⟩ := hi
    exact absurd (step_fail (g := g) (c := b.1) hsw hsc hfin) (tarjanCorrect g b.1 hr).2
  case vc4.step.isTrue.h_2.h_2.h_2 _ _ _ _ _ _ _ _ b mb _ _ _ p off W hsw _ c2 hsc c3 hfin hi =>
    obtain ⟨hev, hf, hr, hlt⟩ := hi
    have hst := step_finish (g := g) (c := b.1) hsw hsc hfin
    rw [(eval_iff g b mb).1 hev |>.symm]
    exact inner_yield hr hlt hf hst
  case vc5.step.isFalse _ _ _ _ _ _ _ _ _ _ _ _ hn hi =>
    obtain ⟨_, hf, hr, hlt⟩ := hi
    exact ⟨hf, hr, hlt, by_contra fun hw => hn ⟨hw, hf⟩⟩
  case vc6.step.isTrue.isTrue.pre b _ _ _ hg r hlow hi =>
    obtain ⟨_, hf, hr, hw⟩ := hi
    have hri : b.1.ri < n := hg.1
    have hst := step_root (g := g) (c := b.1) hw hri hlow
    exact ⟨hf, hr.tail hst, tarjanTerminates g b.1 hr _ hst⟩
  case vc7.step.isTrue.isTrue.post.success b mb _ _ _ _ _ hi res hr =>
    obtain ⟨hev, _⟩ := hi
    obtain ⟨hf, hreach, hlt, hw⟩ := hr
    exact ⟨measure g res.1, (eval_iff g _ _).2 rfl, (eval_iff g b mb).1 hev ▸ hlt, hf, hreach, hw⟩
  case vc8.step.isTrue.isFalse b mb _ _ hg r hlow hi =>
    obtain ⟨hev, hf, hr, hw⟩ := hi
    have hri : b.1.ri < n := hg.1
    have hst := step_skip (g := g) (c := b.1) hw hri hlow
    have hd := tarjanTerminates g b.1 hr _ hst
    exact ⟨_, (eval_iff g _ _).2 rfl, (eval_iff g b mb).1 hev ▸ hd, hf, hr.tail hst, hw⟩
  case vc9.step.isFalse _ _ _ _ hn hi =>
    obtain ⟨_, hf, hr, hw⟩ := hi
    exact ⟨hf, hr, hw, fun hri => hn ⟨hri, hf⟩⟩
  case vc11.post.success res _ hi =>
    obtain ⟨hf, hr, hw, hri⟩ := hi
    have hstop := step_stop (g := g) (c := res.1) hw hri
    have hres : (if res.2 = true then (none : Option (Ctx n)) else some res.1) = some res.1 := by
      simp [hf]
    exact ⟨res.1, hres, (tarjanCorrect g _ hr).1 hstop⟩

end MercLib.Tarjan
