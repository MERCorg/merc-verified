import Aeneas.Std.WP

/-!
# Compatibility shims for removed Aeneas `Std.WP` lemmas

Aeneas commit aa66752b1 ("Remove `spec_imp_exists`") dropped `spec_equiv_exists`,
`spec_imp_exists` and `exists_imp_spec` from `Aeneas.Std.WP`, replacing them with
`spec_and`/`spec_exists`, which no longer expose the `m = ok y` equation. The
translated-code proofs in this repository rely on that equation pervasively
(~100 call sites), so the three lemmas are restated here in the same namespace,
keeping every existing `Std.WP.spec_imp_exists`/`exists_imp_spec` reference
working unchanged. They hold for the new `DWP`-based definition of `spec` too
(`spec_ok`/`spec_vis`/`spec_fail`/`spec_div` are all `simp` lemmas).
-/

namespace Aeneas.Std.WP

open Aeneas.Std Result

theorem spec_equiv_exists (m : Result α) (P : Post α) :
    spec m P ↔ (∃ y, m = ok y ∧ P y) := by
  cases m <;> simp

theorem spec_imp_exists {m : Result α} {P : Post α} :
    spec m P → (∃ y, m = ok y ∧ P y) :=
  (spec_equiv_exists m P).1

theorem exists_imp_spec {m : Result α} {P : Post α} :
    (∃ y, m = ok y ∧ P y) → spec m P :=
  (spec_equiv_exists m P).2

end Aeneas.Std.WP
