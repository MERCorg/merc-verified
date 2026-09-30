import MercVerified.Code.FunsExternal_Template

open Aeneas Aeneas.Std Result
open verified

/-- The comparison of an `Ord` instance never fails and is a total preorder:
    `cmp a b = gt ↔ cmp b a = lt`, and `a ≤ b`, `b ≤ c` imply `a ≤ c` (with `x ≤ y` meaning
    `cmp x y ≠ gt`). This is the standing (documented) requirement of `sort_unstable`. -/
def core.cmp.Ord.IsTotalOrder {T : Type} (I : core.cmp.Ord T) : Prop :=
  (∀ a b, ∃ o, I.cmp a b = ok o) ∧
  (∀ a b, I.cmp a b = ok Ordering.gt ↔ I.cmp b a = ok Ordering.lt) ∧
  (∀ a b c, I.cmp a b ≠ ok Ordering.gt → I.cmp b c ≠ ok Ordering.gt → I.cmp a c ≠ ok Ordering.gt)

/-- `[T]::sort_unstable` never fails, and its result is a permutation of its input. For a
    lawful `Ord` (`IsTotalOrder`) the result is moreover sorted: no element is greater than one
    that comes after it. (The Rust docs only promise this order for lawful instances.) -/
axiom core.slice.Slice.sort_unstable_spec
  {T : Type} (cmpOrdInst : core.cmp.Ord T) (s : Slice T) :
  ∃ s', core.slice.Slice.sort_unstable cmpOrdInst s = ok s' ∧ List.Perm s'.val s.val ∧
    (core.cmp.Ord.IsTotalOrder cmpOrdInst →
      List.Pairwise (fun a b => cmpOrdInst.cmp a b ≠ ok Ordering.gt) s'.val)

/-- `Vec::clear` never fails, and empties the vector - the only property that
    `MercVerified/Refinement/` and `MercVerified/Lts/` needs (the initial contents of the reused builder
    are irrelevant to `strong_bisim_signature`). -/
axiom alloc.vec.Vec.clear_spec
  {T : Type} (A : Type) (v : alloc.vec.Vec T) :
  ∃ v', alloc.vec.Vec.clear A v = ok v' ∧ v'.val = []

/-- `PartialEq` instance whose `eq` never fails and is equality of the values. -/
def core.cmp.PartialEq.IsLawfulEq {T : Type} (I : core.cmp.PartialEq T T) : Prop :=
  ∀ a b, ∃ r, I.eq a b = ok r ∧ (r = true ↔ a = b)

/-- `Vec::dedup` never fails. For a lawful equality it removes exactly the *consecutive*
    duplicates: the result is a sub-list of the input with the same elements, in which no two
    neighbours are equal. -/
axiom alloc.vec.Vec.dedup_spec
  {T : Type} (A : Type) (corecmpPartialEqInst : core.cmp.PartialEq T T)
  (v : alloc.vec.Vec T) :
  ∃ v', alloc.vec.Vec.dedup A corecmpPartialEqInst v = ok v' ∧
    (core.cmp.PartialEq.IsLawfulEq corecmpPartialEqInst →
      (∀ x, x ∈ v'.val ↔ x ∈ v.val) ∧ List.Sublist v'.val v.val ∧
      List.IsChain (fun a b => a ≠ b) v'.val)

/-- Tuple equality (`core::tuple`): `(a₁, b₁) == (a₂, b₂)` is `a₁ == a₂ && b₁ == b₂`
    (short-circuiting). -/
axiom Pair.Insts.CoreCmpPartialEqPair.eq_spec {U T : Type}
  (iU : core.cmp.PartialEq U U) (iT : core.cmp.PartialEq T T) (a₁ a₂ : U) (b₁ b₂ : T) :
  Pair.Insts.CoreCmpPartialEqPair.eq iU iT (a₁, b₁) (a₂, b₂) =
    (do let x ← iU.eq a₁ a₂
        if x then iT.eq b₁ b₂ else ok false)

/-- Tuple ordering (`core::tuple`) is lexicographic: compare the first components, and only when
    they are equal the second ones. -/
axiom Pair.Insts.CoreCmpOrd.cmp_spec {U T : Type}
  (iU : core.cmp.Ord U) (iT : core.cmp.Ord T) (a₁ a₂ : U) (b₁ b₂ : T) :
  Pair.Insts.CoreCmpOrd.cmp iU iT (a₁, b₁) (a₂, b₂) =
    (do let o ← iU.cmp a₁ a₂
        if o = Ordering.eq then iT.cmp b₁ b₂ else ok o)

/-- `Vec::pop` on the empty vector returns `None` and leaves the vector
    unchanged - the exact Rust semantics of
    `alloc::vec::Vec::<T>::pop` restricted to `self.is_empty()`. -/
axiom alloc.vec.Vec.pop_nil_spec
  {T : Type} (A : Type) (v : alloc.vec.Vec T) (h : v.val = []) :
  alloc.vec.Vec.pop A v = ok (none, v)

/-- `Vec::pop` on a non-empty vector removes its *last* element - the exact
    Rust semantics of `alloc::vec::Vec::<T>::pop` restricted to `h : v.val = rest ++ [x]`. -/
axiom alloc.vec.Vec.pop_cons_spec
  {T : Type} (A : Type) (v : alloc.vec.Vec T) (x : T) (rest : List T)
  (h : v.val = rest ++ [x]) :
  ∃ v', alloc.vec.Vec.pop A v = ok (some x, v') ∧ v'.val = rest

/-- `new_worklist_progress` never fails (it only allocates the progress-ticker
    used to log `(iteration, num_blocks)` pairs to stderr). -/
axiom merc_reduction.signature_refinement.new_worklist_progress_spec :
  ∃ progress : merc_io.progress.TimeProgress (Std.Usize × Std.Usize),
    merc_reduction.signature_refinement.new_worklist_progress = ok progress

/-- `TimeProgress::print` never fails (it only writes an `(iteration, blocks)`
    tick line to stderr). -/
axiom merc_io.progress.TimeProgress.print_spec
  {T : Type} (p : merc_io.progress.TimeProgress T) (t : T) :
  merc_io.progress.TimeProgress.print p t = ok ()

/-- `Vec::resize_with` never fails and yields a vector of exactly the requested length (it either
    extends with calls of `f` or truncates) - only its contents are under-specified. -/
axiom alloc.vec.Vec.resize_with_spec
  {T : Type} {F : Type} (A : Type)
  (coreopsfunctionFnMutFTupleTInst : core.ops.function.FnMut F Unit T) :
  (v : alloc.vec.Vec T) → (len : Std.Usize) → (f : F) →
  ∃ w, alloc.vec.Vec.resize_with A coreopsfunctionFnMutFTupleTInst v len f = ok w ∧
    w.val.length = len.val

/-- `Vec::default` never fails - only its contents are under-specified. -/
axiom alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec
  (T : Type) : ∃ v : alloc.vec.Vec T,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default T = ok v

/-- `Timing::measure(name, f)` runs the closure and returns its result - the
    only way `strong_bisim_sigref`'s timing wrapper is used. -/
axiom merc_utilities.timing.Timing.measure_spec
  {F : Type} {O : Type} (coreopsfunctionFnOnceFTupleOInst :
    core.ops.function.FnOnce F Unit O) :
  (timing : merc_utilities.timing.Timing) → (s : Str) → (f : F) →
  ∃ o : O,
    merc_utilities.timing.Timing.measure coreopsfunctionFnOnceFTupleOInst timing s f = ok o ∧
    coreopsfunctionFnOnceFTupleOInst.call_once f () = ok o
