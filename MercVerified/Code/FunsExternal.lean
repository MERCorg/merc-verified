import MercVerified.Code.FunsExternal_Template

open Aeneas Aeneas.Std Result
open verified

/-- `[T]::sort_unstable` never fails, and its result is a permutation of its
    input - the only property of sorting that `MercVerified/Signatures/`
    needs (it deliberately does not characterize sortedness itself). -/
axiom core.slice.Slice.sort_unstable_spec
  {T : Type} (cmpOrdInst : core.cmp.Ord T) (s : Slice T) :
  ∃ s', core.slice.Slice.sort_unstable cmpOrdInst s = ok s' ∧ List.Perm s'.val s.val

/-- `Vec::clear` never fails, and empties the vector - the only property that
    `MercVerified/Signatures/` needs (the initial contents of the reused builder
    are irrelevant to `strong_bisim_signature`). -/
axiom alloc.vec.Vec.clear_spec
  {T : Type} (A : Type) (v : alloc.vec.Vec T) :
  ∃ v', alloc.vec.Vec.clear A v = ok v' ∧ v'.val = []

/-- `Vec::dedup` never fails, and only removes *consecutive* duplicates, so
    (regardless of whether the input happens to be sorted) it never changes
    which elements are present - only how many times each one repeats. -/
axiom alloc.vec.Vec.dedup_spec
  {T : Type} (A : Type) (corecmpPartialEqInst : core.cmp.PartialEq T T)
  (v : alloc.vec.Vec T) :
  ∃ v', alloc.vec.Vec.dedup A corecmpPartialEqInst v = ok v' ∧
    ∀ x, x ∈ v'.val ↔ x ∈ v.val

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

/-- `HashMap::len` never fails - only its value is under-specified. -/
axiom std.collections.hash.map.HashMap.len_spec
  {K : Type} {V : Type} {S : Type} {A : Type}
  (h : std.collections.hash.map.HashMap K V S A) :
  ∃ n : Std.Usize, std.collections.hash.map.HashMap.len h = ok n

/-- `Vec::resize_with` never fails - only its contents are under-specified. -/
axiom alloc.vec.Vec.resize_with_spec
  {T : Type} {F : Type} (A : Type)
  (coreopsfunctionFnMutFTupleTInst : core.ops.function.FnMut F Unit T) :
  (v : alloc.vec.Vec T) → (len : Std.Usize) → (f : F) →
  ∃ w, alloc.vec.Vec.resize_with A coreopsfunctionFnMutFTupleTInst v len f = ok w

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
