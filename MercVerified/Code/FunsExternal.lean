module

public import MercVerified.Code.FunsExternal_Template

@[expose] public section

open Aeneas Aeneas.Std Result
open verified

/-- The comparison of an `Ord` instance never fails and is a total preorder:
    `cmp a b = gt ↔ cmp b a = lt`, and `a ≤ b`, `b ≤ c` imply `a ≤ c` (with `x ≤ y` meaning
    `cmp x y ≠ gt`). This is the standing (documented) requirement of `sort_unstable`. -/
def core.cmp.Ord.IsTotalOrder {T : Type} (I : core.cmp.Ord T) : Prop :=
  (∀ a b, ∃ o, I.cmp a b = ok o) ∧
  (∀ a b, I.cmp a b = ok Ordering.gt ↔ I.cmp b a = ok Ordering.lt) ∧
  (∀ a b c, I.cmp a b ≠ ok Ordering.gt → I.cmp b c ≠ ok Ordering.gt → I.cmp a c ≠ ok Ordering.gt)

/-- `[T]::sort_unstable` with a lawful `Ord` (`IsTotalOrder`: `cmp` never fails and is a total
    preorder) never fails, and its result is a permutation of its input that is sorted: no element
    is greater than one that comes after it. (For a non-total order Rust may panic, and the
    comparison may fail, so nothing is claimed.) Allocation failure is excluded. -/
axiom core.slice.Slice.sort_unstable_spec
  {T : Type} (cmpOrdInst : core.cmp.Ord T) (hT : core.cmp.Ord.IsTotalOrder cmpOrdInst)
  (s : Slice T) :
  ∃ s', core.slice.Slice.sort_unstable cmpOrdInst s = ok s' ∧ List.Perm s'.val s.val ∧
    List.Pairwise (fun a b => cmpOrdInst.cmp a b ≠ ok Ordering.gt) s'.val

/-- `Vec::clear` never fails, and empties the vector - the only property that
    `MercVerified/Refinement/` and `MercVerified/Lts/` needs (the initial contents of the reused builder
    are irrelevant to `strong_bisim_signature`). -/
axiom alloc.vec.Vec.clear_spec
  {T : Type} (A : Type) (v : alloc.vec.Vec T) :
  ∃ v', alloc.vec.Vec.clear A v = ok v' ∧ v'.val = []

/-- `PartialEq` instance whose `eq` never fails and is equality of the values. -/
def core.cmp.PartialEq.IsLawfulEq {T : Type} (I : core.cmp.PartialEq T T) : Prop :=
  ∀ a b, ∃ r, I.eq a b = ok r ∧ (r = true ↔ a = b)

/-- `Eq` instance whose `eq` never fails and is equality of the values (so reflexive, symmetric,
    transitive, and a hash consistent with it is just a function of the value). -/
def core.cmp.Eq.IsLawful {T : Type} (I : core.cmp.Eq T) : Prop :=
  core.cmp.PartialEq.IsLawfulEq I.partialEqInst

/-- `Hasher` whose `write` and `finish` never fail. -/
def core.hash.Hasher.IsTotal {H : Type} (I : core.hash.Hasher H) : Prop :=
  (∀ h s, ∃ h', I.write h s = ok h') ∧ (∀ h, ∃ r, I.finish h = ok r)

/-- `Hash` instance whose `hash` never fails when run with a total `Hasher`. -/
def core.hash.Hash.IsTotal {T : Type} (I : core.hash.Hash T) : Prop :=
  ∀ {H : Type} (HI : core.hash.Hasher H), core.hash.Hasher.IsTotal HI →
    ∀ x h, ∃ h', I.hash HI x h = ok h'

/-- `BuildHasher` whose `build_hasher` never fails and whose hashers are total. -/
def verified.core.hash.BuildHasher.IsTotal {S Hs : Type}
    (B : verified.core.hash.BuildHasher S Hs) : Prop :=
  (∀ s, ∃ h, B.build_hasher s = ok h) ∧ core.hash.Hasher.IsTotal B.HasherInst

/-- `Vec::dedup` with a lawful equality (`IsLawfulEq`: `eq` never fails and is equality) never
    fails and removes exactly the *consecutive* duplicates: the result is a sub-list of the input
    with the same elements, in which no two neighbours are equal. -/
axiom alloc.vec.Vec.dedup_spec
  {T : Type} (A : Type) (corecmpPartialEqInst : core.cmp.PartialEq T T)
  (hEq : core.cmp.PartialEq.IsLawfulEq corecmpPartialEqInst) (v : alloc.vec.Vec T) :
  ∃ v', alloc.vec.Vec.dedup A corecmpPartialEqInst v = ok v' ∧
    (∀ x, x ∈ v'.val ↔ x ∈ v.val) ∧ List.Sublist v'.val v.val ∧
    List.IsChain (fun a b => a ≠ b) v'.val

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

/-- `TimeProgress::print` only writes a tick line to stderr. It never fails, apart from the
    stderr write panicking, which is excluded (like allocation failure). -/
axiom merc_io.progress.TimeProgress.print_spec
  {T : Type} (p : merc_io.progress.TimeProgress T) (t : T) :
  merc_io.progress.TimeProgress.print p t = ok ()

/-- `FnMut` instance whose `call_mut` never fails. -/
def core.ops.function.FnMut.IsTotal {F T : Type} (I : core.ops.function.FnMut F Unit T) : Prop :=
  ∀ f, ∃ r, I.call_mut f () = ok r

/-- `Vec::resize_with` with a closure that never fails (`FnMut.IsTotal`) never fails and yields a
    vector of exactly the requested length (it either extends with calls of `f` or truncates) -
    only its contents are under-specified. Allocation failure is excluded. -/
axiom alloc.vec.Vec.resize_with_spec
  {T : Type} {F : Type} (A : Type)
  (coreopsfunctionFnMutFTupleTInst : core.ops.function.FnMut F Unit T)
  (hf : core.ops.function.FnMut.IsTotal coreopsfunctionFnMutFTupleTInst) :
  (v : alloc.vec.Vec T) → (len : Std.Usize) → (f : F) →
  ∃ w, alloc.vec.Vec.resize_with A coreopsfunctionFnMutFTupleTInst v len f = ok w ∧
    w.val.length = len.val

/-- `Vec::default` never fails and yields the empty vector. -/
axiom alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec
  (T : Type) : ∃ v : alloc.vec.Vec T,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default T = ok v ∧ v.val = []

/-- `Timing::measure(name, f)` runs the closure and returns its result: it succeeds exactly
    when `f` does, with the same value. -/
axiom merc_utilities.timing.Timing.measure_spec
  {F : Type} {O : Type} (coreopsfunctionFnOnceFTupleOInst :
    core.ops.function.FnOnce F Unit O) :
  (timing : merc_utilities.timing.Timing) → (s : Str) → (f : F) →
  merc_utilities.timing.Timing.measure coreopsfunctionFnOnceFTupleOInst timing s f =
    coreopsfunctionFnOnceFTupleOInst.call_once f ()
