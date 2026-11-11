module

public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# Control flow graphs of linear processes

The control flow graphs of [J. van de Pol and M. Timmer, *State Space Reduction of Linear Processes
Using Control Flow Reconstruction*][vandePol2009] (Section 3), and the way an implementation obtains
them from terms.

In the paper, the source and the destination of a parameter for a summand are *values*
(Definitions 2 and 3), and so are the locations of a control flow parameter and the endpoints of the
edges of its control flow graph (Definitions 4 and 6). Proposition 1 then states that every
transition of a summand that a control flow parameter rules follows an edge of its graph.

An implementation obtains sources and destinations as closed terms in normal form instead. Distinct
normal forms can have the same value, when `==` is coarser than syntactic equality, so comparing
terms as terms can miss an edge. The implementation therefore decides the equality of every two
*location terms* of a candidate parameter with a sound procedure, such as rewriting `a == b` to
`true` or `false`, and only accepts the parameter when every pair is decided (`Decided`). Then two
location terms are in the same location exactly when they have the same value
(`decidedLocationsAreValues`), and a summand whose source is in another location than the current
value cannot be enabled (`locationPruningSound`).

There is no page on the merc website for this theory yet.

## Main definitions

- `LinearProcess`: a linear process equation with enabling and next-state functions.
- `IsSource`, `IsDestination`: source and destination functions (Definitions 2 and 3).
- `Rules`, `Edge`: the summands that a parameter rules and the edges of its control flow graph
  (Definitions 4 and 6).
- `SoundEquality`, `Decided`: a sound decision procedure for the equality of terms, and that it
  decides every pair of a set of location terms.

## Main statements

- `Proposition1`: a transition of a summand that a parameter rules follows an edge of its control
  flow graph (Proposition 1).
- `DecidedLocationsAreValues`: on decided location terms, the decision is equality of values.
- `LocationPruningSound`: a summand whose source term is not decided equal to the location term of
  the current value is not enabled.

## References

- [vandePol2009]
-/

namespace MercLib.ControlFlow.Lpe

/-- A linear process equation of [vandePol2009] (Section 2) with parameters `J`, all of which take
values in `Val`, summands `I` and local variables `E`: summand `i` is enabled in the state `v` for
the local variables `e` if `enabled i v e`, and then leads to the state `next i v e`. The actions do
not influence the control flow graphs, so they are left out. -/
structure LinearProcess (J I E Val : Type) where
  /-- The enabling function of every summand. -/
  enabled : I → (J → Val) → E → Prop
  /-- The next-state function of every summand. -/
  next : I → (J → Val) → E → (J → Val)

variable {J I E Val : Type}

/-- `source` is a source function (Definition 2): `source i j = some s` implies that summand `i` is
only enabled in states in which parameter `j` has the value `s`. -/
def IsSource (L : LinearProcess J I E Val) (source : I → J → Option Val) : Prop :=
  ∀ i j s, source i j = some s → ∀ v e, L.enabled i v e → v j = s

/-- `destination` is a destination function (Definition 3): `destination i j = some t` implies that
parameter `j` has the value `t` after taking summand `i`. -/
def IsDestination (L : LinearProcess J I E Val) (destination : I → J → Option Val) : Prop :=
  ∀ i j t, destination i j = some t → ∀ v e, L.enabled i v e → L.next i v e j = t

/-- Parameter `j` rules summand `i` when both its source and its destination are known
(Definition 4). -/
def Rules (source destination : I → J → Option Val) (i : I) (j : J) : Prop :=
  (source i j).isSome ∧ (destination i j).isSome

/-- The edge `(s, i, t)` of the control flow graph of parameter `j` (Definition 6). -/
def Edge (source destination : I → J → Option Val) (j : J) (s : Val) (i : I) (t : Val) : Prop :=
  source i j = some s ∧ destination i j = some t

/-- **Proposition 1 of [vandePol2009].** If parameter `j` rules summand `i`, and `i` is enabled in
state `v` for the local variables `e`, then the control flow graph of `j` has an edge from `v j` to
the value of `j` in the next state. -/
def Proposition1 (L : LinearProcess J I E Val) (source destination : I → J → Option Val) : Prop :=
  IsSource L source → IsDestination L destination →
    ∀ i j v e, Rules source destination i j → L.enabled i v e →
      Edge source destination j (v j) i (L.next i v e j)

/-- A procedure `decide` that decides the equality of terms is sound for the evaluation `eval` of
terms: `decide a b = some true` implies that `a` and `b` have the same value, and
`decide a b = some false` that they have different values. It may also not decide, `none`. -/
def SoundEquality {Term : Type} (eval : Term → Val) (decide : Term → Term → Option Bool) : Prop :=
  ∀ a b, (decide a b = some true → eval a = eval b) ∧ (decide a b = some false → eval a ≠ eval b)

/-- `decide` decides the equality of every two location terms of `locations`. -/
def Decided {Term : Type} (decide : Term → Term → Option Bool) (locations : Set Term) : Prop :=
  ∀ a ∈ locations, ∀ b ∈ locations, (decide a b).isSome

/-- **Decided locations are values.** If `decide` is sound and decides every two location terms of
`locations`, then it decides two location terms equal exactly when they have the same value: the
locations of the implementation are the locations of [vandePol2009]. -/
def DecidedLocationsAreValues {Term : Type} (eval : Term → Val) (decide : Term → Term → Option Bool)
    (locations : Set Term) : Prop :=
  SoundEquality eval decide → Decided decide locations →
    ∀ a ∈ locations, ∀ b ∈ locations, (decide a b = some true ↔ eval a = eval b)

/-- **Pruning by locations is sound.** Let `source` be the source terms of a source function, with
values given by `eval`, let `decide` be sound and decide every two location terms of `locations`.
If parameter `j` has the value of the location term `l` in state `v`, and the source term `s` of
summand `i` for `j` is a location term that `decide` does not decide equal to `l`, then `i` is not
enabled in `v`. -/
def LocationPruningSound {Term : Type} (L : LinearProcess J I E Val) (eval : Term → Val)
    (decide : Term → Term → Option Bool) (locations : Set Term) (source : I → J → Option Term) :
    Prop :=
  IsSource L (fun i j => (source i j).map eval) → SoundEquality eval decide →
    Decided decide locations →
    ∀ i j v e l s, l ∈ locations → s ∈ locations → v j = eval l → source i j = some s →
      decide l s ≠ some true → ¬ L.enabled i v e

end MercLib.ControlFlow.Lpe
