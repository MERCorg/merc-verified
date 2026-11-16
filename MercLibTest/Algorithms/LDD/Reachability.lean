import MercLib.Algorithms.LDD.Reachability
import MercLibTest.Algorithms.LDD.Operations

/-!
# Tests for `MercLib.Algorithms.LDD.Reachability`

Runs breadth-first search, chaining, recursive and node-wise saturation and REACH on small models and compares their results with
the reachable vectors computed explicitly, vector by vector, with `applyB` from the operation tests.
-/

namespace MercLibTest.LDD

open MercLib.LDD MercLib.LDD.Ldd

/-- The explicit successors of the vectors `X` under event `e`, whose relation is given as the list
    of vectors `R`. -/
def postEvent (e : Event ℕ) (R : List (List ℕ)) (X : List (List ℕ)) : List (List ℕ) :=
  post (e.metaAt 0) X R

/-- The vectors reachable from `X` with the events `E` (each with its relation as a list),
    computed explicitly, within `fuel` rounds. -/
def reachList : ℕ → List (Event ℕ × List (List ℕ)) → List (List ℕ) → List (List ℕ)
  | 0, _, X => X
  | fuel + 1, E, X =>
    let Y := (X ++ E.flatMap fun (e, R) => postEvent e R X).dedup
    if Y.length = X.length then X else reachList fuel E Y

/-- The events of `E`, with their relations as LDDs. -/
def events (E : List (Event ℕ × List (List ℕ))) : List (Event ℕ) :=
  E.map fun (e, R) => { e with rel := ofList R }

/-! ## The worked example of the website

Two positions, from `(0, 0)`. Event `a` moves position 1 from 0 to 1; event `b` moves position 0
from 0 to 1 when position 1 holds 1. -/

def a : Event ℕ × List (List ℕ) := ({ top := 1, access := [.readWrite], rel := zero }, [[0, 1]])
def b : Event ℕ × List (List ℕ) :=
  ({ top := 0, access := [.readWrite, .read], rel := zero }, [[0, 1, 1]])

def example₁ : List (List ℕ) := [[0, 0], [0, 1], [1, 1]]

#guard reachList 10 [a, b] [[0, 0]] == example₁
#guard bfs (events [a, b]) (ofList [[0, 0]]) == ofList example₁
#guard chaining (events [a, b]) (ofList [[0, 0]]) == ofList example₁
#guard saturate (events [a, b]) 2 0 (ofList [[0, 0]]) == ofList example₁
-- the order of the events does not matter
#guard saturate (events [b, a]) 2 0 (ofList [[0, 0]]) == ofList example₁
#guard saturateNodewise (events [a, b]) 2 0 (ofList [[0, 0]]) == ofList example₁
#guard saturateNodewise (events [b, a]) 2 0 (ofList [[0, 0]]) == ofList example₁
#guard reach (events [a, b]) 2 0 (ofList [[0, 0]]) == ofList example₁
#guard reach (events [b, a]) 2 0 (ofList [[0, 0]]) == ofList example₁

/-! ## Three counters

Every position counts up to 3; a counter may only step while the counter before it is larger,
except the first one, and the last counter may reset the second one. -/

def inc₀ : Event ℕ × List (List ℕ) :=
  ({ top := 0, access := [.readWrite], rel := zero }, [[0, 1], [1, 2], [2, 3]])
def inc₁ : Event ℕ × List (List ℕ) :=
  ({ top := 0, access := [.read, .readWrite], rel := zero },
    [[1, 0, 1], [2, 0, 1], [2, 1, 2], [3, 0, 1], [3, 1, 2], [3, 2, 3]])
def inc₂ : Event ℕ × List (List ℕ) :=
  ({ top := 1, access := [.read, .readWrite], rel := zero },
    [[1, 0, 1], [2, 0, 1], [2, 1, 2], [3, 0, 1], [3, 1, 2], [3, 2, 3]])
def reset : Event ℕ × List (List ℕ) :=
  ({ top := 1, access := [.write, .read], rel := zero }, [[0, 3]])

def counters : List (Event ℕ × List (List ℕ)) := [inc₀, inc₁, inc₂, reset]
def expected₂ : List (List ℕ) := reachList 100 counters [[0, 0, 0]]

#guard expected₂.length == 23
#guard bfs (events counters) (ofList [[0, 0, 0]]) == ofList expected₂
#guard chaining (events counters) (ofList [[0, 0, 0]]) == ofList expected₂
#guard saturate (events counters) 3 0 (ofList [[0, 0, 0]]) == ofList expected₂
#guard saturate (events counters.reverse) 3 0 (ofList [[0, 0, 0]]) == ofList expected₂
#guard saturateNodewise (events counters) 3 0 (ofList [[0, 0, 0]]) == ofList expected₂
#guard saturateNodewise (events counters.reverse) 3 0 (ofList [[0, 0, 0]]) == ofList expected₂
#guard reach (events counters) 3 0 (ofList [[0, 0, 0]]) == ofList expected₂
#guard reach (events counters.reverse) 3 0 (ofList [[0, 0, 0]]) == ofList expected₂


end MercLibTest.LDD
