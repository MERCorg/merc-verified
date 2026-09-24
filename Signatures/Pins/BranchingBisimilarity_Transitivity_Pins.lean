import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.HasTau
import Signatures.BranchingBisimilarity
import Signatures.Proofs.BranchingBisimilarity_Transitivity_Proofs

open Cslib (LTS HasTau)

-- Contract pin: fails to compile if `BranchingBisimilarity.refl`'s signature drifts.
example [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈br[lts] s :=
  BranchingBisimilarity.refl s

-- Contract pin: fails to compile if `BranchingBisimilarity.symm`'s signature drifts.
example [HasTau Label] {lts : LTS State Label}
    {s s' : State} (h : s ≈br[lts] s') : s' ≈br[lts] s :=
  BranchingBisimilarity.symm h

-- Contract pin: fails to compile if `BranchingBisimilarity.trans`'s signature drifts.
example [HasTau Label] {lts : LTS State Label}
    {s1 s2 s3 : State} (h12 : s1 ≈br[lts] s2) (h23 : s2 ≈br[lts] s3) :
    s1 ≈br[lts] s3 :=
  BranchingBisimilarity.trans h12 h23
