#!/usr/bin/env python3
"""Check that the "headline" theorems below depend on no axioms beyond:
  - the three Lean/mathlib kernel axioms (propext, Classical.choice, Quot.sound)
  - the hand-vetted boundary axioms declared in MercVerified/Basic.lean and
    MercVerified/Code/*External*.lean (Aeneas external-function stubs -
    see CLAUDE.md)
  - `sorryAx`, reported as a known-incomplete proof (see KNOWN_INCOMPLETE
    below) rather than a failure

These are exactly the theorems that also get a signature-drift pin (an
`example := <theorem>` right after them in the same file) - see the
lean-conventions skill. Run after a successful `lake build` (needs built
.olean files); see .github/workflows/lean_action_ci.yml.
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

THEOREMS = [
    "IsStable.bisimilarity",
    "StrongFixPoint.bisimilarity",
    "Cslib.LTS.Bisimilarity.strongFixPoint",
    "IsStable.branchingBisimilarity",
    "BranchingBisimilarity.refl",
    "BranchingBisimilarity.symm",
    "BranchingBisimilarity.trans",
    "IsStable.branchingBisimilarity_inductive",
    "InductiveBranchingFixPoint.branchingBisimilarity",
    "BranchingBisimilarity.inductiveBranchingFixPoint",
    "MercVerified.Signatures.Proofs.strong_bisim_sigref_correct",
    "MercVerified.Signatures.Proofs.strong_bisim_signature_spec",
]

# Theorems allowed to depend on `sorryAx` without failing the check (open,
# tracked contracts - see their module doc comments).
KNOWN_INCOMPLETE = {
    "MercVerified.Signatures.Proofs.strong_bisim_sigref_correct",
}

IMPORTS = [
    "Signatures.Proofs.Signature_Proofs",
    "Signatures.Proofs.BranchingBisimilarity_Transitivity_Proofs",
    "Signatures.Proofs.InductiveSignatures_Proofs",
    "MercVerified.Signatures.Proofs.Refinement_Proofs",
    "MercVerified.Signatures.Proofs.StrongSignature_Proofs",
]

KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

AXIOM_DECL_RE = re.compile(r"^axiom ([A-Za-z0-9_.]+)", re.MULTILINE)
PRINT_AXIOMS_RE = re.compile(
    r"^'(?P<name>[^']+)' "
    r"(?:does not depend on any axioms"
    r"|depends on axioms: \[(?P<axioms>[^\]]*)\])$",
    re.MULTILINE,
)


def boundary_axioms() -> set[str]:
    """Axioms already declared for the translated-code boundary: anything
    declared in MercVerified/Basic.lean or MercVerified/Code/*External*.lean
    is pre-approved (see CLAUDE.md - hand-written stubs, edited as needed)."""
    axioms: set[str] = set()
    paths = [REPO_ROOT / "MercVerified" / "Basic.lean"]
    paths += sorted((REPO_ROOT / "MercVerified" / "Code").glob("*External*.lean"))
    for path in paths:
        if path.exists():
            axioms.update(AXIOM_DECL_RE.findall(path.read_text()))
    return axioms


def main() -> int:
    approved = KERNEL_AXIOMS | boundary_axioms()

    lean_src = "\n".join(f"import {i}" for i in IMPORTS)
    lean_src += "\n" + "\n".join(f"#print axioms {t}" for t in THEOREMS) + "\n"

    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(lean_src)
        tmp_path = Path(f.name)

    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
    finally:
        tmp_path.unlink(missing_ok=True)

    if result.stderr.strip():
        print(result.stderr, file=sys.stderr, end="")

    failed = False
    seen: set[str] = set()
    for match in PRINT_AXIOMS_RE.finditer(result.stdout):
        name = match.group("name")
        seen.add(name)
        axioms_str = match.group("axioms")
        if axioms_str is None:
            print(f"OK          {name}: no axioms")
            continue

        axioms = {a.strip() for a in axioms_str.split(",") if a.strip()}
        has_sorry = "sorryAx" in axioms
        unexpected = axioms - approved - {"sorryAx"}

        if unexpected:
            print(f"FAIL        {name}: unapproved axioms: {', '.join(sorted(unexpected))}")
            failed = True
        elif has_sorry:
            if name in KNOWN_INCOMPLETE:
                print(f"INCOMPLETE  {name}: depends on sorryAx (tracked, see module doc)")
            else:
                print(f"FAIL        {name}: depends on sorryAx but is not listed in KNOWN_INCOMPLETE")
                failed = True
        else:
            print(f"OK          {name}: only approved axioms")

    missing = [t for t in THEOREMS if t not in seen]
    if missing:
        for name in missing:
            print(f"FAIL        {name}: no `#print axioms` output (build or import failure?)")
        failed = True

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
