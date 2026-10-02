#!/usr/bin/env python3
"""Check that the "headline" theorems below depend on no axioms beyond:
  - the three Lean/mathlib kernel axioms (propext, Classical.choice, Quot.sound)
  - the hand-vetted boundary axioms declared in
    MercVerified/Code/*External*.lean.
  - the Aeneas Lean backend's own Std-library axioms (everything under
    3rd-party/aeneas/backends/lean/Aeneas/) - the translation framework's own
    trusted primitives (e.g. `core.fmt.Formatter`), out of this project's
    control
  - `_native.decide.ax_N` axioms whose statement is exactly the byte-length
    bound check `Aeneas.Std.toStr` discharges via `decide +native` for a string
    literal (`decide ("<lit>".toByteArray.size <= U32.max) = true`). These get a
    fresh per-declaration name each time (and, when they sit inside a `private`
    declaration, an abbreviated `_private`-mangled `✝`-suffixed name), so they
    can't be approved by name; their statement shape is checked instead (see
    `is_tostr_bound_check`) before they're waved through.
  - `sorryAx`, reported as a known-incomplete proof (see KNOWN_INCOMPLETE below)
    rather than a failure
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
    "MercVerified.Refinement.Proofs.strong_bisim_sigref_correct",
    "MercVerified.Refinement.Proofs.strong_bisim_signature_spec",
    "MercVerified.Refinement.Proofs.strong_bisim_sigref_same_block_iff_bisimilar",
    "traceRefines_iff_not_reachable_trWitness",
    "stableFailuresRefines_iff_not_reachable_sfWitness",
    "failuresDivergencesRefines_iff_not_reachable_fdWitness",
    "foundWitness_iff_exists_witness",
    "AlgRun.terminates",
    "foundWitness_iff_exists_witness_finite",
    "traceRefines_iff_not_foundWitness",
    "stableFailuresRefines_iff_not_foundWitness",
    "failuresDivergencesRefines_iff_not_foundWitness",
]

# Theorems allowed to depend on `sorryAx` without failing the check (open,
# tracked contracts - see their module doc comments).
KNOWN_INCOMPLETE : set[str] = set()

IMPORTS = [
    "Signatures.Proofs.Signature_Proofs",
    "Signatures.Proofs.BranchingBisimilarity_Transitivity_Proofs",
    "Signatures.Proofs.InductiveSignatures_Proofs",
    "MercVerified.Refinement.Proofs.Refinement_Proofs",
    "MercVerified.Refinement.Proofs.StrongSignature_Proofs",
    "Refinement.Proofs.Product_Proofs",
    "Refinement.Proofs.Algorithm_Proofs",
]

KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# `\s*` (not a literal space) because Aeneas line-wraps long declarations as
# `axiom\n  <name>` when `axiom <name>` would overflow its line-length limit -
# a literal space here silently drops every wrapped declaration.
AXIOM_DECL_RE = re.compile(r"^axiom\s*([A-Za-z0-9_.]+)?", re.MULTILINE)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)\s*$")
SECTION_RE = re.compile(r"^section(?:\s+\S+)?\s*$")
END_RE = re.compile(r"^end(?:\s+\S+)?\s*$")
PRINT_AXIOMS_RE = re.compile(
    r"^'(?P<name>[^']+)' "
    r"(?:does not depend on any axioms"
    r"|depends on axioms: \[(?P<axioms>[^\]]*)\])$",
    re.MULTILINE,
)
# `#print axioms` reports the `_native.decide.ax_N` axiom a `decide +native` in a
# *private* declaration as `_private`-mangled-away and `✝`-suffixed
# (`verified.foo._native.decide.ax_1✝`), so the suffix has to be tolerated here.
NATIVE_DECIDE_RE = re.compile(r"\._native\.decide\.ax_\d+(?:_\d+)*✝?$")
# Start of one `logInfo` record emitted by `native_decide_statements`, with or
# without the `path:line:col: info: ` prefix Lean may prepend.
NATIVE_DECIDE_DUMP_RE = re.compile(
    r"^(?:\S+:\d+:\d+: (?:info|warning|error): )?AXIOM\|", re.MULTILINE
)
# Lean's pretty-printer only varies on *where* it line-wraps this, never the
# tokens, so whitespace is collapsed before matching.
TOSTR_BOUND_CHECK_RE = re.compile(
    r'^axiom \S+ : decide \(".*"\.toByteArray\.size ≤ Aeneas\.Std\.U32\.max\) = true$'
)


def qualified_axiom_names(text: str) -> set[str]:
    """Fully-qualified names of every `axiom` declared at the top level of
    `text`, tracking `namespace`/`end` nesting (needed for the Aeneas Std
    library, which wraps its axioms in e.g. `namespace Aeneas.Std`; `#print
    axioms` reports the qualified name, so an unqualified scan would miss
    the approval). `section`s are tracked only to balance `end`s correctly -
    they don't contribute to a declaration's qualified name."""
    names: set[str] = set()
    stack: list[str | None] = []
    lines = text.split("\n")
    for i, line in enumerate(lines):
        if ns_m := NAMESPACE_RE.match(line):
            stack.append(ns_m.group(1))
            continue
        if SECTION_RE.match(line):
            stack.append(None)
            continue
        if END_RE.match(line):
            if stack:
                stack.pop()
            continue
        if ax_m := AXIOM_DECL_RE.match(line):
            name = ax_m.group(1)
            if name is None:
                # Name wrapped onto the next non-blank line.
                for j in range(i + 1, len(lines)):
                    if lines[j].strip():
                        name = lines[j].strip().split()[0]
                        break
            if name:
                prefix = ".".join(p for p in stack if p is not None)
                names.add(f"{prefix}.{name}" if prefix else name)
    return names


def boundary_axioms() -> set[str]:
    """Axioms already declared for the translated-code boundary: anything
    declared in MercVerified/Code/*External*.lean is pre-approved, as is
    anything declared in the Aeneas Lean backend's own Std library
    (3rd-party/aeneas/backends/lean/Aeneas/**/*.lean) - that's the translation
    framework's own trusted primitive layer, not this project's."""
    axioms: set[str] = set()
    paths = []
    paths += sorted((REPO_ROOT / "MercVerified" / "Code").glob("*External*.lean"))
    paths += sorted(
        (REPO_ROOT / "3rd-party" / "aeneas" / "backends" / "lean" / "Aeneas").rglob("*.lean")
    )
    
    for path in paths:
        if path.exists():
            axioms.update(qualified_axiom_names(path.read_text()))
    return axioms


def is_tostr_bound_check(statement: str) -> bool:
    """Whether a `#print <axiom>` statement is exactly the byte-length bound
    check `Aeneas.Std.toStr` discharges via `decide +native` for a string
    literal argument - the only shape `_native.decide.ax_N` axioms are
    expected to take in this project (verified by name, not just assumed)."""
    return bool(TOSTR_BOUND_CHECK_RE.match(" ".join(statement.split())))


def run_lean(lean_src: str) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(lean_src)
        tmp_path = Path(f.name)

    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
    finally:
        tmp_path.unlink(missing_ok=True)

    if result.stderr.strip():
        print(result.stderr, file=sys.stderr, end="")
    return result.stdout


def native_decide_statements() -> dict[str, str]:
    """Map every `_native.decide.ax_N` axiom's real (environment) name to its
    `#print`-shaped `axiom <name> : <statement>` line.

    Needed because `#print axioms` reports such an axiom in an abbreviated form
    (`verified.foo._native.decide.ax_1✝` for
    `_private.MercVerified.Code.Funs.0.verified.foo._native.decide.ax_1`) that is
    not parseable back as a Lean identifier, so `#print <name>` can't be used to
    recover its statement. Read the statements straight out of the environment
    instead and let the caller match the two spellings by suffix."""
    imports = "\n".join(f"import {i}" for i in IMPORTS)
    lean_src = f"""{imports}
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if ci matches .axiomInfo _ then
      if (n.toString).contains "_native.decide" then
        logInfo m!"AXIOM|{{n}}|{{ci.type}}"
"""
    stdout = run_lean(lean_src)

    starts = [m.start() for m in NATIVE_DECIDE_DUMP_RE.finditer(stdout)]
    statements: dict[str, str] = {}
    for i, start in enumerate(starts):
        end = starts[i + 1] if i + 1 < len(starts) else len(stdout)
        header, _, rest = stdout[start:end].partition("\n")
        fields = header.split("|", 2)
        if len(fields) != 3:
            continue
        statements[fields[1]] = " ".join(f"{fields[2]}\n{rest}".split())
    return statements


def approved_native_decide_axioms(candidates: set[str]) -> set[str]:
    """Of the `_native.decide.ax_N`-shaped `candidates`, the subset whose
    statement is actually the `toStr` bound check (see
    `is_tostr_bound_check`) - checked mechanically rather than approved by
    name alone, since their names are fresh per declaration."""
    if not candidates:
        return set()

    imports = "\n".join(f"import {i}" for i in IMPORTS)
    # A `✝`-suffixed name isn't a parseable Lean identifier, so it can't be
    # `#print`ed; those candidates go straight to the environment dump below.
    printable = sorted(n for n in candidates if not n.endswith("✝"))
    blocks: list[str] = []
    if printable:
        prints = "\n".join(f"#print {name}" for name in printable)
        stdout = run_lean(f"{imports}\n{prints}\n")

        # `lean` prints consecutive `#print` results back-to-back with no blank
        # line between them, so split right before each `axiom <name> :` header.
        blocks = re.split(r"(?=^axiom \S+ :)", stdout, flags=re.MULTILINE)

    approved: set[str] = set()
    for name in printable:
        prefix = f"axiom {name} :"
        for block in blocks:
            if block.startswith(prefix) and is_tostr_bound_check(block):
                approved.add(name)
                break

    # `#print` can only speak the un-abbreviated names, so any candidate still
    # unresolved is looked up in the environment dump.
    unresolved = candidates - approved
    if unresolved:
        statements = native_decide_statements()
        for name in unresolved:
            key = name[:-1] if name.endswith("✝") else name
            for real_name, statement in statements.items():
                if real_name.endswith(key) and is_tostr_bound_check(
                    f"axiom {real_name} : {statement}"
                ):
                    approved.add(name)
                    break
    return approved


def main() -> int:
    approved = KERNEL_AXIOMS | boundary_axioms()

    lean_src = "\n".join(f"import {i}" for i in IMPORTS)
    lean_src += "\n" + "\n".join(f"#print axioms {t}" for t in THEOREMS) + "\n"
    stdout = run_lean(lean_src)

    parsed = list(PRINT_AXIOMS_RE.finditer(stdout))

    # `_native.decide.ax_N` axioms get a fresh name per declaration, so they
    # can never be in `approved` by name; check any such names that would
    # otherwise fail against their actual statement before reporting.
    native_decide_candidates = {
        a.strip()
        for match in parsed
        if match.group("axioms")
        for a in match.group("axioms").split(",")
        if NATIVE_DECIDE_RE.search(a.strip())
    }
    approved |= approved_native_decide_axioms(native_decide_candidates)

    failed = False
    seen: set[str] = set()
    for match in parsed:
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
