#!/usr/bin/env python3
"""Delegate one `sorry` in a `Proofs/` file to an opencode instance, then check the result.

    scripts/delegate_proof.py [-m MODEL] [-t SECONDS] FILE DECL [HINT ...]

Runs the opencode agent `prover` (`.opencode/agents/prover.md`) on the declaration `DECL` of
`FILE`, then checks what it did without trusting its own report:

* the declaration is still there and the file has fewer `sorry`s than before;
* no added line contains `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, ...;
* only `sorry` lines were removed (anything else may be a changed statement);
* `lake build <module>` succeeds.

Verdict (last line of output, and the exit code):

    PROVED  (0)  all checks passed; the proof is in FILE
    REVIEW  (2)  it builds, but lines other than the `sorry` changed: read the diff
    FAILED  (1)  FILE was restored to its state before the run

Everything is logged under `.lake/delegate/<time>-<decl>/` (the agent's transcript, the file
before and after, the diff, the build log). See the `delegate-proofs` skill.
"""

import argparse
import difflib
import fcntl
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / ".lake" / "delegate"

# Tokens a delegated proof may not introduce.
BANNED = re.compile(
    r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|reduceBool|ofReduceBool)\b"
    r"|set_option\s+debug\."
)
# What may precede `sorry` on a removed line without it being part of a statement.
PROOF_PREFIX = re.compile(r"^(\s|by\b|:=|·|\.|<;>|\||=>|exact\b|;|\(|\))*$")


def sorry_count(text: str) -> int:
    return len(re.findall(r"\bsorry\b", text))


def has_decl(text: str, decl: str) -> bool:
    return re.search(r"\b(theorem|lemma|def|instance|example)\s+" + re.escape(decl) + r"(?![\w.'])", text) is not None


def suspicious_removals(before: list[str], after: list[str]) -> list[str]:
    """Removed lines that are not just a `sorry` proof placeholder."""
    removed, added = [], []
    for line in difflib.ndiff(before, after):
        if line.startswith("- "):
            removed.append(line[2:])
        elif line.startswith("+ "):
            added.append(line[2:])
    bad = []
    for line in removed:
        if not line.strip():
            continue
        if "sorry" not in line:
            bad.append(line)
            continue
        prefix = line.split("sorry", 1)[0].rstrip()
        if PROOF_PREFIX.match(prefix):
            continue
        # `theorem foo : P := by sorry` on one line: the part before `sorry` must survive.
        if not any(a.startswith(prefix) for a in added):
            bad.append(line)
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file", help="Lean file under a Proofs/ directory, relative to the repository root")
    ap.add_argument("decl", help="name of the declaration whose `sorry` is to be proved")
    ap.add_argument("hint", nargs="*", help="optional hint for the prover (proof idea, lemmas to use)")
    ap.add_argument("-m", "--model", default=os.environ.get("MERC_PROVER_MODEL"),
                    help="opencode model, provider/model (default: $MERC_PROVER_MODEL, else opencode's default)")
    ap.add_argument("-t", "--timeout", type=int, default=int(os.environ.get("MERC_PROVER_TIMEOUT", "1200")),
                    help="seconds before the opencode run is killed (default 1200)")
    args = ap.parse_args()

    path = (ROOT / args.file).resolve()
    try:
        rel = path.relative_to(ROOT)
    except ValueError:
        sys.exit(f"error: {args.file} is outside the repository")
    if "Proofs" not in rel.parts or path.suffix != ".lean" or not path.is_file():
        sys.exit(f"error: {rel} is not an existing .lean file under a Proofs/ directory")
    before = path.read_text()
    if not has_decl(before, args.decl):
        sys.exit(f"error: no declaration `{args.decl}` in {rel}")
    if sorry_count(before) == 0:
        sys.exit(f"error: {rel} contains no `sorry`")

    WORK.mkdir(parents=True, exist_ok=True)
    # One delegate per file: two instances editing the same file overwrite each other.
    lock = open(WORK / (str(rel).replace("/", "__") + ".lock"), "w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        sys.exit(f"error: another delegate is already working on {rel}")

    run = WORK / f"{time.strftime('%Y%m%d-%H%M%S')}-{re.sub(r'[^\w.]', '_', args.decl)}"
    run.mkdir()
    (run / "before.lean").write_text(before)

    prompt = (
        f"Prove the declaration `{args.decl}` in `{rel}`: replace its `sorry` with a proof. "
        "Change nothing else in the file except adding private helper lemmas directly above it."
    )
    if args.hint:
        prompt += "\n\nHint from the requester: " + " ".join(args.hint)
    cmd = ["opencode", "run", "--agent", "prover", "--auto", "--archived", "--title", f"prove {args.decl}"]
    if args.model:
        cmd += ["--model", args.model]
    cmd.append(prompt)

    print(f"delegating {args.decl} ({rel}) to opencode"
          f"{' model ' + args.model if args.model else ''}; log: {run.relative_to(ROOT)}/", flush=True)
    timed_out = False
    with open(run / "opencode.log", "w") as log:
        try:
            subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
        except FileNotFoundError:
            sys.exit("error: `opencode` is not on PATH")

    after = path.read_text()
    (run / "after.lean").write_text(after)
    diff = "".join(difflib.unified_diff(
        before.splitlines(keepends=True), after.splitlines(keepends=True), f"a/{rel}", f"b/{rel}"))
    (run / "proof.diff").write_text(diff)

    transcript = (run / "opencode.log").read_text(errors="replace")
    claims = re.findall(r"RESULT: (?:PROVED|FAILED).*", transcript)
    tail = transcript.strip().splitlines()[-12:]

    problems: list[str] = []   # FAILED
    review: list[str] = []     # REVIEW
    if timed_out:
        problems.append(f"opencode timed out after {args.timeout}s")
    if after == before:
        problems.append("the file was not changed")
    else:
        if not has_decl(after, args.decl):
            problems.append(f"declaration `{args.decl}` no longer exists")
        if sorry_count(after) >= sorry_count(before):
            problems.append(f"`sorry` count did not go down ({sorry_count(before)} -> {sorry_count(after)})")
        added = [l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++")]
        banned = [l.strip() for l in added if BANNED.search(l)]
        if banned:
            problems.append("added lines use a banned construct: " + " | ".join(banned[:5]))
        removed = suspicious_removals(before.splitlines(), after.splitlines())
        if removed:
            review.append("lines other than the `sorry` were removed or rewritten:\n"
                          + "\n".join("      - " + l.strip() for l in removed[:10]))

    if not problems:
        module = ".".join(rel.with_suffix("").parts)
        # Serialise builds: concurrent `lake build`s write the same .olean files.
        with open(WORK / "build.lock", "w") as build_lock:
            fcntl.flock(build_lock, fcntl.LOCK_EX)
            build = subprocess.run(["lake", "build", module], cwd=ROOT, capture_output=True, text=True)
        (run / "build.log").write_text(build.stdout + build.stderr)
        if build.returncode != 0:
            errors = [l for l in (build.stdout + build.stderr).splitlines() if "error" in l][:8]
            problems.append(f"`lake build {module}` failed:\n" + "\n".join("      " + l for l in errors))

    print()
    if claims:
        print("agent said:", claims[-1])
    if problems:
        path.write_text(before)  # keep the tree compiling; the attempt is in after.lean
        print("agent's last lines:")
        print("\n".join("    " + l for l in tail))
        for p in problems:
            print("  ✗", p)
        print(f"{rel} restored; the attempt is in {run.relative_to(ROOT)}/after.lean")
        print("FAILED")
        return 1
    print(diff)
    if review:
        for r in review:
            print("  ?", r)
        print("It builds, but check in the diff above that no statement was changed.")
        print("REVIEW")
        return 2
    remaining = sorry_count(after)
    print(f"builds; {remaining} `sorry` left in {rel}")
    print("PROVED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
