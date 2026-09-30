#!/usr/bin/env python3
"""Rewrite absolute repo paths in Aeneas-generated `Source: '...'` comments
to be relative to the repo root.

Aeneas embeds the absolute path it was invoked from in `Source:` doc comments
(e.g. `Source: '/home/alice/merc-verified/3rd-party/merc/crates/.../foo.rs'`).
That path is machine- and checkout-specific, so regenerating on a different
machine (or a different clone path) produces a spurious diff in every touched
file. This rewrites any such path that falls under the repo root to be
relative (e.g. `3rd-party/merc/crates/.../foo.rs`), leaving paths outside the
repo (e.g. `/rustc/library/...`, `/cargo/registry/...`) untouched.

Usage:
    scripts/strip_source_paths.py [FILE ...]

With no arguments, rewrites every `*.lean` file under `MercVerified/Code/`.
"""

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Matches the path inside `Source: '<path>', lines ...` comments that Aeneas
# emits above translated declarations.
SOURCE_RE = re.compile(r"(Source: ')([^']+)(')")


def strip_prefix(path: str) -> str:
    """Rewrite `path` to be relative to REPO_ROOT if it falls under it,
    otherwise leave it unchanged (e.g. `/rustc/...`, `/cargo/...` paths that
    don't refer to this checkout)."""
    resolved = Path(path)
    try:
        return str(resolved.relative_to(REPO_ROOT))
    except ValueError:
        return path


def rewrite(text: str) -> str:
    return SOURCE_RE.sub(lambda m: m.group(1) + strip_prefix(m.group(2)) + m.group(3), text)


def main() -> int:
    paths = [Path(p) for p in sys.argv[1:]] or sorted((REPO_ROOT / "MercVerified" / "Code").glob("*.lean"))

    for path in paths:
        original = path.read_text()
        updated = rewrite(original)
        if updated != original:
            path.write_text(updated)
            print(f"stripped source paths in {path.relative_to(REPO_ROOT)}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
