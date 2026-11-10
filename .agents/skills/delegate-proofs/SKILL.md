---
name: delegate-proofs
description: How to split proving work across Claude subagents (`lean-prover`) and opencode instances (`scripts/delegate_proof.py`, agent `prover`). Use when there are several `sorry`s to close, when a proof breaks into independent helper lemmas, or when the user asks to delegate or parallelise proofs.
---

## The two kinds of workers

| Worker | What it is | Use it for |
|---|---|---|
| `lean-prover` | Claude Code subagent (`.claude/agents/lean-prover.md`), lean-lsp MCP, may delegate further | Proofs that need a plan: invariants, inductions over `while`/`for` loops, Aeneas `WP` loop specs, anything spanning several helper lemmas |
| opencode `prover` | `scripts/delegate_proof.py FILE DECL [HINT]` runs `opencode run --agent prover` (`.opencode/agents/prover.md`) with the lean-lsp MCP from `opencode.json` | One routine lemma: list/`Nat` arithmetic, unfold-and-`simp`, case splits, goals `grind`/`aesop` nearly close |

The opencode agent can only edit files under `Proofs/` and may only run `lake build`,
`lake env lean`, `grep`/`rg` and read-only `git`. The script does not trust its report. It checks
that the declaration still exists, that the number of `sorry`s went down, that no added line uses
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `set_option debug.*`,
that only `sorry` lines were removed, and that `lake build <module>` succeeds. The last line of
its output, and its exit code, is the verdict:

- `PROVED` (0): all checks passed; the proof is in the file.
- `REVIEW` (2): it builds, but lines other than a `sorry` were removed or rewritten. Read the
  printed diff: a changed statement is a contract change and must be reverted.
- `FAILED` (1): the file is restored. The agent's explanation (remaining goal, suspected missing
  hypothesis, counterexample) is printed and kept in the log.

Every run is logged under `.lake/delegate/<time>-<decl>/` (`opencode.log`, `before.lean`,
`after.lean`, `proof.diff`, `build.log`).

Options: `-m provider/model` (or `MERC_PROVER_MODEL`) picks the opencode model; without it
opencode uses its own default. Check `opencode models` for what is available. `-t SECONDS` (or
`MERC_PROVER_TIMEOUT`, default 1200) bounds a run.

## Workflow

1. **Inventory.** List the open goals: `grep -rn --include=*.lean '\bsorry\b' MercLib MercVerified`
   (the `sorry`s in `Challenges/` are intended). For each, note the file and the enclosing
   declaration.
2. **Triage.** `lean_goal` on each `sorry` and one `lean_multi_attempt` with
   `["grind", "simp_all", "omega", "aesop"]`. A goal that closes is done; just apply it. A goal
   that automation nearly closes, or that is a small self-contained fact, goes to opencode. The
   rest goes to `lean-prover`, grouped by file.
3. **Fan out.**
   - Opencode: one `scripts/delegate_proof.py` per lemma, run with `run_in_background`. Runs on
     *different* files may go in parallel (the script refuses a second run on the same file, and
     serialises the `lake build`s). Lemmas in the same file go one after another.
   - `lean-prover`: one Agent call per file or group of related files. Name the declarations, and
     give the plan if you have one. Do not give two agents the same file, and do not delegate to
     opencode a file a `lean-prover` agent is editing.
   - A large proof: first state its helper lemmas with `sorry` yourself and check that the main
     proof compiles from them, then hand the helpers out. The statements are where the thinking
     is; proving them is the part that parallelises.
4. **Collect.** For each `FAILED`, read the explanation. If it says the statement is false or
   lacks a hypothesis, fix the statement (it is your helper lemma, not a spec) or rethink the
   plan, rather than retrying the same thing. Retry with another model or a hint at most once;
   then give the lemma to `lean-prover` or prove it yourself.
5. **Check once at the end.** `lake build`, then `lake comparator --config comparator.json` and
   `lake comparator --config comparator_MercVerified.json`, then
   `lake env lean --run scripts/CheckExports.lean` (see the `build` skill). Helpers added by
   workers are `private`, so `EXPORTS.md` should not change; if it does, a worker exported
   something by mistake.

## Rules

- Workers only ever edit `Proofs/` files. A change to a spec file, `Challenges/`, a comparator
  config or `EXPORTS.md` is the main session's decision and needs to be reported to the user.
- Report delegated results as what the checks established (`PROVED` after `lake build`), not what
  a worker said. A worker's `RESULT: PROVED` without the script's `PROVED` means nothing.
- Leave `.lake/delegate/` logs in place until the work is reported; they are not committed
  (`.lake/` is ignored).
