# avgRS — Lean formalization

Lean 4 proofs accompanying `avgRS.tex` (the average Robinson–Schensted tableau):

| statement | file | paper |
|---|---|---|
| `AvgRS.shift_identity` | `RequestProject/ShiftProof.lean` | Theorem 2.1 |
| `AvgRS.zline_identity` | `RequestProject/ZLineProof.lean` | Conjecture 3.2, all `k ≥ 2`, all `N`, all `t` |

Read `VERIFY.md` before trusting either: it says what a clean build does and does
not establish, and where the proof is unreadable by design.

## Running the check

    git remote add origin git@github.com:<you>/avgRS-verify.git
    git push -u origin main

The push starts the `verify` workflow (Actions → verify). It runs the import-closure
audit, a cold `lake build`, and `lake env lean Audit.lean`, and uploads both logs as
an artifact. Budget several hours: two files in `ZLineAlg*` took 14 and 25 minutes on
the machine that produced them, and the runner is slower. The workflow can also be
started by hand with **Run workflow**.

By hand, on a machine with `elan`:

    lake exe cache get
    lake build
    lake env lean Audit.lean

## Layout

- `RequestProject/` — the library; `Computations/` — finite `native_decide` checks,
  imported by nothing in `RequestProject`.
- `Audit.lean` — eleven `#print axioms` lines; outside both library globs.
- `scripts/audit_sorries.py` — the closure audit, plain Python 3.
- `avgRS.tex`, `zline_closed_system.md` — the paper and the research note.
- `zline_*.py` — independent checkers, exact rationals, no packages.
- `COMMISSION*.md`, `REPORT_BATCH*.md`, `AUDIT_batch*.md` — the record of the
  seven commissions, the runs' reports, and my audits of them.
- `attic/` — a superseded skeleton, still carrying `sorry`s, kept out of the build.

## Attribution

The Lean library was produced by [Aristotle](https://aristotle.harmonic.fun) over
seven commissioned runs. To cite Aristotle:

- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
