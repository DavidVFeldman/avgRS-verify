# How to verify this project

The claim to be checked: `AvgRS.zline_identity` in `RequestProject/ZLineProof.lean` is Conjecture 3.2
of `avgRS.tex` — for all `k ≥ 2`, all `N` and all `t`,

    ∑_{λ ⊢ N+1, λ_k ≤ k−1} w_t(λ) = (N+1)(N+1−t) ∑_{μ ⊢ N, μ_{k−1} ≤ k} w_t(μ),

with `contentWt p t = N!² w_t(λ)` — and that it is proved from Mathlib alone, with no `sorry` and no
`native_decide` on its import path.

## Automatic

Push to GitHub and run the `verify` workflow (Actions → verify → Run workflow).

1. **Closure audit** — `scripts/audit_sorries.py` walks the import closure of `ZLineProof` and fails
   if any file in it contains `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`,
   `@[implemented_by]` or `extern`, after stripping comments; it also fails if the `Computations`
   library (which does use `native_decide`, for finite checks unrelated to the proof) is reachable.
2. **Toolchain** — `elan` at the pinned `lean-toolchain` — then the **Mathlib cache**.
3. **The shift side** — `ShiftProof`, `AverageTableau`, `DiagonalArrivalAllN`, `ZLine` — then
   `lake env lean AuditShift.lean`, which prints `#print axioms` for `shift_identity`,
   `avgEntry_diag`, `zline_identity_two`, `content0_all`, `giambelli_formula` and
   `giambelli_content`. None of the four large `ZLineAlg*` modules is in the import closure of any of
   those, so this record is produced whether or not the z-line algebra builds.
4. **The z-line algebra, one large module per step**: `ZLineAlgG01m`, `ZLineAlgFin`, `ZLineAlgBig`,
   `ZLineAlgG11m`, then `ZLineProof`, then everything else. The four have disjoint import closures
   and are reached only through `ZLineAlgMain`, so a single `lake build -j4` elaborates all four at
   once; one per step removes that peak, and names the module if one fails. Each step reports wall
   time and peak resident memory, and on failure prints the tail of its log, the lines Lean marked
   as errors, any OOM-killer message, and what the exit code means.
5. **Axiom audit** — `lake env lean Audit.lean`, the same for eleven theorems, `zline_identity` and
   the soundness lemma of the reflection tactic among them. Both audit steps fail if `sorryAx`,
   `ofReduceBool` or `trustCompiler` appears.
6. All logs (`build-*.log`, `mem-*.txt`, both `axioms*.log`) are uploaded as an artifact.

Before any of that the job reclaims disk and puts 24 GiB of swap on the runner's temporary disk.
Run #1 died at module 8060 of 8093 with exit 143 — SIGTERM, the host gone, which is what a hosted
runner reports when it is reclaimed after memory exhaustion rather than 137. Swap makes an
over-large elaboration slow instead of fatal. Each stage prints a memory heartbeat to the step log
every 30 seconds, not only to `mem-*.txt`, because when the host dies the artifact upload does not
run and the step log is the only surviving evidence.

The build needs the `--tstack=4000000` in `lakefile.toml`; three files in `ZLineAlg*` also disable
the linters, which is recorded in those files. Expect a long run: two of the `ZLineAlg*` files took
about 14 and 25 minutes on the machine that produced them, and the runner is slower, so serializing
them costs an hour or more. The 350-minute timeout is deliberate. If a step is killed for memory
even on its own, the file to watch is `ZLineAlgG11m.lean` and a larger runner is the remedy.

## By hand

    elan toolchain install $(cat lean-toolchain)
    lake exe cache get
    lake build RequestProject.ShiftProof RequestProject.AverageTableau \
               RequestProject.DiagonalArrivalAllN RequestProject.ZLine
    lake env lean AuditShift.lean
    for m in ZLineAlgG01m ZLineAlgFin ZLineAlgBig ZLineAlgG11m ZLineProof; do
      lake build "RequestProject.$m" || break
    done
    lake build
    lake env lean Audit.lean

A plain `lake build` also works, on a machine with memory to spare.

## What a clean run establishes, and what it does not

It establishes that Lean's kernel accepts the proof, on Mathlib's axioms only. It does not make the
proof readable: the algebraic core is three polynomial identities of some 10⁵ characters each,
checked by the reflection tactic in `RingRefl.lean`/`RingKernel.lean`. That tactic adds no trusted
code — its soundness lemma `eq_of_toPolyK_eq` is proved in Lean, and is included in the audit — but
it does not produce an argument a person can follow. Extracting one is the open problem now.

## Layout

- `RequestProject/` — the library. `ZLineProof.lean` holds the theorem; `ZLineAlg*.lean` the
  algebraic core; `ZLineTransfer*.lean` the passage from truncated matrices to their limits;
  `Formal/` the Plancherel-case machinery that Section 5 of the paper rests on.
- `Computations/` — finite checks by `native_decide`, imported by nothing in `RequestProject`.
- `Audit.lean`, `AuditShift.lean` — the axiom audits; outside both library globs, so neither is part
  of the build. `AuditShift.lean` covers what does not depend on the four large `ZLineAlg*` modules.
- `attic/ZLineR8.lean` — a skeleton from an earlier commission, unused and still carrying `sorry`s;
  kept out of the way rather than deleted.
- `zline_*.py`, `scripts/` — the independent checkers, in plain Python with exact rationals.
