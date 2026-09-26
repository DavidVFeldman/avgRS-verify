# How to verify this project

The claim to be checked: `AvgRS.zline_identity` in `RequestProject/ZLineProof.lean` is Conjecture 3.2
of `avgRS.tex` — for all `k ≥ 2`, all `N` and all `t`,

    ∑_{λ ⊢ N+1, λ_k ≤ k−1} w_t(λ) = (N+1)(N+1−t) ∑_{μ ⊢ N, μ_{k−1} ≤ k} w_t(μ),

with `contentWt p t = N!² w_t(λ)` — and that it is proved from Mathlib alone, with no `sorry` and no
`native_decide` on its import path.

## Automatic

Push to GitHub and run the `verify` workflow (Actions → verify → Run workflow). It does five things,
each visible in the log:

1. **Closure audit** — `scripts/audit_sorries.py` walks the import closure of `ZLineProof` and fails
   if any file in it contains `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`,
   `@[implemented_by]` or `extern`, after stripping comments; it also fails if the `Computations`
   library (which does use `native_decide`, for finite checks unrelated to the proof) is reachable.
2. **Toolchain** — `elan` at the pinned `lean-toolchain`.
3. **Mathlib cache**, then `lake build` on both library targets. The build needs the
   `--tstack=4000000` in `lakefile.toml`; three files in `ZLineAlg*` also disable the linters,
   which is recorded in those files.
4. **Axiom audit** — `lake env lean Audit.lean` prints `#print axioms` for eleven theorems,
   including `zline_identity`, `shift_identity`, `avgEntry_diag` and the soundness lemma of the
   reflection tactic. The step fails if `sorryAx`, `ofReduceBool` or `trustCompiler` appears.
5. Logs are uploaded as an artifact.

Expect a long build: two of the files in `ZLineAlg*` took about 14 and 25 minutes on the machine
that produced them, and the runner is slower. The 350-minute timeout is deliberate. If the job is
killed for memory, the file to watch is `ZLineAlgG11m.lean`; a larger runner is the remedy.

## By hand

    elan toolchain install $(cat lean-toolchain)
    lake exe cache get
    lake build
    lake env lean Audit.lean

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
- `Audit.lean` — the axiom audit; outside both library globs, so it is not part of the build.
- `attic/ZLineR8.lean` — a skeleton from an earlier commission, unused and still carrying `sorry`s;
  kept out of the way rather than deleted.
- `zline_*.py`, `scripts/` — the independent checkers, in plain Python with exact rationals.
