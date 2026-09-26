# Static audit — Aristotle batch 5 (avgRS campaign, z-line operator layer)

Ground truth: `output-final_aristotle` (`RequestProject/ZLineRec.lean` 1095 lines, plus two new
files `ZLineGen.lean` 343 and `ZLineGenODE.lean` 209). Not built here; "builds" and the
`#print axioms` list are Aristotle's claims, to be confirmed by the cold build. Census, statement
comparison and independent numerical checks below are mine.

## 1. Census

- `sorry`: two. `zline_identity` (`ZLine.lean:153`, Conjecture 3.2, untouched as instructed) and the
  commented-out original C4 (`ZLineRec.lean:985`, inside a block comment, so not a live declaration).
  No other `sorry` in `RequestProject`.
- `native_decide`: only the two in `Computations`, unchanged and still unimported by
  `RequestProject`.
- No `axiom`, no `admit`.
- All 38 statements of my skeleton are present. Textual comparison of every statement against my
  file: 38/38 identical, character for character, apart from C4 (below). No hypothesis was added.

## 2. The one reported error is real, and it is mine

C4 (`P2_of_RZp`) was stated in my skeleton as an *exact* identity for the `m × m` truncations. It is
not: pairing C2 with `Mv` inherits C2's boundary defect. Aristotle reports this, proves the falsity
formally (`P2_of_RZp_false`, witness `m = 1`, `ω = 0`, `t = 2`), keeps my statement commented out
with the explanation, and proves the corrected `P2_of_RZp_trunc` with an error divisible by `X^m`.

Checked here independently (`c4test.py`): the defect's first nonzero coefficient is `r^{2m}` for
`m = 3, …, 8`, exactly as reported. The `m = 1, ω = 0, t = 2` witness is right by hand: `p = v`,
`A = 0`, so the left side is `0` and the right side is `−r² t P = 2r²`.

Why my checker missed it: it compares coefficients up to `r^{N−6}` with index range `n = N/2 + 2`,
so the first defect at `r^{2n} = r^{N+4}` is always out of range. The check is therefore sound for
the identities as statements about the infinite matrices — and C4 *is* true there, so the paper is
unaffected — but it is structurally blind to the exact/up-to-`X^m` distinction. Fixed: the script
now takes an index range and a `strict` flag and reports, per identity, whether it is exact for the
truncations or from which order the defect starts. Classification at `n = 6`:

| exact for the truncations | defect from |
|---|---|
| W1–W6, A1–A4, B1–B9 (20 items) | A5 `r^13`, C1 `r^14`, C2 `r^6`, C3 `r^6`, C4 `r^12` |

which matches the five statements Aristotle carries error terms on, and only those.

## 3. New mathematics in the delivery

Two items go beyond what the commission asked for, and both check out here (`commtest.py`, exact
rational arithmetic, all indices, no residual at any order):

1. **Closed forms for the twisted commutators.** I supplied only the structural fact that
   `[D₀Xᵀ, C₁]` has rank at most four and asked for the scalar bookkeeping. Aristotle instead
   computed the commutator itself: up to `X^m`,

       [D₀Xᵀ, C₁] = r(1−r²)⟨Λv,v⟩ v⊗Mv + r² v⊗M(A−1)c + r² Av⊗Mc − c⊗MAv − (A+1)c⊗Mv,
       [D₂Xᵀ, Ĉ₁] = r(1−r²)⟨Mv,v⟩ v⊗Λv + r² v⊗Λ(A+3)ĉ + r² Av⊗Λĉ − ĉ⊗ΛAv − (A+1)ĉ⊗Λv,

   with `c = HΛv`, `ĉ = HMv`. Both verified exactly here.

2. **The reason they hold**, recorded in the report as `M[Y,C₁] = −[X,C₁]ᵀM`. Stated
   conceptually: with the pairing `⟨f,g⟩_M = ⟨Mf,g⟩`, the identity `XᵀM = M D₀Xᵀ` (W2) says exactly
   that **`D₀Xᵀ` is the `M`-adjoint of `X`**, and `C₁` is `M`-self-adjoint (B3's ingredient), so

       [D₀Xᵀ, C₁] = [X*, C₁] = −[X, C₁]*,

   and the commutator formula is A5 read backwards. Likewise `D₂Xᵀ` is the `Λ`-adjoint of `X` and
   `Ĉ₁` is `Λ`-self-adjoint. Verified here: `⟨Mf, Xg⟩ = ⟨M D₀Xᵀf, g⟩` and the `Λ` analogue hold
   exactly for the truncations, as does `M`-self-adjointness of `C₁`.

   Consequence for the write-up: items A3, A3h and the weights `N`, `M⁻` (W4, W6) were scaffolding
   of mine and are not needed for C2 and C3. The derivation of both recurrences is A5 plus
   adjointness. This shortens the eventual Section 3 substantially.

Also delivered beyond the commission: the `P̂₂` analogue of C4 (`Ph2_of_RZph_trunc`), and the
generic layer — `ZLineGen.lean` and `ZLineGenODE.lean` prove B1–B9 once for two arbitrary diagonal
weights `l, μ`, so that the hatted objects are the unhatted ones with `Λ` and `M` exchanged and each
hatted statement is a one-line instance. The skeleton's definitions are definitionally equal to the
generic ones (visible in proofs such as `HMum_mul_Gzz := Gg_mul_HD …`). This is a better
architecture than the duplicated one I wrote.

B10 was correctly left alone, with no `sorry` added, as the commission asked.

## 4. What the campaign now establishes on the z-line (subject to the cold build)

Proved: the bridge from `H_z H_{z'}ᵀ` to `C₁ = HΛHM` for every `z`, with no genericity argument
(Aristotle used `det(1+AB) = det(1+BA)` twice instead of conjugating, so invertibility of
`diag(α)` never arises — cleaner than the proof I supplied); the weight and operator identities;
the two commutators; the resolvent identities and the four differential equations; the first
integral `Q₁ + Q̂₁ + Q = rPP̂ + ωrQ²`; the three recurrences (RXp), (RZp), (RZp̂); and the `P₂`,
`P̂₂` consequences.

Open, and mine: the remaining first integrals (R6, R7), the closed forms for the resolvent entries,
and Conjecture 3.2 itself.

## 5. For the cold build

`lake build`, then `#print axioms` on the 40-odd names listed in `REPORT_BATCH5.md` §`#print axioms`,
plus `P2_of_RZp_false`. Expected: `propext`, `Classical.choice`, `Quot.sound`.

## 6. Protocol notes

Report-rather-than-repair worked as intended: a false statement of mine came back as a proof of its
falsity, a corrected statement, and the original preserved in a comment. Nothing was silently
weakened, and no hypotheses were added. The one thing to carry forward: for any future item, say in
the commission whether it is expected to be exact for the truncations or to hold modulo `X^m`, and
run the `strict` pass of the checker before writing the statement.
