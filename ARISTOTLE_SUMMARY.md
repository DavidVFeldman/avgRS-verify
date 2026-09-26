# Summary of changes for run c06043aa-2634-4ec1-a2bd-63a1fc9dd3f0
Conjecture 3.2 of `avgRS.tex` (the shift identity on the line z+z'=−2) is now formally proved in Lean. The paper leaves it as an open conjecture. The theorem is `AvgRS.zline_identity` in `RequestProject/ZLineProof.lean`: for all k ≥ 2, all N and all t, the sum of w_t(λ) over partitions λ of N+1 with (k,k) ∉ λ equals (N+1)(N+1−t) times the sum of w_t(μ) over partitions μ of N with (k−1,k+1) ∉ μ. The statement has not changed from the earlier sessions. `#print axioms AvgRS.zline_identity` reports only `propext`, `Classical.choice` and `Quot.sound`, so there is no `native_decide` and no custom axiom. The full `lake build` (default targets `RequestProject` and `Computations`) finishes without errors. The only `sorry` in the project is inside a block that was already commented out (`ZLineRec.lean`, an old statement that was shown to be false and replaced by a corrected version).

What was done in this session:
- **New tactic for large polynomial identities.** Earlier, several huge polynomial identities in `RequestProject/ZLineAlg*.lean` would not build with `ring`. They are now checked by `ring_refl` (`RequestProject/RingRefl.lean`), used as `linear_combination (norm := ring_refl) …`. It rewrites each side into a symbolic polynomial and normalises both using `RequestProject/RingKernel.lean`. The equality is then checked by Lean's kernel through the lemma `AvgRS.RingKernel.eq_of_toPolyK_eq`, so it adds no trusted code.
- **Faster elaboration.** On the long lines of the slowest files I added explicit type annotations: `X` becomes `(X : ℚ⟦X⟧)` and `^N` becomes `^(N:ℕ)`. The statements themselves are unchanged. With this, `ZLineAlgBig` now builds in about 14 minutes; it was stopped unfinished after about 95 minutes before. `ZLineAlgG11m` builds in about 25 minutes.
- **One proof fix.** A coefficient calculation in `zG11` (`ZLineAlgG11.lean`) failed because `simp` does not simplify `constantCoeff 2`. I fixed it by adding explicit `map_ofNat` / `coeff_C` steps.

In the Properties table, `zline-conjecture` (`AvgRS.zline_identity`) and `zline-alg-core` (`AvgRS.zline_alg`) are now marked proved, with updated comments. All work is committed.

# Summary of changes for run e76e9081-9013-447b-b3fc-3008a59eb09b
Conjecture 3.2 (`zline_identity`) is **not yet verified**. Its proof is now assembled from end to end in Lean, but two of the files it depends on have never built successfully.

**What I found.** An earlier session had left work that isn't described in `ARISTOTLE_SUMMARY.md`:
- a proof of the algebraic core `zline_alg` in `RequestProject/ZLineAlg*.lean`. Its statement: any scalar data satisfying the closed system in `zline_closed_system.md` (differential equations, recurrences, first integral R2, the two determinant formulas, initial values) gives identity (B4).
- `RequestProject/ZLineTransfer*.lean`, which builds that scalar data (`zdata`) as limits of the truncated matrices.

What was missing was the step joining these to the conjecture.

**What I added.** A new file, `RequestProject/ZLineProof.lean`:
- `zline_formal`: identity (B4) for the determinants `det(1 + ω H_z H_{z'}ᵀ)` and `det(1 + Ω H_z H_{z'}ᵀ)`, when `(z+1)² ≠ 0, 1` and `ω ≠ 0, 1`. It uses the earlier result `det_one_add_diag_Czz` to pass from `H_z H_{z'}ᵀ` to `HΛHM`, then applies `zline_alg` to `zdata`.
- `zline_identity`, your statement word for word. It combines `zline_formal` with `zline_identity_of_formal` at `t = (n+2)²` for every natural number `n`. Both sides are polynomials in `t`, so the identity then holds for all `t`.
- The theorem had to move out of `ZLine.lean`, because every file it depends on imports `ZLine.lean`. The original statement is still there as a comment saying where it went.
- I type-checked these steps separately against the existing files, with `zline_alg` assumed.

**Why it isn't verified.** `zline_alg` rests on three lemmas, each proved by one enormous `linear_combination` step (about 70, 95 and 155 thousand characters):
- `ZLineAlgG01m.lean` now builds, after about 18 minutes. Two fixes were needed to get there: I added `set_option linter.all false` to it (and to the other two), because the linters ran out of stack on these proofs; and I added `--tstack` to `lakefile.toml` as a build option that doesn't force a rebuild, because `ring` itself also ran out of stack.
- `ZLineAlgG11m.lean` ran out of memory after about 2.5 hours and was killed.
- I stopped the `ZLineAlgBig.lean` build after about 2.3 hours so that it wouldn't use up the memory `ZLineAlgG11m.lean` needed.
- `ZLineAlgG01.lean` had a separate error, which I fixed (a missing `coeff_X_pow`). It now builds.

So at the moment the `RequestProject` library does not fully build, and `zline_identity` must not be treated as proved. The Properties table shows it as in progress, with this explanation.

**Other changes.** I deleted the unused files `ScratchG.lean`, `ScratchT.lean` and `ScratchLow.lean`, which didn't compile and contained `sorry`.

**Next step.** Restate the three large identities over an arbitrary commutative ring with a derivation instead of power series, which should be much cheaper to check. The script that generates these versions is in `scripts/zline_generic_gen.py`. I'll then time the `ZLineAlgG01m.lean` version against the current 18 minutes and, if it is faster, apply the same approach to the other two.

# Summary of changes for run 58e6e892-79d7-4d60-bdfa-6eee822741d3
Batch 5 is done: every item in the skeleton is proved except C4, which is false exactly as stated. I've proved it false in Lean and proved a corrected version. The whole `RequestProject` library builds. The only `sorry` left is `zline_identity` (Conjecture 3.2), which I didn't touch as you asked. The full write-up is in `REPORT_BATCH5.md`.

**Files.** I moved your skeleton to `RequestProject/ZLineRec.lean` and filled in all its proofs. The only change to it besides proofs is one extra import. Two new files hold the generic part: `RequestProject/ZLineGen.lean` and `RequestProject/ZLineGenODE.lean`. Swapping `Λ` and `M` turns each unhatted object into its hatted version, so B1–B9 are proved once for two arbitrary diagonal weights and used twice. `ZLineRec.lean` is now about 1100 lines; I didn't split it, so every statement stays where you put it.

**What's proved:**
- **A0** (`det_one_add_diag_Czz`): holds for every `z`, with no invertibility or polynomial-in-`z` argument. It writes `H_z = diag(α) H diag(β)` and applies `det(1+AB) = det(1+BA)` twice.
- **W1–W6, A1–A5, B1–B9**: all proved. A5 holds up to `X^m`; B9 holds exactly.
- **C1, C3**: proved up to `X^m`.
- **C2**: proved up to `X^m`, including the cancellation you left open. I computed the commutator itself (`Y_comm_Czz`), up to `X^m`:
  `[D₀Xᵀ, C₁] = r(1−r²)⟨Λv,v⟩ v⊗Mv + r² v⊗M(A−1)c + r² Av⊗Mc − c⊗MAv − (A+1)c⊗Mv`.
  - The four constants `⟨N·,·⟩` cancel in pairs.
  - The derivation through A3 divides by `1 − t`, so `t = 1` is handled separately; there `M = 0` and both sides vanish.
  - The C3 counterpart (`Yh_comm_Chzz`) is the same formula with `(A+3)` in place of `(A−1)` and needs no division.

**C4 is false as stated.** The exact equality `P2_of_RZp` fails for the truncations.
- `P2_of_RZp_false` proves this in Lean with `m = 1`, `ω = 0`, `t = 2`: the left side is `0` and the right side is `2r²`.
- The reason is that pairing C2 with `Mv` leaves the term `r⟨Mv, err⟩`, which doesn't vanish.
- An informal check with a modified copy of your script, not part of the Lean work, found the defect first appears at `r^{2m}`. Your script compares coefficients only up to `r^20` with `n = 15`, so it doesn't reach that order.
- I kept the original statement in the file, commented out with this explanation.
- The corrected version `P2_of_RZp_trunc` is your identity plus an error term divisible by `X^m`, and it is proved.

**Optional items:**
- The `P̂₂` analogue of C4 is proved up to `X^m` (`Ph2_of_RZph_trunc`), by pairing C3 with `Λv`.
- B10 wasn't attempted and, as you asked, isn't in the file.
- The `xlim` layer wasn't done.

**Axioms:** `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for all 42 new top-level results; the list is in the report. There is no `native_decide` in `RequestProject`, and the `Computations` library is unchanged and not imported by it.

The Properties table now includes these results, with the skeleton's exact C4 marked as negated.

# Summary of changes for run b13c10c9-1712-464f-84d7-99bca6a6f994
I proved B3 and B4, verified (H1_z)–(H4_z) in Lean, proved the `k = 2` case on the line (`zline_identity_two`, Theorem 3.6), and did all the housekeeping. Both libraries build (`RequestProject` and the new `Computations`). The only `sorry` left is `zline_identity`, Conjecture 3.2 for general `k`, which is still open for `k ≥ 3`. The details, including the full `#print axioms` list, are in `REPORT_BATCH4.md`.

**B3 and B4** (`RequestProject/ZLineDet.lean`, moved here from the upload):
- **B3:** `coeff_det_Cz_eq_sum_partitions`, `G0m_succ`, `G2m_succ` and `zlineGF` are proved. The proof is Cauchy–Binet with the two matrices `H_z` and `H_{z'}`, followed by the weighted Giambelli formula B2 and the Frobenius-coordinate bijection.
- **B4:** `zline_identity_of_formal` is proved.
- **One statement change:** the skeleton's `(X / 2)` doesn't typecheck in `ℚ⟦X⟧` (you can't divide a power series by a natural number there), so it is written `C (1/2) * X`. No other statement was changed.

**B5, `k ≥ 3`:**
- (H1_z)–(H4_z) are proved entrywise for arbitrary rational `z` in the new file `RequestProject/ZLineHook.lean` (`deriv_hzE`, `X_mul_deriv_uz`, `X_mul_deriv_utz`, `hzE_H2`, `hzE_H3`, `hzE_H4`). The `z'` versions are the same lemmas at `-z - 2`.
- No closed system was found. The only structural fact I recorded is that `d/dX (H_z H_{z'}ᵀ)` has rank two. I did not derive the analogues of Lemmas 5.10–5.14, so `zline_identity` keeps its `sorry`.

**`k = 2`** (new file `RequestProject/ZLineTwo.lean`, used by `zline_identity_two` in `ZLine.lean`): the proof takes a shorter route than the paper's.
- Hooks and two-column shapes are enumerated explicitly.
- After multiplying by `t`, the identity becomes `∑_{i+j=n} j²(j²−t) y_i y_j = n(n−t) ∑_{i+j=n}(j²−ij) y_i y_j`, where `y_n = ∏_{i<n}(i²−t)/n!²`.
- That is the `X^n` coefficient of `Y(ϑ⁴−tϑ²)Y = ϑ(ϑ−t)(Yϑ²Y−(ϑY)²)`, with `ϑ = X d/dX`. This follows from the hypergeometric equation `(1−X)ϑ²Y = −tXY` alone, so Gessel's determinant, Euler's transformation and the contiguous relations aren't needed.
- The case `t = 0` follows because both sides are polynomials in `t`.

**Axioms:** every new theorem above, and `shift_identity`, `content0_all` and `avgEntry_diag`, uses only `propext`, `Classical.choice` and `Quot.sound`.

**Housekeeping:**
- **Citations:** docstrings now follow the new tex's numbering, with the LaTeX label given alongside. I counted the theorem environments in the tex myself, and four numbers differ from your list: `lem:Gids`, `lem:rec` and `lem:odes` are 5.9, 5.10 and 5.11, and `prop:closed` is 1.10. The labels are there so you can check them against the PDF.
- **`HookMatrix.lean`:** deleted.
- **Tex copies:** only `avgRS.tex` remains, now holding the newer upload. The duplicate root copies of `ZLine.lean` and `ZLineDet.lean` are removed.
- **Finite checks:** `content0_of_le` and `content0_check_fast` are deleted. `diagArrival_values` couldn't be re-proved with kernel `decide`, because the evaluator's recursion doesn't reduce. So I moved it, with `FastCount.lean` and `Computations.lean`, into a separate library `Computations/` that no `RequestProject` file imports. That keeps `native_decide` off the import path of every theorem of the paper.

The Properties table is updated to match.

# Summary of changes for run 0e7848ae-333a-4e76-a170-9dd399ac85a6
I added your three files to the project and proved everything in them except the two `z`-line identities at the end of `ZLine.lean`. One is the paper's open Conjecture 3.2; the other is its `k = 2` case, which the file marks optional. The whole project builds. The only remaining `sorry`s are those two statements, and every other new result uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Setup changes.** The files import `RequestProject.*` modules, so I moved them into `RequestProject/`: `RequestProject/UpRule.lean`, `RequestProject/DiagonalArrivalAllN.lean` and `RequestProject/ZLine.lean`. In `ZLine.lean`, `hookF` did not resolve, so I changed `open Finset` to `open Finset Formal`. None of your statements were changed.

**`UpRule.lean` (item A1), all proved.**
- The helper lemmas `addBox_zero`, `addBox_sum` and `addBox_pos`.
- `DU_sub_UD`: the identity `DU − UD = I` on Young's lattice, for an arbitrary function `F` of partitions.
- `syt_up`: `∑_{λ ⋗ ν} f_λ = (|ν|+1) f_ν`, proved by strong induction from `DU_sub_UD`.

**`DiagonalArrivalAllN.lean` (items A2′, A2, A3), all proved.**
- `sum_numSYT_sq`: `∑_{λ ⊢ N} f_λ² = N!`.
- `arrival_diag_box`, `boxAbsentSum_one_one` and `telescope_rowEq`.
- `content0_all`: Theorem 4.1 (finite form) for every `N`, derived from `shift_identity` and the up rule. It previously held only for `N ≤ 25`, by computation.
- The main tool is a new lemma, `sum_partition_down_eq_up`: summing over pairs `μ ⋖ λ` gives the same total whether the pairs are grouped by `λ` or by `μ`. The telescoping step uses the fact that `λ_i = i` (or `λ_i = i + 1`) holds for at most one `i`.

**`ZLine.lean`.**
- B1, `contentWt_eq_prod`: proved.
- B2, `giambelli_content` (weighted Giambelli): proved. Rather than redoing the branching argument, I derived it from the existing `giambelli_formula`. The hook content product splits as `(∏_{m=0}^{a}(z+m))·(∏_{m=1}^{b}(z−m))`, a factor depending only on the row times one depending only on the column, so it comes out of the determinant. The content product of `λ` is then the product of these factors over its Frobenius hooks (`contentProd_eq_prod_hooks`).
- `zline_identity` (B5, open for `k ≥ 3`) and `zline_identity_two` (optional): not proved. The paper proves the `k = 2` case with a long hypergeometric generating-function argument (Gessel's determinant, Euler transformations, contiguous relations), which I did not formalize.
- As an informal check only, not a Lean proof, a short script found the Lean statement holds for `k = 2, 3, 4`, `N ≤ 11`, at several rational values of `t`. So the formalization is at least consistent with the paper's data.

Your files refer to `COMMISSION.md`, which wasn't included in the upload. I followed the argument outlines in the docstrings and in the paper instead, and did not add anything for items B3 and B4, since the files don't state them.

The Properties table now includes the up rule, Theorem 4.1 for all `N`, B1/B2 and the `contentWt` definition, all marked proved except the definition. The `z`-line conjecture entry remains in progress.

# Summary of changes for run 126822c9-6ab3-4036-b3c1-6ad9fa5d46ed
I proved Giambelli's formula, which was the last `sorry` in the project. As a result, the paper's main theorem (Theorem 2.1, the shift identity) and Corollary 7.13 are now fully proved. The whole project builds with no `sorry` and no warnings. `#print axioms` shows that `shift_identity`, `avgEntry_diag` and `giambelli_formula` use only `propext`, `Classical.choice` and `Quot.sound`.

**What was proved.** `giambelli_formula` in `RequestProject/ShiftProof.lean` says that for every partition `λ ⊢ n`, `f_λ / n! = det(F(a_i | b_j))_{i,j<d(λ)}`, where `F(a|b) = 1/(a! b! (a+b+1))` and `(a | b)` are the Frobenius coordinates of `λ`. The proof works by strong induction on `n`: it shows that the determinant satisfies the same branching rule as `f_λ/n!`, namely `n · G(λ) = ∑_{corners c} G(λ ∖ c)`. It is split across two new files.

- **`RequestProject/GiambelliAlg.lean`** (the algebra):
  - An adjugate identity (`det_mul_sum_eq_sum_update`): if `X_{ij} + Y_{ij} = (u_i + v_j) M_{ij}`, then `(∑u + ∑v) det M` equals the sum of the determinants with one row replaced by a row of `X`, plus those with one column replaced by a column of `Y`.
  - It is applied with `F(a−1|b) + F(a|b−1) = (a+b+1) F(a|b)`, using a boundary convention at `a = 0` and `b = 0`.
  - The result, `GD_branch`, is the recursion `(∑a + ∑b + k) · G = ∑_i G(a − e_i, b) + ∑_j G(a, b − e_j) + [Durfee corner term]`.
- **`RequestProject/GiambelliComb.lean`** (the combinatorics):
  - Corners of `λ` are matched with moves of its Frobenius coordinates. A corner at the end of an arm lowers one `a_i`, a corner at the end of a leg lowers one `b_j`, and the corner of the Durfee square shrinks the square by one (`corner_data`).
  - Moves that would break strict decrease give a matrix with two equal rows or columns, so they contribute zero (`sum_corners_eq`).
  - The induction against the branching definition of `f_λ` is `syt_div_eq_GD`.

**Consequences.** These results previously depended on Giambelli's formula and now hold outright:
- `shift_identity`: for all `k ≥ 2` and all `N`, `∑_{λ ⊢ N+1, (k,k) ∉ λ} f_λ² = (N+1) ∑_{μ ⊢ N, (k−1,k+1) ∉ μ} f_μ²`.
- `avgEntry_diag`: `F(k,k) = F(k−1,k+1) + 1` for every `k ≥ 2` (Corollary 7.13).
- Lemma 7.3, obtained as `durfeeGF_of_giambelli giambelli_formula`.

I also updated the docstrings that described Giambelli's formula as an unproved outside result, and marked these results as proved in the Properties table.

**Still not formalized** (unchanged from before):
- the identification of `F` with expected arrival times via Robinson–Schensted;
- the general-`N` Bessel-function proof of Theorem 5.1, which is only checked by computation for `N ≤ 25`;
- the z-measure and Fock-space material, and `F(1,4)`;
- the full range of Computation 2.7, which is only checked for `k ≤ 5`, `N ≤ 25`.

# Summary of changes for run 13d6018a-9966-4903-80e0-d264c8a20b9f
I formalized a large part of `avgRS.tex` in Lean, in the `AvgRS` namespace under `RequestProject/`. The whole project builds. **The paper's main theorem, the shift identity (Theorem 2.1) for general `k`, is not proved.** `shift_identity` in `ShiftIdentity.lean` is stated faithfully but still ends in `sorry`, and it is the only `sorry` in the project. Corollary 7.13 (`avgEntry_diag`) depends on it, so that result is not proved either.

**Definitions**
- `f_λ` (number of standard Young tableaux) is defined by the branching rule (`syt`, `numSYT`). It is not connected to explicit tableaux.
- `boxAbsentSum N i j` is the sum of `f_λ²` over partitions `λ ⊢ N` that don't contain box `(i,j)`.
- `F(m,n)` (`avgEntry`) is defined by the series of Proposition 1.4, and the series is proved to converge.

**Proved without `sorry`**
- **Theorem 2.5:** the shift identity for `k = 2` and every `N` (`shift_identity_two`). This uses `f` of a hook `= C(a+b,b)`, the ballot formula for two-column shapes, and the Catalan identity.
- **Proposition 1.7:** `F(1,1)=1`, `F(1,2)=e`, `F(1,3)=Σ C_N/N!`, `F(1,3)=e²(I₀(2)−I₁(2))` and `F(2,2)=F(1,3)+1`. The Bessel functions are defined in `Bessel.lean`.
- **The step from the shift identity to Corollary 7.13:** if the identity holds for a given `k`, then `F(k,k)=F(k−1,k+1)+1`, including convergence (`avgEntry_diag_eq_of_shift`).
- **Lemma 7.5 (H1)–(H6):** the hook-matrix identities, stated entrywise, with (H6) using infinite sums (`HookMatrix.lean`).
- **The algebra of Section 7:** Lemma 7.11, Proposition 7.12 steps 1–3, and the final substitution giving (C′) (`HookMatrix.lean`).
- **Exact computations**, checked with `native_decide` through fast evaluators that are proved equal to the definitions:
  - the shift identity for `2 ≤ k ≤ 5` and `N ≤ 25` (`Computations.lean`), which is only part of the range in Computation 2.7;
  - Theorem 5.1, equation (5.2), for `N ≤ 25`, and the values `1,0,0,4,30,…,2089296` of `(N+1)!·P(c_{N+1}=0)` for `N+1 ≤ 11` (`DiagonalArrival.lean`).

**Not formalized**
- The Robinson–Schensted/probabilistic identification of `F` with expected arrival times.
- The analytic parts of Section 7: the Fredholm determinants, resolvent ODEs and ℓ² theory needed for the general shift identity.
- The general-`N` Bessel proof of Theorem 5.1, the z-measure results (Theorem 3.5), the Fock-space material, and `F(1,4)`.

The results that are proved use only the standard axioms, plus the `native_decide` axiom for the computations. The Properties table shows each result's status.