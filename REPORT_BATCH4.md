# Batch 4 report

The whole project builds (both libraries: `RequestProject` and `Computations`).
The only `sorry` left is `zline_identity` (Conjecture 3.2 for general `k`), which is open for `k ≥ 3`.

## Files

| file | contents |
|---|---|
| `RequestProject/ZLineDet.lean` | B3, B4 (from the uploaded skeleton `ZLineDet.lean`) |
| `RequestProject/ZLineHook.lean` | (H1_z)–(H4_z), stated entrywise (new) |
| `RequestProject/ZLineTwo.lean` | proof of Theorem 3.6 (`k = 2` on the line), used by `zline_identity_two` (new) |
| `RequestProject/ZLine.lean` | `zline_identity_two` is now proved; `zline_identity` remains `sorry` |
| `Computations/` | separate library holding every `native_decide` check (see Housekeeping) |

## Changes to skeleton statements

* `zline_identity_of_formal`: the skeleton's `(X / 2)` does not elaborate, because `ℚ⟦X⟧` has no
  division by a natural number. It is written `(C (1/2 : ℚ) * X)` instead. The statement is otherwise
  unchanged. It concerns the single value `t = (z+1)²`, so no interpolation in `t` is needed.
* No other statement was changed.

## `#print axioms`

All of the following depend only on `[propext, Classical.choice, Quot.sound]`:
`coeff_det_Cz_eq_sum_partitions`, `G0m_succ`, `G2m_succ`, `zlineGF`, `zline_identity_of_formal`,
`deriv_hzE`, `X_mul_deriv_uz`, `X_mul_deriv_utz`, `hzE_H2`, `hzE_H3`, `hzE_H4`,
`zline_identity_two`, `shift_identity`, `content0_all`, `avgEntry_diag`.

`zline_identity` depends on `sorryAx` (it is open).
`diagArrival_values`, in the separate `Computations` library, uses `native_decide`
(`Lean.ofReduceBool`, `Lean.trustCompiler`).

## B3 (proved)

The truncated `det(1 + diag(ω) H_z H_{z'}ᵀ)` is expanded by the principal-minor expansion and
Cauchy–Binet, now with two different matrices (`det_one_add_diag_Cz`). Each minor factors as
`X^{frobWt} · det(G_z(f_i|g_j))`. The Frobenius bijection `sum_durfee_eq_sum_smono` and the
weighted Giambelli formula B2 then identify the `X^{2N}` coefficient with
`∑_λ (∏ ω(a_i)) w_t(λ)/N!²` (`coeff_det_Cz_eq_sum_partitions`).
Coherence of the truncations (`G0m_succ`, `G2m_succ`) follows from `H_z(m+1) ≡ blk(H_z(m), 0)`
modulo `X^{m+1}`. `zlineGF` is the case `m = 2N+3`.

## B4 (proved)

`zline_identity_of_formal` adapts `durfee_sum_identity` and `shift_identity_of_durfeeGF`. Taking the
`X^{2N+1}` coefficient of `d/dX G₀ = 2Xw(zz' G₂ + (X/2) d/dX G₂)` gives
`∑_{λ⊢N+1} w^{d(λ)} w_t(λ) = (N+1)(N+1−t) w ∑_{λ⊢N} w^{N₂(λ)} w_t(λ)`, using `zz' = 1 − t`.
Both sides are polynomials in `w` that agree at every `w ≠ 0, 1`, so they agree identically.
Summing the coefficients of `w^j` for `j < k` gives the statement.

## B5

**Verified in Lean** (`ZLineHook.lean`, all entrywise, for arbitrary rational `z`; the `z'`
versions are the same lemmas at `-z - 2`):

* (H1_z) `d/dX (H_z)_{ab} = z u_a ũ_b` (`deriv_hzE`), `X u_a' = a u_a` (`X_mul_deriv_uz`),
  `X ũ_b' = b ũ_b` (`X_mul_deriv_utz`);
* (H2_z) `(a+b+1)(H_z)_{ab} = z X u_a ũ_b` (`hzE_H2`);
* (H3_z) `(a+1)(H_z)_{a+1,b}(z−1−b) = (b+1)(H_z)_{a,b+1}(z+1+a)` (`hzE_H3`). Denominators are
  cleared, so the identity holds even where `z+1+a` or `z−1−b` vanishes;
* (H4_z) `(z+a)·a(H_z)_{a−1,b} − b(H_z)_{a,b−1}(z−b) = z(a−b) u_a ũ_b` (`hzE_H4`), the
  `(a,b)` entry of `(z+A)XH_z − H_zXᵀ(z−A) = z(Au⊗ũ − u⊗Aũ)`, including the boundary rows and
  columns `a = 0`, `b = 0`.

**Closed system:** none was found. The one structural fact recorded is that for
`C = H_z H_{z'}ᵀ`, (H1_z) gives `dC/dX = z u⊗(H_{z'}ũ) + z'(H_z ũ')⊗u'`, a rank-two derivative
(rank one in the Plancherel case). The analogues of Lemmas 5.10–5.14, meaning the recurrences for
`𝒢u`, `𝒢H_z ũ`, the ODE system for the scalars and its first integrals, were not derived. The work
stops there, and `zline_identity` keeps its `sorry`.

**The case `k = 2` (`zline_identity_two`) is proved**, by a shorter route than the paper's.
With `P₀(n) = ∏_{i<n}(i² − t)`, `P₁(n) = ∏_{i<n}((i+1)² − t)` and `y_n = P₀(n)/n!²` (the
coefficients of `₂F₁(−s,s;1;x)`):

1. Hooks and two-column shapes are enumerated (`sum_hook_eq`, `sum_twoCol_eq`). Their weights are
   `C(N,b)² P₁(b+1) P₀(N−b)` and `ballot(N,j)² P₁(N−j) P₀(j)` (`cwt_hookP`, `cwt_twoColP`).
2. Since `t P₁(m) = −P₀(m+1)` and `ballot(N,j)(N+1−j)! j! = N!(N+1−2j)`, multiplying by `−t/N!²`
   turns the identity into
   `∑_{i+j=n} j²(j²−t) y_i y_j = n(n−t) ∑_{i+j=n} (j² − ij) y_i y_j`, with `n = N+1`. The two-column
   side is first symmetrised under `j ↦ N+1−j`.
3. This is the `X^n` coefficient of
   `Y(ϑ⁴ − tϑ²)Y = ϑ(ϑ − t)(Yϑ²Y − (ϑY)²)`, where `ϑ = X d/dX` (`ySer_key`). The identity reduces
   to `(1−X)(R² + tYϑR − tbR − tYR) = 0`, with `b = ϑY` and `R = ϑ²Y`. That follows from the
   hypergeometric equation `(1−X)ϑ²Y = −tXY` (`ySer_ode`) and its `ϑ`-derivative.
4. The case `t = 0` follows because both sides are polynomials in `t`.

Gessel's determinant, Euler's transformation and the contiguous relations are not needed. As in
the paper, this route relies on the special structure of two-column shapes and does not extend
directly to `k ≥ 3`.

## Housekeeping

1. **Citations** in docstrings now follow the numbering of the new `avgRS.tex`, with the LaTeX label
   given alongside: Section 5; Lemma 5.4 `lem:durfeedet`; Lemma 5.5 `lem:Cprime`; Lemma 5.6
   `lem:Hids`; Lemma 5.7 `lem:five`; Definition 5.8 `def:pq`; Lemma 5.9 `lem:Gids`; equation
   `eq:ts`; Lemma 5.10 `lem:rec`; Lemma 5.11 `lem:odes`; Proposition 5.12 `prop:level0`; Lemma 5.13
   `lem:level1`; Proposition 5.14 `prop:level1`; Corollary 5.15 `cor:Fshift`; Theorem 4.1,
   Computation 4.2; Theorem 2.4, Computation 2.6; Proposition 1.10 `prop:closed`; Proposition 1.6
   `prop:series`; Definition 1.3.
   The numbers come from counting the theorem-like environments in the tex (one shared counter per
   section). They differ from the commission's list in four places:
   * `lem:Gids`, `lem:rec` and `lem:odes` are 5.9, 5.10 and 5.11, not 5.10, 5.11 and 5.12;
   * `prop:closed` is 1.10, not 1.9.

   The labels are given so the references can be checked against the PDF. Equation numbers are
   cited by label only.
2. `HookMatrix.lean` (real-valued, superseded by `Formal/`) has been deleted.
3. and 5. Only one copy of the tex is kept: `avgRS.tex`, which is the newer version uploaded with
   this commission. The duplicate root copies of `ZLine.lean` and `ZLineDet.lean` have been
   removed; the files live in `RequestProject/`.
4. `content0_of_le` and `content0_check_fast` have been deleted. `diagArrival_values` could not be
   re-proved by kernel `decide`, because the well-founded recursion in the evaluator does not reduce.
   It has therefore been moved, together with its fast evaluator and `FastCount.lean` and
   `Computations.lean`, into the separate library `Computations`
   (`Computations/FastCount.lean`, `Computations/ShiftIdentityCheck.lean`,
   `Computations/DiagonalArrivalCheck.lean`). No file of `RequestProject` imports it, so
   `native_decide` is off the import path of every theorem of the paper. Both libraries are default
   build targets.
