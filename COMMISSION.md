Go!

# Commission, batch 4 (run on top of the batch-3 session)

The batch-3 upload reached you without its `COMMISSION.md`; this file is that commission,
reduced to what is still open, plus one new skeleton file:

- `RequestProject/ZLineDet.lean` — items B3 and B4 (statements; proofs supplied below)
- `RequestProject/ZLine.lean` — item B5 (`zline_identity`, open) and `zline_identity_two` (optional)

Rules as before: keep the skeleton statements verbatim (if one is wrong, say so and fix it);
no `sorry`, `admit`, new axioms or `native_decide` on the import path of any theorem of the paper;
report `#print axioms` for each new top-level theorem. B3 and B4 are formalization work with
proofs supplied; B5 is open mathematics — search, report what was tried, leave the `sorry` if
it does not close.

## Part B. The identity on the line `z + z′ = −2` (Section 3, Conjecture 3.2)

Definitions in `ZLine.lean`: boxes of `p : n.Partition` are `(i, j)` with `i < col p j`
(`Frobenius.lean`), content `j − i`; `contentWt p t = f_λ² ∏ ((j − i − 1)² − t)`;
`contentProd p z = ∏ (z + j − i)`.

The statement `zline_identity` is Conjecture 3.2 (eq. (17) of the paper) after clearing the
normalization: the measure of Definition 3.1 is `M_t(λ) = contentWt λ t / (N!² Z_N(t))` with
`Z_N(t) = (1−t)_N / N!`, so `Z_{N+1}/Z_N = (N+1−t)/(N+1)`, and
`M_{t}^{(N+1)}(λ_k ≤ k−1) = M_t^{(N)}(λ_{k−1} ≤ k)` becomes
`∑_{λ ⊢ N+1, λ_k ≤ k−1} w_t(λ) = (N+1)(N+1−t) ∑_{λ ⊢ N, λ_{k−1} ≤ k} w_t(λ)`.
Checked in exact rational arithmetic for `k = 2, 3, 4`, `N ≤ 9`, `t = 5/3` (and by Computation 3.4
symbolically in `t` for `k ≤ 4`). The coefficient of `(−t)^{N+1}` is Theorem 2.1 (already proved:
`shift_identity`), so `zline_identity` is the full polynomial identity in `t` of which
`shift_identity` is the leading term.

Items B1 (`contentWt_eq_prod`) and B2 (`giambelli_content`) were proved in batch 3.

### B3, B4 (determinant and generating-function forms; adapt `DetExpand.lean`, `DurfeeLink.lean`)
Let `H_z` be the matrix `(H_z)_{ab} = X^{a+b+1} · hookFz z a b` in `ℚ⟦X⟧` (so the Plancherel `Hm`
is the leading coefficient in `z` of `H_z / z` up to normalization), and `H_{z′}` likewise with
`z′ = −z − 2`. Then, by Cauchy–Binet exactly as in `det_one_add_diag_HH` but with two different
matrices,
```
det(1 + diag(ω) H_z H_{z′}ᵀ) = ∑_k ∑_{f,g strictly increasing} (∏ ω∘f) det(H_z)_{f,g} det(H_{z′})_{f,g}
                             = ∑_k ∑_{f,g} (∏ ω∘f) X^{2(∑f+∑g+k)} det(G_z(f_i|g_j)) det(G_{z′}(f_i|g_j)),
```
and by B1, B2 and the Frobenius bijection `sum_durfee_eq_sum_smono`, the coefficient of `X^{2N}`
with `ω = w` is `∑_{λ ⊢ N} w^{d(λ)} contentWt λ t / N!²`, and with `ω = (1,1,w,w,…)` it is
`∑_{λ ⊢ N} w^{N₂(λ)} contentWt λ t / N!²`. Writing `G₀(w) = det(1 + w H_z H_{z′}ᵀ)`, `G₂(w) =
det(1 + W H_z H_{z′}ᵀ)` (as `X`-adic limits of truncations, as in `Transfer.lean`), the identity
`zline_identity` for all `k` is equivalent (by the argument of `shift_identity_of_durfeeGF`,
with `(N+1)(N+1−t)` in place of `(N+1)`, and `zz′ = 1 − t`) to
```
(B4)   d/dX G₀ = 2 X w · ( zz′ · G₂ + (X/2) · d/dX G₂ ),      i.e.  ∂_q G₀ = w (zz′ + q ∂_q) G₂,  q = X².
```
(The Plancherel case is `w · zz′ G₂` with the `q ∂_q` term absent: divide by `zz′` and let
`z → ∞`.) Checked numerically in the hook-matrix form for `N ≤ 6`.

### B5. Prove (B4), hence `zline_identity`  — OPEN

No proof is known. The Plancherel proof (Section 5 of the paper, `Formal/*.lean`) rests on the
three structural identities (H1), (H2), (H4) for the single symmetric matrix `H` and the vector
`v`. For `H_z` the analogues exist, with the Euler operator `A` shifted by `z`; all four were verified
symbolically on `6 × 6` truncations. Write
`(H_z)_{ab} = X^{a+b+1} · z (z+1)_a (−1)^b (1−z)_b / (a! b! (a+b+1))` (Pochhammer symbols; this is
`hookFz`), and put `u_a = X^a (z+1)_a / a!`, `ũ_b = X^b (−1)^b (1−z)_b / b!`. Then:
- (H1_z) `d/dX H_z = z · u ⊗ ũ` (rank one), and `X · d/dX u = A u`, `X · d/dX ũ = A ũ`;
- (H2_z) `H_z A + (A + 1) H_z = z X · u ⊗ ũ`;
- (H3_z) `Xᵀ H_z (z − 1 − A) = (z + 1 + A) H_z X` (entrywise: `(a+1)(H_z)_{a+1,b}/(z+1+a) =
  (b+1)(H_z)_{a,b+1}/(z−1−b)`);
- (H4_z) `(z + A) X H_z − H_z Xᵀ (z − A) = z · (A u ⊗ ũ − u ⊗ A ũ)` (rank two).
For `H_{z′}` the same with `z′ = −z−2`, and note `u^{(z′)}_a = X^a (−z−1)_a / a!`, `ũ^{(z′)}_b =
X^b (−1)^b (z+3)_b / b!`. The product `H_z H_{z′}ᵀ` replaces `H²`; the resolvent is `(1 + w H_z
H_{z′}ᵀ)⁻¹`, and the two derivative formulas of Lemma 5.7 (Jacobi, rank-two perturbation) hold
verbatim. What is missing is the analogue of Lemma 5.10–5.14: the closed system for the scalars
and its first integrals. A reasonable first target is the case `k = 2` (`zline_identity_two`),
for which the paper has an independent proof (Theorem 3.6) through the generating functions
of hooks and two-column shapes in terms of one hypergeometric function `y = ₂F₁(−s, s; 1; x)`,
`s² = t`; that proof is formalizable as an identity of formal power series in `x` (all functions
involved are power series with rational-in-`t` coefficients, and the differential equation
(19) is `x(1−x)y″ + (1−x)y′ + t y = 0`), but it is a separate route and does not extend to `k ≥ 3`.

Report for B5: which of (H1_z)–(H4_z) were verified in Lean (these are worth having in any
case), what closed system was found, and where it stops.

---


## Housekeeping

1. Docstrings in `Formal/*.lean`, `DurfeeLink.lean`, `ShiftProof.lean`, `AverageTableau.lean`
   cite "Section 7", "Lemma 7.3/7.4/7.5/7.9/7.10/7.11", "Definition 7.7", "Proposition 7.12",
   "Corollary 7.13", "(7.14)", "Theorem 5.1", "Computation 5.2", "Theorem 2.5", "Computation 2.7",
   "Proposition 1.7". In `avgRS.pdf` these are: Section 5; Lemma 5.4 (`lem:durfeedet`), Lemma
   5.7 (`lem:five`), Lemma 5.5 (`lem:Cprime`), Lemma 5.6 (`lem:Hids`), Lemma 5.10 (`lem:Gids`),
   Lemma 5.11 (`lem:rec`), Lemma 5.12 (`lem:odes`), Definition 5.8 (`def:pq`), Proposition 5.12
   (`prop:level0`), Proposition 5.14 (`prop:level1`), Corollary 5.15 (`cor:Fshift`), eq. (31)
   (`eq:ts`); Theorem 4.1 (`thm:content0`), Computation 4.2; Theorem 2.4 (`thm:k2`), Computation
   2.6 (`comp:main`), Proposition 1.9 (`prop:closed`). Please correct them.
2. `HookMatrix.lean` (real-valued (H1)–(H6) and pointwise algebra from batch 1) is superseded by
   `Formal/`; delete it or mark it as superseded in its header.
3. Do not include a second copy of the tex in the delivery.
4. `content0_all` (batch 3) supersedes `content0_of_le` and `content0_check_fast` in
   `DiagonalArrival.lean`: delete them. `diagArrival_values` is a computation; either re-prove it
   without `native_decide` (`decide`/`norm_num` on the eleven values, using `content0_all` to
   reduce to `rowEqSum`) or delete it. After this, `Computations.lean` is the only file with
   `native_decide`; move it to a separate library target not imported by `Main.lean`, or delete it.
5. The delivery now carries three copies of the tex (`avgRS.tex`, `avgRS(1).tex`, `avgRS(2).tex`);
   keep only the one uploaded with this commission.
