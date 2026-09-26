# Batch 5 report

The whole `RequestProject` library builds. Every item of the batch-5 skeleton is proved, with one
exception: **item C4 is false as stated** (details and a corrected version below). The only `sorry`
left in the library is still `zline_identity` (Conjecture 3.2), which was not touched.

## Files

| file | contents |
|---|---|
| `RequestProject/ZLineRec.lean` | the uploaded skeleton, moved into `RequestProject/`, with all proofs filled in |
| `RequestProject/ZLineGen.lean` | new: the resolvent layer for two arbitrary diagonal weights `l, μ` (B1–B4, A1, A4, plus small helpers) |
| `RequestProject/ZLineGenODE.lean` | new: B5–B9 for arbitrary weights, and the scalar/vector identities used by C1–C3 |

The only change to `ZLineRec.lean` apart from filling in proofs is one extra import,
`RequestProject.ZLineGenODE`. Helper lemmas were added to the file (listed below). The file is about
1100 lines long. I did not split it, so that every skeleton statement stays where you put it.

**How the generic files work.** The hatted objects are the unhatted ones with `Λ` and `M` exchanged:
`Ĉ₁ = C(M,Λ)`, `p̂ = p(M,Λ)`, `q = H Λ p(M,Λ)`, `q̂ = H M p(Λ,M)`, `P̂ = P(M,Λ)`, `Q̂ = Q(M,Λ)`.
So B1–B9 are proved once, for weights `l, μ : ℕ → ℚ` (`Cg`, `Gg`, `pg`, `qg`, `Pg`, `Qg`, …),
and each skeleton item is then a one-line instance. For example, `Qzz_eq_Qhzz` is `Qg_symm`, and
B7 is B5 with the weights swapped. The skeleton definitions are definitionally equal to these
instances.

## Changes to skeleton statements

* **C4 (`P2_of_RZp`) is false for the truncations.** The exact equality fails. Pairing C2 with `Mv`
  gives the identity only up to `r⟨Mv, err⟩`, where `err` is the boundary defect of C2, and this
  term does not vanish:
  * `P2_of_RZp_false` proves it formally, with the witness `m = 1`, `ω = 0`, `t = 2`. There `p = v`
    and `A = 0`, so the left side is `0`, while the right side is `−r² t P = −r²·2·(1−2) = 2r²`.
  * A separate informal check (a scratch copy of your script, run at `m = 2`, `t = −23/10`, `ω = 3/5`;
    not part of the Lean development) found the defect first appearing at `r^{2m}`.
  * Your script does not see it because it compares coefficients only up to `r^{N−6} = r^{20}`,
    with `n = N/2 + 2 = 15`.
  * The skeleton statement is kept in the file, commented out, with this explanation.

  **Corrected identity** (`P2_of_RZp_trunc`, in the style of C1–C3): there is an `e` with
  `X^m ∣ e` such that

      (1 − r²) P₂ = ω r (1−r²)(P Q₁ + P₁ Q − ω r P Q²) + ω r (1 + r²) P Q − r² t P
                    − ω r² (1−r²) P² P̂ + e.

  Its right-hand side is exactly the skeleton's plus `e`, and in fact `e = r ⟨Mv, err_C2⟩`. For the
  `X`-adic limits the defect disappears.
* No other statement was changed. None of the helper lemmas carries extra hypotheses.

## What was proved, and how

**A0** (`det_one_add_diag_Czz`) holds for every `z`, with no case split and no interpolation in `z`.
* Write `H_z = diag(α) H diag(β)`, where `α_a = armProd z a` and `β_b = legProd z b`.
* Then `H_z H_{z'}ᵀ = diag(α)(HΛH)diag(α')`, because `β_b β'_b = λ_b` and `α_a α'_a = μ_a`.
* Two uses of `det(1 + AB) = det(1 + BA)` (Mathlib's `Matrix.det_one_add_mul_comm`), together with
  the fact that diagonal matrices commute, turn `det(1 + D·diag(α)·HΛH·diag(α'))` into
  `det(1 + D·HΛH·M)`. Invertibility of `diag(α)` is never needed.

**W1–W6, A1–A4** are as in the commission.
* The shift identities are instances of two generic lemmas, `XmT_mul_Dg` and `Xm_mul_Dg`:
  `Xᵀ diag(f) = diag(g) Xᵀ` whenever `f(a+1) = g(a)`, and `X diag(f) = diag(g) X` whenever
  `f(b) = g(b+1)`.
* A2 and the second half of A2 (`Dmz_two_mul_Hm`) are entrywise consequences of `hE_H2`.

**A5** follows your two steps. It uses `Xᵀ A v ≡ r(A+1)v (mod X^m)` (`vm_H5a_A`). The error is
`H Λ D₂ E₃ M` plus rank-one terms coming from the boundary defects of `Xᵀv` and `XᵀAv`.

**B1–B9** follow your proofs.
* B3 comes from `G(l,μ)ᵀ diag(μ) = diag(μ) G(l,μ)`.
* B6 is derived from B7, via `q = HΛp̂`, together with A1 and B2.
* B9 uses the lemma you suggested, `X f' = −f ⇒ f = 0` (`eq_zero_of_X_mul_deriv_eq_neg`), applied
  to the difference of the two sides.

**C1** follows your proof exactly. The final step is one `linear_combination` using B9 with
coefficient `ωr`.

**C2: the cancellation you asked for.** Instead of pairing term by term, I computed the commutator
itself in closed form (`Y_comm_Czz`). Up to an error divisible by `X^m`:

    [D₀Xᵀ, C₁] = r(1−r²)⟨Λv,v⟩ v⊗Mv + r² v⊗M(A−1)c + r² Av⊗Mc − c⊗MAv − (A+1)c⊗Mv.

* **Derivation.** Your chain (Hm_H3, W4, Hm_H4, W2, A3) gives, exactly,
  `(1−t)[Y,C₁] = −r R₂ M Y + D₀HNEM + (1−t) D₀E₃ΛHM`. Then:
  * `R₂MY = R₂XᵀM`, which is `v⊗MXHN(A+1)v − Av⊗MXHNv`.
  * `MXHNu = M(HXᵀNu + ⟨v,Nu⟩Av − ⟨Av,Nu⟩v)`, where `XᵀN = ND₁Xᵀ` and `ND₁ = (1−t)Λ`.
  * `D₀HNu = HD₁Nu − r(⟨(A+1)v,Nu⟩v − ⟨v,Nu⟩Av)`.
* **The constants cancel.** The four constants `⟨Nv,v⟩`, `⟨NAv,v⟩ = ⟨Av,Nv⟩`, `⟨N(A+1)v,v⟩` and
  `⟨N(A+1)v,Av⟩` cancel in pairs. Each constant appears once through `MXHN·` and once through
  `D₀HN·`, with opposite signs. What remains is exactly `(1−t)` times the formula above.
* **The case `t = 1`.** Dividing by `1 − t` needs `t ≠ 1`. For `t = 1` we have `M = 0`, so both
  sides vanish.
* The formula is the `M`-adjoint of A5: `M[Y,C₁] = −[X,C₁]ᵀM`.
* **The recurrence.** C2 then follows from `Y p = G Y v − ω G [Y,C₁] p`, with
  `Yv = r(A²−t)v + D₀e₅`, together with `⟨Mc,p⟩ = Q`, `⟨MAc,p⟩ = rPL₀ − Q̂₁ − Q`, B4, `GAc`, `GA²v`
  and B9 (coefficient `ωr²`).

**C3.** The hatted commutator needs no division (`Yh_comm_Chzz`). Up to an error divisible by `X^m`:

    [D₂Xᵀ, Ĉ₁] = r(1−r²)⟨Mv,v⟩ v⊗Λv + r² v⊗Λ(A+3)ĉ + r² Av⊗Λĉ − ĉ⊗ΛAv − (A+1)ĉ⊗Λv,   ĉ = HMv.

* It is derived through W3, Hm_H4, W5 and A3h, together with `XᵀM⁻ = M⁻D₋₁Xᵀ` and `D₋₁M⁻ = M`.
* Here the constants `⟨M⁻·,·⟩` cancel in the same way.
* C3 then follows, with B9 again entering at coefficient `ωr²`.

## Optional items

* **`P̂₂` analogue of C4.** Proved in its truncated form (`Ph2_of_RZph_trunc`), by pairing C3 with
  `Λv`. Up to an error divisible by `X^m`:

      (1−r²) P̂₂ = 4r² P̂₁ + ω r (1−r²)(P̂ Q̂₁ + P̂₁ Q − ω r P̂ Q²) + ω r (1 − 3r²) P̂ Q
                  + (4−t) r² P̂ − ω r² (1−r²) P P̂².

* **B10.** Not attempted, and, as you asked, not added to the file.
* **The `xlim` layer.** Not done.

## Helper lemmas added to `ZLineRec.lean`

`Dmz_eq`, `Dmz_two_mul_Hm`, `XT_mul_Mumm`, `Mumm_mul_Dmz_neg_one`, `XT_Mumm_vm`, `XT_Mumm_Am_vm`,
`Xm_Hm_mulVec`, `Dmz_two_Hm_mulVec`, `Yh_comm_Chzz`, `XT_mul_Num`, `Dmz_zero_Hm_mulVec`,
`Y_comm_Czz_scaled`, `Y_comm_Czz`.

## `#print axioms`

Each of the following depends only on `[propext, Classical.choice, Quot.sound]`:

* **A0, W and A items:** `isUnit_det_Bzz`, `isUnit_det_Bhzz`, `det_one_add_diag_Czz`, `muW_succ`,
  `lamW_succ`, `nuW_succ`, `one_sub_mul_lamW`, `XT_mul_Mum`, `Xm_mul_Mum`, `Xm_mul_Lamm`,
  `XT_mul_Lamm`, `Dmz_one_mul_Num`, `Dmz_neg_one_mul_Mumm`, `HLam_H2`, `Dmz_zero_mul_Hm`,
  `Dmz_zero_HNH`, `Dmz_two_HMmH`, `Am_comm_Czz`, `Xm_comm_Czz`.
* **B items:** `Gzz_mul_HLam`, `HMum_mul_Gzz`, `c_HMum_mulVec_qzz`, `Qzz_eq_Qhzz`,
  `Gzz_mulVec_Am_vm`, `ode_pzz`, `ode_qzz`, `ode_phzz`, `ode_qhzz`, `ode_Pzz`, `ode_Phzz`,
  `ode_Qzz`, `ode_Q1zz`, `ode_Qh1zz`, `first_integral_R2`.
* **C items and extras:** `RXp_trunc`, `RZp_trunc`, `RZph_trunc`, `P2_of_RZp_trunc`,
  `P2_of_RZp_false`, `Ph2_of_RZph_trunc`, `Y_comm_Czz`, `Yh_comm_Chzz`.

No `native_decide` is used anywhere in `RequestProject`. The `Computations` library is unchanged and
still not imported by any `RequestProject` file.
