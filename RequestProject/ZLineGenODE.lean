module

public import RequestProject.ZLineGen

@[expose] public section

/-!
# Differential equations and the first integral on the line `z + z' = −2` (general weights)

Items B5–B9 of batch 5 for arbitrary diagonal weights `l, μ`: the vector equations for
`p(l,μ)`, `q(l,μ)`, the scalar equations obtained by pairing, and the first integral (`R2`).
These are the z-line analogues of Lemma 5.11 (`lem:odes`).
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

variable {w : ℚ} {l μ : ℕ → ℚ} {m : ℕ}

local notation "HH" => Hm ℚ m
local notation "vv" => vm ℚ m
local notation "AA" => Am ℚ m
local notation "rr" => (X : ℚ⟦X⟧)
local notation "ww" => (C w : ℚ⟦X⟧)

/-- A power series with `X f' = −f` vanishes. -/
lemma eq_zero_of_X_mul_deriv_eq_neg {f : ℚ⟦X⟧} (h : X * d⁄dX ℚ f = -f) : f = 0 := by
  ext n
  have hc := congrArg (coeff n) h
  have e : coeff n (X * d⁄dX ℚ f) = n * coeff n f := by
    cases n with
    | zero => simp
    | succ n => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring
  rw [e, map_neg] at hc
  have : ((n : ℚ) + 1) * coeff n f = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (by positivity)
  · simpa using h1

lemma vv_mul_DHD : vecMulVec vv vv * (Dg l m * (HH * Dg μ m)) = vecMulVec vv (Dg μ m *ᵥ cg l m) := by
  rw [vecMulVec_mul_eq, cg]
  congr 1
  simp only [Matrix.transpose_mul, Dg_transpose, Hm_transpose, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

lemma HD_vv_D : HH * (Dg l m * (vecMulVec vv vv * Dg μ m)) = vecMulVec (cg l m) (Dg μ m *ᵥ vv) := by
  rw [vecMulVec_mul_eq, Dg_transpose, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, cg,
    Matrix.mulVec_mulVec]

/-- `C(l,μ)' = v ⊗ diag(μ) c(l) + c(l) ⊗ diag(μ) v`. -/
lemma dM_Cg : dM (Cg l μ m) = vecMulVec vv (Dg μ m *ᵥ cg l m) + vecMulVec (cg l m) (Dg μ m *ᵥ vv) := by
  rw [Cg, dM_mul, dM_mul, dM_mul, dM_Dg, dM_Dg, dM_Hm]
  simp only [Matrix.mul_zero, add_zero, Matrix.add_mul, Matrix.mul_assoc, vv_mul_DHD, HD_vv_D]

/-- `G' = −ω (p ⊗ diag(μ) q + q ⊗ diag(μ) p)`. -/
lemma dM_Gg : dM (Gg w l μ m) = -(ww • (vecMulVec (pg w l μ m) (Dg μ m *ᵥ qg w l μ m)
    + vecMulVec (qg w l μ m) (Dg μ m *ᵥ pg w l μ m))) := by
  rw [Gg, dM_inv _ isUnit_det_Bg, ← Gg, Bg, dM_add, dM_one, zero_add, dM_C_smul, dM_Cg,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Gg_vecMulVec_D_Gg,
    Gg_vecMulVec_D_Gg, Gg_mulVec_cg, Gg_mulVec_vm]

lemma dot_Dv_eq_P (u : Fin m → ℚ⟦X⟧) : (Dg μ m *ᵥ u) ⬝ᵥ vv = (Dg μ m *ᵥ vv) ⬝ᵥ u := by
  rw [← dot_Dg_symm, dotProduct_comm]

/-- **B5** (general form): `r p' = A p − 2 ω r P q`. -/
lemma ode_pg : rr • dV (pg w l μ m)
    = AA *ᵥ pg w l μ m - (2 * ww * rr * Pg w l μ m) • qg w l μ m := by
  have h1 : dV (pg w l μ m) = dM (Gg w l μ m) *ᵥ vv + Gg w l μ m *ᵥ dV vv := dV_mulVec _ _
  have h2 : rr • (Gg w l μ m *ᵥ dV vv) = Gg w l μ m *ᵥ (AA *ᵥ vv) := by
    rw [← Matrix.mulVec_smul, X_smul_dV_vm]
  rw [h1, smul_add, h2, Gg_mulVec_Am_vm, dM_Gg, Matrix.neg_mulVec, Matrix.smul_mulVec,
    Matrix.add_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', dot_Dv_eq_P, dot_Dv_eq_P, ← Qg, ← Pg]
  module

/-- **B6** (general form): `r q' = 2 r P(μ,l) p − (A + 1) q`. -/
lemma ode_qg : rr • dV (qg w l μ m)
    = (2 * rr * Pg w μ l m) • pg w l μ m - (AA *ᵥ qg w l μ m + qg w l μ m) := by
  have h1 : dV (qg w l μ m) = dM (HH * Dg l m) *ᵥ pg w μ l m + (HH * Dg l m) *ᵥ dV (pg w μ l m) :=
    dV_mulVec _ _
  have h3 : dM (HH * Dg l m) *ᵥ pg w μ l m = Pg w μ l m • vv := by
    rw [dM_mul, dM_Dg, Matrix.mul_zero, add_zero, dM_Hm, vecMulVec_mul_eq, Dg_transpose,
      vecMulVec_mulVec']
    rfl
  have h4 : (HH * Dg l m) *ᵥ (AA *ᵥ pg w μ l m)
      = (rr * Pg w μ l m) • vv - (AA *ᵥ qg w l μ m + qg w l μ m) := by
    rw [Matrix.mulVec_mulVec, HD_mul_Am, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec',
      ← Matrix.mulVec_mulVec, ← qg, Matrix.add_mulVec, Matrix.one_mulVec, smul_smul]
    rfl
  have h5 := C_smul_HD_qg (w := w) (l := μ) (μ := l) (m := m)
  have h2 : rr • ((HH * Dg l m) *ᵥ dV (pg w μ l m))
      = (HH * Dg l m) *ᵥ (AA *ᵥ pg w μ l m) - (2 * rr * Pg w μ l m) • (vv - pg w l μ m) := by
    rw [← Matrix.mulVec_smul, ode_pg, Matrix.mulVec_sub, Matrix.mulVec_smul, ← h5, smul_smul]
    congr 2; ring
  rw [h1, smul_add, h2, h3, h4]
  module

lemma Dg_Am_mulVec (u : Fin m → ℚ⟦X⟧) : Dg μ m *ᵥ (AA *ᵥ u) = AA *ᵥ (Dg μ m *ᵥ u) := by
  rw [Matrix.mulVec_mulVec, Dg_comm_Am, ← Matrix.mulVec_mulVec]

lemma X_mul_deriv_dot (u y : Fin m → ℚ⟦X⟧) :
    rr * d⁄dX ℚ (u ⬝ᵥ y) = (rr • dV u) ⬝ᵥ y + u ⬝ᵥ (rr • dV y) := by
  rw [d_dotProduct, mul_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]

lemma X_smul_dV_Dg_vm : rr • dV (Dg μ m *ᵥ vv) = Dg μ m *ᵥ (AA *ᵥ vv) := by
  rw [dV_mulVec, dM_Dg, Matrix.zero_mulVec, zero_add, ← Matrix.mulVec_smul, X_smul_dV_vm]

lemma X_smul_dV_Dg_Am_vm : rr • dV (Dg μ m *ᵥ (AA *ᵥ vv)) = Dg μ m *ᵥ (AA *ᵥ (AA *ᵥ vv)) := by
  rw [dV_mulVec, dM_Dg, Matrix.zero_mulVec, zero_add, dV_mulVec, dM_Am, Matrix.zero_mulVec,
    zero_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, X_smul_dV_vm]

/-- `r P' = 2 P₁ − 2 ω r P Q`. -/
lemma ode_Pg : rr * d⁄dX ℚ (Pg w l μ m)
    = 2 * P1g w l μ m - 2 * ww * rr * Pg w l μ m * Qg w l μ m := by
  rw [Pg, X_mul_deriv_dot, X_smul_dV_Dg_vm, ode_pg, dotProduct_sub, dotProduct_smul,
    dot_A_symm, ← Dg_Am_mulVec, ← P1g, ← Pg, ← Qg, smul_eq_mul]
  ring

/-- `r Q' = 2 r P(l,μ) P(μ,l) − Q`. -/
lemma ode_Qg : rr * d⁄dX ℚ (Qg w l μ m)
    = 2 * rr * Pg w l μ m * Pg w μ l m - Qg w l μ m := by
  rw [Qg, X_mul_deriv_dot, X_smul_dV_Dg_vm, ode_qg, dotProduct_sub, dotProduct_smul,
    dotProduct_add, dot_A_symm, ← Dg_Am_mulVec, ← Pg, ← Qg, smul_eq_mul]
  ring

/-- `r Q₁' = 2 r P(μ,l) P₁(l,μ) − Q₁`. -/
lemma ode_Q1g : rr * d⁄dX ℚ (Q1g w l μ m)
    = 2 * rr * Pg w μ l m * P1g w l μ m - Q1g w l μ m := by
  rw [Q1g, X_mul_deriv_dot, X_smul_dV_Dg_Am_vm, ode_qg, dotProduct_sub, dotProduct_smul,
    dotProduct_add, dot_A_symm (u := Dg μ m *ᵥ (AA *ᵥ vv)), ← Dg_Am_mulVec, ← P1g, ← Q1g,
    smul_eq_mul]
  ring

/-- **B9** (general form): the first integral `Q₁ + Q̂₁ + Q = r P P̂ + ω r Q²`. -/
theorem first_integral_g : Q1g w l μ m + Q1g w μ l m + Qg w l μ m
    = rr * Pg w l μ m * Pg w μ l m + ww * rr * Qg w l μ m ^ 2 := by
  have hP := ode_Pg (w := w) (l := l) (μ := μ) (m := m)
  have hP' := ode_Pg (w := w) (l := μ) (μ := l) (m := m)
  have hQ := ode_Qg (w := w) (l := l) (μ := μ) (m := m)
  have hQ1 := ode_Q1g (w := w) (l := l) (μ := μ) (m := m)
  have hQ1' := ode_Q1g (w := w) (l := μ) (μ := l) (m := m)
  rw [← Qg_symm] at hP'
  set F := Q1g w l μ m + Q1g w μ l m + Qg w l μ m
    - (rr * Pg w l μ m * Pg w μ l m + ww * rr * Qg w l μ m ^ 2) with hF
  have dmul : ∀ f g : ℚ⟦X⟧, d⁄dX ℚ (f * g) = d⁄dX ℚ f * g + f * d⁄dX ℚ g := by
    intro f g; rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  have key : X * d⁄dX ℚ F = -F := by
    rw [hF]
    simp only [map_add, map_sub, dmul, pow_two, derivative_X, derivative_C]
    linear_combination hQ1 + hQ1' + (1 - 2 * ww * rr * Qg w l μ m) * hQ
      - (rr * Pg w μ l m) * hP - (rr * Pg w l μ m) * hP'
  have := eq_zero_of_X_mul_deriv_eq_neg key
  rw [hF] at this
  exact sub_eq_zero.mp this

/-! ### Scalar and vector identities used by the recurrences -/

/-- `H A u = r ⟨v, u⟩ v − (A + 1) H u`. -/
lemma Hm_Am_mulVec (u : Fin m → ℚ⟦X⟧) :
    HH *ᵥ (AA *ᵥ u) = (rr * (vv ⬝ᵥ u)) • vv - (AA *ᵥ (HH *ᵥ u) + HH *ᵥ u) := by
  have hHA : HH * AA = rr • vecMulVec vv vv - (AA + 1) * HH := by
    rw [← Hm_H2 (K := ℚ)]; abel
  rw [Matrix.mulVec_mulVec, hHA, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec',
    Matrix.add_mul, Matrix.one_mul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, smul_smul]

/-- `ω ⟨diag(μ) q(l,μ), c(l)⟩ = ⟨diag(l) v, v⟩ − P(μ,l)`. -/
lemma dot_Dq_cg : ww * ((Dg μ m *ᵥ qg w l μ m) ⬝ᵥ cg l m)
    = (Dg l m *ᵥ vv) ⬝ᵥ vv - Pg w μ l m := by
  rw [cg, ← Matrix.mulVec_mulVec, dot_H_symm, Matrix.mulVec_mulVec, ← smul_eq_mul,
    ← smul_dotProduct, C_smul_HD_qg, sub_dotProduct, Pg, dotProduct_comm vv,
    dotProduct_comm (pg w μ l m)]

/-- `⟨diag(μ) p(l,μ), c(l)⟩ = Q(l,μ)`. -/
lemma dot_Dp_cg : (Dg μ m *ᵥ pg w l μ m) ⬝ᵥ cg l m = Qg w l μ m := by
  rw [cg, ← Matrix.mulVec_mulVec, dot_H_symm, Matrix.mulVec_mulVec, Qg_symm, Qg, qg,
    dotProduct_comm]

/-- `G A c = A q + r (⟨diag(l) v, v⟩ − P(μ,l)) p − ω r Q q`. -/
lemma Gg_Am_cg : Gg w l μ m *ᵥ (AA *ᵥ cg l m) = AA *ᵥ qg w l μ m
    + (rr * ((Dg l m *ᵥ vv) ⬝ᵥ vv - Pg w μ l m)) • pg w l μ m
    - (ww * rr * Qg w l μ m) • qg w l μ m := by
  rw [Gg_Am_mulVec, Gg_mulVec_cg, dot_Dp_cg]
  linear_combination (norm := module) dot_Dq_cg • (rr • pg w l μ m)

/-- `G A² v = A² p + ω r (Q A p − P A q) + ω r (Q₁ p − P₁ q)`. -/
lemma Gg_Am_Am_vm : Gg w l μ m *ᵥ (AA *ᵥ (AA *ᵥ vv)) = AA *ᵥ (AA *ᵥ pg w l μ m)
    + (ww * rr * Qg w l μ m) • (AA *ᵥ pg w l μ m) - (ww * rr * Pg w l μ m) • (AA *ᵥ qg w l μ m)
    + (ww * rr * Q1g w l μ m) • pg w l μ m - (ww * rr * P1g w l μ m) • qg w l μ m := by
  rw [Gg_Am_mulVec, Gg_mulVec_Am_vm, ← dot_Dg_symm, ← dot_Dg_symm,
    dotProduct_comm (qg w l μ m), dotProduct_comm (pg w l μ m), ← Q1g, ← P1g]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  module

/-- `⟨(A + 1) diag(μ) c(l), p(l,μ)⟩ = r P ⟨diag(l) v, v⟩ − Q₁(μ,l)`. -/
lemma dot_ADc_pg : (AA *ᵥ (Dg μ m *ᵥ cg l m) + Dg μ m *ᵥ cg l m) ⬝ᵥ pg w l μ m
    = rr * Pg w l μ m * ((Dg l m *ᵥ vv) ⬝ᵥ vv) - Q1g w μ l m := by
  have e1 : (Dg μ m *ᵥ cg l m) ⬝ᵥ pg w l μ m = Qg w l μ m := by
    rw [← dot_Dg_symm, dotProduct_comm, dot_Dp_cg]
  have e2 : (AA *ᵥ (Dg μ m *ᵥ cg l m)) ⬝ᵥ pg w l μ m
      = (Dg l m *ᵥ vv) ⬝ᵥ (HH *ᵥ (AA *ᵥ (Dg μ m *ᵥ pg w l μ m))) := by
    rw [← dot_A_symm, ← dot_Dg_symm, Dg_Am_mulVec, cg, ← Matrix.mulVec_mulVec, ← dot_H_symm]
  have e3 : HH *ᵥ (Dg μ m *ᵥ pg w l μ m) = qg w μ l m := by
    rw [qg, Matrix.mulVec_mulVec]
  rw [add_dotProduct, e1, e2, Hm_Am_mulVec, e3, dot_Dg_symm, ← Pg, dotProduct_sub,
    dotProduct_smul, dotProduct_add, dot_A_symm, ← Dg_Am_mulVec, ← Q1g, ← Qg, ← Qg_symm,
    smul_eq_mul]
  ring

end AvgRS
