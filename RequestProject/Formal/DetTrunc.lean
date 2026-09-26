module

public import RequestProject.Formal.RecODE

@[expose] public section

/-!
# The two determinant formulas (Lemma 5.7, `lem:five`) for the truncations

`D = det(1 + z H²)` and `D_Z = det(1 + Z H²)` with `Z = diag(1, 1, z, z, …)`:
`D' = 2 z Q D` (Jacobi) and `z² D_Z = D ((1 - ξ G₀₀)(1 - ξ G₁₁) - ξ² G₀₁ G₁₀)` (rank-two
perturbation), `ξ = 1 - z`.
-/

namespace AvgRS.Formal

open PowerSeries Matrix

variable {K : Type*} [Field K]

variable (K) in
/-- `D = det(1 + z H²)` (truncated). -/
noncomputable def Dm (m : ℕ) (z : K) : K⟦X⟧ := (Bm K m z).det

variable (K) in
/-- `Z = diag(1, 1, z, z, …)`. -/
noncomputable def Zm (m : ℕ) (z : K) : Matrix (Fin m) (Fin m) K⟦X⟧ :=
  Matrix.diagonal fun a => if (a : ℕ) < 2 then 1 else C z

variable (K) in
/-- `D_Z = det(1 + Z H²)` (truncated). -/
noncomputable def DZm (m : ℕ) (z : K) : K⟦X⟧ := (1 + Zm K m z * (Hm K m * Hm K m)).det

variable {m : ℕ} {z : K}

local notation "HH" => Hm K m
local notation "vv" => vm K m
local notation "BB" => Bm K m z
local notation "GG" => Gm K m z
local notation "cc" => (C z : K⟦X⟧)
local notation "pp" => pm K m z
local notation "qq" => qm K m z
local notation "QQ" => Qm K m z

lemma c_HHG : cc • (HH * HH * GG) = 1 - GG := by
  have h := Bm_mul_Gm (K := K) (m := m) (z := z)
  rw [Bm, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
  rw [← h]; abel

variable [CharZero K]

/-- Jacobi: `D' = 2 z Q D`. -/
lemma deriv_Dm : d⁄dX K (Dm K m z) = 2 * cc * QQ * Dm K m z := by
  rw [Dm, deriv_det _ isUnit_det_Bm, ← Gm]
  have hB : dM BB = cc • (vecMulVec vv (HH *ᵥ vv) + vecMulVec (HH *ᵥ vv) vv) := by
    rw [Bm, dM_add, dM_one, zero_add, dM_C_smul, dM_mul, dM_Hm, Matrix.vecMulVec_mul,
      Matrix.mul_vecMulVec, ← Matrix.mulVec_transpose, Hm_transpose]
  rw [hB, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
    ← pm, dot_H_symm, Hm_mulVec_pm, ← qm, dotProduct_comm qq, smul_eq_mul]
  simp only [Qm]
  ring

omit [CharZero K] in
/-- The rank-two perturbation formula for `D_Z`. -/
lemma DZm_eq (n : ℕ) :
    (C z : K⟦X⟧) ^ 2 * DZm K (n + 2) z = Dm K (n + 2) z *
      ((1 - (1 - C z) * Gm K (n + 2) z 0 0) * (1 - (1 - C z) * Gm K (n + 2) z 1 1)
        - (1 - C z) ^ 2 * (Gm K (n + 2) z 0 1 * Gm K (n + 2) z 1 0)) := by
  let ι : Fin 2 → Fin (n + 2) := fun j => ⟨j, by omega⟩
  let U : Matrix (Fin (n + 2)) (Fin 2) K⟦X⟧ := Matrix.of fun a j => if (a : ℕ) = (j : ℕ) then 1 - (C z : K⟦X⟧) else 0
  let V : Matrix (Fin 2) (Fin (n + 2)) K⟦X⟧ := Matrix.of fun j b => (Hm K (n + 2) * Hm K (n + 2)) (ι j) b
  have hZ : 1 + Zm K (n + 2) z * (Hm K (n + 2) * Hm K (n + 2)) = Bm K (n + 2) z + U * V := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.add_apply, Zm, Matrix.diagonal_mul, Bm, Matrix.add_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply (M := U), Fin.sum_univ_two]
    simp only [U, V, Matrix.of_apply]
    obtain ⟨a, ha⟩ := a
    rcases a with _ | _ | a
    · simp [ι]; ring
    · simp [ι]; ring
    · simp [ι]
  have hUV : ∀ i j, (V * Gm K (n + 2) z * U) i j = (1 - (C z : K⟦X⟧)) * (Hm K (n + 2) * Hm K (n + 2) * Gm K (n + 2) z) (ι i) (ι j) := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (ι j)]
    · simp only [U, Matrix.of_apply, ι, V]
      rw [mul_comm]
      congr 1
    · intro b _ hb
      simp only [U, Matrix.of_apply]
      rw [if_neg, mul_zero]
      intro h; apply hb; ext; simp [ι, h]
    · simp
  have hc : ∀ x y, (C z : K⟦X⟧) * (Hm K (n + 2) * Hm K (n + 2) * Gm K (n + 2) z) x y = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) K⟦X⟧) x y - Gm K (n + 2) z x y := by
    intro x y
    have := congrFun (congrFun (c_HHG (K := K) (m := n + 2) (z := z)) x) y
    simpa using this
  have hdet : (C z : K⟦X⟧) ^ 2 * (1 + V * Gm K (n + 2) z * U).det
      = (1 - (1 - (C z : K⟦X⟧)) * Gm K (n + 2) z 0 0) * (1 - (1 - (C z : K⟦X⟧)) * Gm K (n + 2) z 1 1) - (1 - (C z : K⟦X⟧)) ^ 2 * (Gm K (n + 2) z 0 1 * Gm K (n + 2) z 1 0) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, hUV, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide :
      (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    have h00 := hc 0 0
    have h11 := hc 1 1
    have h01 := hc 0 1
    have h10 := hc 1 0
    have e0 : ι 0 = 0 := rfl
    have e1 : ι 1 = 1 := by ext; simp [ι]
    rw [e0, e1]
    rw [Matrix.one_apply_eq] at h00 h11
    rw [Matrix.one_apply_ne (by simp)] at h01 h10
    linear_combination (1 - C z) * (C z + (1 - C z) * C z *
        (Hm K (n + 2) * Hm K (n + 2) * Gm K (n + 2) z) 1 1) * h00
      + (1 - C z) * (C z + (1 - C z) * (1 - Gm K (n + 2) z 0 0)) * h11
      - (1 - C z) ^ 2 * C z * (Hm K (n + 2) * Hm K (n + 2) * Gm K (n + 2) z) 1 0 * h01
      + (1 - C z) ^ 2 * Gm K (n + 2) z 0 1 * h10
  rw [DZm, hZ, Matrix.det_add_mul U V isUnit_det_Bm, ← Gm, ← Dm, ← hdet]
  ring

end AvgRS.Formal
