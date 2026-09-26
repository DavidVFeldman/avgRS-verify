module

public import RequestProject.ZLineAlgG01m

@[expose] public section

/-!
# The closed system on the line `z + z' = −2`: first integrals, closed forms, and (B4)
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- (G01) `(1−ω)(1−t) r u G₀₁ = ω (u P₁ + t r² P)`. -/
lemma zG01 (Z : ZAlgData t w) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hE0 : (-X^8*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 + X^8*(C t)^2*Z.P*Z.Ph*Z.p0^2 + 2*X^8*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 - 2*X^8*(C t)*Z.P*Z.Ph*Z.p0^2 - X^8*(C w)*Z.P*Z.Ph*Z.p0^2 + X^8*Z.P*Z.Ph*Z.p0^2 + 3*X^6*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 - 3*X^6*(C t)^2*Z.P*Z.Ph*Z.p0^2 - 6*X^6*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 + 6*X^6*(C t)*Z.P*Z.Ph*Z.p0^2 + X^6*(C w)^2*Z.P^2*Z.Q^2 + 3*X^6*(C w)*Z.P*Z.Ph*Z.p0^2 - 3*X^6*Z.P*Z.Ph*Z.p0^2 - X^5*(C t)^2*(C w)*Z.Q*Z.p0^2 + X^5*(C t)^2*Z.Q*Z.p0^2 + 2*X^5*(C t)*(C w)*Z.Q*Z.p0^2 - 2*X^5*(C t)*Z.Q*Z.p0^2 + 2*X^5*(C w)*Z.P^2*Z.Q - 2*X^5*(C w)*Z.P*Z.Q*Z.P1 - X^5*(C w)*Z.Q*Z.p0^2 + X^5*Z.Q*Z.p0^2 - 3*X^4*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 + 3*X^4*(C t)^2*Z.P*Z.Ph*Z.p0^2 + 6*X^4*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 - 6*X^4*(C t)*Z.P*Z.Ph*Z.p0^2 - 2*X^4*(C w)^2*Z.P^2*Z.Q^2 - 3*X^4*(C w)*Z.P*Z.Ph*Z.p0^2 + X^4*Z.P^2 + 3*X^4*Z.P*Z.Ph*Z.p0^2 - 2*X^4*Z.P*Z.P1 + X^4*Z.P1^2 + 2*X^3*(C t)^2*(C w)*Z.Q*Z.p0^2 - 2*X^3*(C t)^2*Z.Q*Z.p0^2 - 4*X^3*(C t)*(C w)*Z.Q*Z.p0^2 + 4*X^3*(C t)*Z.Q*Z.p0^2 - 2*X^3*(C w)*Z.P^2*Z.Q + 4*X^3*(C w)*Z.P*Z.Q*Z.P1 + 2*X^3*(C w)*Z.Q*Z.p0^2 - 2*X^3*Z.Q*Z.p0^2 + X^2*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 - X^2*(C t)^2*Z.P*Z.Ph*Z.p0^2 - 2*X^2*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 + 2*X^2*(C t)*Z.P*Z.Ph*Z.p0^2 + X^2*(C w)^2*Z.P^2*Z.Q^2 + X^2*(C w)*Z.P*Z.Ph*Z.p0^2 - X^2*Z.P*Z.Ph*Z.p0^2 + 2*X^2*Z.P*Z.P1 - 2*X^2*Z.P1^2 - X*(C t)^2*(C w)*Z.Q*Z.p0^2 + X*(C t)^2*Z.Q*Z.p0^2 + 2*X*(C t)*(C w)*Z.Q*Z.p0^2 - 2*X*(C t)*Z.Q*Z.p0^2 - 2*X*(C w)*Z.P*Z.Q*Z.P1 - X*(C w)*Z.Q*Z.p0^2 + X*Z.Q*Z.p0^2 + Z.P1^2) = 0)
    (hE1 : (-X^5*(C t)^2*(C w)*Z.p0*Z.q0 + X^5*(C t)^2*Z.p0*Z.q0 + 2*X^5*(C t)*(C w)*Z.p0*Z.q0 - 2*X^5*(C t)*Z.p0*Z.q0 - X^5*(C w)*Z.p0*Z.q0 + X^5*Z.p0*Z.q0 + 2*X^3*(C t)^2*(C w)*Z.p0*Z.q0 - 2*X^3*(C t)^2*Z.p0*Z.q0 - 4*X^3*(C t)*(C w)*Z.p0*Z.q0 + 4*X^3*(C t)*Z.p0*Z.q0 - X^3*(C w)*Z.P*Z.Q + 2*X^3*(C w)*Z.p0*Z.q0 - 2*X^3*Z.p0*Z.q0 - X^2*Z.P + X^2*Z.P1 - X*(C t)^2*(C w)*Z.p0*Z.q0 + X*(C t)^2*Z.p0*Z.q0 + 2*X*(C t)*(C w)*Z.p0*Z.q0 - 2*X*(C t)*Z.p0*Z.q0 + X*(C w)*Z.P*Z.Q - X*(C w)*Z.p0*Z.q0 + X*Z.p0*Z.q0 - Z.P1) = 0) (hE2 : (-X^5*(C t)^2*(C w)*Z.q0^2 + X^5*(C t)^2*Z.q0^2 + 2*X^5*(C t)*(C w)*Z.q0^2 - 2*X^5*(C t)*Z.q0^2 - X^5*(C w)*Z.q0^2 + X^5*Z.q0^2 + 2*X^3*(C t)^2*(C w)*Z.q0^2 - 2*X^3*(C t)^2*Z.q0^2 - 4*X^3*(C t)*(C w)*Z.q0^2 + 4*X^3*(C t)*Z.q0^2 + 2*X^3*(C w)*Z.q0^2 + X^3*Z.P*Z.Ph - 2*X^3*Z.q0^2 - X*(C t)^2*(C w)*Z.q0^2 + X*(C t)^2*Z.q0^2 + 2*X*(C t)*(C w)*Z.q0^2 - 2*X*(C t)*Z.q0^2 - X*(C w)*Z.q0^2 - X*Z.P*Z.Ph + X*Z.q0^2 + Z.Q) = 0)
    (hS33 : (X^8*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + X^8*(C w)*Z.P^3*Z.Ph^2 + X^7*(C w)*Z.P^2*Z.Ph*Z.Q - 2*X^7*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 - X^6*(C t)*Z.P^2*Z.Ph - 3*X^6*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 - 3*X^6*(C w)*Z.P^3*Z.Ph^2 + X^6*Z.Ph*Z.P1^2 - X^5*(C w)*Z.P^2*Z.Ph*Z.Q + 6*X^5*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 + 2*X^4*(C t)*Z.P^2*Z.Ph + 3*X^4*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + 3*X^4*(C w)*Z.P^3*Z.Ph^2 - X^4*(C w)*Z.P*Z.Q^2 - X^4*Z.P^2*Z.Ph - 3*X^4*Z.Ph*Z.P1^2 - X^3*(C t)*Z.P*Z.Q - X^3*(C w)*Z.P^2*Z.Ph*Z.Q - 6*X^3*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 - X^3*Z.P*Z.Q + 2*X^3*Z.Q*Z.P1 - X^2*(C t)*Z.P^2*Z.Ph - X^2*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 - X^2*(C w)*Z.P^3*Z.Ph^2 + X^2*(C w)*Z.P*Z.Q^2 + X^2*Z.P^2*Z.Ph + 3*X^2*Z.Ph*Z.P1^2 + X*(C t)*Z.P*Z.Q + X*(C w)*Z.P^2*Z.Ph*Z.Q + 2*X*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 - X*Z.P*Z.Q - 2*X*Z.Q*Z.P1 - Z.Ph*Z.P1^2) = 0) :
    ((1 - C w) * (1 - C t) * X * (1 - X ^ 2) * Z.G01 - C w * ((1 - X ^ 2) * Z.P1 + C t * X ^ 2 * Z.P)) = 0 := by
  have main := zG01main Z hE0 hE1 hE2 hS33
  have hc : ((1 - C w) * (1 - C t) ^ 2) ≠ 0 := by
    rw [show ((1 - C w) * (1 - C t) ^ 2) = C ((1 - w) * (1 - t) ^ 2) by simp]
    exact zps_C_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hw1)) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1))))
  have hPs : (Z.P + (1 - X ^ 2) * (Z.P1 - C w * X * Z.P * Z.Q)) ≠ 0 := by
    refine Formal.ne_zero_of_constantCoeff_ne_zero ?_
    have hl := zlow0 Z
    rw [show constantCoeff (Z.P + (1 - X ^ 2) * (Z.P1 - C w * X * Z.P * Z.Q)) = 1 - t by simp [Z.hcP, hl.2.2.2.1, hl.1]]
    exact sub_ne_zero.mpr (Ne.symm ht1)
  have hM : (((1 - C w) * (1 - C t) ^ 2) * X * (1 - X ^ 2) ^ 2 * (-X^3*Z.P*Z.Ph + X*Z.P*Z.Ph - Z.Q) * (C t * C w * X * (Z.P + (1 - X ^ 2) * (Z.P1 - C w * X * Z.P * Z.Q)))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hc X_ne_zero) (pow_ne_zero 2 zps_u_ne_zero))
      (zb_ne_zero Z ht1 hw1)) (mul_ne_zero (mul_ne_zero (mul_ne_zero (zps_C_ne_zero ht0)
      (zps_C_ne_zero hw0)) X_ne_zero) hPs)
  have e := sub_eq_zero.mp ((mul_eq_zero.mp main).resolve_left hM)
  refine eq_zero_of_X_mul_deriv e (fun n => ?_)
  have h12 := zlow12 Z
  by_cases hn : n = 1
  · left; subst hn
    simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_X, coeff_X_pow, Z.hcG01, h12.2.2.2.1]
  · right
    simp
    intro h; apply hn; exact_mod_cast h
end AvgRS
