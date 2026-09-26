module

public import RequestProject.ZLineAlgE12

@[expose] public section

/-!
# The closed system on the line `z + z' = −2`: first integrals, closed forms, and (B4)
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

set_option maxHeartbeats 0
set_option maxRecDepth 20000

lemma zG00main (Z : ZAlgData t w) (hE1 : (-X^5*(C t)^2*(C w)*Z.p0*Z.q0 + X^5*(C t)^2*Z.p0*Z.q0 + 2*X^5*(C t)*(C w)*Z.p0*Z.q0 - 2*X^5*(C t)*Z.p0*Z.q0 - X^5*(C w)*Z.p0*Z.q0 + X^5*Z.p0*Z.q0 + 2*X^3*(C t)^2*(C w)*Z.p0*Z.q0 - 2*X^3*(C t)^2*Z.p0*Z.q0 - 4*X^3*(C t)*(C w)*Z.p0*Z.q0 + 4*X^3*(C t)*Z.p0*Z.q0 - X^3*(C w)*Z.P*Z.Q + 2*X^3*(C w)*Z.p0*Z.q0 - 2*X^3*Z.p0*Z.q0 - X^2*Z.P + X^2*Z.P1 - X*(C t)^2*(C w)*Z.p0*Z.q0 + X*(C t)^2*Z.p0*Z.q0 + 2*X*(C t)*(C w)*Z.p0*Z.q0 - 2*X*(C t)*Z.p0*Z.q0 + X*(C w)*Z.P*Z.Q - X*(C w)*Z.p0*Z.q0 + X*Z.p0*Z.q0 - Z.P1) = 0) :
    (((1 - C w) * (1 - C t) ^ 2) * X * (1 - X ^ 2) ^ 2) * (X * (1 - X ^ 2) * d⁄dX ℚ ((1 - C w) * (1 - C t) * (1 - X ^ 2) * Z.G00 - (1 - C t) * (1 - X ^ 2) + C w * Z.P) - (-(2 * X ^ 2)) * ((1 - C w) * (1 - C t) * (1 - X ^ 2) * Z.G00 - (1 - C t) * (1 - X ^ 2) + C w * Z.P)) = 0 := by
  obtain ⟨P, Ph, Q, P1, Ph1, Q1, Qh1, p0, q0, p1, q1, G00, G01, G10, G11, D, DZ, hP, hPh, hQ, hQ1,
    hQh1, hP1, hPh1, hp0, hq0, hp1, hG00, hG01, hG10, hG11, hD, hDZ, hR2, hL0, hF1, hF2, hcP, hcPh,
    hP1X, hPh1X, hcp0, hcG00, hcG11, hcG01, hcG10, hcD⟩ := Z
  dsimp only at *
  set T : ℚ⟦X⟧ := C t with hT
  set W : ℚ⟦X⟧ := C w with hW
  have dT : d⁄dX ℚ T = 0 := derivative_C t
  have dW : d⁄dX ℚ W = 0 := derivative_C w
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, derivative_C, derivative_X, Derivation.map_one_eq_zero, deriv_ofNat', Nat.cast_ofNat, map_zero, dT, dW]
  linear_combination (X^7*T^2*W^2 - X^7*T^2*W - 2*X^7*T*W^2 + 2*X^7*T*W + X^7*W^2 - X^7*W - 3*X^5*T^2*W^2 + 3*X^5*T^2*W + 6*X^5*T*W^2 - 6*X^5*T*W - 3*X^5*W^2 + 3*X^5*W + 3*X^3*T^2*W^2 - 3*X^3*T^2*W - 6*X^3*T*W^2 + 6*X^3*T*W + 3*X^3*W^2 - 3*X^3*W - X*T^2*W^2 + X*T^2*W + 2*X*T*W^2 - 2*X*T*W - X*W^2 + X*W) * hP + (-X^10*T^3*W^2 + 2*X^10*T^3*W - X^10*T^3 + 3*X^10*T^2*W^2 - 6*X^10*T^2*W + 3*X^10*T^2 - 3*X^10*T*W^2 + 6*X^10*T*W - 3*X^10*T + X^10*W^2 - 2*X^10*W + X^10 + 4*X^8*T^3*W^2 - 8*X^8*T^3*W + 4*X^8*T^3 - 12*X^8*T^2*W^2 + 24*X^8*T^2*W - 12*X^8*T^2 + 12*X^8*T*W^2 - 24*X^8*T*W + 12*X^8*T - 4*X^8*W^2 + 8*X^8*W - 4*X^8 - 6*X^6*T^3*W^2 + 12*X^6*T^3*W - 6*X^6*T^3 + 18*X^6*T^2*W^2 - 36*X^6*T^2*W + 18*X^6*T^2 - 18*X^6*T*W^2 + 36*X^6*T*W - 18*X^6*T + 6*X^6*W^2 - 12*X^6*W + 6*X^6 + 4*X^4*T^3*W^2 - 8*X^4*T^3*W + 4*X^4*T^3 - 12*X^4*T^2*W^2 + 24*X^4*T^2*W - 12*X^4*T^2 + 12*X^4*T*W^2 - 24*X^4*T*W + 12*X^4*T - 4*X^4*W^2 + 8*X^4*W - 4*X^4 - X^2*T^3*W^2 + 2*X^2*T^3*W - X^2*T^3 + 3*X^2*T^2*W^2 - 6*X^2*T^2*W + 3*X^2*T^2 - 3*X^2*T*W^2 + 6*X^2*T*W - 3*X^2*T + X^2*W^2 - 2*X^2*W + X^2) * hG00 + (2*X^5*T^2*W^2 - 2*X^5*T^2*W - 4*X^5*T*W^2 + 4*X^5*T*W + 2*X^5*W^2 - 2*X^5*W - 4*X^3*T^2*W^2 + 4*X^3*T^2*W + 8*X^3*T*W^2 - 8*X^3*T*W - 4*X^3*W^2 + 4*X^3*W + 2*X*T^2*W^2 - 2*X*T^2*W - 4*X*T*W^2 + 4*X*T*W + 2*X*W^2 - 2*X*W) * hE1

/-- (I4) `(1−ω)(1−t) u G₀₀ = (1−t) u − ω P`. -/
lemma zG00 (Z : ZAlgData t w) (ht1 : t ≠ 1) (hw1 : w ≠ 1) (hE1 : (-X^5*(C t)^2*(C w)*Z.p0*Z.q0 + X^5*(C t)^2*Z.p0*Z.q0 + 2*X^5*(C t)*(C w)*Z.p0*Z.q0 - 2*X^5*(C t)*Z.p0*Z.q0 - X^5*(C w)*Z.p0*Z.q0 + X^5*Z.p0*Z.q0 + 2*X^3*(C t)^2*(C w)*Z.p0*Z.q0 - 2*X^3*(C t)^2*Z.p0*Z.q0 - 4*X^3*(C t)*(C w)*Z.p0*Z.q0 + 4*X^3*(C t)*Z.p0*Z.q0 - X^3*(C w)*Z.P*Z.Q + 2*X^3*(C w)*Z.p0*Z.q0 - 2*X^3*Z.p0*Z.q0 - X^2*Z.P + X^2*Z.P1 - X*(C t)^2*(C w)*Z.p0*Z.q0 + X*(C t)^2*Z.p0*Z.q0 + 2*X*(C t)*(C w)*Z.p0*Z.q0 - 2*X*(C t)*Z.p0*Z.q0 + X*(C w)*Z.P*Z.Q - X*(C w)*Z.p0*Z.q0 + X*Z.p0*Z.q0 - Z.P1) = 0) :
    ((1 - C w) * (1 - C t) * (1 - X ^ 2) * Z.G00 - (1 - C t) * (1 - X ^ 2) + C w * Z.P) = 0 := by
  have main := zG00main Z hE1
  have hc : ((1 - C w) * (1 - C t) ^ 2) ≠ 0 := by
    rw [show ((1 - C w) * (1 - C t) ^ 2) = C ((1 - w) * (1 - t) ^ 2) by simp]
    exact zps_C_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hw1)) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1))))
  have hPs : (Z.P + (1 - X ^ 2) * (Z.P1 - C w * X * Z.P * Z.Q)) ≠ 0 := by
    refine Formal.ne_zero_of_constantCoeff_ne_zero ?_
    have hl := zlow0 Z
    rw [show constantCoeff (Z.P + (1 - X ^ 2) * (Z.P1 - C w * X * Z.P * Z.Q)) = 1 - t by simp [Z.hcP, hl.2.2.2.1, hl.1]]
    exact sub_ne_zero.mpr (Ne.symm ht1)
  have hM : (((1 - C w) * (1 - C t) ^ 2) * X * (1 - X ^ 2) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc X_ne_zero) (pow_ne_zero 2 zps_u_ne_zero)
  have e := sub_eq_zero.mp ((mul_eq_zero.mp main).resolve_left hM)
  refine eq_zero_of_X_mul_deriv e (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    rw [coeff_zero_eq_constantCoeff_apply]
    simp [Z.hcG00, Z.hcP]; ring
  · right
    simp
    exact hn.ne'
end AvgRS
