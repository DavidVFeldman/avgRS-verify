module

public import RequestProject.ZLineAlgBase

@[expose] public section

/-!
# The closed system on the line `z + z' = −2`: first integrals, closed forms, and (B4)
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

set_option maxHeartbeats 0
set_option maxRecDepth 20000

lemma zS0 (Z : ZAlgData t w) (ht1 : t ≠ 1) :
    ((X : ℚ⟦X⟧)^(6:ℕ)*(C w)^(2:ℕ)*Z.P*Z.Ph*Z.Q^(2:ℕ) + (X : ℚ⟦X⟧)^(6:ℕ)*(C w)*Z.P^(2:ℕ)*Z.Ph^(2:ℕ) - (X : ℚ⟦X⟧)^(5:ℕ)*(C w)*Z.P*Z.Ph*Z.Q - (X : ℚ⟦X⟧)^(5:ℕ)*(C w)*Z.P*Z.Q*Z.Ph1 - (X : ℚ⟦X⟧)^(5:ℕ)*(C w)*Z.Ph*Z.Q*Z.P1 - (X : ℚ⟦X⟧)^(4:ℕ)*(C t)*Z.P*Z.Ph - 2*(X : ℚ⟦X⟧)^(4:ℕ)*(C w)^(2:ℕ)*Z.P*Z.Ph*Z.Q^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(4:ℕ)*(C w)*Z.P^(2:ℕ)*Z.Ph^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(4:ℕ)*Z.P*Z.Ph - (X : ℚ⟦X⟧)^(4:ℕ)*Z.P*Z.Ph1 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*Z.Ph*Z.P1 + (X : ℚ⟦X⟧)^(4:ℕ)*Z.P1*Z.Ph1 + 2*(X : ℚ⟦X⟧)^(3:ℕ)*(C w)*Z.P*Z.Ph*Z.Q + 2*(X : ℚ⟦X⟧)^(3:ℕ)*(C w)*Z.P*Z.Q*Z.Ph1 + 2*(X : ℚ⟦X⟧)^(3:ℕ)*(C w)*Z.Ph*Z.Q*Z.P1 + (X : ℚ⟦X⟧)^(2:ℕ)*(C t)*Z.P*Z.Ph + (X : ℚ⟦X⟧)^(2:ℕ)*(C w)^(2:ℕ)*Z.P*Z.Ph*Z.Q^(2:ℕ) + (X : ℚ⟦X⟧)^(2:ℕ)*(C w)*Z.P^(2:ℕ)*Z.Ph^(2:ℕ) + (X : ℚ⟦X⟧)^(2:ℕ)*(C w)*Z.Q^(2:ℕ) - (X : ℚ⟦X⟧)^(2:ℕ)*Z.P*Z.Ph + (X : ℚ⟦X⟧)^(2:ℕ)*Z.P*Z.Ph1 - 3*(X : ℚ⟦X⟧)^(2:ℕ)*Z.Ph*Z.P1 - 2*(X : ℚ⟦X⟧)^(2:ℕ)*Z.P1*Z.Ph1 - (X : ℚ⟦X⟧)*(C t)*Z.Q - (X : ℚ⟦X⟧)*(C w)*Z.P*Z.Ph*Z.Q - (X : ℚ⟦X⟧)*(C w)*Z.P*Z.Q*Z.Ph1 - (X : ℚ⟦X⟧)*(C w)*Z.Ph*Z.Q*Z.P1 + (X : ℚ⟦X⟧)*Z.Q + Z.P1*Z.Ph1) = 0 := by
  obtain ⟨P, Ph, Q, P1, Ph1, Q1, Qh1, p0, q0, p1, q1, G00, G01, G10, G11, D, DZ, hP, hPh, hQ, hQ1,
    hQh1, hP1, hPh1, hp0, hq0, hp1, hG00, hG01, hG10, hG11, hD, hDZ, hR2, hL0, hF1, hF2, hcP, hcPh,
    hP1X, hPh1X, hcp0, hcG00, hcG11, hcG01, hcG10, hcD⟩ := Z
  dsimp only at *
  set T : ℚ⟦X⟧ := C t with hT
  set W : ℚ⟦X⟧ := C w with hW
  have dT : d⁄dX ℚ T = 0 := derivative_C t
  have dW : d⁄dX ℚ W = 0 := derivative_C w
  have hd : d⁄dX ℚ (X^3*W*P*Q*q0 + X^3*P*Ph*p0 + X^2*P*q0 - X^2*P1*q0 - X*W*P*Q*q0 - X*P*Ph*p0 + Q*p0 + P1*q0) = 0 := by
    rw [show (X^3*W*P*Q*q0 + X^3*P*Ph*p0 + X^2*P*q0 - X^2*P1*q0 - X*W*P*Q*q0 - X*P*Ph*p0 + Q*p0 + P1*q0) = 0 by linear_combination hL0]; exact map_zero _
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, derivative_C, derivative_X, Derivation.map_one_eq_zero, deriv_ofNat', Nat.cast_ofNat, map_zero, dT, dW] at hd
  have key : (2*(X : ℚ⟦X⟧)^(3:ℕ)*P - 2*(X : ℚ⟦X⟧)*P) * ((X : ℚ⟦X⟧)^(6:ℕ)*W^(2:ℕ)*P*Ph*Q^(2:ℕ) + (X : ℚ⟦X⟧)^(6:ℕ)*W*P^(2:ℕ)*Ph^(2:ℕ) - (X : ℚ⟦X⟧)^(5:ℕ)*W*P*Ph*Q - (X : ℚ⟦X⟧)^(5:ℕ)*W*P*Q*Ph1 - (X : ℚ⟦X⟧)^(5:ℕ)*W*Ph*Q*P1 - (X : ℚ⟦X⟧)^(4:ℕ)*T*P*Ph - 2*(X : ℚ⟦X⟧)^(4:ℕ)*W^(2:ℕ)*P*Ph*Q^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(4:ℕ)*W*P^(2:ℕ)*Ph^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(4:ℕ)*P*Ph - (X : ℚ⟦X⟧)^(4:ℕ)*P*Ph1 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*Ph*P1 + (X : ℚ⟦X⟧)^(4:ℕ)*P1*Ph1 + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Ph*Q + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Q*Ph1 + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*Ph*Q*P1 + (X : ℚ⟦X⟧)^(2:ℕ)*T*P*Ph + (X : ℚ⟦X⟧)^(2:ℕ)*W^(2:ℕ)*P*Ph*Q^(2:ℕ) + (X : ℚ⟦X⟧)^(2:ℕ)*W*P^(2:ℕ)*Ph^(2:ℕ) + (X : ℚ⟦X⟧)^(2:ℕ)*W*Q^(2:ℕ) - (X : ℚ⟦X⟧)^(2:ℕ)*P*Ph + (X : ℚ⟦X⟧)^(2:ℕ)*P*Ph1 - 3*(X : ℚ⟦X⟧)^(2:ℕ)*Ph*P1 - 2*(X : ℚ⟦X⟧)^(2:ℕ)*P1*Ph1 - (X : ℚ⟦X⟧)*T*Q - (X : ℚ⟦X⟧)*W*P*Ph*Q - (X : ℚ⟦X⟧)*W*P*Q*Ph1 - (X : ℚ⟦X⟧)*W*Ph*Q*P1 + (X : ℚ⟦X⟧)*Q + P1*Ph1) * p0 = 0 := by
    linear_combination (norm := ring_refl) (-(X : ℚ⟦X⟧)^(6:ℕ)*W*P*Q - (X : ℚ⟦X⟧)^(5:ℕ)*P + (X : ℚ⟦X⟧)^(5:ℕ)*P1 + 2*(X : ℚ⟦X⟧)^(4:ℕ)*W*P*Q + (X : ℚ⟦X⟧)^(3:ℕ)*P - 2*(X : ℚ⟦X⟧)^(3:ℕ)*P1 - (X : ℚ⟦X⟧)^(2:ℕ)*W*P*Q + (X : ℚ⟦X⟧)*P1) * hd + ((X : ℚ⟦X⟧)^(8:ℕ)*W^(2:ℕ)*P*Q^(2:ℕ)*q0 + (X : ℚ⟦X⟧)^(8:ℕ)*W*P*Ph*Q*p0 + 2*(X : ℚ⟦X⟧)^(7:ℕ)*W*P*Q*q0 - (X : ℚ⟦X⟧)^(7:ℕ)*W*Q*P1*q0 + (X : ℚ⟦X⟧)^(7:ℕ)*P*Ph*p0 - (X : ℚ⟦X⟧)^(7:ℕ)*Ph*P1*p0 - 3*(X : ℚ⟦X⟧)^(6:ℕ)*W^(2:ℕ)*P*Q^(2:ℕ)*q0 - 3*(X : ℚ⟦X⟧)^(6:ℕ)*W*P*Ph*Q*p0 + (X : ℚ⟦X⟧)^(6:ℕ)*P*q0 - (X : ℚ⟦X⟧)^(6:ℕ)*P1*q0 - 4*(X : ℚ⟦X⟧)^(5:ℕ)*W*P*Q*q0 + 3*(X : ℚ⟦X⟧)^(5:ℕ)*W*Q*P1*q0 - 2*(X : ℚ⟦X⟧)^(5:ℕ)*P*Ph*p0 + 3*(X : ℚ⟦X⟧)^(5:ℕ)*Ph*P1*p0 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*W^(2:ℕ)*P*Q^(2:ℕ)*q0 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*W*P*Ph*Q*p0 - (X : ℚ⟦X⟧)^(4:ℕ)*P*q0 + 2*(X : ℚ⟦X⟧)^(4:ℕ)*P1*q0 + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Q*q0 - 3*(X : ℚ⟦X⟧)^(3:ℕ)*W*Q*P1*q0 + (X : ℚ⟦X⟧)^(3:ℕ)*P*Ph*p0 - 3*(X : ℚ⟦X⟧)^(3:ℕ)*Ph*P1*p0 - (X : ℚ⟦X⟧)^(2:ℕ)*W^(2:ℕ)*P*Q^(2:ℕ)*q0 - (X : ℚ⟦X⟧)^(2:ℕ)*W*P*Ph*Q*p0 - (X : ℚ⟦X⟧)^(2:ℕ)*P1*q0 + (X : ℚ⟦X⟧)*W*Q*P1*q0 + (X : ℚ⟦X⟧)*Ph*P1*p0) * hP + ((X : ℚ⟦X⟧)^(8:ℕ)*W*P^(2:ℕ)*Q*p0 + (X : ℚ⟦X⟧)^(7:ℕ)*P^(2:ℕ)*p0 - (X : ℚ⟦X⟧)^(7:ℕ)*P*P1*p0 - 3*(X : ℚ⟦X⟧)^(6:ℕ)*W*P^(2:ℕ)*Q*p0 - 2*(X : ℚ⟦X⟧)^(5:ℕ)*P^(2:ℕ)*p0 + 3*(X : ℚ⟦X⟧)^(5:ℕ)*P*P1*p0 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*W*P^(2:ℕ)*Q*p0 + (X : ℚ⟦X⟧)^(3:ℕ)*P^(2:ℕ)*p0 - 3*(X : ℚ⟦X⟧)^(3:ℕ)*P*P1*p0 - (X : ℚ⟦X⟧)^(2:ℕ)*W*P^(2:ℕ)*Q*p0 + (X : ℚ⟦X⟧)*P*P1*p0) * hPh + ((X : ℚ⟦X⟧)^(8:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q*q0 + (X : ℚ⟦X⟧)^(7:ℕ)*W*P^(2:ℕ)*q0 - (X : ℚ⟦X⟧)^(7:ℕ)*W*P*P1*q0 - 3*(X : ℚ⟦X⟧)^(6:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q*q0 - 2*(X : ℚ⟦X⟧)^(5:ℕ)*W*P^(2:ℕ)*q0 + (X : ℚ⟦X⟧)^(5:ℕ)*W*P*Q*p0 + 3*(X : ℚ⟦X⟧)^(5:ℕ)*W*P*P1*q0 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q*q0 + (X : ℚ⟦X⟧)^(4:ℕ)*P*p0 - (X : ℚ⟦X⟧)^(4:ℕ)*P1*p0 + (X : ℚ⟦X⟧)^(3:ℕ)*W*P^(2:ℕ)*q0 - 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Q*p0 - 3*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*P1*q0 - (X : ℚ⟦X⟧)^(2:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q*q0 - (X : ℚ⟦X⟧)^(2:ℕ)*P*p0 + 2*(X : ℚ⟦X⟧)^(2:ℕ)*P1*p0 + (X : ℚ⟦X⟧)*W*P*Q*p0 + (X : ℚ⟦X⟧)*W*P*P1*q0 - P1*p0) * hQ + ((X : ℚ⟦X⟧)^(5:ℕ)*W*P*Q*q0 + (X : ℚ⟦X⟧)^(4:ℕ)*P*q0 - (X : ℚ⟦X⟧)^(4:ℕ)*P1*q0 - 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Q*q0 - (X : ℚ⟦X⟧)^(2:ℕ)*P*q0 + 2*(X : ℚ⟦X⟧)^(2:ℕ)*P1*q0 + (X : ℚ⟦X⟧)*W*P*Q*q0 - P1*q0) * hP1 + ((X : ℚ⟦X⟧)^(9:ℕ)*W*P^(2:ℕ)*Ph*Q + (X : ℚ⟦X⟧)^(8:ℕ)*P^(2:ℕ)*Ph - (X : ℚ⟦X⟧)^(8:ℕ)*P*Ph*P1 - 3*(X : ℚ⟦X⟧)^(7:ℕ)*W*P^(2:ℕ)*Ph*Q + (X : ℚ⟦X⟧)^(6:ℕ)*W*P*Q^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(6:ℕ)*P^(2:ℕ)*Ph + 3*(X : ℚ⟦X⟧)^(6:ℕ)*P*Ph*P1 + 3*(X : ℚ⟦X⟧)^(5:ℕ)*W*P^(2:ℕ)*Ph*Q + (X : ℚ⟦X⟧)^(5:ℕ)*P*Q - (X : ℚ⟦X⟧)^(5:ℕ)*Q*P1 - 2*(X : ℚ⟦X⟧)^(4:ℕ)*W*P*Q^(2:ℕ) + (X : ℚ⟦X⟧)^(4:ℕ)*P^(2:ℕ)*Ph - 3*(X : ℚ⟦X⟧)^(4:ℕ)*P*Ph*P1 - (X : ℚ⟦X⟧)^(3:ℕ)*W*P^(2:ℕ)*Ph*Q - (X : ℚ⟦X⟧)^(3:ℕ)*P*Q + 2*(X : ℚ⟦X⟧)^(3:ℕ)*Q*P1 + (X : ℚ⟦X⟧)^(2:ℕ)*W*P*Q^(2:ℕ) + (X : ℚ⟦X⟧)^(2:ℕ)*P*Ph*P1 - (X : ℚ⟦X⟧)*Q*P1) * hp0 + ((X : ℚ⟦X⟧)^(8:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q^(2:ℕ) + 2*(X : ℚ⟦X⟧)^(7:ℕ)*W*P^(2:ℕ)*Q - 2*(X : ℚ⟦X⟧)^(7:ℕ)*W*P*Q*P1 - 3*(X : ℚ⟦X⟧)^(6:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q^(2:ℕ) + (X : ℚ⟦X⟧)^(6:ℕ)*P^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(6:ℕ)*P*P1 + (X : ℚ⟦X⟧)^(6:ℕ)*P1^(2:ℕ) - 4*(X : ℚ⟦X⟧)^(5:ℕ)*W*P^(2:ℕ)*Q + 6*(X : ℚ⟦X⟧)^(5:ℕ)*W*P*Q*P1 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q^(2:ℕ) - (X : ℚ⟦X⟧)^(4:ℕ)*P^(2:ℕ) + 4*(X : ℚ⟦X⟧)^(4:ℕ)*P*P1 - 3*(X : ℚ⟦X⟧)^(4:ℕ)*P1^(2:ℕ) + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P^(2:ℕ)*Q - 6*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Q*P1 - (X : ℚ⟦X⟧)^(2:ℕ)*W^(2:ℕ)*P^(2:ℕ)*Q^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(2:ℕ)*P*P1 + 3*(X : ℚ⟦X⟧)^(2:ℕ)*P1^(2:ℕ) + 2*(X : ℚ⟦X⟧)*W*P*Q*P1 - P1^(2:ℕ)) * hq0 + (2*(X : ℚ⟦X⟧)^(6:ℕ)*W*P^(2:ℕ)*Ph + (X : ℚ⟦X⟧)^(5:ℕ)*W*P*Q - 2*(X : ℚ⟦X⟧)^(4:ℕ)*T*P - 4*(X : ℚ⟦X⟧)^(4:ℕ)*W*P^(2:ℕ)*Ph + (X : ℚ⟦X⟧)^(4:ℕ)*P + (X : ℚ⟦X⟧)^(4:ℕ)*P1 + 2*(X : ℚ⟦X⟧)^(2:ℕ)*T*P + 2*(X : ℚ⟦X⟧)^(2:ℕ)*W*P^(2:ℕ)*Ph - (X : ℚ⟦X⟧)^(2:ℕ)*P - 2*(X : ℚ⟦X⟧)^(2:ℕ)*P1 - (X : ℚ⟦X⟧)*W*P*Q + P1) * hL0
  have hX : (X : ℚ⟦X⟧) ≠ 0 := X_ne_zero
  have hP0 : P ≠ 0 := Formal.ne_zero_of_constantCoeff_ne_zero (by rw [hcP]; exact sub_ne_zero.mpr (Ne.symm ht1))
  have hp00 : p0 ≠ 0 := Formal.ne_zero_of_constantCoeff_ne_zero (by rw [hcp0]; exact one_ne_zero)
  have hu : (1 - X ^ 2 : ℚ⟦X⟧) ≠ 0 := Formal.ne_zero_of_constantCoeff_ne_zero (by simp)
  have h2 : (2 : ℚ⟦X⟧) ≠ 0 := zps_two_ne_zero
  have : (-2 * (X : ℚ⟦X⟧) * P * (1 - (X : ℚ⟦X⟧) ^ 2)) * (((X : ℚ⟦X⟧)^(6:ℕ)*W^(2:ℕ)*P*Ph*Q^(2:ℕ) + (X : ℚ⟦X⟧)^(6:ℕ)*W*P^(2:ℕ)*Ph^(2:ℕ) - (X : ℚ⟦X⟧)^(5:ℕ)*W*P*Ph*Q - (X : ℚ⟦X⟧)^(5:ℕ)*W*P*Q*Ph1 - (X : ℚ⟦X⟧)^(5:ℕ)*W*Ph*Q*P1 - (X : ℚ⟦X⟧)^(4:ℕ)*T*P*Ph - 2*(X : ℚ⟦X⟧)^(4:ℕ)*W^(2:ℕ)*P*Ph*Q^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(4:ℕ)*W*P^(2:ℕ)*Ph^(2:ℕ) - 2*(X : ℚ⟦X⟧)^(4:ℕ)*P*Ph - (X : ℚ⟦X⟧)^(4:ℕ)*P*Ph1 + 3*(X : ℚ⟦X⟧)^(4:ℕ)*Ph*P1 + (X : ℚ⟦X⟧)^(4:ℕ)*P1*Ph1 + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Ph*Q + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*P*Q*Ph1 + 2*(X : ℚ⟦X⟧)^(3:ℕ)*W*Ph*Q*P1 + (X : ℚ⟦X⟧)^(2:ℕ)*T*P*Ph + (X : ℚ⟦X⟧)^(2:ℕ)*W^(2:ℕ)*P*Ph*Q^(2:ℕ) + (X : ℚ⟦X⟧)^(2:ℕ)*W*P^(2:ℕ)*Ph^(2:ℕ) + (X : ℚ⟦X⟧)^(2:ℕ)*W*Q^(2:ℕ) - (X : ℚ⟦X⟧)^(2:ℕ)*P*Ph + (X : ℚ⟦X⟧)^(2:ℕ)*P*Ph1 - 3*(X : ℚ⟦X⟧)^(2:ℕ)*Ph*P1 - 2*(X : ℚ⟦X⟧)^(2:ℕ)*P1*Ph1 - (X : ℚ⟦X⟧)*T*Q - (X : ℚ⟦X⟧)*W*P*Ph*Q - (X : ℚ⟦X⟧)*W*P*Q*Ph1 - (X : ℚ⟦X⟧)*W*Ph*Q*P1 + (X : ℚ⟦X⟧)*Q + P1*Ph1) * p0) = 0 := by linear_combination key
  simpa [hX, hP0, hp00, hu, h2] using this
end AvgRS
