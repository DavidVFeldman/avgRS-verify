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

lemma zR1 (Z : ZAlgData t w) (hR3 : (2*X^4*Z.P*Z.Ph + X^4*Z.P*Z.Ph1 - X^4*Z.Ph*Z.P1 - 2*X^2*Z.P*Z.Ph - 2*X^2*Z.P*Z.Ph1 + 2*X^2*Z.Ph*Z.P1 - 2*X*Z.Q + Z.P*Z.Ph1 - Z.Ph*Z.P1) = 0) :
    (2*X^2*Z.Q - X^2*Z.Q1 + X^2*Z.Qh1 + Z.Q1 - Z.Qh1) = 0 := by
  obtain ⟨P, Ph, Q, P1, Ph1, Q1, Qh1, p0, q0, p1, q1, G00, G01, G10, G11, D, DZ, hP, hPh, hQ, hQ1,
    hQh1, hP1, hPh1, hp0, hq0, hp1, hG00, hG01, hG10, hG11, hD, hDZ, hR2, hL0, hF1, hF2, hcP, hcPh,
    hP1X, hPh1X, hcp0, hcG00, hcG11, hcG01, hcG10, hcD⟩ := Z
  dsimp only at *
  set T : ℚ⟦X⟧ := C t with hT
  set W : ℚ⟦X⟧ := C w with hW
  have dT : d⁄dX ℚ T = 0 := derivative_C t
  have dW : d⁄dX ℚ W = 0 := derivative_C w
  refine eq_zero_of_X_mul_deriv (g := 1 - X ^ 2) (c := -(1 + X ^ 2)) ?_ ?_
  · simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, derivative_C, derivative_X, Derivation.map_one_eq_zero, deriv_ofNat', Nat.cast_ofNat, map_zero, dT, dW]
    linear_combination (-2*X^4 + 2*X^2) * hQ + (X^4 - 2*X^2 + 1) * hQ1 + (-X^4 + 2*X^2 - 1) * hQh1 + (-2*X) * hR3
  · intro n; right
    simp only [map_sub, map_one, map_pow, constantCoeff_X, map_neg, map_add, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, add_zero, mul_one]
    intro h; have := Nat.cast_nonneg (α := ℚ) n; linarith
end AvgRS
