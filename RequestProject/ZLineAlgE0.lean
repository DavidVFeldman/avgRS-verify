module

public import RequestProject.ZLineAlgE0a
public import RequestProject.ZLineAlgE0b

@[expose] public section

/-!
# The closed system on the line `z + z' = −2`: first integrals, closed forms, and (B4)
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- (E0) `a² = (1−ω)(1−t)² · r u² b · p₀²` where `a = σ + r²P`, `b = r u P P̂ − Q`. -/
lemma zE0 (Z : ZAlgData t w) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hw1 : w ≠ 1)
    (hrel : ZRels Z) :
    (-X^8*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 + X^8*(C t)^2*Z.P*Z.Ph*Z.p0^2 + 2*X^8*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 - 2*X^8*(C t)*Z.P*Z.Ph*Z.p0^2 - X^8*(C w)*Z.P*Z.Ph*Z.p0^2 + X^8*Z.P*Z.Ph*Z.p0^2 + 3*X^6*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 - 3*X^6*(C t)^2*Z.P*Z.Ph*Z.p0^2 - 6*X^6*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 + 6*X^6*(C t)*Z.P*Z.Ph*Z.p0^2 + X^6*(C w)^2*Z.P^2*Z.Q^2 + 3*X^6*(C w)*Z.P*Z.Ph*Z.p0^2 - 3*X^6*Z.P*Z.Ph*Z.p0^2 - X^5*(C t)^2*(C w)*Z.Q*Z.p0^2 + X^5*(C t)^2*Z.Q*Z.p0^2 + 2*X^5*(C t)*(C w)*Z.Q*Z.p0^2 - 2*X^5*(C t)*Z.Q*Z.p0^2 + 2*X^5*(C w)*Z.P^2*Z.Q - 2*X^5*(C w)*Z.P*Z.Q*Z.P1 - X^5*(C w)*Z.Q*Z.p0^2 + X^5*Z.Q*Z.p0^2 - 3*X^4*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 + 3*X^4*(C t)^2*Z.P*Z.Ph*Z.p0^2 + 6*X^4*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 - 6*X^4*(C t)*Z.P*Z.Ph*Z.p0^2 - 2*X^4*(C w)^2*Z.P^2*Z.Q^2 - 3*X^4*(C w)*Z.P*Z.Ph*Z.p0^2 + X^4*Z.P^2 + 3*X^4*Z.P*Z.Ph*Z.p0^2 - 2*X^4*Z.P*Z.P1 + X^4*Z.P1^2 + 2*X^3*(C t)^2*(C w)*Z.Q*Z.p0^2 - 2*X^3*(C t)^2*Z.Q*Z.p0^2 - 4*X^3*(C t)*(C w)*Z.Q*Z.p0^2 + 4*X^3*(C t)*Z.Q*Z.p0^2 - 2*X^3*(C w)*Z.P^2*Z.Q + 4*X^3*(C w)*Z.P*Z.Q*Z.P1 + 2*X^3*(C w)*Z.Q*Z.p0^2 - 2*X^3*Z.Q*Z.p0^2 + X^2*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 - X^2*(C t)^2*Z.P*Z.Ph*Z.p0^2 - 2*X^2*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 + 2*X^2*(C t)*Z.P*Z.Ph*Z.p0^2 + X^2*(C w)^2*Z.P^2*Z.Q^2 + X^2*(C w)*Z.P*Z.Ph*Z.p0^2 - X^2*Z.P*Z.Ph*Z.p0^2 + 2*X^2*Z.P*Z.P1 - 2*X^2*Z.P1^2 - X*(C t)^2*(C w)*Z.Q*Z.p0^2 + X*(C t)^2*Z.Q*Z.p0^2 + 2*X*(C t)*(C w)*Z.Q*Z.p0^2 - 2*X*(C t)*Z.Q*Z.p0^2 - 2*X*(C w)*Z.P*Z.Q*Z.P1 - X*(C w)*Z.Q*Z.p0^2 + X*Z.Q*Z.p0^2 + Z.P1^2) = 0 := by
  have main := zE0main Z (zT2 Z ht0 ht1 hrel)
  have hlow := zlow0 Z
  have hab := zlowab Z
  obtain ⟨P, Ph, Q, P1, Ph1, Q1, Qh1, p0, q0, p1, q1, G00, G01, G10, G11, D, DZ, hP, hPh, hQ, hQ1,
    hQh1, hP1, hPh1, hp0, hq0, hp1, hG00, hG01, hG10, hG11, hD, hDZ, hR2, hL0, hF1, hF2, hcP, hcPh,
    hP1X, hPh1X, hcp0, hcG00, hcG11, hcG01, hcG10, hcD⟩ := Z
  dsimp only at *
  set T : ℚ⟦X⟧ := C t with hT
  set W : ℚ⟦X⟧ := C w with hW
  have dT : d⁄dX ℚ T = 0 := derivative_C t
  have dW : d⁄dX ℚ W = 0 := derivative_C w
  obtain ⟨cQ, cQ1, cQh1, cP1, cPh1⟩ := hlow
  obtain ⟨a', b', ha', hb', ha0, hb0⟩ := hab
  have ea : (X^3*W*P*Q + X^2*P - X^2*P1 - X*W*P*Q + P1) = X ^ 2 * a' := by rw [← ha']; ring
  have eb : (-X^3*P*Ph + X*P*Ph - Q) = X ^ 3 * b' := by rw [← hb']; ring
  have eV : (-X^8*P*Ph + 3*X^6*P*Ph - X^5*Q - 3*X^4*P*Ph + 2*X^3*Q + X^2*P*Ph - X*Q) = X ^ 4 * ((1 - X ^ 2) ^ 2 * b') := by
    rw [show (-X^8*P*Ph + 3*X^6*P*Ph - X^5*Q - 3*X^4*P*Ph + 2*X^3*Q + X^2*P*Ph - X*Q) = X * (1 - X ^ 2) ^ 2 * (X * (1 - X ^ 2) * P * Ph - Q) by ring, hb']; ring
  have eh : (-X^8*T^2*W*P*Ph*p0^2 + X^8*T^2*P*Ph*p0^2 + 2*X^8*T*W*P*Ph*p0^2 - 2*X^8*T*P*Ph*p0^2 - X^8*W*P*Ph*p0^2 + X^8*P*Ph*p0^2 + 3*X^6*T^2*W*P*Ph*p0^2 - 3*X^6*T^2*P*Ph*p0^2 - 6*X^6*T*W*P*Ph*p0^2 + 6*X^6*T*P*Ph*p0^2 + X^6*W^2*P^2*Q^2 + 3*X^6*W*P*Ph*p0^2 - 3*X^6*P*Ph*p0^2 - X^5*T^2*W*Q*p0^2 + X^5*T^2*Q*p0^2 + 2*X^5*T*W*Q*p0^2 - 2*X^5*T*Q*p0^2 + 2*X^5*W*P^2*Q - 2*X^5*W*P*Q*P1 - X^5*W*Q*p0^2 + X^5*Q*p0^2 - 3*X^4*T^2*W*P*Ph*p0^2 + 3*X^4*T^2*P*Ph*p0^2 + 6*X^4*T*W*P*Ph*p0^2 - 6*X^4*T*P*Ph*p0^2 - 2*X^4*W^2*P^2*Q^2 - 3*X^4*W*P*Ph*p0^2 + X^4*P^2 + 3*X^4*P*Ph*p0^2 - 2*X^4*P*P1 + X^4*P1^2 + 2*X^3*T^2*W*Q*p0^2 - 2*X^3*T^2*Q*p0^2 - 4*X^3*T*W*Q*p0^2 + 4*X^3*T*Q*p0^2 - 2*X^3*W*P^2*Q + 4*X^3*W*P*Q*P1 + 2*X^3*W*Q*p0^2 - 2*X^3*Q*p0^2 + X^2*T^2*W*P*Ph*p0^2 - X^2*T^2*P*Ph*p0^2 - 2*X^2*T*W*P*Ph*p0^2 + 2*X^2*T*P*Ph*p0^2 + X^2*W^2*P^2*Q^2 + X^2*W*P*Ph*p0^2 - X^2*P*Ph*p0^2 + 2*X^2*P*P1 - 2*X^2*P1^2 - X*T^2*W*Q*p0^2 + X*T^2*Q*p0^2 + 2*X*T*W*Q*p0^2 - 2*X*T*Q*p0^2 - 2*X*W*P*Q*P1 - X*W*Q*p0^2 + X*Q*p0^2 + P1^2) = X ^ 4 * (a' ^ 2 - (1 - W) * (1 - T) ^ 2 * (1 - X ^ 2) ^ 2 * b' * p0 ^ 2) := by
    have : (-X^8*T^2*W*P*Ph*p0^2 + X^8*T^2*P*Ph*p0^2 + 2*X^8*T*W*P*Ph*p0^2 - 2*X^8*T*P*Ph*p0^2 - X^8*W*P*Ph*p0^2 + X^8*P*Ph*p0^2 + 3*X^6*T^2*W*P*Ph*p0^2 - 3*X^6*T^2*P*Ph*p0^2 - 6*X^6*T*W*P*Ph*p0^2 + 6*X^6*T*P*Ph*p0^2 + X^6*W^2*P^2*Q^2 + 3*X^6*W*P*Ph*p0^2 - 3*X^6*P*Ph*p0^2 - X^5*T^2*W*Q*p0^2 + X^5*T^2*Q*p0^2 + 2*X^5*T*W*Q*p0^2 - 2*X^5*T*Q*p0^2 + 2*X^5*W*P^2*Q - 2*X^5*W*P*Q*P1 - X^5*W*Q*p0^2 + X^5*Q*p0^2 - 3*X^4*T^2*W*P*Ph*p0^2 + 3*X^4*T^2*P*Ph*p0^2 + 6*X^4*T*W*P*Ph*p0^2 - 6*X^4*T*P*Ph*p0^2 - 2*X^4*W^2*P^2*Q^2 - 3*X^4*W*P*Ph*p0^2 + X^4*P^2 + 3*X^4*P*Ph*p0^2 - 2*X^4*P*P1 + X^4*P1^2 + 2*X^3*T^2*W*Q*p0^2 - 2*X^3*T^2*Q*p0^2 - 4*X^3*T*W*Q*p0^2 + 4*X^3*T*Q*p0^2 - 2*X^3*W*P^2*Q + 4*X^3*W*P*Q*P1 + 2*X^3*W*Q*p0^2 - 2*X^3*Q*p0^2 + X^2*T^2*W*P*Ph*p0^2 - X^2*T^2*P*Ph*p0^2 - 2*X^2*T*W*P*Ph*p0^2 + 2*X^2*T*P*Ph*p0^2 + X^2*W^2*P^2*Q^2 + X^2*W*P*Ph*p0^2 - X^2*P*Ph*p0^2 + 2*X^2*P*P1 - 2*X^2*P1^2 - X*T^2*W*Q*p0^2 + X*T^2*Q*p0^2 + 2*X*T*W*Q*p0^2 - 2*X*T*Q*p0^2 - 2*X*W*P*Q*P1 - X*W*Q*p0^2 + X*Q*p0^2 + P1^2) = ((1 - X ^ 2) * (P1 - W * X * P * Q) + X ^ 2 * P) ^ 2 - (1 - W) * (1 - T) ^ 2 * X * (1 - X ^ 2) ^ 2 * (X * (1 - X ^ 2) * P * Ph - Q) * p0 ^ 2 := by ring
    rw [this, ha', hb']; ring
  have e1 : (1 - X ^ 2) * (X^3*W*P*Q + X^2*P - X^2*P1 - X*W*P*Q + P1) * (-X^8*P*Ph + 3*X^6*P*Ph - X^5*Q - 3*X^4*P*Ph + 2*X^3*Q + X^2*P*Ph - X*Q) = X ^ 6 * ((1 - X ^ 2) ^ 3 * a' * b') := by
    rw [ea, eV]; ring
  have e2 : (X^3*W*P*Q + X^2*P - X^2*P1 - X*W*P*Q + P1) * (X * (1 - X ^ 2) * d⁄dX ℚ (-X^8*P*Ph + 3*X^6*P*Ph - X^5*Q - 3*X^4*P*Ph + 2*X^3*Q + X^2*P*Ph - X*Q)) - 4 * W * P * (-X^3*P*Ph + X*P*Ph - Q) * X * (1 - X ^ 2) * (-X^8*P*Ph + 3*X^6*P*Ph - X^5*Q - 3*X^4*P*Ph + 2*X^3*Q + X^2*P*Ph - X*Q)
      = X ^ 6 * (a' * (4 * (1 - X ^ 2) ^ 3 * b' + X * (1 - X ^ 2) * d⁄dX ℚ ((1 - X ^ 2) ^ 2 * b'))
        - 4 * W * P * X ^ 2 * (1 - X ^ 2) ^ 3 * b' ^ 2) := by
    rw [ea, eb, eV]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, derivative_X]
    ring
  rw [e1, e2, eh] at main
  have hX6 : (X : ℚ⟦X⟧) ^ 6 ≠ 0 := pow_ne_zero 6 X_ne_zero
  set H := X ^ 4 * (a' ^ 2 - (1 - W) * (1 - T) ^ 2 * (1 - X ^ 2) ^ 2 * b' * p0 ^ 2) with hH
  have main2 : X * ((1 - X ^ 2) ^ 3 * a' * b') * d⁄dX ℚ H = (a' * (4 * (1 - X ^ 2) ^ 3 * b' + X * (1 - X ^ 2) * d⁄dX ℚ ((1 - X ^ 2) ^ 2 * b'))
        - 4 * W * P * X ^ 2 * (1 - X ^ 2) ^ 3 * b' ^ 2) * H := by
    apply mul_left_cancel₀ hX6; linear_combination main
  rw [eh]
  refine eq_zero_of_X_mul_deriv main2 fun n => ?_
  have hc : (1 - w) * (1 - t) ^ 2 ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hw1)) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1)))
  by_cases hn : n = 4
  · left; subst hn; rw [hH, coeff_X_pow_mul', if_pos le_rfl]
    simp [ha0, hb0, hcp0, hT, hW]; ring
  · right
    have g0 : constantCoeff ((1 - X ^ 2) ^ 3 * a' * b') = ((1 - w) * (1 - t) ^ 2) ^ 2 := by
      simp [ha0, hb0, map_ofNat]; ring
    have k0 : constantCoeff (a' * (4 * (1 - X ^ 2) ^ 3 * b' + X * (1 - X ^ 2) * d⁄dX ℚ ((1 - X ^ 2) ^ 2 * b'))
        - 4 * W * P * X ^ 2 * (1 - X ^ 2) ^ 3 * b' ^ 2) = 4 * ((1 - w) * (1 - t) ^ 2) ^ 2 := by
      simp [ha0, hb0, map_ofNat]; ring
    rw [g0, k0]
    intro h
    apply hn
    have : ((n : ℚ) - 4) * ((1 - w) * (1 - t) ^ 2) ^ 2 = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact_mod_cast (sub_eq_zero.mp h')
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h') hc
end AvgRS
