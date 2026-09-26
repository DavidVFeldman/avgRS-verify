module

public import RequestProject.ZLineAlgE0

@[expose] public section

/-!
# The closed system on the line `z + z' = −2`: first integrals, closed forms, and (B4)
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

set_option maxHeartbeats 0
set_option maxRecDepth 20000

lemma za_ne_zero (Z : ZAlgData t w) (ht1 : t ≠ 1) (hw1 : w ≠ 1) :
    (X^3*(C w)*Z.P*Z.Q + X^2*Z.P - X^2*Z.P1 - X*(C w)*Z.P*Z.Q + Z.P1) ≠ 0 := by
  obtain ⟨a', b', ha', hb', ha0, hb0⟩ := zlowab Z
  rw [show (X^3*(C w)*Z.P*Z.Q + X^2*Z.P - X^2*Z.P1 - X*(C w)*Z.P*Z.Q + Z.P1) = ((1 - X ^ 2) * (Z.P1 - C w * X * Z.P * Z.Q) + X ^ 2 * Z.P) by ring, ha']
  refine mul_ne_zero (pow_ne_zero 2 X_ne_zero) (Formal.ne_zero_of_constantCoeff_ne_zero ?_)
  rw [ha0]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hw1)) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1)))

lemma zb_ne_zero (Z : ZAlgData t w) (ht1 : t ≠ 1) (hw1 : w ≠ 1) :
    (-X^3*Z.P*Z.Ph + X*Z.P*Z.Ph - Z.Q) ≠ 0 := by
  obtain ⟨a', b', ha', hb', ha0, hb0⟩ := zlowab Z
  rw [show (-X^3*Z.P*Z.Ph + X*Z.P*Z.Ph - Z.Q) = (X * (1 - X ^ 2) * Z.P * Z.Ph - Z.Q) by ring, hb']
  refine mul_ne_zero (pow_ne_zero 3 X_ne_zero) (Formal.ne_zero_of_constantCoeff_ne_zero ?_)
  rw [hb0]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hw1)) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1)))

lemma zp0_ne_zero (Z : ZAlgData t w) : Z.p0 ≠ 0 :=
  Formal.ne_zero_of_constantCoeff_ne_zero (by rw [Z.hcp0]; exact one_ne_zero)

/-- (E1) `(1−ω)(1−t)² r u² p₀ q₀ = a`. -/
lemma zE1 (Z : ZAlgData t w) (ht1 : t ≠ 1) (hw1 : w ≠ 1) (hE0 : (-X^8*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 + X^8*(C t)^2*Z.P*Z.Ph*Z.p0^2 + 2*X^8*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 - 2*X^8*(C t)*Z.P*Z.Ph*Z.p0^2 - X^8*(C w)*Z.P*Z.Ph*Z.p0^2 + X^8*Z.P*Z.Ph*Z.p0^2 + 3*X^6*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 - 3*X^6*(C t)^2*Z.P*Z.Ph*Z.p0^2 - 6*X^6*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 + 6*X^6*(C t)*Z.P*Z.Ph*Z.p0^2 + X^6*(C w)^2*Z.P^2*Z.Q^2 + 3*X^6*(C w)*Z.P*Z.Ph*Z.p0^2 - 3*X^6*Z.P*Z.Ph*Z.p0^2 - X^5*(C t)^2*(C w)*Z.Q*Z.p0^2 + X^5*(C t)^2*Z.Q*Z.p0^2 + 2*X^5*(C t)*(C w)*Z.Q*Z.p0^2 - 2*X^5*(C t)*Z.Q*Z.p0^2 + 2*X^5*(C w)*Z.P^2*Z.Q - 2*X^5*(C w)*Z.P*Z.Q*Z.P1 - X^5*(C w)*Z.Q*Z.p0^2 + X^5*Z.Q*Z.p0^2 - 3*X^4*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 + 3*X^4*(C t)^2*Z.P*Z.Ph*Z.p0^2 + 6*X^4*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 - 6*X^4*(C t)*Z.P*Z.Ph*Z.p0^2 - 2*X^4*(C w)^2*Z.P^2*Z.Q^2 - 3*X^4*(C w)*Z.P*Z.Ph*Z.p0^2 + X^4*Z.P^2 + 3*X^4*Z.P*Z.Ph*Z.p0^2 - 2*X^4*Z.P*Z.P1 + X^4*Z.P1^2 + 2*X^3*(C t)^2*(C w)*Z.Q*Z.p0^2 - 2*X^3*(C t)^2*Z.Q*Z.p0^2 - 4*X^3*(C t)*(C w)*Z.Q*Z.p0^2 + 4*X^3*(C t)*Z.Q*Z.p0^2 - 2*X^3*(C w)*Z.P^2*Z.Q + 4*X^3*(C w)*Z.P*Z.Q*Z.P1 + 2*X^3*(C w)*Z.Q*Z.p0^2 - 2*X^3*Z.Q*Z.p0^2 + X^2*(C t)^2*(C w)*Z.P*Z.Ph*Z.p0^2 - X^2*(C t)^2*Z.P*Z.Ph*Z.p0^2 - 2*X^2*(C t)*(C w)*Z.P*Z.Ph*Z.p0^2 + 2*X^2*(C t)*Z.P*Z.Ph*Z.p0^2 + X^2*(C w)^2*Z.P^2*Z.Q^2 + X^2*(C w)*Z.P*Z.Ph*Z.p0^2 - X^2*Z.P*Z.Ph*Z.p0^2 + 2*X^2*Z.P*Z.P1 - 2*X^2*Z.P1^2 - X*(C t)^2*(C w)*Z.Q*Z.p0^2 + X*(C t)^2*Z.Q*Z.p0^2 + 2*X*(C t)*(C w)*Z.Q*Z.p0^2 - 2*X*(C t)*Z.Q*Z.p0^2 - 2*X*(C w)*Z.P*Z.Q*Z.P1 - X*(C w)*Z.Q*Z.p0^2 + X*Z.Q*Z.p0^2 + Z.P1^2) = 0) :
    (-X^5*(C t)^2*(C w)*Z.p0*Z.q0 + X^5*(C t)^2*Z.p0*Z.q0 + 2*X^5*(C t)*(C w)*Z.p0*Z.q0 - 2*X^5*(C t)*Z.p0*Z.q0 - X^5*(C w)*Z.p0*Z.q0 + X^5*Z.p0*Z.q0 + 2*X^3*(C t)^2*(C w)*Z.p0*Z.q0 - 2*X^3*(C t)^2*Z.p0*Z.q0 - 4*X^3*(C t)*(C w)*Z.p0*Z.q0 + 4*X^3*(C t)*Z.p0*Z.q0 - X^3*(C w)*Z.P*Z.Q + 2*X^3*(C w)*Z.p0*Z.q0 - 2*X^3*Z.p0*Z.q0 - X^2*Z.P + X^2*Z.P1 - X*(C t)^2*(C w)*Z.p0*Z.q0 + X*(C t)^2*Z.p0*Z.q0 + 2*X*(C t)*(C w)*Z.p0*Z.q0 - 2*X*(C t)*Z.p0*Z.q0 + X*(C w)*Z.P*Z.Q - X*(C w)*Z.p0*Z.q0 + X*Z.p0*Z.q0 - Z.P1) = 0 := by
  have ha := za_ne_zero Z ht1 hw1
  have hL0 := Z.hL0
  refine (mul_eq_zero.mp ?_).resolve_left ha
  linear_combination (-X^5*(C t)^2*(C w)*Z.p0 + X^5*(C t)^2*Z.p0 + 2*X^5*(C t)*(C w)*Z.p0 - 2*X^5*(C t)*Z.p0 - X^5*(C w)*Z.p0 + X^5*Z.p0 + 2*X^3*(C t)^2*(C w)*Z.p0 - 2*X^3*(C t)^2*Z.p0 - 4*X^3*(C t)*(C w)*Z.p0 + 4*X^3*(C t)*Z.p0 + 2*X^3*(C w)*Z.p0 - 2*X^3*Z.p0 - X*(C t)^2*(C w)*Z.p0 + X*(C t)^2*Z.p0 + 2*X*(C t)*(C w)*Z.p0 - 2*X*(C t)*Z.p0 - X*(C w)*Z.p0 + X*Z.p0) * hL0 - hE0

/-- (E2) `(1−ω)(1−t)² r u² q₀² = b`. -/
lemma zE2 (Z : ZAlgData t w) (ht1 : t ≠ 1) (hw1 : w ≠ 1) (hE1 : (-X^5*(C t)^2*(C w)*Z.p0*Z.q0 + X^5*(C t)^2*Z.p0*Z.q0 + 2*X^5*(C t)*(C w)*Z.p0*Z.q0 - 2*X^5*(C t)*Z.p0*Z.q0 - X^5*(C w)*Z.p0*Z.q0 + X^5*Z.p0*Z.q0 + 2*X^3*(C t)^2*(C w)*Z.p0*Z.q0 - 2*X^3*(C t)^2*Z.p0*Z.q0 - 4*X^3*(C t)*(C w)*Z.p0*Z.q0 + 4*X^3*(C t)*Z.p0*Z.q0 - X^3*(C w)*Z.P*Z.Q + 2*X^3*(C w)*Z.p0*Z.q0 - 2*X^3*Z.p0*Z.q0 - X^2*Z.P + X^2*Z.P1 - X*(C t)^2*(C w)*Z.p0*Z.q0 + X*(C t)^2*Z.p0*Z.q0 + 2*X*(C t)*(C w)*Z.p0*Z.q0 - 2*X*(C t)*Z.p0*Z.q0 + X*(C w)*Z.P*Z.Q - X*(C w)*Z.p0*Z.q0 + X*Z.p0*Z.q0 - Z.P1) = 0) :
    (-X^5*(C t)^2*(C w)*Z.q0^2 + X^5*(C t)^2*Z.q0^2 + 2*X^5*(C t)*(C w)*Z.q0^2 - 2*X^5*(C t)*Z.q0^2 - X^5*(C w)*Z.q0^2 + X^5*Z.q0^2 + 2*X^3*(C t)^2*(C w)*Z.q0^2 - 2*X^3*(C t)^2*Z.q0^2 - 4*X^3*(C t)*(C w)*Z.q0^2 + 4*X^3*(C t)*Z.q0^2 + 2*X^3*(C w)*Z.q0^2 + X^3*Z.P*Z.Ph - 2*X^3*Z.q0^2 - X*(C t)^2*(C w)*Z.q0^2 + X*(C t)^2*Z.q0^2 + 2*X*(C t)*(C w)*Z.q0^2 - 2*X*(C t)*Z.q0^2 - X*(C w)*Z.q0^2 - X*Z.P*Z.Ph + X*Z.q0^2 + Z.Q) = 0 := by
  have hL0 := Z.hL0
  refine (mul_eq_zero.mp ?_).resolve_left (zp0_ne_zero Z)
  linear_combination Z.q0 * hE1 + hL0
end AvgRS
