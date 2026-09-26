module

public import RequestProject.ZLineAlgBase

@[expose] public section

/-!
# Low-order coefficients of the scalar data on the line `z + z' = −2`

From the differential equations and the constant terms, the coefficients of `r` and `r²` of
`P, P̂, Q, P₁, P̂₁, Q₁, Q̂₁` are determined; they fix the resonant coefficients needed by the
uniqueness arguments.
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

lemma coeff_ofNat_z (n k : ℕ) [k.AtLeastTwo] :
    coeff n (no_index (OfNat.ofNat k : ℚ⟦X⟧)) = if n = 0 then (OfNat.ofNat k : ℚ) else 0 := by
  rw [← map_ofNat (C (R := ℚ)) k, coeff_C]

/-- The low-order coefficients. -/
lemma zlow12 (Z : ZAlgData t w) :
    coeff 1 Z.Q = 1 - t ∧ coeff 1 Z.Q1 = 0 ∧ coeff 1 Z.Qh1 = 0 ∧ coeff 1 Z.P1 = 0 ∧
    coeff 1 Z.Ph1 = 0 ∧ coeff 1 Z.P = 0 ∧ coeff 1 Z.Ph = 0 ∧
    coeff 2 Z.P1 = -(t * (1 - t)) ∧ coeff 2 Z.Ph1 = 4 - t ∧
    coeff 2 Z.P = -(t * (1 - t)) - w * (1 - t) ^ 2 ∧ coeff 2 Z.Ph = 4 - t - w * (1 - t) := by
  have hlow := zlow0 Z
  obtain ⟨P, Ph, Q, P1, Ph1, Q1, Qh1, p0, q0, p1, q1, G00, G01, G10, G11, D, DZ, hP, hPh, hQ, hQ1,
    hQh1, hP1, hPh1, hp0, hq0, hp1, hG00, hG01, hG10, hG11, hD, hDZ, hR2, hL0, hF1, hF2, hcP, hcPh,
    hP1X, hPh1X, hcp0, hcG00, hcG11, hcG01, hcG10, hcD⟩ := Z
  dsimp only at *
  obtain ⟨cQ, cQ1, cQh1, cP1, cPh1⟩ := hlow
  have e0 : ∀ f : ℚ⟦X⟧, coeff 0 f = constantCoeff f := fun f => coeff_zero_eq_constantCoeff_apply f
  have key : ∀ {f g : ℚ⟦X⟧}, f = g → ∀ n, coeff n f = coeff n g := fun h n => by rw [h]
  -- coefficient simp set
  have k_q1 := key hQ 1
  have k_qq1 := key hQ1 1
  have k_qh1 := key hQh1 1
  have k_p11 := key hP1 1
  have k_ph11 := key hPh1 1
  have k_pp1 := key hP 1
  have k_pph1 := key hPh 1
  have k_p12 := key hP1 2
  have k_ph12 := key hPh1 2
  have k_pp2 := key hP 2
  have k_pph2 := key hPh 2
  simp only [pow_two, pow_three, coeff_one_mul', coeff_two_mul', coeff_zero_mul', coeff_X, coeff_C,
    coeff_ofNat_z, coeff_derivative, map_sub, map_add, map_neg, coeff_one] at k_q1 k_qq1 k_qh1 k_p11 k_ph11 k_pp1 k_pph1 k_p12 k_ph12 k_pp2 k_pph2
  simp only [e0, hcP, hcPh, cQ, cQ1, cQh1, cP1, cPh1] at k_q1 k_qq1 k_qh1 k_p11 k_ph11 k_pp1 k_pph1 k_p12 k_ph12 k_pp2 k_pph2
  norm_num at k_q1 k_qq1 k_qh1 k_p11 k_ph11 k_pp1 k_pph1 k_p12 k_ph12 k_pp2 k_pph2
  have hQ1c : coeff 1 Q = 1 - t := by linarith
  have hQ11 : coeff 1 Q1 = 0 := by linarith
  have hQh11 : coeff 1 Qh1 = 0 := by linarith
  have hP11 : coeff 1 P1 = 0 := by linarith
  have hPh11 : coeff 1 Ph1 = 0 := by linarith
  have hP12 : coeff 1 P = 0 := by linarith
  have hPh12 : coeff 1 Ph = 0 := by linarith
  simp only [hQ1c, hQ11, hQh11, hP11, hPh11] at k_p12 k_ph12 k_pp2 k_pph2
  have hP1_2 : coeff 2 P1 = -(t * (1 - t)) := by linarith
  have hPh1_2 : coeff 2 Ph1 = 4 - t := by linarith
  refine ⟨hQ1c, hQ11, hQh11, hP11, hPh11, hP12, hPh12, hP1_2, hPh1_2, ?_, ?_⟩
  · rw [hP1_2] at k_pp2; linarith
  · rw [hPh1_2] at k_pph2; linarith

/-- Valuations of `a = σ + r²P` and `b = r u P P̂ − Q`: `a = r² a'`, `b = r³ b'` with
`a'(0) = b'(0) = (1 − ω)(1 − t)²`. -/
lemma zlowab (Z : ZAlgData t w) :
  ∃ a' b' : ℚ⟦X⟧, (1 - X^2) * (Z.P1 - C w * X * Z.P * Z.Q) + X^2 * Z.P = X^2 * a' ∧
    X * (1 - X^2) * Z.P * Z.Ph - Z.Q = X^3 * b' ∧
    constantCoeff a' = (1-w)*(1-t)^2 ∧ constantCoeff b' = (1-w)*(1-t)^2 := by
  have hlow := zlow0 Z
  have h12 := zlow12 Z
  obtain ⟨P, Ph, Q, P1, Ph1, Q1, Qh1, p0, q0, p1, q1, G00, G01, G10, G11, D, DZ, hP, hPh, hQ, hQ1,
    hQh1, hP1, hPh1, hp0, hq0, hp1, hG00, hG01, hG10, hG11, hD, hDZ, hR2, hL0, hF1, hF2, hcP, hcPh,
    hP1X, hPh1X, hcp0, hcG00, hcG11, hcG01, hcG10, hcD⟩ := Z
  dsimp only at *
  obtain ⟨cQ, cQ1, cQh1, cP1, cPh1⟩ := hlow
  obtain ⟨q1c, -, -, p11, -, pp1, pph1, p12, -, pp2, pph2⟩ := h12
  have e0 : ∀ f : ℚ⟦X⟧, coeff 0 f = constantCoeff f := fun f => coeff_zero_eq_constantCoeff_apply f
  have key : ∀ {f g : ℚ⟦X⟧}, f = g → ∀ n, coeff n f = coeff n g := fun h n => by rw [h]
  have k2 := key hQ 2
  have k3 := key hQ 3
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_X, coeff_derivative, e0, hcP, hcPh, pp1, pph1, pp2, pph2, coeff_ofNat_z] at k2 k3
  have hQ2 : coeff 2 Q = 0 := by linarith
  have hQ3 : coeff 3 Q = (1 - t) * (2 - t - w * (1 - t)) := by linarith
  have ca : ∀ n < 3, coeff n ((1 - X^2) * (P1 - C w * X * P * Q) + X^2 * P) =
      if n = 2 then (1-w)*(1-t)^2 else 0 := by
    intro n hn
    interval_cases n <;>
    (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_X, e0, hcP, cQ, cP1, p11, p12, pp1, q1c, coeff_X_pow]; try ring)
  have cb : ∀ n < 4, coeff n (X * (1 - X^2) * P * Ph - Q) =
      if n = 3 then (1-w)*(1-t)^2 else 0 := by
    intro n hn
    interval_cases n <;>
    (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_X, e0, hcP, hcPh, cQ, q1c, hQ2, hQ3, pp1, pph1, pp2, pph2, coeff_X_pow]; try ring)
  obtain ⟨a', ha'⟩ := (X_pow_dvd_iff (n := 2)).mpr (fun n hn => by rw [ca n (by omega)]; simp; omega)
  obtain ⟨b', hb'⟩ := (X_pow_dvd_iff (n := 3)).mpr (fun n hn => by rw [cb n (by omega)]; simp; omega)
  refine ⟨a', b', ha', hb', ?_, ?_⟩
  · have := ca 2 (by norm_num); rw [ha', coeff_X_pow_mul', if_pos le_rfl] at this; simpa using this
  · have := cb 3 (by norm_num); rw [hb', coeff_X_pow_mul', if_pos le_rfl] at this; simpa using this

end AvgRS
