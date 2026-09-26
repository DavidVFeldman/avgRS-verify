module

public import RequestProject.Formal.Sec7Alg
public import RequestProject.RingRefl

@[expose] public section

/-!
# The closed system on the line `z + z' = −2`: data and tools

`ZAlgData t w` bundles the scalar power series of the two-matrix resolvent on the line
`z + z' = −2` (in the limit of the truncations) together with the identities they satisfy:
the differential equations (B5–B8 paired, and the pairings `P₁' , P̂₁'` closed by the exact
limits of (P2q), (P̂2q)), the level-0 and level-1 components of the recurrences (RXp), (RZp),
the first integral R2, the entry equations for the resolvent, the Jacobi formula for
`G₀ = det(1 + ω C₁)`, the rank-two formula for `G₂ = det(1 + Ω C₁)`, and initial data.

The file `ZLineAlg.lean` derives from these the remaining first integrals R1, R3, R6, R7, the
closed forms (I3b), (I4), (G01), (G11) and finally the identity (B4).

Tools: a uniqueness lemma for first-order linear differential equations `X g f' = c f` in
`ℚ⟦X⟧`, and coefficient formulas for products.
-/

namespace AvgRS

open PowerSeries

/-- The scalar data of the resolvent on the line `z + z' = −2`, with `r = X`, `u = 1 − r²`,
`T = t = (z+1)²`, `W = ω`. -/
structure ZAlgData (t w : ℚ) where
  (P Ph Q P1 Ph1 Q1 Qh1 p0 q0 p1 q1 G00 G01 G10 G11 D DZ : ℚ⟦X⟧)
  hP : X * d⁄dX ℚ P = 2 * P1 - 2 * C w * X * P * Q
  hPh : X * d⁄dX ℚ Ph = 2 * Ph1 - 2 * C w * X * Ph * Q
  hQ : X * d⁄dX ℚ Q = 2 * X * P * Ph - Q
  hQ1 : X * d⁄dX ℚ Q1 = 2 * X * Ph * P1 - Q1
  hQh1 : X * d⁄dX ℚ Qh1 = 2 * X * P * Ph1 - Qh1
  hP1 : X * (1 - X ^ 2) * d⁄dX ℚ P1
    = 2 * (C w * X * (1 - X ^ 2) * (P * Q1 + P1 * Q - C w * X * P * Q ^ 2)
      + C w * X * (1 + X ^ 2) * P * Q - X ^ 2 * C t * P - C w * X ^ 2 * (1 - X ^ 2) * P ^ 2 * Ph)
      - 2 * C w * X * (1 - X ^ 2) * P * Q1
  hPh1 : X * (1 - X ^ 2) * d⁄dX ℚ Ph1
    = 2 * (4 * X ^ 2 * Ph1 + C w * X * (1 - X ^ 2) * (Ph * Qh1 + Ph1 * Q - C w * X * Ph * Q ^ 2)
      + C w * X * (1 - 3 * X ^ 2) * Ph * Q + (4 - C t) * X ^ 2 * Ph
      - C w * X ^ 2 * (1 - X ^ 2) * P * Ph ^ 2)
      - 2 * C w * X * (1 - X ^ 2) * Ph * Qh1
  hp0 : d⁄dX ℚ p0 = -(2 * C w * P * q0)
  hq0 : X * d⁄dX ℚ q0 = 2 * X * Ph * p0 - q0
  hp1 : X * d⁄dX ℚ p1 = p1 - 2 * C w * X * P * q1
  hG00 : d⁄dX ℚ G00 = -(2 * C w * (1 - C t) * p0 * q0)
  hG01 : d⁄dX ℚ G01 = C w * C t * (1 - C t) * (p0 * q1 + q0 * p1)
  hG10 : d⁄dX ℚ G10 = -(C w * (1 - C t) * (p1 * q0 + q1 * p0))
  hG11 : d⁄dX ℚ G11 = 2 * C w * C t * (1 - C t) * p1 * q1
  hD : d⁄dX ℚ D = 2 * C w * Q * D
  hDZ : C w ^ 2 * DZ
    = D * ((1 - (1 - C w) * G00) * (1 - (1 - C w) * G11) - (1 - C w) ^ 2 * G01 * G10)
  hR2 : Q1 + Qh1 + Q = X * P * Ph + C w * X * Q ^ 2
  hL0 : ((1 - X ^ 2) * (P1 - C w * X * P * Q) + X ^ 2 * P) * q0
    = (X * (1 - X ^ 2) * P * Ph - Q) * p0
  hF1 : C t * p1 + C w * ((1 - X ^ 2) * (P1 - C w * X * P * Q) + P) * q0
    + (C w * X ^ 2 * Q - X * C t - C w * X * (1 - X ^ 2) * P * Ph) * p0 = 0
  hF2 : X * p0 = p1 * (1 + C w * X * (X * (1 - X ^ 2) * P * Ph - Q))
    - C w * X * (P + (1 - X ^ 2) * (P1 - C w * X * P * Q)) * q1
  hcP : constantCoeff P = 1 - t
  hcPh : constantCoeff Ph = 1
  hP1X : X ∣ P1
  hPh1X : X ∣ Ph1
  hcp0 : constantCoeff p0 = 1
  hcG00 : constantCoeff G00 = 1
  hcG11 : constantCoeff G11 = 1
  hcG01 : constantCoeff G01 = 0
  hcG10 : constantCoeff G10 = 0
  hcD : constantCoeff D = 1

lemma deriv_ofNat' (n : ℕ) [n.AtLeastTwo] : d⁄dX ℚ (no_index (OfNat.ofNat n : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat (C (R := ℚ)) n]
  exact derivative_C _

/-- Uniqueness for `X g f' = c f`: the coefficient recursion `(n g₀ − c₀) f_n = (lower terms)`
determines `f` from the coefficients at the resonant indices `n` with `n g₀ = c₀`. -/
lemma eq_zero_of_X_mul_deriv {f g c : ℚ⟦X⟧} (h : X * g * d⁄dX ℚ f = c * f)
    (hn : ∀ n : ℕ, coeff n f = 0 ∨ (n : ℚ) * constantCoeff g ≠ constantCoeff c) : f = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases hn n with h0 | hne
  · simpa using h0
  have hc := congrArg (coeff n) h
  have lhs : coeff n (X * g * d⁄dX ℚ f) = (n : ℚ) * constantCoeff g * coeff n f := by
    rw [mul_comm X g, mul_assoc, coeff_mul]
    rw [Finset.sum_eq_single (0, n)]
    · cases n with
      | zero => simp
      | succ n => simp [coeff_succ_X_mul, coeff_derivative]; ring
    · rintro ⟨i, j⟩ hij hne'
      rw [Finset.mem_antidiagonal] at hij
      have hj : j < n := by
        rcases Nat.eq_zero_or_pos i with hi | hi
        · exact absurd (by simp_all) hne'
        · omega
      cases j with
      | zero => simp
      | succ j => rw [coeff_succ_X_mul, coeff_derivative, ih (j + 1) hj]; simp
    · simp
  have rhs : coeff n (c * f) = constantCoeff c * coeff n f := by
    rw [coeff_mul, Finset.sum_eq_single (0, n)]
    · simp
    · rintro ⟨i, j⟩ hij hne'
      rw [Finset.mem_antidiagonal] at hij
      have hj : j < n := by
        rcases Nat.eq_zero_or_pos i with hi | hi
        · exact absurd (by simp_all) hne'
        · omega
      rw [ih j hj]; simp
    · simp
  rw [lhs, rhs] at hc
  have : ((n : ℚ) * constantCoeff g - constantCoeff c) * coeff n f = 0 := by linear_combination hc
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · simpa using h1

lemma coeff_one_mul' (f g : ℚ⟦X⟧) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ]

lemma coeff_two_mul' (f g : ℚ⟦X⟧) :
    coeff 2 (f * g) = coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  ring

lemma coeff_zero_mul' (f g : ℚ⟦X⟧) : coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  simp

lemma coeff_ofNat' (n k : ℕ) [k.AtLeastTwo] :
    coeff n (OfNat.ofNat k : ℚ⟦X⟧) = if n = 0 then (OfNat.ofNat k : ℚ) else 0 := by
  rw [← map_ofNat (C (R := ℚ)) k, coeff_C]

lemma zps_two_ne_zero : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat (C (R := ℚ)) 2]; exact (map_ne_zero_iff _ C_injective).mpr two_ne_zero

lemma zps_C_ne_zero {a : ℚ} (h : a ≠ 0) : (C a : ℚ⟦X⟧) ≠ 0 := (map_ne_zero_iff _ C_injective).mpr h

lemma zps_u_ne_zero : (1 - X ^ 2 : ℚ⟦X⟧) ≠ 0 :=
  Formal.ne_zero_of_constantCoeff_ne_zero (by simp)

lemma zlow0 {t w : ℚ} (Z : ZAlgData t w) : constantCoeff Z.Q = 0 ∧ constantCoeff Z.Q1 = 0 ∧
    constantCoeff Z.Qh1 = 0 ∧ constantCoeff Z.P1 = 0 ∧ constantCoeff Z.Ph1 = 0 := by
  obtain ⟨P, Ph, Q, P1, Ph1, Q1, Qh1, p0, q0, p1, q1, G00, G01, G10, G11, D, DZ, hP, hPh, hQ, hQ1,
    hQh1, hP1, hPh1, hp0, hq0, hp1, hG00, hG01, hG10, hG11, hD, hDZ, hR2, hL0, hF1, hF2, hcP, hcPh,
    hP1X, hPh1X, hcp0, hcG00, hcG11, hcG01, hcG10, hcD⟩ := Z
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg constantCoeff hQ; simp at this; linear_combination this
  · have := congrArg constantCoeff hQ1; simp at this; linear_combination this
  · have := congrArg constantCoeff hQh1; simp at this; linear_combination this
  · obtain ⟨k, hk⟩ := hP1X; rw [hk]; simp
  · obtain ⟨k, hk⟩ := hPh1X; rw [hk]; simp


end AvgRS
