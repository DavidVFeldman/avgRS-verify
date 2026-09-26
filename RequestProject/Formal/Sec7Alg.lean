module

public import Mathlib

@[expose] public section

/-!
# The algebra of Section 5 in `K⟦X⟧`

Given scalar power series satisfying the recurrences at levels `0` and `1`, the differential
equations of Lemma 5.11 (`lem:odes`) and the determinant formulas of Lemma 5.7 (`lem:five`), we derive the first
integrals (I1)–(I4), the closed forms of `G₀₁`, `G₁₁` (Proposition 5.14, `prop:level1`) and finally the
identity (C) `D' = 2 r z D_Z`.  Everything is an identity of formal power series.
-/

namespace AvgRS.Formal

open PowerSeries

variable {K : Type*} [Field K]

lemma deriv_mul' (a b : K⟦X⟧) : d⁄dX K (a * b) = a * d⁄dX K b + b * d⁄dX K a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

lemma deriv_one' : d⁄dX K (1 : K⟦X⟧) = 0 := Derivation.map_one_eq_zero _

lemma deriv_sq' (a : K⟦X⟧) : d⁄dX K (a ^ 2) = 2 * a * d⁄dX K a := by
  rw [pow_two, deriv_mul']; ring

lemma ne_zero_of_constantCoeff_ne_zero {f : K⟦X⟧} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  rintro rfl; simp at h

variable [CharZero K]

/-- A power series with zero derivative and zero constant term vanishes. -/
lemma eq_zero_of_deriv_eq_zero {u : K⟦X⟧} (hd : d⁄dX K u = 0) (hc : constantCoeff u = 0) :
    u = 0 :=
  derivative.ext (by rw [hd, map_zero]) (by rw [hc, map_zero])

/-- Wronskian lemma: if `u' g = u g'`, `g(0) ≠ 0` and `u(0) = 0`, then `u = 0`. -/
lemma eq_zero_of_wronskian {u g : K⟦X⟧} (hg : constantCoeff g ≠ 0) (hu : constantCoeff u = 0)
    (h : d⁄dX K u * g = u * d⁄dX K g) : u = 0 := by
  have hgi : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel g hg
  have hw : d⁄dX K (u * g⁻¹) = 0 := by
    rw [deriv_mul', derivative_inv']
    have : u * (-g⁻¹ ^ 2 * d⁄dX K g) + g⁻¹ * d⁄dX K u
        = g⁻¹ ^ 2 * (d⁄dX K u * g - u * d⁄dX K g) := by
      linear_combination (-(g⁻¹ * d⁄dX K u)) * hgi
    rw [this, h, sub_self, mul_zero]
  have hw0 : u * g⁻¹ = 0 := eq_zero_of_deriv_eq_zero hw (by rw [map_mul, hu, zero_mul])
  calc u = u * g⁻¹ * g := by rw [mul_assoc, mul_comm g⁻¹, hgi, mul_one]
    _ = 0 := by rw [hw0, zero_mul]

set_option maxHeartbeats 2000000 in
/-- **The core algebra of Section 5.**  Here `P₁ = r τ + r² P` and `Q = r Q_r` (so that
`τ = (P₁ - r² P)/r` and `Q/r = Q_r`), `σ = r s` with `s = τ + r P - z r P Q_r`, `β = r g` with
`g = 1 - z P²` and `W = r w₀` with `w₀ = P² - Q_r`.  From the level-0 and level-1 components of
(Rq), (Rp), the ODEs of Lemma 5.11, (G1) and the two determinant formulas of Lemma 5.7 we get
(I1)–(I4) (Proposition 5.12, `prop:level0`), Lemma 5.13 (`lem:level1`), Proposition 5.14 and finally (C): `D' = 2 r z D_Z`. -/
theorem sec7_core (z : K) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (P Qr τ ε p0 q0 p1 q1 G00 G01 G11 D DZ : K⟦X⟧)
    (hP : d⁄dX K P = 2 * (τ + X * P - C z * X * P * Qr))
    (hQr : X * d⁄dX K Qr = 2 * P ^ 2 - 2 * Qr)
    (hτ : X * d⁄dX K τ = 2 * X * (1 - C z * P ^ 2) * P
      + 2 * C z * Qr * X * (P + X * (τ + X * P - C z * X * P * Qr)) - τ
      - 2 * X ^ 2 * (τ + X * P - C z * X * P * Qr) - 2 * X * P)
    (hp0 : d⁄dX K p0 = -(2 * C z * P * q0))
    (hq0 : X * d⁄dX K q0 = 2 * X * P * p0 - q0)
    (hG00 : d⁄dX K G00 = -(C z * (p0 * q0 + q0 * p0)))
    (hG01 : d⁄dX K G01 = -(C z * (p0 * q1 + q0 * p1)))
    (hG11 : d⁄dX K G11 = -(C z * (p1 * q1 + q1 * p1)))
    (hD : d⁄dX K D = 2 * C z * (X * Qr) * D)
    (hDZ : C z ^ 2 * DZ = D * ((1 - (1 - C z) * G00) * (1 - (1 - C z) * G11)
      - (1 - C z) ^ 2 * (G01 * G01)))
    (hR0a : (τ + X * P - C z * X * P * Qr) * p0 = (1 - C z * P ^ 2) * q0)
    (hR0b : C z * X * (P ^ 2 - Qr) * p0 - C z * X * (τ + X * P - C z * X * P * Qr) * q0
      + ε = 0)
    (hR1a : q0 = P * p1 - X * (τ + X * P - C z * X * P * Qr) * p1
      + X * (1 - C z * P ^ 2) * q1)
    (hR1b : X * p0 = p1 - C z * X * P * q1 + C z * X * (X * (P ^ 2 - Qr)) * p1
      - C z * X * (X * (τ + X * P - C z * X * P * Qr)) * q1 + X * ε * X)
    (hcP : constantCoeff P = 1) (hcp0 : constantCoeff p0 = 1)
    (hcG00 : constantCoeff G00 = 1) (hcG11 : constantCoeff G11 = 1)
    (hcG01 : constantCoeff G01 = 0) (hcτ : constantCoeff τ = 0) (hcQr : constantCoeff Qr = 1) :
    d⁄dX K D = 2 * X * C z * DZ := by
  set s := τ + X * P - C z * X * P * Qr with hs
  set g := 1 - C z * P ^ 2 with hg
  set w0 := P ^ 2 - Qr with hw0
  set c := (C z : K⟦X⟧) with hc
  have hX : (X : K⟦X⟧) ≠ 0 := X_ne_zero
  have hc0 : c ≠ 0 := by rw [hc]; exact (map_ne_zero_iff _ (C_injective)).mpr hz0
  have hP0 : P ≠ 0 := ne_zero_of_constantCoeff_ne_zero (by rw [hcP]; exact one_ne_zero)
  have hp00 : p0 ≠ 0 := ne_zero_of_constantCoeff_ne_zero (by rw [hcp0]; exact one_ne_zero)
  have h1z : (1 : K) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hcg : constantCoeff g = 1 - z := by simp [hg, hc, hcP]
  have hg0 : g ≠ 0 := ne_zero_of_constantCoeff_ne_zero (by rw [hcg]; exact h1z)
  have h2 : (2 : K⟦X⟧) ≠ 0 := ne_zero_of_constantCoeff_ne_zero (by rw [map_ofNat]; exact two_ne_zero)
  -- the derivative of the level-0 relation
  have hF : X * d⁄dX K (g * q0 - s * p0) = X * (2 * c * P) * (w0 * p0 - s * q0) - (g * q0 - s * p0) := by
    simp only [hs, hg, hw0, hc, map_sub, map_add, deriv_mul', deriv_one', deriv_sq', derivative_C, derivative_X]
    rw [hP, hp0]
    linear_combination (-p0) * hτ + (C z*X*P*p0) * hQr + (1 - C z*P^2) * hq0
  have S1 : w0 * p0 = s * q0 := by
    have h0 : g * q0 - s * p0 = 0 := by rw [hR0a]; ring
    rw [h0, map_zero, mul_zero, sub_zero] at hF
    have := (mul_eq_zero.mp hF.symm).resolve_left (by simp [hX, hc0, hP0, h2])
    exact sub_eq_zero.mp this
  have hε : ε = 0 := by linear_combination hR0b - c * X * S1
  have I1 : s ^ 2 = g * w0 := by
    have : (s ^ 2 - g * w0) * p0 = 0 := by linear_combination s * hR0a - g * S1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hp00)
  have I3 : (1 - c) * p0 ^ 2 = g := by
    have := eq_zero_of_wronskian (u := (1 - c) * p0 ^ 2 - g) (g := g) (by rw [hcg]; exact h1z)
      (by simp [hc, hg, hcp0, hcP]) (by
        simp only [hg, hc, map_sub, deriv_mul', deriv_one', deriv_sq', derivative_C]
        rw [hP, hp0]
        linear_combination (4 * C z * P * p0 * (1 - C z)) * hR0a)
    exact sub_eq_zero.mp this
  have E1 : (1 - c) * (p0 * q0) = s := by
    refine mul_left_cancel₀ hg0 ?_
    linear_combination (1 - c) * p0 * hR0a.symm + s * I3
  have E2 : (1 - c) * q0 ^ 2 = w0 := by
    refine mul_left_cancel₀ hg0 ?_
    linear_combination (1 - c) * q0 * hR0a.symm + s * E1 + I1
  have I4 : (1 - c) * G00 = 1 - c * P := by
    have := eq_zero_of_deriv_eq_zero (u := (1 - c) * G00 + c * P - 1) (by
        simp only [hc, map_sub, map_add, deriv_mul', deriv_one', derivative_C]
        rw [hP, hG00]
        linear_combination (-2 * C z) * E1) (by simp [hc, hcG00, hcP])
    linear_combination this
  rw [hε] at hR1b
  have L1 : p1 = X * g * p0 + c * (X * s + P) * q0 := by
    refine mul_left_cancel₀ hX ?_
    linear_combination (-(c * X * (X * s + P))) * hR1a - (X * g) * hR1b + (c * X ^ 3 * p1) * I1
  have L2 : X * q1 = X * (X * s - P) * p0 + (1 + c * X ^ 2 * w0) * q0 := by
    linear_combination (-(1 + c * X ^ 2 * w0)) * hR1a + (P - X * s) * hR1b + (c * X ^ 3 * q1) * I1
  subst L1
  have T1 : (1 - c) * G01 = c * τ := by
    have key : X * d⁄dX K τ = -((1 - c) * (p0 * (X * q1) + X * q0 * (X * g * p0 + c * (X * s + P) * q0))) := by
      rw [hs, hg, hw0] at *
      linear_combination hτ + (1 - c) * p0 * L2 + (X * (X * s - P)) * I3
        + (1 + c * X ^ 2 * w0 + X ^ 2 * g) * E1 + (c * X * (X * s + P)) * E2
    have hd : d⁄dX K ((1 - c) * G01 - c * τ) = 0 := by
      refine mul_left_cancel₀ hX ?_
      simp only [hc, map_sub, deriv_mul', deriv_one', derivative_C]
      rw [hG01]
      linear_combination (-C z) * key
    have := eq_zero_of_deriv_eq_zero hd (by simp [hc, hcG01, hcτ])
    linear_combination this
  have T2 : (1 - (1 - c) * G11) * P = c * (Qr + τ ^ 2) := by
    have := eq_zero_of_wronskian (u := (1 - (1 - c) * G11) * P - c * (Qr + τ ^ 2)) (g := P)
      (by rw [hcP]; exact one_ne_zero) (by simp [hc, hcG11, hcP, hcQr, hcτ]) (by
        refine mul_left_cancel₀ (pow_ne_zero 2 hX) ?_
        simp only [hc, map_sub, map_add, deriv_mul', deriv_one', deriv_sq', derivative_C]
        rw [hG11, hP]
        rw [hs, hg, hw0] at *
        linear_combination (2 * C z * P ^ 2 * (1 - C z) * X * (X * g * p0 + c * (X * s + P) * q0)) * L2
          + (2 * C z * P ^ 2 * X * (X * g) * (X * (X * s - P))) * I3
          + (2 * C z * P ^ 2 * X * ((X * g) * (1 + c * X ^ 2 * w0) + (c * (X * s + P)) * (X * (X * s - P)))) * E1
          + (2 * C z * P ^ 2 * X * (c * (X * s + P)) * (1 + c * X ^ 2 * w0)) * E2
          - (C z * P * X) * hQr - (2 * C z * P * X * τ) * hτ
          + (-2 * X * C z * (P ^ 3 * Qr * X ^ 4 * C z ^ 2 - P ^ 3 * X ^ 4 * C z - P ^ 2 * X ^ 3 * C z * τ
            + P * Qr * X ^ 2 * C z - P * X ^ 2 - P - X * τ)) * I1)
    linear_combination this
  have hDZ' : DZ = D * Qr := by
    refine mul_left_cancel₀ (mul_ne_zero hP0 (pow_ne_zero 2 hc0)) ?_
    linear_combination P * hDZ + D * (1 - (1 - c) * G00) * T2 - D * c * (Qr + τ ^ 2) * I4
      - P * D * ((1 - c) * G01 + c * τ) * T1
  rw [hD, hDZ']
  ring
end AvgRS.Formal

namespace AvgRS.Formal

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- **Section 5, conclusion (C)**, stated for scalar power series satisfying the relations
obtained from the resolvent: the ODEs of Lemma 5.11 (multiplied by `r` where they involve
`1/r`), (G1) for the entries `G₀₀, G₀₁, G₁₁`, the Jacobi formula `D' = 2 z Q D`, the rank-two
formula for `D_Z`, the level-0 and level-1 components of (Rq) and (Rp), and the constant terms
of Definition 5.8 (`def:pq`).  Then `D' = 2 r z D_Z`. -/
theorem sec7_conclusion (z : K) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (P Q P1 Q1 p0 q0 p1 q1 G00 G01 G11 D DZ : K⟦X⟧)
    (hP : X * d⁄dX K P = 2 * P1 - 2 * C z * X * P * Q)
    (hQ : X * d⁄dX K Q = 2 * X * P ^ 2 - Q)
    (hP1 : d⁄dX K P1 = 2 * (X * (1 - C z * P ^ 2)) * P
      + 2 * C z * Q * (P + (P1 - C z * X * P * Q)))
    (hp0 : X * d⁄dX K p0 = -(2 * C z * X * P * q0))
    (hq0 : X * d⁄dX K q0 = 2 * X * P * p0 - q0)
    (hG00 : d⁄dX K G00 = -(C z * (p0 * q0 + q0 * p0)))
    (hG01 : d⁄dX K G01 = -(C z * (p0 * q1 + q0 * p1)))
    (hG11 : d⁄dX K G11 = -(C z * (p1 * q1 + q1 * p1)))
    (hD : d⁄dX K D = 2 * C z * Q * D)
    (hDZ : C z ^ 2 * DZ = D * ((1 - (1 - C z) * G00) * (1 - (1 - C z) * G11)
      - (1 - C z) ^ 2 * (G01 * G01)))
    (hR0a : 0 = -(P1 - C z * X * P * Q) * p0 + X * (1 - C z * P ^ 2) * q0)
    (hR0b : 0 = C z * X * (X * P ^ 2 - Q) * p0 - C z * X * (P1 - C z * X * P * Q) * q0
      + X * (C z * (2 * Q1 + Q - X * C z * Q ^ 2 - X * P ^ 2)))
    (hR1a : q0 = P * p1 - (P1 - C z * X * P * Q) * p1 + X * (1 - C z * P ^ 2) * q1)
    (hR1b : X * p0 = p1 - C z * X * P * q1 + C z * X * (X * P ^ 2 - Q) * p1
      - C z * X * (P1 - C z * X * P * Q) * q1
      + X * (C z * (2 * Q1 + Q - X * C z * Q ^ 2 - X * P ^ 2)) * X)
    (hcP : constantCoeff P = 1) (hcp0 : constantCoeff p0 = 1)
    (hcG00 : constantCoeff G00 = 1) (hcG11 : constantCoeff G11 = 1)
    (hcG01 : constantCoeff G01 = 0) (hP1d : (X : K⟦X⟧) ^ 2 ∣ P1) (hQd : (X : K⟦X⟧) ∣ Q) :
    d⁄dX K D = 2 * X * C z * DZ := by
  have hX : (X : K⟦X⟧) ≠ 0 := X_ne_zero
  obtain ⟨k, hk⟩ := hP1d
  obtain ⟨τ, hτd, hcτ⟩ : ∃ τ, P1 = X * τ + X ^ 2 * P ∧ constantCoeff τ = 0 :=
    ⟨X * k - X * P, by rw [hk]; ring, by simp⟩
  obtain ⟨Qr, hQr⟩ := hQd
  subst hτd hQr
  have hQ' : X * d⁄dX K Qr = 2 * P ^ 2 - 2 * Qr := by
    refine mul_left_cancel₀ hX ?_
    rw [deriv_mul', derivative_X] at hQ
    linear_combination hQ
  have hcQr : constantCoeff Qr = 1 := by
    have := congrArg constantCoeff hQ'
    simp only [map_mul, constantCoeff_X, zero_mul, map_sub, map_pow, hcP, map_ofNat] at this
    linear_combination this / 2
  refine sec7_core z hz0 hz1 P Qr τ (C z * (2 * Q1 + X * Qr - X * C z * (X * Qr) ^ 2 - X * P ^ 2))
    p0 q0 p1 q1 G00 G01 G11 D DZ ?_ hQ' ?_ ?_ hq0 hG00 hG01 hG11 hD hDZ ?_ ?_ ?_ ?_
    hcP hcp0 hcG00 hcG11 hcG01 hcτ hcQr
  · refine mul_left_cancel₀ hX ?_
    linear_combination hP
  · refine mul_left_cancel₀ hX ?_
    rw [map_add, deriv_mul', deriv_mul', derivative_X, deriv_sq', derivative_X] at hP1
    have hP' : X * d⁄dX K P = 2 * (X * τ + X ^ 2 * P) - 2 * C z * X * P * (X * Qr) := hP
    linear_combination X * hP1 - X ^ 2 * hP'
  · refine mul_left_cancel₀ hX ?_
    linear_combination hp0
  · refine mul_left_cancel₀ hX ?_
    linear_combination hR0a
  · refine mul_left_cancel₀ hX ?_
    linear_combination -hR0b
  · linear_combination hR1a
  · linear_combination hR1b

end AvgRS.Formal
