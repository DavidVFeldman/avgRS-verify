module

public import RequestProject.ZLineDet

@[expose] public section

/-!
# Item B5: the structural identities (H1_z)–(H4_z) for the hook matrix `H_z`

`(H_z)_{ab} = X^{a+b+1} G_z(a|b)` (the entries of `Hzm`, `ZLineDet.lean`) and
`u_a = X^a (z+1)_a / a!`, `ũ_b = X^b (−1)^b (1−z)_b / b!`.  Entrywise, with `A = diag(0,1,2,…)`,
`(Xf)_a = a f_{a−1}`, `(Xᵀ f)_a = (a+1) f_{a+1}`:

* (H1_z) `d/dX (H_z)_{ab} = z u_a ũ_b`, `X u_a' = a u_a`, `X ũ_b' = b ũ_b`;
* (H2_z) `(H_z A + (A+1) H_z)_{ab} = (a+b+1)(H_z)_{ab} = z X u_a ũ_b`;
* (H3_z) `(a+1)(H_z)_{a+1,b}(z−1−b) = (b+1)(H_z)_{a,b+1}(z+1+a)`;
* (H4_z) `(z+a)·a(H_z)_{a−1,b} − b(H_z)_{a,b−1}·(z−b) = z(a−b) u_a ũ_b`
  (the entry `((z+A) X H_z − H_z Xᵀ (z−A))_{ab}`; for `a = 0` resp. `b = 0` the corresponding
  term vanishes because of the factor `a` resp. `b`).

The versions for `z' = −z−2` are the instances at `-z - 2`.
-/

namespace AvgRS

open Finset PowerSeries Formal

/-- `(z+1)_a / a!`. -/
noncomputable def uCoef (z : ℚ) (a : ℕ) : ℚ := (∏ m ∈ range a, (z + 1 + m)) / (a.factorial : ℚ)

/-- `(−1)^b (1−z)_b / b! = ∏_{m=1}^{b} (z − m) / b!`. -/
noncomputable def utCoef (z : ℚ) (b : ℕ) : ℚ := legProd z b / (b.factorial : ℚ)

/-- `u_a = X^a (z+1)_a / a!`. -/
noncomputable def uz (z : ℚ) (a : ℕ) : ℚ⟦X⟧ := C (uCoef z a) * X ^ a

/-- `ũ_b = X^b (−1)^b (1−z)_b / b!`. -/
noncomputable def utz (z : ℚ) (b : ℕ) : ℚ⟦X⟧ := C (utCoef z b) * X ^ b

/-- The entry `(H_z)_{ab} = X^{a+b+1} G_z(a|b)`. -/
noncomputable def hzE (z : ℚ) (a b : ℕ) : ℚ⟦X⟧ := C (hookFz z a b) * X ^ (a + b + 1)

lemma Hzm_apply (z : ℚ) (m : ℕ) (a b : Fin m) : Hzm z m a b = hzE z a b := rfl

lemma utCoef_eq (z : ℚ) (b : ℕ) :
    utCoef z b = (-1) ^ b * (∏ m ∈ range b, (1 - z + m)) / (b.factorial : ℚ) := by
  unfold utCoef legProd
  congr 1
  induction b with
  | zero => simp
  | succ b ih => rw [prod_range_succ, prod_range_succ, ih, pow_succ]; ring

lemma hookFz_eq (z : ℚ) (a b : ℕ) :
    hookFz z a b = z * uCoef z a * utCoef z b / ((a : ℚ) + b + 1) := by
  unfold hookFz uCoef utCoef hookF
  rw [hookContentProd_eq, armProd, Finset.prod_range_succ']
  have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hab : ((a : ℚ) + b + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  have e : ∏ x ∈ range a, (z + ((x : ℚ) + 1)) = ∏ x ∈ range a, (z + 1 + x) :=
    Finset.prod_congr rfl fun _ _ => by ring
  rw [e]; ring

lemma uCoef_succ (z : ℚ) (a : ℕ) : ((a : ℚ) + 1) * uCoef z (a + 1) = (z + 1 + a) * uCoef z a := by
  unfold uCoef
  have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp

lemma utCoef_succ (z : ℚ) (b : ℕ) : ((b : ℚ) + 1) * utCoef z (b + 1) = (z - 1 - b) * utCoef z b := by
  unfold utCoef legProd
  have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The entry identity behind (H1_z) and (H2_z): `(a+b+1) G_z(a|b) = z (z+1)_a/a! · (−1)^b(1−z)_b/b!`. -/
lemma hookFz_mul (z : ℚ) (a b : ℕ) :
    ((a : ℚ) + b + 1) * hookFz z a b = z * uCoef z a * utCoef z b := by
  rw [hookFz_eq]
  have hab : ((a : ℚ) + b + 1) ≠ 0 := by positivity
  field_simp

/-- **(H1_z)**: `d/dX (H_z)_{ab} = z u_a ũ_b` (the derivative of `H_z` has rank one). -/
theorem deriv_hzE (z : ℚ) (a b : ℕ) : d⁄dX ℚ (hzE z a b) = C z * uz z a * utz z b := by
  unfold hzE uz utz
  rw [deriv_C_mul_X_pow]
  have h := hookFz_mul z a b
  rw [show hookFz z a b * ((a + b : ℕ) + 1 : ℚ) = z * uCoef z a * utCoef z b by
    push_cast; linear_combination h, map_mul, map_mul, pow_add]
  ring

/-- **(H1_z)**: `X u_a' = a u_a`. -/
theorem X_mul_deriv_uz (z : ℚ) (a : ℕ) : X * d⁄dX ℚ (uz z a) = (a : ℚ⟦X⟧) * uz z a := by
  unfold uz
  rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, mul_one]
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [pow_succ]; ring

/-- **(H1_z)**: `X ũ_b' = b ũ_b`. -/
theorem X_mul_deriv_utz (z : ℚ) (b : ℕ) : X * d⁄dX ℚ (utz z b) = (b : ℚ⟦X⟧) * utz z b := by
  unfold utz
  rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, mul_one]
  rcases b with _ | b
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [pow_succ]; ring

/-- **(H2_z)** entrywise: `(H_z A + (A + 1) H_z)_{ab} = z X u_a ũ_b`. -/
theorem hzE_H2 (z : ℚ) (a b : ℕ) :
    hzE z a b * (b : ℚ⟦X⟧) + ((a : ℚ⟦X⟧) + 1) * hzE z a b = C z * X * uz z a * utz z b := by
  unfold hzE uz utz
  have h := hookFz_mul z a b
  rw [natCast_eq_C, natCast_eq_C]
  calc _ = C (((a : ℚ) + b + 1) * hookFz z a b) * X ^ (a + b + 1) := by
        simp only [map_mul, map_add, map_one]; ring
    _ = _ := by rw [h, map_mul, map_mul, pow_succ, pow_add]; ring

lemma hookFz_H3 (z : ℚ) (a b : ℕ) :
    ((a : ℚ) + 1) * hookFz z (a + 1) b * (z - 1 - b)
      = ((b : ℚ) + 1) * hookFz z a (b + 1) * (z + 1 + a) := by
  have hD : ((a : ℚ) + b + 2) ≠ 0 := by positivity
  have h1 := hookFz_mul z (a + 1) b
  have h2 := hookFz_mul z a (b + 1)
  have hu := uCoef_succ z a
  have hv := utCoef_succ z b
  push_cast at h1 h2
  apply mul_left_cancel₀ hD
  linear_combination ((a : ℚ) + 1) * (z - 1 - b) * h1 - ((b : ℚ) + 1) * (z + 1 + a) * h2
    + z * utCoef z b * (z - 1 - b) * hu - z * uCoef z a * (z + 1 + a) * hv

lemma C_mul_X_pow_congr {p q : ℚ} (n : ℕ) (h : p = q) : C p * (X : ℚ⟦X⟧) ^ n = C q * X ^ n := by
  rw [h]

/-- **(H3_z)** entrywise: `(a+1)(H_z)_{a+1,b}(z−1−b) = (b+1)(H_z)_{a,b+1}(z+1+a)`. -/
theorem hzE_H3 (z : ℚ) (a b : ℕ) :
    ((a : ℚ⟦X⟧) + 1) * hzE z (a + 1) b * C (z - 1 - b)
      = ((b : ℚ⟦X⟧) + 1) * hzE z a (b + 1) * C (z + 1 + a) := by
  unfold hzE
  rw [show a + 1 + b + 1 = a + (b + 1) + 1 by ring, natCast_eq_C, natCast_eq_C]
  have e : ∀ (p q r : ℚ) (n : ℕ), (C p + 1) * (C q * X ^ n) * C r
      = C ((p + 1) * q * r) * (X : ℚ⟦X⟧) ^ n := by
    intro p q r n; simp only [map_mul, map_add, map_one]; ring
  rw [e, e]
  exact C_mul_X_pow_congr _ (hookFz_H3 z a b)

/-- **(H4_z)** entrywise: `((z + A) X H_z − H_z Xᵀ (z − A))_{ab} = z (a − b) u_a ũ_b`, i.e.
`(z+a)·a(H_z)_{a−1,b} − b(H_z)_{a,b−1}·(z−b) = z(a−b) u_a ũ_b` (the right side is the entry of
the rank-two matrix `z (A u ⊗ ũ − u ⊗ A ũ)`). -/
theorem hzE_H4 (z : ℚ) (a b : ℕ) :
    C (z + a) * ((a : ℚ⟦X⟧) * hzE z (a - 1) b) - ((b : ℚ⟦X⟧) * hzE z a (b - 1)) * C (z - b)
      = C z * ((a : ℚ⟦X⟧) - b) * uz z a * utz z b := by
  unfold hzE uz utz
  simp only [natCast_eq_C]
  rcases a with _ | a <;> rcases b with _ | b
  · simp
  · simp only [Nat.cast_zero, map_zero, zero_mul, mul_zero, zero_sub, Nat.add_sub_cancel,
      pow_zero, add_zero]
    rw [show 0 + b + 1 = b + 1 by ring]
    have h1 := hookFz_mul z 0 b
    have hv := utCoef_succ z b
    have key : -(((b + 1 : ℕ) : ℚ) * hookFz z 0 b * (z - ((b + 1 : ℕ) : ℚ)))
        = z * (-((b + 1 : ℕ) : ℚ)) * uCoef z 0 * utCoef z (b + 1) := by
      push_cast at h1 ⊢
      linear_combination (-(z - (b + 1))) * h1 + z * uCoef z 0 * hv
    have eL : -(C ((b + 1 : ℕ) : ℚ) * (C (hookFz z 0 b) * X ^ (b + 1)) * C (z - ((b + 1 : ℕ) : ℚ)))
        = C (-(((b + 1 : ℕ) : ℚ) * hookFz z 0 b * (z - ((b + 1 : ℕ) : ℚ)))) * (X : ℚ⟦X⟧) ^ (b + 1) := by
      simp only [map_mul, map_neg]; ring
    have eR : C z * -C ((b + 1 : ℕ) : ℚ) * (C (uCoef z 0) * 1) * (C (utCoef z (b + 1)) * X ^ (b + 1))
        = C (z * (-((b + 1 : ℕ) : ℚ)) * uCoef z 0 * utCoef z (b + 1)) * (X : ℚ⟦X⟧) ^ (b + 1) := by
      simp only [map_mul, map_neg]; ring
    rw [eL, eR, key]
  · simp only [Nat.cast_zero, map_zero, zero_mul, sub_zero, Nat.add_sub_cancel,
      pow_zero, add_zero]
    have h1 := hookFz_mul z a 0
    have hu := uCoef_succ z a
    have key : (z + ((a + 1 : ℕ) : ℚ)) * (((a + 1 : ℕ) : ℚ) * hookFz z a 0)
        = z * ((a + 1 : ℕ) : ℚ) * uCoef z (a + 1) * utCoef z 0 := by
      push_cast at h1 ⊢
      linear_combination (z + (a + 1)) * h1 - z * utCoef z 0 * hu
    have eL : C (z + ((a + 1 : ℕ) : ℚ)) * (C ((a + 1 : ℕ) : ℚ) * (C (hookFz z a 0) * X ^ (a + 0 + 1)))
        = C ((z + ((a + 1 : ℕ) : ℚ)) * (((a + 1 : ℕ) : ℚ) * hookFz z a 0)) * (X : ℚ⟦X⟧) ^ (a + 1) := by
      simp only [map_mul, add_zero]; ring
    have eR : C z * C ((a + 1 : ℕ) : ℚ) * (C (uCoef z (a + 1)) * X ^ (a + 1)) * (C (utCoef z 0) * 1)
        = C (z * ((a + 1 : ℕ) : ℚ) * uCoef z (a + 1) * utCoef z 0) * (X : ℚ⟦X⟧) ^ (a + 1) := by
      simp only [map_mul]; ring
    rw [eL, eR, key]
  · simp only [Nat.add_sub_cancel]
    have h1 := hookFz_mul z a (b + 1)
    have h2 := hookFz_mul z (a + 1) b
    have hu := uCoef_succ z a
    have hv := utCoef_succ z b
    have hD : ((a : ℚ) + b + 2) ≠ 0 := by positivity
    have key : (z + ((a + 1 : ℕ) : ℚ)) * (((a + 1 : ℕ) : ℚ) * hookFz z a (b + 1))
          - ((b + 1 : ℕ) : ℚ) * hookFz z (a + 1) b * (z - ((b + 1 : ℕ) : ℚ))
        = z * (((a + 1 : ℕ) : ℚ) - ((b + 1 : ℕ) : ℚ)) * uCoef z (a + 1) * utCoef z (b + 1) := by
      push_cast at h1 h2 ⊢
      apply mul_left_cancel₀ hD
      linear_combination (z + (a + 1)) * (a + 1) * h1 - (b + 1) * (z - (b + 1)) * h2
        - z * (a + 1) * utCoef z (b + 1) * hu + z * (b + 1) * uCoef z (a + 1) * hv
    have eL : C (z + ((a + 1 : ℕ) : ℚ)) * (C ((a + 1 : ℕ) : ℚ) * (C (hookFz z a (b + 1)) * X ^ (a + (b + 1) + 1)))
          - C ((b + 1 : ℕ) : ℚ) * (C (hookFz z (a + 1) b) * X ^ (a + 1 + b + 1)) * C (z - ((b + 1 : ℕ) : ℚ))
        = C ((z + ((a + 1 : ℕ) : ℚ)) * (((a + 1 : ℕ) : ℚ) * hookFz z a (b + 1))
          - ((b + 1 : ℕ) : ℚ) * hookFz z (a + 1) b * (z - ((b + 1 : ℕ) : ℚ))) * (X : ℚ⟦X⟧) ^ (a + 1 + (b + 1)) := by
      rw [show a + (b + 1) + 1 = a + 1 + (b + 1) by ring, show a + 1 + b + 1 = a + 1 + (b + 1) by ring]
      simp only [map_mul, map_sub]; ring
    have eR : C z * (C ((a + 1 : ℕ) : ℚ) - C ((b + 1 : ℕ) : ℚ)) * (C (uCoef z (a + 1)) * X ^ (a + 1))
          * (C (utCoef z (b + 1)) * X ^ (b + 1))
        = C (z * (((a + 1 : ℕ) : ℚ) - ((b + 1 : ℕ) : ℚ)) * uCoef z (a + 1) * utCoef z (b + 1))
          * (X : ℚ⟦X⟧) ^ (a + 1 + (b + 1)) := by
      simp only [map_mul, map_sub, pow_add]; ring
    rw [eL, eR, key]

end AvgRS
