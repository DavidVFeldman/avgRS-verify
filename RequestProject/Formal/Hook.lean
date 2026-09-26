module

public import Mathlib

@[expose] public section

/-!
# The hook matrix over formal power series

Entries `H_{ab} = r^{a+b+1}/(a! b! (a+b+1))` and `v_a = r^a/a!` as elements of `K⟦X⟧`
(with `r = X`), and the entrywise identities (H1)–(H5) of Lemma 5.6 (`lem:Hids`).
-/

namespace AvgRS.Formal

open PowerSeries
open scoped Nat

variable {K : Type*} [Field K]

/-- The hook entry `H_{ab} = r^{a+b+1}/(a! b! (a+b+1))`. -/
noncomputable def hE (a b : ℕ) : K⟦X⟧ :=
  C ((a ! * b ! * (a + b + 1) : K)⁻¹) * X ^ (a + b + 1)

/-- The vector entry `v_a = r^a/a!`. -/
noncomputable def vE (a : ℕ) : K⟦X⟧ := C ((a ! : K)⁻¹) * X ^ a

lemma natCast_eq_C (a : ℕ) : (a : K⟦X⟧) = C (a : K) := (map_natCast C a).symm

lemma hE_symm (a b : ℕ) : (hE a b : K⟦X⟧) = hE b a := by
  unfold hE
  rw [add_comm a b]
  congr 3
  ring

lemma vE_zero : (vE 0 : K⟦X⟧) = 1 := by simp [vE]

lemma vE_one : (vE 1 : K⟦X⟧) = X := by simp [vE]

lemma X_pow_dvd_hE (a b : ℕ) : (X : K⟦X⟧) ^ (a + b + 1) ∣ hE a b :=
  Dvd.intro_left _ rfl

lemma X_pow_dvd_vE (a : ℕ) : (X : K⟦X⟧) ^ a ∣ vE a := Dvd.intro_left _ rfl

variable [CharZero K]

lemma fact_ne_zero (a : ℕ) : (a ! : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a

lemma succ_ne_zero' (a : ℕ) : ((a : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a

omit [CharZero K] in
lemma deriv_C_mul_X_pow (k : K) (e : ℕ) :
    d⁄dX K (C k * X ^ (e + 1)) = C (k * (e + 1)) * X ^ e := by
  ext n
  rw [coeff_derivative, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  by_cases h : n = e
  · subst h; simp
  · rw [if_neg (by omega), if_neg h, zero_mul]

/-- (H1): `H'_{ab} = v_a v_b`. -/
lemma deriv_hE (a b : ℕ) : d⁄dX K (hE a b) = vE a * vE b := by
  unfold hE vE
  rw [deriv_C_mul_X_pow]
  have ha := fact_ne_zero (K := K) a
  have hb := fact_ne_zero (K := K) b
  have hab : ((a : K) + b + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (a + b)
  calc _ = C ((a ! : K)⁻¹ * (b ! : K)⁻¹) * X ^ (a + b) := by
        congr 2; push_cast; field_simp
    _ = _ := by rw [map_mul, pow_add]; ring

omit [CharZero K] in
/-- (H1): `r v'_a = a v_a`. -/
lemma X_mul_deriv_vE (a : ℕ) : X * d⁄dX K (vE a) = (a : K⟦X⟧) * vE a := by
  unfold vE
  rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, mul_one]
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [pow_succ]; ring

/-- (H2) entrywise: `(a + b + 1) H_{ab} = r v_a v_b`. -/
lemma hE_H2 (a b : ℕ) :
    hE a b * (b : K⟦X⟧) + ((a : K⟦X⟧) + 1) * hE a b = X * vE a * vE b := by
  unfold hE vE
  have ha := fact_ne_zero (K := K) a
  have hb := fact_ne_zero (K := K) b
  have hab : ((a : K) + b + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (a + b)
  rw [natCast_eq_C, natCast_eq_C]
  calc _ = C ((a ! * b ! * (a + b + 1) : K)⁻¹ * ((b : K) + (a + 1))) * X ^ (a + b + 1) := by
        simp only [map_mul, map_add, map_one]; ring
    _ = C ((a ! : K)⁻¹ * (b ! : K)⁻¹) * X ^ (a + b + 1) := by
        congr 2; field_simp; ring
    _ = _ := by rw [map_mul, pow_succ, pow_add]; ring

/-- (H3) entrywise: `(a+1) H_{a+1,b} = (b+1) H_{a,b+1}`. -/
lemma hE_H3 (a b : ℕ) :
    ((a : K⟦X⟧) + 1) * hE (a + 1) b = ((b : K⟦X⟧) + 1) * hE a (b + 1) := by
  unfold hE
  rw [show a + 1 + b + 1 = a + (b + 1) + 1 by ring]
  have ha := fact_ne_zero (K := K) a
  have hb := fact_ne_zero (K := K) b
  have h1 : ((a : K) + 1 + b + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (a + 1 + b)
  have h2 : ((a : K) + (b + 1) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (a + (b + 1))
  rw [natCast_eq_C, natCast_eq_C, ← map_one C, ← map_add, ← map_add, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← map_mul]
  congr 2
  push_cast [Nat.factorial_succ]
  field_simp
  ring

/-- (H4) entrywise, generic case: `(a+1) H_{a,b+1} - (b+1) H_{a+1,b} = (a-b) v_{a+1} v_{b+1}`. -/
lemma hE_H4 (a b : ℕ) :
    ((a : K⟦X⟧) + 1) * hE a (b + 1) - ((b : K⟦X⟧) + 1) * hE (a + 1) b
      = ((a : K⟦X⟧) - (b : K⟦X⟧)) * vE (a + 1) * vE (b + 1) := by
  unfold hE vE
  rw [show a + 1 + b + 1 = a + (b + 1) + 1 by ring]
  have ha := fact_ne_zero (K := K) a
  have hb := fact_ne_zero (K := K) b
  have h1 : ((a : K) + 1 + b + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (a + 1 + b)
  have h2 : ((a : K) + (b + 1) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (a + (b + 1))
  rw [natCast_eq_C, natCast_eq_C, ← map_one C, ← map_add, ← map_add, ← map_sub,
    ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← sub_mul, ← map_sub]
  rw [show (C ((a : K) - b) * (C ((a + 1)! : K)⁻¹ * X ^ (a + 1)) * (C ((b + 1)! : K)⁻¹ * X ^ (b + 1))
      : K⟦X⟧) = C (((a : K) - b) * ((a + 1)! : K)⁻¹ * ((b + 1)! : K)⁻¹) * X ^ (a + (b + 1) + 1) by
    rw [show a + (b + 1) + 1 = (a + 1) + (b + 1) by ring, pow_add]; simp only [map_mul]; ring]
  congr 2
  push_cast [Nat.factorial_succ]
  field_simp
  ring

omit [CharZero K] in
/-- (H4) entrywise, `b = 0` column: `H_{a,0} = v_{a+1}`. -/
lemma hE_zero_right (a : ℕ) : (hE a 0 : K⟦X⟧) = vE (a + 1) := by
  unfold hE vE
  congr 2
  push_cast [Nat.factorial_succ]
  ring

/-- (H5): `(a+1) v_{a+1} = r v_a`. -/
lemma vE_H5a (a : ℕ) : ((a : K⟦X⟧) + 1) * vE (a + 1) = X * vE a := by
  unfold vE
  have ha := fact_ne_zero (K := K) a
  rw [natCast_eq_C, ← map_one C, ← map_add, ← mul_assoc, ← map_mul, pow_succ]
  have : ((a : K) + 1) * ((a + 1)! : K)⁻¹ = (a ! : K)⁻¹ := by
    push_cast [Nat.factorial_succ]
    field_simp
  rw [this]; ring

/-- (H5): `(a+1)² v_{a+1} = r (a+1) v_a`. -/
lemma vE_H5b (a : ℕ) :
    ((a : K⟦X⟧) + 1) ^ 2 * vE (a + 1) = X * (((a : K⟦X⟧) + 1) * vE a) := by
  rw [pow_two, mul_assoc, vE_H5a]; ring

end AvgRS.Formal
