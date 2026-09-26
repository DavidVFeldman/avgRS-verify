module

public import RequestProject.AverageTableau

@[expose] public section

namespace AvgRS

open Polynomial Finset
open scoped Nat

lemma coeff_one_add_X_sq_pow (j n : ℕ) :
    ((1 + X ^ 2 : ℕ[X]) ^ j).coeff n = if 2 ∣ n then j.choose (n / 2) else 0 := by
  have : (1 + X ^ 2 : ℕ[X]) ^ j = expand ℕ 2 ((1 + X) ^ j) := by
    simp [map_pow, map_add]
  rw [this, coeff_expand (by norm_num), add_comm, coeff_X_add_one_pow, Nat.cast_id]

lemma trinomial_coeff (n k : ℕ) :
    (2 * n).choose k = ∑ j ∈ range (n + 1),
      n.choose j * 2 ^ (n - j) * (if n - j ≤ k then ((1 + X ^ 2 : ℕ[X]) ^ j).coeff (k - (n - j))
        else 0) := by
  have h : ((1 + X : ℕ[X]) ^ (2 * n)) = ((1 + X ^ 2) + C 2 * X) ^ n := by
    rw [pow_mul]; congr 1; simp only [map_ofNat]; ring
  have h2 := congrArg (fun p => p.coeff k) h
  simp only at h2
  rw [add_comm (1 : ℕ[X]) X, coeff_X_add_one_pow, Nat.cast_id] at h2
  rw [h2, add_pow, finset_sum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_pow, ← C_pow, mul_comm, ← C_eq_natCast, coeff_C_mul, mul_left_comm, coeff_C_mul,
    coeff_mul_X_pow', Nat.cast_id]
  ring


/-- The modified Bessel function of the first kind of integer order,
`I_ν(x) = ∑_m (x/2)^{2m+ν} / (m! (m+ν)!)`. -/
noncomputable def besselI (ν : ℕ) (x : ℝ) : ℝ := ∑' m : ℕ, (x / 2) ^ (2 * m + ν) / (m ! * (m + ν)!)

/-- Even-indexed coefficients of `I₀(2)`. -/
noncomputable def bI0 (k : ℕ) : ℝ := if k % 2 = 0 then 1 / ((k / 2)! * (k / 2)! : ℝ) else 0
/-- Odd-indexed coefficients of `I₁(2)`. -/
noncomputable def bI1 (k : ℕ) : ℝ := if k % 2 = 1 then 1 / ((k / 2)! * (k / 2 + 1)! : ℝ) else 0

lemma bI0_even (m : ℕ) : bI0 (2 * m) = 1 / (m ! * m ! : ℝ) := by
  simp [bI0]
lemma bI0_odd (m : ℕ) : bI0 (2 * m + 1) = 0 := by
  simp [bI0, Nat.add_mod]
lemma bI1_even (m : ℕ) : bI1 (2 * m) = 0 := by
  simp [bI1]
lemma bI1_odd (m : ℕ) : bI1 (2 * m + 1) = 1 / (m ! * (m + 1)! : ℝ) := by
  have h : (2 * m + 1) / 2 = m := by omega
  simp [bI1, Nat.add_mod, h]

lemma inv_fact_mul_le (m k : ℕ) : (1 : ℝ) / (m ! * k !) ≤ 1 / m ! := by
  have h1 : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have : (0 : ℝ) < m ! := by positivity
  nlinarith

lemma summable_inv_fact_mul (j : ℕ) : Summable (fun m : ℕ => (1 : ℝ) / (m ! * (m + j)!)) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => inv_fact_mul_le m _) ?_
  simpa using Real.summable_pow_div_factorial 1

lemma summable_bI0 : Summable bI0 := by
  apply Summable.even_add_odd
  · simpa [bI0_even] using summable_inv_fact_mul 0
  · simp [bI0_odd]

lemma summable_bI1 : Summable bI1 := by
  apply Summable.even_add_odd
  · simp [bI1_even]
  · simpa [bI1_odd] using summable_inv_fact_mul 1

lemma tsum_bI0 : ∑' k, bI0 k = besselI 0 2 := by
  rw [← tsum_even_add_odd (by simpa [bI0_even] using summable_inv_fact_mul 0) (by simp [bI0_odd])]
  simp [bI0_even, bI0_odd, besselI]

lemma tsum_bI1 : ∑' k, bI1 k = besselI 1 2 := by
  rw [← tsum_even_add_odd (by simp [bI1_even]) (by simpa [bI1_odd] using summable_inv_fact_mul 1)]
  simp [bI1_even, bI1_odd, besselI]

lemma centralBinom_div_factorial (n : ℕ) :
    ((2 * n).choose n : ℝ) / n ! = ∑ k ∈ range (n + 1), bI0 k * (2 ^ (n - k) / (n - k)!) := by
  rw [trinomial_coeff n n, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [if_pos (by omega), show n - (n - j) = j by omega, coeff_one_add_X_sq_pow]
  have hc1 : (n.choose j : ℝ) * j ! * (n - j)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · have hc2 : ((2 * m).choose m : ℝ) * m ! * m ! = (2 * m)! := by
      have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
      rw [show 2 * m - m = m by omega] at this
      exact_mod_cast this
    rw [if_pos (by omega), show 2 * m / 2 = m by omega, bI0_even]
    have h0 : (n.choose (2 * m) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj).ne'
    have h0' : ((2 * m).choose m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [← hc1, ← hc2]
    push_cast
    field_simp
  · rw [if_neg (by omega), bI0_odd]
    simp

lemma choose_succ_div_factorial (n : ℕ) :
    ((2 * n).choose (n + 1) : ℝ) / n ! = ∑ k ∈ range (n + 1), bI1 k * (2 ^ (n - k) / (n - k)!) := by
  rw [trinomial_coeff n (n + 1), Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [if_pos (by omega), show n + 1 - (n - j) = j + 1 by omega, coeff_one_add_X_sq_pow]
  have hc1 : (n.choose j : ℝ) * j ! * (n - j)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · rw [if_neg (by omega), bI1_even]
    simp
  · have hc2 : ((2 * m + 1).choose (m + 1) : ℝ) * (m + 1)! * m ! = (2 * m + 1)! := by
      have := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 2 * m + 1 by omega)
      rw [show 2 * m + 1 - (m + 1) = m by omega] at this
      exact_mod_cast this
    rw [if_pos (by omega), show (2 * m + 1 + 1) / 2 = m + 1 by omega, bI1_odd]
    have h0 : (n.choose (2 * m + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj).ne'
    have h0' : ((2 * m + 1).choose (m + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [← hc1, ← hc2]
    push_cast
    field_simp

lemma exp_two_eq_tsum : Real.exp 2 = ∑' n : ℕ, (2 : ℝ) ^ n / n ! := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma tsum_mul_exp_two {b : ℕ → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) :
    (∑' k, b k) * Real.exp 2 = ∑' n, ∑ k ∈ range (n + 1), b k * (2 ^ (n - k) / (n - k)!) := by
  rw [exp_two_eq_tsum, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm]
  · simpa [Real.norm_eq_abs, abs_of_nonneg (hb0 _)] using hb
  · simpa [Real.norm_eq_abs, abs_of_nonneg, abs_div] using Real.summable_pow_div_factorial 2

/-- `∑_N C(2N,N)/N! = e² I₀(2)`. -/
theorem tsum_centralBinom_div_factorial :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) / n ! = Real.exp 2 * besselI 0 2 := by
  rw [mul_comm, ← tsum_bI0, tsum_mul_exp_two summable_bI0 (fun k => by
    unfold bI0; split_ifs <;> positivity)]
  exact tsum_congr centralBinom_div_factorial

/-- `∑_N C(2N,N+1)/N! = e² I₁(2)`. -/
theorem tsum_choose_succ_div_factorial :
    ∑' n : ℕ, ((2 * n).choose (n + 1) : ℝ) / n ! = Real.exp 2 * besselI 1 2 := by
  rw [mul_comm, ← tsum_bI1, tsum_mul_exp_two summable_bI1 (fun k => by
    unfold bI1; split_ifs <;> positivity)]
  exact tsum_congr choose_succ_div_factorial

lemma catalan_eq_sub (n : ℕ) :
    (catalan n : ℝ) = ((2 * n).choose n : ℝ) - ((2 * n).choose (n + 1) : ℝ) := by
  have h1 := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h1
  have h2 := Nat.choose_succ_right_eq (2 * n) n
  rw [show 2 * n - n = n by omega] at h2
  have h1' : ((n : ℝ) + 1) * catalan n = ((2 * n).choose n : ℝ) := by exact_mod_cast h1
  have h2' : ((2 * n).choose (n + 1) : ℝ) * (n + 1) = ((2 * n).choose n : ℝ) * n := by
    exact_mod_cast h2
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  linear_combination h1' + h2'

lemma summable_choose_div_factorial (f : ℕ → ℕ) :
    Summable (fun n : ℕ => ((2 * n).choose (f n) : ℝ) / n !) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_div_factorial 4)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := Nat.choose_le_two_pow (2 * n) (f n)
  have h' : ((2 * n).choose (f n) : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by exact_mod_cast h
  calc ((2 * n).choose (f n) : ℝ) ≤ (2 : ℝ) ^ (2 * n) := h'
    _ = 4 ^ n := by rw [pow_mul]; norm_num

/-- **Proposition 1.10 (`prop:closed`):** `F(1,3) = e² (I₀(2) - I₁(2))`. -/
theorem avgEntry_one_three_bessel :
    avgEntry 1 3 = Real.exp 2 * (besselI 0 2 - besselI 1 2) := by
  rw [avgEntry_one_three, mul_sub, ← tsum_centralBinom_div_factorial,
    ← tsum_choose_succ_div_factorial, ← Summable.tsum_sub]
  · refine tsum_congr fun n => ?_
    rw [catalan_eq_sub, sub_div]
  · exact summable_choose_div_factorial (fun n => n)
  · exact summable_choose_div_factorial (fun n => n + 1)

end AvgRS
