module

public import RequestProject.ShiftProof

@[expose] public section

/-!
# The case `k = 2` of the identity on the line `z + z' = −2` (Theorem 3.6)

For `k = 2` the two sides of Conjecture 3.2 are sums over hooks `(N−b+1, 1^b)` of `N+1` and over
two-column shapes `(2^j, 1^{N−2j})` of `N`.  With `P₀(n) = ∏_{i<n} (i² − t)`,
`P₁(n) = ∏_{i<n} ((i+1)² − t)` and `y_n = P₀(n)/n!²` (the coefficients of
`₂F₁(−s, s; 1; x)`, `s² = t`) the weights are
`w_t(hook) = C(N,b)² P₁(b+1) P₀(N−b)` and `w_t(2^j 1^{N−2j}) = ballot(N,j)² P₁(N−j) P₀(j)`, and
since `t P₁(m) = −P₀(m+1)` the identity becomes, after multiplication by `−t/N!²`,
`∑_{i+j=n} j²(j²−t) y_i y_j = n(n−t) ∑_{i+j=n} (j² − ij) y_i y_j`, `n = N+1`.
With `ϑ = X d/dX` and `Y = ∑ y_n X^n` this is the coefficient of `X^n` in
`Y (ϑ⁴ − t ϑ²) Y = ϑ(ϑ − t) (Y ϑ²Y − (ϑY)²)`, which follows from the hypergeometric equation
`(1 − X) ϑ²Y = −t X Y` alone.  (This replaces the paper's route through Gessel's determinant,
Euler's transformation and contiguous relations by a shorter computation.)
-/

namespace AvgRS

open Finset PowerSeries

/-! ### The sequence `y` and the differential identity -/

/-- `P₀(n) = ∏_{i<n} (i² − t)`. -/
noncomputable def P0 (t : ℚ) (n : ℕ) : ℚ := ∏ i ∈ range n, ((i : ℚ) ^ 2 - t)

/-- `P₁(n) = ∏_{i<n} ((i+1)² − t)`. -/
noncomputable def P1 (t : ℚ) (n : ℕ) : ℚ := ∏ i ∈ range n, (((i : ℚ) + 1) ^ 2 - t)

/-- `y_n = P₀(n) / n!²`, the coefficients of `₂F₁(−s, s; 1; x)` with `s² = t`. -/
noncomputable def ySeq (t : ℚ) (n : ℕ) : ℚ := P0 t n / (n.factorial : ℚ) ^ 2

lemma P0_succ (t : ℚ) (n : ℕ) : P0 t (n + 1) = P0 t n * ((n : ℚ) ^ 2 - t) := by
  rw [P0, prod_range_succ]; rfl

lemma P0_succ' (t : ℚ) (n : ℕ) : P0 t (n + 1) = -t * P1 t n := by
  rw [P0, prod_range_succ', P1]; push_cast; ring

lemma ySeq_succ (t : ℚ) (n : ℕ) :
    ((n : ℚ) + 1) ^ 2 * ySeq t (n + 1) = ((n : ℚ) ^ 2 - t) * ySeq t n := by
  unfold ySeq
  have h : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [P0_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- The Euler operator `ϑ = X d/dX`. -/
noncomputable def th (f : ℚ⟦X⟧) : ℚ⟦X⟧ := X * d⁄dX ℚ f

lemma coeff_th (f : ℚ⟦X⟧) (n : ℕ) : coeff n (th f) = n * coeff n f := by
  unfold th
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

lemma th_mul (f g : ℚ⟦X⟧) : th (f * g) = th f * g + f * th g := by
  unfold th; rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

lemma th_add (f g : ℚ⟦X⟧) : th (f + g) = th f + th g := by unfold th; rw [map_add]; ring

lemma th_sub (f g : ℚ⟦X⟧) : th (f - g) = th f - th g := by unfold th; rw [map_sub]; ring

lemma th_neg (f : ℚ⟦X⟧) : th (-f) = -th f := by unfold th; rw [map_neg]; ring

lemma th_C (c : ℚ) : th (C c) = 0 := by unfold th; rw [derivative_C, mul_zero]

lemma th_X : th (X : ℚ⟦X⟧) = X := by unfold th; rw [derivative_X, mul_one]

lemma th_C_mul (c : ℚ) (f : ℚ⟦X⟧) : th (C c * f) = C c * th f := by
  rw [th_mul, th_C, zero_mul, zero_add]

/-- The series `Y = ∑ y_n X^n = ₂F₁(−s, s; 1; X)`. -/
noncomputable def ySer (t : ℚ) : ℚ⟦X⟧ := PowerSeries.mk (ySeq t)

/-- The hypergeometric equation `(1 − X) ϑ²Y = −t X Y`. -/
lemma ySer_ode (t : ℚ) : (1 - X) * th (th (ySer t)) = -(C t * X * ySer t) := by
  ext n
  rw [sub_mul, one_mul, map_sub, map_neg, mul_comm (C t) X, mul_assoc]
  cases n with
  | zero => simp [coeff_th]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_C_mul, coeff_th, coeff_th, coeff_th, coeff_th]
    simp only [ySer, coeff_mk]
    push_cast
    linear_combination ySeq_succ t m

/-- The differential identity `Y (ϑ⁴ − t ϑ²) Y = ϑ(ϑ − t)(Y ϑ²Y − (ϑY)²)`. -/
theorem ySer_key (t : ℚ) :
    ySer t * (th (th (th (th (ySer t)))) - C t * th (th (ySer t)))
      = th (th (ySer t * th (th (ySer t)) - th (ySer t) ^ 2))
        - C t * th (ySer t * th (th (ySer t)) - th (ySer t) ^ 2) := by
  have hode := ySer_ode t
  set Y := ySer t
  set b := th Y
  set R := th b
  have hode' : (1 - X) * th R = X * R - C t * X * Y - C t * X * b := by
    have h := congrArg th hode
    rw [th_mul, th_sub, th_neg, mul_assoc, th_C_mul, th_mul, th_X,
      show th (1 : ℚ⟦X⟧) = 0 by rw [← map_one C]; exact th_C 1] at h
    linear_combination h
  have hW : th (Y * R - b ^ 2) = Y * th R - b * R := by
    rw [th_sub, th_mul, pow_two, th_mul]; ring
  have hW2 : th (Y * th R - b * R) = Y * th (th R) - R * R := by
    rw [th_sub, th_mul, th_mul]; ring
  rw [hW, hW2]
  have hz : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h; have := congrArg (coeff 0) h; simp at this
  have key : (1 - X) * (R * R + C t * Y * th R - C t * b * R - C t * Y * R) = 0 := by
    linear_combination (R - C t * b - C t * Y) * hode + C t * Y * hode'
  have := (mul_eq_zero.mp key).resolve_left hz
  linear_combination this

/-- Coefficient form: `∑_{i+j=n} j²(j²−t) y_i y_j = n(n−t) ∑_{i+j=n} (j² − ij) y_i y_j`. -/
theorem ySeq_conv (t : ℚ) (n : ℕ) :
    ∑ ij ∈ antidiagonal n, ((ij.2 : ℚ) ^ 2 * ((ij.2 : ℚ) ^ 2 - t)) * ySeq t ij.1 * ySeq t ij.2
      = (n : ℚ) * ((n : ℚ) - t) *
          ∑ ij ∈ antidiagonal n, ((ij.2 : ℚ) ^ 2 - (ij.1 : ℚ) * ij.2) * ySeq t ij.1 * ySeq t ij.2 := by
  have h := congrArg (coeff n) (ySer_key t)
  rw [mul_sub, mul_left_comm (ySer t) (C t) (th (th (ySer t)))] at h
  simp only [map_sub, coeff_C_mul] at h
  simp only [map_sub, coeff_mul, coeff_th, pow_two, ySer, coeff_mk] at h
  rw [← sum_sub_distrib] at h
  have e1 : ∑ ij ∈ antidiagonal n, ((ij.2 : ℚ) ^ 2 * ((ij.2 : ℚ) ^ 2 - t)) * ySeq t ij.1 * ySeq t ij.2
      = ∑ ij ∈ antidiagonal n, ySeq t ij.1 * ((ij.2 : ℚ) * ((ij.2 : ℚ) * ((ij.2 : ℚ) *
          ((ij.2 : ℚ) * ySeq t ij.2))))
        - t * ∑ ij ∈ antidiagonal n, ySeq t ij.1 * ((ij.2 : ℚ) * ((ij.2 : ℚ) * ySeq t ij.2)) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have e2 : ∑ ij ∈ antidiagonal n, ((ij.2 : ℚ) ^ 2 - (ij.1 : ℚ) * ij.2) * ySeq t ij.1 * ySeq t ij.2
      = ∑ ij ∈ antidiagonal n, (ySeq t ij.1 * ((ij.2 : ℚ) * ((ij.2 : ℚ) * ySeq t ij.2))
          - (ij.1 : ℚ) * ySeq t ij.1 * ((ij.2 : ℚ) * ySeq t ij.2)) :=
    sum_congr rfl fun _ _ => by ring
  rw [e1, h, e2]
  ring

/-! ### Hooks and two-column shapes -/

/-- The weight `f_λ² ∏_{(i,j) ∈ λ} ((j − i − 1)² − t)` (this is `contentWt`, `ZLine.lean`). -/
noncomputable def cwt {n : ℕ} (p : n.Partition) (t : ℚ) : ℚ :=
  (numSYT p : ℚ) ^ 2 * ∏ j ∈ range n, ∏ i ∈ range (col p j), (((j : ℚ) - i - 1) ^ 2 - t)

/-- The hook `(N − b + 1, 1^b)` of `N + 1` (for `b ≤ N`). -/
def hookP (N b : ℕ) : (N + 1).Partition := hookPartition N (min b N) (min_le_right b N)

/-- The two-column shape `(2^j, 1^{N−2j})` of `N` (for `2j ≤ N`). -/
def twoColP (N j : ℕ) : N.Partition := twoColPartition N (min j (N / 2)) (by omega)

lemma sum_hook_eq (N : ℕ) (g : (N + 1).Partition → ℚ) :
    ∑ p : (N + 1).Partition with ¬ HasBox p 2 2, g p = ∑ b ∈ range (N + 1), g (hookP N b) := by
  symm
  refine Finset.sum_bij' (fun b _ => hookP N b) (fun p _ => Multiset.card p.parts - 1)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le]
    show Multiset.card (Multiset.filter (fun x => 2 ≤ x) (hookParts (N - min b N) (min b N))) < 2
    simp only [hookParts]
    rw [Multiset.filter_cons, Multiset.filter_eq_nil.mpr (by
      intro x hx; rw [Multiset.mem_replicate] at hx; omega)]
    split_ifs <;> simp
  · intro p _
    simp only [Finset.mem_range]
    have := card_le_sum_of_pos (fun x hx => p.parts_pos hx)
    rw [p.parts_sum] at this
    omega
  · intro b hb
    have hb := mem_range.mp hb
    show Multiset.card (hookParts (N - min b N) (min b N)) - 1 = b
    simp only [hookParts, Multiset.card_cons, Multiset.card_replicate]
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le] at hp
    have hne : p.parts ≠ 0 := by
      intro h; have := p.parts_sum; rw [h] at this; simp at this
    have hc := hook_char (fun x hx => p.parts_pos hx) hp hne
    have hcard := card_le_sum_of_pos (fun x hx => p.parts_pos hx)
    have hcard0 : Multiset.card p.parts ≠ 0 := by simpa using hne
    rw [p.parts_sum] at hc hcard
    apply Nat.Partition.ext
    show hookParts (N - min (Multiset.card p.parts - 1) N) (min (Multiset.card p.parts - 1) N)
      = p.parts
    rw [min_eq_left (by omega)]
    conv_rhs => rw [hc]
    congr 1
    omega

lemma sum_twoCol_eq (N : ℕ) (g : N.Partition → ℚ) :
    ∑ p : N.Partition with ¬ HasBox p 1 3, g p = ∑ j ∈ range (N / 2 + 1), g (twoColP N j) := by
  symm
  refine Finset.sum_bij' (fun j _ => twoColP N j)
    (fun p _ => Multiset.card (p.parts.filter (fun x => 2 ≤ x))) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le, Nat.lt_one_iff,
      Multiset.card_eq_zero]
    show Multiset.filter (fun x => 3 ≤ x)
      (twoColParts (min j (N / 2)) (N - 2 * min j (N / 2))) = 0
    apply Multiset.filter_eq_nil.mpr
    intro x hx
    simp only [twoColParts, Multiset.mem_add, Multiset.mem_replicate] at hx
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le, Nat.lt_one_iff,
      Multiset.card_eq_zero, Multiset.filter_eq_nil, not_le] at hp
    have hc := twoCol_char (fun x hx => p.parts_pos hx) hp
    have hs := p.parts_sum
    set a := Multiset.card (p.parts.filter (fun x => 2 ≤ x))
    set b := Multiset.card (p.parts.filter (fun x => ¬ 2 ≤ x))
    rw [hc] at hs
    simp [twoColParts] at hs
    simp only [Finset.mem_range]
    omega
  · intro j hj
    have hj := mem_range.mp hj
    show Multiset.card (Multiset.filter (fun x => 2 ≤ x)
      (twoColParts (min j (N / 2)) (N - 2 * min j (N / 2)))) = j
    rw [min_eq_left (by omega)]
    simp only [twoColParts, Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega),
      Multiset.filter_eq_nil.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega)]
    simp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le, Nat.lt_one_iff,
      Multiset.card_eq_zero, Multiset.filter_eq_nil, not_le] at hp
    have hc := twoCol_char (fun x hx => p.parts_pos hx) hp
    have hs := p.parts_sum
    set a := Multiset.card (p.parts.filter (fun x => 2 ≤ x))
    set b := Multiset.card (p.parts.filter (fun x => ¬ 2 ≤ x))
    rw [hc] at hs
    simp [twoColParts] at hs
    apply Nat.Partition.ext
    show twoColParts (min a (N / 2)) (N - 2 * min a (N / 2)) = p.parts
    rw [min_eq_left (by omega)]
    conv_rhs => rw [hc]
    congr 1
    omega

lemma prod_col_extend {n : ℕ} (p : n.Partition) (F : ℕ → ℕ → ℚ) (m : ℕ) (hm : n ≤ m) :
    ∏ j ∈ range n, ∏ i ∈ range (col p j), F j i = ∏ j ∈ range m, ∏ i ∈ range (col p j), F j i := by
  rw [← prod_range_mul_prod_Ico _ hm, prod_eq_one (s := Ico n m), mul_one]
  intro j hj
  rw [col_eq_zero p (mem_Ico.mp hj).1, range_zero, prod_empty]

lemma col_hookP (N b : ℕ) (hb : b ≤ N) (j : ℕ) :
    col (hookP N b) j = if j = 0 then b + 1 else if j ≤ N - b then 1 else 0 := by
  unfold col
  show Multiset.card (Multiset.filter (fun x => j < x) (hookParts (N - min b N) (min b N))) = _
  rw [min_eq_left hb]
  simp only [hookParts]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Multiset.filter_eq_self.mpr (by
      intro x hx
      simp only [Multiset.mem_cons, Multiset.mem_replicate] at hx
      omega)]
    simp
  · rw [Multiset.filter_cons, Multiset.filter_eq_nil.mpr (by
      intro x hx
      rw [Multiset.mem_replicate] at hx
      omega)]
    rw [if_neg (show ¬ (j = 0) by omega)]
    by_cases h : j ≤ N - b
    · rw [if_pos h, if_pos (by omega)]; simp
    · rw [if_neg h, if_neg (by omega)]; simp

lemma col_twoColP (N j : ℕ) (hj : 2 * j ≤ N) (c : ℕ) :
    col (twoColP N j) c = if c = 0 then N - j else if c = 1 then j else 0 := by
  unfold col
  show Multiset.card (Multiset.filter (fun x => c < x)
    (twoColParts (min j (N / 2)) (N - 2 * min j (N / 2)))) = _
  rw [min_eq_left (by omega : j ≤ N / 2)]
  simp only [twoColParts, Multiset.filter_add, Multiset.card_add]
  rcases Nat.lt_trichotomy c 1 with h | rfl | h
  · obtain rfl : c = 0 := by omega
    rw [Multiset.filter_eq_self.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega),
      Multiset.filter_eq_self.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega)]
    simp; omega
  · rw [Multiset.filter_eq_self.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega),
      Multiset.filter_eq_nil.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega)]
    simp
  · rw [Multiset.filter_eq_nil.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega),
      Multiset.filter_eq_nil.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega),
      if_neg (show ¬ c = 0 by omega), if_neg (show ¬ c = 1 by omega)]
    simp

lemma numSYT_hookP (N b : ℕ) (hb : b ≤ N) : numSYT (hookP N b) = N.choose b := by
  show syt (hookParts (N - min b N) (min b N)) = _
  rw [min_eq_left hb, syt_hookParts, Nat.sub_add_cancel hb]

lemma numSYT_twoColP (N j : ℕ) (hj : 2 * j ≤ N) : (numSYT (twoColP N j) : ℤ) = ballot N j := by
  show (syt (twoColParts (min j (N / 2)) (N - 2 * min j (N / 2))) : ℤ) = _
  rw [min_eq_left (by omega : j ≤ N / 2), syt_twoColParts]
  congr 1; omega

lemma cwt_hookP (N b : ℕ) (hb : b ≤ N) (t : ℚ) :
    cwt (hookP N b) t = (N.choose b : ℚ) ^ 2 * P1 t (b + 1) * P0 t (N - b) := by
  unfold cwt
  rw [numSYT_hookP N b hb, prod_range_succ', col_hookP N b hb 0, if_pos rfl, mul_assoc]
  congr 1
  rw [mul_comm]
  congr 1
  · unfold P1
    refine prod_congr rfl fun i _ => ?_
    push_cast; ring
  · rw [← prod_range_mul_prod_Ico _ (show N - b ≤ N by omega), prod_eq_one (s := Ico (N - b) N),
      mul_one]
    · unfold P0
      refine prod_congr rfl fun j hj => ?_
      have hj := mem_range.mp hj
      rw [col_hookP N b hb, if_neg (by omega), if_pos (by omega)]
      simp
    · intro k hk
      have := (mem_Ico.mp hk).1
      rw [col_hookP N b hb, if_neg (by omega), if_neg (by omega)]
      simp

lemma cwt_twoColP (N j : ℕ) (hj : 2 * j ≤ N) (t : ℚ) :
    cwt (twoColP N j) t = ((ballot N j : ℤ) : ℚ) ^ 2 * P1 t (N - j) * P0 t j := by
  unfold cwt
  have hf : ((numSYT (twoColP N j) : ℕ) : ℚ) = ((ballot N j : ℤ) : ℚ) := by
    exact_mod_cast numSYT_twoColP N j hj
  rw [hf, prod_col_extend _ _ (N + 2) (by omega), prod_range_succ', prod_range_succ',
    prod_eq_one (s := range N), one_mul, col_twoColP N j hj 0, col_twoColP N j hj 1,
    if_pos rfl, if_neg one_ne_zero, if_pos rfl, mul_assoc, mul_comm (∏ i ∈ range j, _)]
  · congr 2
    · unfold P1
      refine prod_congr rfl fun i _ => ?_
      push_cast; ring
    · unfold P0
      refine prod_congr rfl fun i _ => ?_
      push_cast; ring
  · intro c _
    rw [col_twoColP N j hj, if_neg (by omega), if_neg (by omega)]
    simp

/-! ### Assembly -/

lemma hook_term (N b : ℕ) (hb : b ≤ N) (t : ℚ) :
    t * ((N.choose b : ℚ) ^ 2 * P1 t (b + 1) * P0 t (N - b))
      = -((N.factorial : ℚ) ^ 2) * ((((b + 1 : ℕ) : ℚ) ^ 2 * (((b + 1 : ℕ) : ℚ) ^ 2 - t))
          * ySeq t (N - b) * ySeq t (b + 1)) := by
  have h1 := P0_succ' t (b + 1)
  have h2 := P0_succ t (b + 1)
  have hc : (N.choose b : ℚ) * b.factorial * (N - b).factorial = N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hb
  have hb1 : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hb2 : ((N - b).factorial : ℚ) ≠ 0 := by exact_mod_cast (N - b).factorial_ne_zero
  unfold ySeq
  rw [← hc, Nat.factorial_succ]
  push_cast at h2 ⊢
  field_simp
  linear_combination ((N.choose b : ℚ) ^ 2 * P0 t (N - b)) * (h1 - h2)

lemma ballot_fact (N j : ℕ) (hj : j ≤ N + 1) :
    ((ballot N j : ℤ) : ℚ) * ((N + 1 - j).factorial : ℚ) * (j.factorial : ℚ)
      = N.factorial * ((N : ℚ) + 1 - 2 * j) := by
  rcases j with _ | k
  · simp [ballot, Nat.factorial_succ]; ring
  · have hk : k ≤ N := by omega
    have hB : (N.choose k : ℚ) * k.factorial * (N - k).factorial = N.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    have hS : (N.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = N.choose k * ((N : ℚ) - k) := by
      have := Nat.choose_succ_right_eq N k
      rw [← Nat.cast_sub hk]
      exact_mod_cast this
    simp only [ballot, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    rw [show N + 1 - (k + 1) = N - k by omega, Nat.factorial_succ]
    push_cast
    linear_combination ((k.factorial : ℚ) * (N - k).factorial) * hS
      + ((N : ℚ) - 1 - 2 * k) * hB

lemma twoCol_term (N j : ℕ) (hj : j ≤ N) (t : ℚ) :
    t * (((ballot N j : ℤ) : ℚ) ^ 2 * P1 t (N - j) * P0 t j)
      = -((N.factorial : ℚ) ^ 2) * (((N : ℚ) + 1 - 2 * j) ^ 2 * ySeq t j * ySeq t (N + 1 - j)) := by
  have hbf := ballot_fact N j (by omega)
  have h1 := P0_succ' t (N - j)
  rw [show N - j + 1 = N + 1 - j by omega] at h1
  have hj1 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hj2 : ((N + 1 - j).factorial : ℚ) ≠ 0 := by exact_mod_cast (N + 1 - j).factorial_ne_zero
  rw [show -((N.factorial : ℚ) ^ 2) * (((N : ℚ) + 1 - 2 * j) ^ 2 * ySeq t j * ySeq t (N + 1 - j))
      = -((N.factorial : ℚ) * ((N : ℚ) + 1 - 2 * j)) ^ 2 * (ySeq t j * ySeq t (N + 1 - j)) by ring,
    ← hbf]
  unfold ySeq
  field_simp
  linear_combination (((ballot N j : ℤ) : ℚ) ^ 2 * P0 t j) * h1

lemma sum_half_symm (N : ℕ) (f : ℕ → ℚ) (hsymm : ∀ j ≤ N + 1, f (N + 1 - j) = f j)
    (hmid : ∀ j, 2 * j = N + 1 → f j = 0) :
    2 * ∑ j ∈ range (N / 2 + 1), f j = ∑ j ∈ range (N + 2), f j := by
  obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
  · rw [show 2 * M / 2 + 1 = M + 1 by omega, show 2 * M + 2 = (M + 1) + (M + 1) by ring,
      Finset.sum_range_add f (M + 1) (M + 1), two_mul]
    congr 1
    rw [← sum_range_reflect (fun k => f (M + 1 + k)) (M + 1)]
    refine sum_congr rfl fun x hx => ?_
    have hx := mem_range.mp hx
    rw [← hsymm x (by omega)]
    congr 1; omega
  · rw [show (2 * M + 1) / 2 + 1 = M + 1 by omega, show 2 * M + 1 + 2 = (M + 1) + (M + 2) by ring,
      Finset.sum_range_add f (M + 1) (M + 2), two_mul,
      Finset.sum_range_succ' (fun k => f (M + 1 + k)) (M + 1),
      hmid (M + 1 + 0) (by omega), add_zero]
    congr 1
    rw [← sum_range_reflect (fun k => f (M + 1 + (k + 1))) (M + 1)]
    refine sum_congr rfl fun x hx => ?_
    have hx := mem_range.mp hx
    rw [← hsymm x (by omega)]
    congr 1; omega

lemma antidiag_sq_sub (N : ℕ) (g : ℕ → ℚ) :
    ∑ ij ∈ antidiagonal N, ((ij.1 : ℚ) - ij.2) ^ 2 * g ij.1 * g ij.2
      = 2 * ∑ ij ∈ antidiagonal N, ((ij.2 : ℚ) ^ 2 - (ij.1 : ℚ) * ij.2) * g ij.1 * g ij.2 := by
  have hswap : ∑ ij ∈ antidiagonal N, ((ij.1 : ℚ) ^ 2 - (ij.1 : ℚ) * ij.2) * g ij.1 * g ij.2
      = ∑ ij ∈ antidiagonal N, ((ij.2 : ℚ) ^ 2 - (ij.1 : ℚ) * ij.2) * g ij.1 * g ij.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    refine sum_congr rfl fun ij _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]; ring
  rw [two_mul]
  conv_rhs => arg 1; rw [← hswap]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ij _ => by ring

lemma hook_sum_mul_t (N : ℕ) (t : ℚ) :
    t * ∑ b ∈ range (N + 1), (N.choose b : ℚ) ^ 2 * P1 t (b + 1) * P0 t (N - b)
      = -((N.factorial : ℚ) ^ 2) * ∑ ij ∈ antidiagonal (N + 1),
          ((ij.2 : ℚ) ^ 2 * ((ij.2 : ℚ) ^ 2 - t)) * ySeq t ij.1 * ySeq t ij.2 := by
  rw [mul_sum, sum_congr rfl (fun b hb => hook_term N b (by have := mem_range.mp hb; omega) t),
    ← mul_sum]
  congr 1
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    zero_add]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      (((j + 1 : ℕ) : ℚ) ^ 2 * (((j + 1 : ℕ) : ℚ) ^ 2 - t)) * ySeq t i * ySeq t (j + 1)) N,
    ← sum_range_reflect]
  refine sum_congr rfl fun b hb => ?_
  have hb := mem_range.mp hb
  rw [show N + 1 - 1 - b = N - b by omega, show N - (N - b) = b by omega]

lemma twoCol_sum_mul_t (N : ℕ) (t : ℚ) :
    t * ∑ j ∈ range (N / 2 + 1), ((ballot N j : ℤ) : ℚ) ^ 2 * P1 t (N - j) * P0 t j
      = -((N.factorial : ℚ) ^ 2) * ∑ ij ∈ antidiagonal (N + 1),
          ((ij.2 : ℚ) ^ 2 - (ij.1 : ℚ) * ij.2) * ySeq t ij.1 * ySeq t ij.2 := by
  rw [mul_sum, sum_congr rfl (fun j hj => twoCol_term N j (by have := mem_range.mp hj; omega) t),
    ← mul_sum]
  congr 1
  have hfull : ∑ j ∈ range (N + 2), ((N : ℚ) + 1 - 2 * j) ^ 2 * ySeq t j * ySeq t (N + 1 - j)
      = ∑ ij ∈ antidiagonal (N + 1), ((ij.1 : ℚ) - ij.2) ^ 2 * ySeq t ij.1 * ySeq t ij.2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      ((i : ℚ) - j) ^ 2 * ySeq t i * ySeq t j) (N + 1)]
    refine sum_congr rfl fun j hj => ?_
    have hj := mem_range.mp hj
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have hhalf := sum_half_symm N (fun j => ((N : ℚ) + 1 - 2 * j) ^ 2 * ySeq t j * ySeq t (N + 1 - j))
    (fun j hj => by
      simp only
      rw [show N + 1 - (N + 1 - j) = j by omega, Nat.cast_sub hj]
      push_cast
      ring)
    (fun j hj => by
      simp only
      have : (N : ℚ) + 1 - 2 * j = 0 := by
        have : ((2 * j : ℕ) : ℚ) = ((N + 1 : ℕ) : ℚ) := by rw [hj]
        push_cast at this; linarith
      rw [this]; ring)
  simp only at hhalf
  rw [hfull, antidiag_sq_sub] at hhalf
  linarith

/-- The polynomial in `t` behind `cwt`. -/
noncomputable def cwtPoly {n : ℕ} (p : n.Partition) : Polynomial ℚ :=
  Polynomial.C ((numSYT p : ℚ) ^ 2) *
    ∏ j ∈ range n, ∏ i ∈ range (col p j), (Polynomial.C (((j : ℚ) - i - 1) ^ 2) - Polynomial.X)

lemma cwt_eq_eval {n : ℕ} (p : n.Partition) (t : ℚ) : cwt p t = (cwtPoly p).eval t := by
  simp [cwt, cwtPoly, Polynomial.eval_prod]

/-- **Theorem 3.6** in the form of `zline_identity_two`, for the weight `cwt`. -/
theorem cwt_identity_two (N : ℕ) (t : ℚ) :
    ∑ p : (N + 1).Partition with ¬ HasBox p 2 2, cwt p t
      = (N + 1) * ((N : ℚ) + 1 - t) * ∑ p : N.Partition with ¬ HasBox p 1 3, cwt p t := by
  have main : ∀ t : ℚ, t ≠ 0 → ∑ p : (N + 1).Partition with ¬ HasBox p 2 2, cwt p t
      = (N + 1) * ((N : ℚ) + 1 - t) * ∑ p : N.Partition with ¬ HasBox p 1 3, cwt p t := by
    intro t ht
    rw [sum_hook_eq N (fun p => cwt p t), sum_twoCol_eq N (fun p => cwt p t),
      sum_congr rfl fun b hb => cwt_hookP N b (by have := mem_range.mp hb; omega) t,
      sum_congr rfl fun j hj => cwt_twoColP N j (by have := mem_range.mp hj; omega) t]
    apply mul_left_cancel₀ ht
    have h1 := hook_sum_mul_t N t
    have h2 := twoCol_sum_mul_t N t
    have h3 := ySeq_conv t (N + 1)
    push_cast at h3
    linear_combination h1 - ((N : ℚ) + 1) * ((N : ℚ) + 1 - t) * h2
      - (N.factorial : ℚ) ^ 2 * h3
  set D : Polynomial ℚ := ∑ p : (N + 1).Partition with ¬ HasBox p 2 2, cwtPoly p
    - Polynomial.C ((N : ℚ) + 1) * (Polynomial.C ((N : ℚ) + 1) - Polynomial.X)
      * ∑ p : N.Partition with ¬ HasBox p 1 3, cwtPoly p with hDdef
  have hD : ∀ t : ℚ, D.eval t = ∑ p : (N + 1).Partition with ¬ HasBox p 2 2, cwt p t
      - ((N : ℚ) + 1) * ((N : ℚ) + 1 - t) * ∑ p : N.Partition with ¬ HasBox p 1 3, cwt p t := by
    intro t
    simp only [hDdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_finset_sum,
      Polynomial.eval_C, Polynomial.eval_X, cwt_eq_eval]
  have hD0 : D = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (Set.Finite.infinite_compl (Set.finite_singleton (0 : ℚ))).mono fun t ht => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hD, main t ht, sub_self]
  have := hD t
  rw [hD0, Polynomial.eval_zero] at this
  linarith

end AvgRS
