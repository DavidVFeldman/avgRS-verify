module

public import RequestProject.Frobenius
public import RequestProject.Formal.DetExpand

@[expose] public section

/-!
# The branching recursion for the Giambelli determinant

For Frobenius data `(α | β)` with `k` hooks, `GD k α β = det (F(α_i | β_j))_{i,j<k}` with
`F(a|b) = 1/(a! b! (a+b+1))`.  Using `F(a-1|b) + F(a|b-1) = (a+b+1) F(a|b)` and the
adjugate, we show
`(∑ α + ∑ β + k) · GD k α β = ∑_i GD k (α - e_i) β + ∑_j GD k α (β - e_j) + [Durfee corner]`.
-/

namespace AvgRS

open Finset Matrix Formal

/-- `n · det M = ∑_i det(M with row i replaced by X_i) + ∑_j det(M with column j replaced by
`Y_{·j}`)` whenever `X + Y = (u_i + v_j) M_{ij}` and `n = ∑ u + ∑ v`. -/
theorem det_mul_sum_eq_sum_update {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M X Y : Matrix n n R) (u v : n → R)
    (hXY : ∀ i j, X i j + Y i j = (u i + v j) * M i j) :
    (∑ i, u i + ∑ j, v j) * M.det
      = ∑ i, (M.updateRow i (X i)).det + ∑ j, (M.updateCol j (fun i => Y i j)).det := by
  have hr : ∀ i, (M.updateRow i (X i)).det = ∑ l, M.adjugate l i * X i l := by
    intro i
    rw [← det_transpose, ← updateCol_transpose, ← cramer_apply, cramer_eq_adjugate_mulVec,
      ← adjugate_transpose]
    simp [mulVec, dotProduct]
  have hc : ∀ j, (M.updateCol j (fun i => Y i j)).det = ∑ l, M.adjugate j l * Y l j := by
    intro j
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp [mulVec, dotProduct]
  simp only [hr, hc]
  rw [Finset.sum_comm (f := fun j l => M.adjugate j l * Y l j), ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← mul_add, hXY]
  have h1 : ∑ i, ∑ l, M.adjugate l i * ((u i + v l) * M i l)
      = trace (M * M.adjugate * diagonal u) + trace (M.adjugate * M * diagonal v) := by
    simp only [trace, Matrix.diag, Matrix.mul_diagonal]
    simp only [mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun l i => M.adjugate l i * M i l * v l), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h1, mul_adjugate, adjugate_mul]
  simp [trace, Finset.sum_mul, add_mul, mul_comm, Finset.sum_add_distrib]

/-- The Giambelli determinant of the Frobenius data `(α | β)` with `k` hooks. -/
noncomputable def GD (k : ℕ) (α β : ℕ → ℕ) : ℚ :=
  (Matrix.of fun i j : Fin k => (hookF (α i) (β j) : ℚ)).det

/-- The row replacement `F(a-1|b)` (with the boundary convention at `a = 0`). -/
noncomputable def gA (a b : ℕ) : ℚ := if a = 0 then (if b = 0 then 1 else 0) else hookF (a - 1) b

/-- The column replacement `F(a|b-1)` (with the boundary convention at `b = 0`). -/
noncomputable def gB (a b : ℕ) : ℚ := if b = 0 then 0 else hookF a (b - 1)

lemma gA_add_gB (a b : ℕ) : gA a b + gB a b = ((a + 1 : ℚ) + b) * hookF a b := by
  unfold gA gB hookF
  rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp [Nat.factorial_succ]
    field_simp
    ring
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    simp [Nat.factorial_succ]
    field_simp
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp [Nat.factorial_succ]
    field_simp
    ring

end AvgRS

namespace AvgRS

open Finset Matrix Formal

/-- The Giambelli matrix of `(α | β)`. -/
noncomputable abbrev GM (k : ℕ) (α β : ℕ → ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun i j : Fin k => (hookF (α i) (β j) : ℚ)

lemma GD_eq (k : ℕ) (α β : ℕ → ℕ) : GD k α β = (GM k α β).det := rfl

lemma det_row_ne (k : ℕ) (α β : ℕ → ℕ) (i : Fin k) (hα : α i ≠ 0) :
    ((GM k α β).updateRow i (fun j => gA (α i) (β j))).det
      = GD k (Function.update α i (α i - 1)) β := by
  unfold GD; congr 1; ext i' j
  by_cases h : i' = i
  · subst h; simp [gA, hα]
  · simp [Matrix.updateRow_ne h, Function.update_of_ne (fun e => h (Fin.ext e))]

lemma det_col_ne (k : ℕ) (α β : ℕ → ℕ) (j : Fin k) (hβ : β j ≠ 0) :
    ((GM k α β).updateCol j (fun i => gB (α i) (β j))).det
      = GD k α (Function.update β j (β j - 1)) := by
  unfold GD; congr 1; ext i j'
  by_cases h : j' = j
  · subst h; simp [gB, hβ]
  · simp [Matrix.updateCol_ne h, Function.update_of_ne (fun e => h (Fin.ext e))]

lemma det_col_zero (k : ℕ) (α β : ℕ → ℕ) (j : Fin k) (hβ : β j = 0) :
    ((GM k α β).updateCol j (fun i => gB (α i) (β j))).det = 0 :=
  det_eq_zero_of_column_eq_zero j fun i => by simp [gB, hβ]

lemma SAnti.eq_last_of_eq_zero {k : ℕ} {α : ℕ → ℕ} (h : SAnti k α) {i : ℕ} (hi : i < k)
    (h0 : α i = 0) : i = k - 1 := by
  by_contra hne
  have := h i (k - 1) (by omega) (by omega)
  omega

lemma det_row_zero (k : ℕ) (α β : ℕ → ℕ) (hβ : SAnti k β) (hα : SAnti k α) (i : Fin k)
    (h0 : α i = 0) :
    ((GM k α β).updateRow i (fun j => gA (α i) (β j))).det
      = if β (k - 1) = 0 then GD (k - 1) α β else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := i.2; omega⟩
  have hi : i = Fin.last k := Fin.ext (by simp [hα.eq_last_of_eq_zero i.2 h0])
  subst hi
  simp only [h0, gA, if_true, Nat.add_sub_cancel]
  split_ifs with hb
  · have hrow : (fun j : Fin (k + 1) => if β j = 0 then (1 : ℚ) else 0)
        = fun j => if j = Fin.last k then 1 else 0 := by
      funext j
      by_cases hj : j = Fin.last k
      · subst hj; simp [hb]
      · have hj' : (j : ℕ) < k := by
          have := j.2; have : (j : ℕ) ≠ k := fun e => hj (Fin.ext e); omega
        have := hβ j k hj' (by omega)
        simp [hj]; omega
    rw [hrow, det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
    · simp only [updateRow_self, if_true, mul_one, Fin.succAbove_last, Fin.val_last]
      rw [show (-1 : ℚ) ^ (k + k) = 1 by rw [← two_mul, pow_mul]; simp, one_mul]
      unfold GD; congr 1; ext a b
      simp
    · intro b _ hb; simp [hb]
    · simp
  · refine det_eq_zero_of_row_eq_zero (Fin.last k) fun j => ?_
    have : β j ≠ 0 := by
      intro hj
      have := hβ.eq_last_of_eq_zero j.2 hj
      apply hb; rw [show (j : ℕ) = k by omega] at hj; exact hj
    simp [this]

end AvgRS

namespace AvgRS

open Finset Matrix Formal

/-- **Branching recursion for the Giambelli determinant.** -/
theorem GD_branch (k : ℕ) (α β : ℕ → ℕ) (hα : SAnti k α) (hβ : SAnti k β) :
    ((∑ i ∈ range k, α i + ∑ i ∈ range k, β i + k : ℕ) : ℚ) * GD k α β =
      ∑ i ∈ range k, (if α i = 0 then 0 else GD k (Function.update α i (α i - 1)) β) +
      ∑ j ∈ range k, (if β j = 0 then 0 else GD k α (Function.update β j (β j - 1))) +
      (if 0 < k ∧ α (k - 1) = 0 ∧ β (k - 1) = 0 then GD (k - 1) α β else 0) := by
  have key := det_mul_sum_eq_sum_update (GM k α β) (of fun i j : Fin k => gA (α i) (β j))
    (of fun i j : Fin k => gB (α i) (β j)) (fun i => (α i : ℚ) + 1) (fun j => (β j : ℚ))
    (fun i j => by simp [gA_add_gB])
  have hn : ((∑ i ∈ range k, α i + ∑ i ∈ range k, β i + k : ℕ) : ℚ)
      = ∑ i : Fin k, ((α i : ℚ) + 1) + ∑ j : Fin k, (β j : ℚ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (α i : ℚ) + 1),
      Fin.sum_univ_eq_sum_range (fun i => (β i : ℚ))]
    push_cast
    rw [Finset.sum_add_distrib]
    simp; ring
  have hrow : ∀ i : Fin k,
      ((GM k α β).updateRow i ((of fun i j : Fin k => gA (α i) (β j)) i)).det
      = (if α i = 0 then 0 else GD k (Function.update α i (α i - 1)) β)
        + (if (i : ℕ) = k - 1 then
            (if α (k - 1) = 0 ∧ β (k - 1) = 0 then GD (k - 1) α β else 0) else 0) := by
    intro i
    by_cases h0 : α i = 0
    · have hi := hα.eq_last_of_eq_zero i.2 h0
      rw [if_pos h0, zero_add, if_pos hi, ← hi, h0]
      simp only [true_and]
      exact det_row_zero k α β hβ hα i h0 |>.trans (by rw [hi])
    · have e : (if (i : ℕ) = k - 1 then
            (if α (k - 1) = 0 ∧ β (k - 1) = 0 then GD (k - 1) α β else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · exact absurd (h1 ▸ h2.1) h0
        · rfl
        · rfl
      rw [if_neg h0, e, add_zero]
      exact det_row_ne k α β i h0
  have hcol : ∀ j : Fin k,
      ((GM k α β).updateCol j (fun i => (of fun i j : Fin k => gB (α i) (β j)) i j)).det
      = if β j = 0 then 0 else GD k α (Function.update β j (β j - 1)) := by
    intro j
    split_ifs with h0
    · exact det_col_zero k α β j h0
    · exact det_col_ne k α β j h0
  rw [GD_eq, hn, key]
  simp only [hrow, hcol, Finset.sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun i => if α i = 0 then (0 : ℚ) else
      GD k (Function.update α i (α i - 1)) β),
    Fin.sum_univ_eq_sum_range (fun i => if i = k - 1 then
      (if α (k - 1) = 0 ∧ β (k - 1) = 0 then GD (k - 1) α β else 0) else (0 : ℚ)),
    Fin.sum_univ_eq_sum_range (fun j => if β j = 0 then (0 : ℚ) else
      GD k α (Function.update β j (β j - 1))),
    Finset.sum_ite_eq']
  simp only [mem_range]
  by_cases hk : 0 < k
  · simp only [show k - 1 < k by omega, if_true, hk, true_and]; ring
  · simp only [show ¬ k - 1 < k by omega, if_false, hk, false_and]; ring

end AvgRS
