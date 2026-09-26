module

public import Mathlib

@[expose] public section

/-!
# Entrywise derivatives of matrices over `K⟦X⟧`, divisibility of matrix entries,
and Jacobi's formula for the derivative of a determinant.
-/

namespace AvgRS.Formal

open PowerSeries Matrix

variable {K : Type*} [CommRing K]

section Deriv

variable {ι : Type*}

/-- Entrywise derivative of a matrix. -/
noncomputable def dM (M : Matrix ι ι K⟦X⟧) : Matrix ι ι K⟦X⟧ := M.map (d⁄dX K)

/-- Entrywise derivative of a vector. -/
noncomputable def dV (u : ι → K⟦X⟧) : ι → K⟦X⟧ := fun i => d⁄dX K (u i)

@[simp] lemma dM_apply (M : Matrix ι ι K⟦X⟧) (i j : ι) : dM M i j = d⁄dX K (M i j) := rfl

@[simp] lemma dV_apply (u : ι → K⟦X⟧) (i : ι) : dV u i = d⁄dX K (u i) := rfl

lemma dM_mul [Fintype ι] (M N : Matrix ι ι K⟦X⟧) : dM (M * N) = dM M * N + M * dM N := by
  refine Matrix.ext fun i j => ?_
  simp only [dM_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma dV_mulVec [Fintype ι] (M : Matrix ι ι K⟦X⟧) (u : ι → K⟦X⟧) :
    dV (M *ᵥ u) = dM M *ᵥ u + M *ᵥ dV u := by
  funext i
  simp only [dV_apply, Matrix.mulVec, dotProduct, Pi.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, dM_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma d_dotProduct [Fintype ι] (u w : ι → K⟦X⟧) :
    d⁄dX K (u ⬝ᵥ w) = dV u ⬝ᵥ w + u ⬝ᵥ dV w := by
  simp only [dotProduct, map_sum, Derivation.leibniz, smul_eq_mul, dV_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma dM_add (M N : Matrix ι ι K⟦X⟧) : dM (M + N) = dM M + dM N := by
  refine Matrix.ext fun i j => ?_; simp

lemma dM_sub (M N : Matrix ι ι K⟦X⟧) : dM (M - N) = dM M - dM N := by
  refine Matrix.ext fun i j => ?_; simp

lemma dV_add (u w : ι → K⟦X⟧) : dV (u + w) = dV u + dV w := by
  funext i; simp

lemma dV_sub (u w : ι → K⟦X⟧) : dV (u - w) = dV u - dV w := by
  funext i; simp

lemma dM_one [DecidableEq ι] : dM (1 : Matrix ι ι K⟦X⟧) = 0 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

lemma dM_smul (f : K⟦X⟧) (M : Matrix ι ι K⟦X⟧) :
    dM (f • M) = f • dM M + d⁄dX K f • M := by
  refine Matrix.ext fun i j => ?_; simp [Derivation.leibniz]; ring

lemma dM_C_smul (k : K) (M : Matrix ι ι K⟦X⟧) : dM (C k • M) = C k • dM M := by
  rw [dM_smul, derivative_C, zero_smul, add_zero]

lemma dV_smul (f : K⟦X⟧) (u : ι → K⟦X⟧) : dV (f • u) = f • dV u + d⁄dX K f • u := by
  funext i; simp [Derivation.leibniz]; ring

lemma dM_vecMulVec (u w : ι → K⟦X⟧) :
    dM (vecMulVec u w) = vecMulVec (dV u) w + vecMulVec u (dV w) := by
  refine Matrix.ext fun i j => ?_; simp [vecMulVec_apply, Derivation.leibniz]; ring

lemma dM_inv [Fintype ι] [DecidableEq ι] (B : Matrix ι ι K⟦X⟧) (hB : IsUnit B.det) :
    dM B⁻¹ = -(B⁻¹ * dM B * B⁻¹) := by
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have h3 : dM B * B⁻¹ + B * dM B⁻¹ = 0 := by rw [← dM_mul, h1, dM_one]
  calc dM B⁻¹ = B⁻¹ * (B * dM B⁻¹) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = B⁻¹ * (-(dM B * B⁻¹)) := by rw [eq_neg_of_add_eq_zero_right h3]
    _ = _ := by rw [Matrix.mul_neg, Matrix.mul_assoc]

end Deriv

section Dvd

variable {ι : Type*}

/-- All entries of `M` are divisible by `X ^ k`. -/
def DvdM (k : ℕ) (M : Matrix ι ι K⟦X⟧) : Prop := ∀ i j, (X : K⟦X⟧) ^ k ∣ M i j

/-- All entries of `u` are divisible by `X ^ k`. -/
def DvdV (k : ℕ) (u : ι → K⟦X⟧) : Prop := ∀ i, (X : K⟦X⟧) ^ k ∣ u i

variable {k : ℕ}

lemma DvdM.mul_left [Fintype ι] {M : Matrix ι ι K⟦X⟧} (h : DvdM k M) (N : Matrix ι ι K⟦X⟧) :
    DvdM k (N * M) := fun i j => by
  rw [Matrix.mul_apply]; exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (h l j) _

lemma DvdM.mul_right [Fintype ι] {M : Matrix ι ι K⟦X⟧} (h : DvdM k M) (N : Matrix ι ι K⟦X⟧) :
    DvdM k (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (h i l) _

lemma DvdM.smul {M : Matrix ι ι K⟦X⟧} (h : DvdM k M) (f : K⟦X⟧) : DvdM k (f • M) :=
  fun i j => by simpa using dvd_mul_of_dvd_right (h i j) f

lemma DvdM.neg {M : Matrix ι ι K⟦X⟧} (h : DvdM k M) : DvdM k (-M) :=
  fun i j => by simpa using h i j

lemma DvdM.add {M N : Matrix ι ι K⟦X⟧} (h : DvdM k M) (h' : DvdM k N) : DvdM k (M + N) :=
  fun i j => by simpa using dvd_add (h i j) (h' i j)

lemma DvdM.mulVec [Fintype ι] {M : Matrix ι ι K⟦X⟧} (h : DvdM k M) (u : ι → K⟦X⟧) : DvdV k (M *ᵥ u) :=
  fun i => Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (h i l) _

lemma DvdV.mulVec [Fintype ι] {u : ι → K⟦X⟧} (h : DvdV k u) (M : Matrix ι ι K⟦X⟧) : DvdV k (M *ᵥ u) :=
  fun _ => Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (h l) _

lemma DvdV.add {u w : ι → K⟦X⟧} (h : DvdV k u) (h' : DvdV k w) : DvdV k (u + w) :=
  fun i => by simpa using dvd_add (h i) (h' i)

lemma DvdV.sub {u w : ι → K⟦X⟧} (h : DvdV k u) (h' : DvdV k w) : DvdV k (u - w) :=
  fun i => by simpa using dvd_sub (h i) (h' i)

lemma DvdV.neg {u : ι → K⟦X⟧} (h : DvdV k u) : DvdV k (-u) :=
  fun i => by simpa using h i

lemma DvdV.smul {u : ι → K⟦X⟧} (h : DvdV k u) (f : K⟦X⟧) : DvdV k (f • u) :=
  fun i => by simpa using dvd_mul_of_dvd_right (h i) f

lemma DvdV.dot [Fintype ι] {u : ι → K⟦X⟧} (h : DvdV k u) (w : ι → K⟦X⟧) : (X : K⟦X⟧) ^ k ∣ w ⬝ᵥ u :=
  Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (h l) _

lemma DvdV.mono {u : ι → K⟦X⟧} {k' : ℕ} (h : DvdV k u) (hk : k' ≤ k) : DvdV k' u :=
  fun i => (pow_dvd_pow _ hk).trans (h i)

lemma DvdV.zero : DvdV k (0 : ι → K⟦X⟧) := fun _ => by simp

end Dvd

section Jacobi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma deriv_prod (s : Finset ι) (f : ι → K⟦X⟧) :
    d⁄dX K (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * d⁄dX K (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne (Ne.symm hne),
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

/-- **Jacobi's formula** in adjugate form: `(det B)' = tr(adj(B) B')`. -/
lemma deriv_det_adj (B : Matrix ι ι K⟦X⟧) :
    d⁄dX K B.det = (B.adjugate * dM B).trace := by
  have h1 : ∀ i, (B.updateCol i (fun k => dM B k i)).det = ∑ k, B.adjugate i k * dM B k i := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ← h1]
  rw [Matrix.det_apply, map_sum]
  simp_rw [Matrix.det_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum, Units.smul_def, Units.smul_def, map_zsmul, deriv_prod]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
  simp only [updateCol_self, mul_comm (dM B (σ x) x)]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hj)]

/-- **Jacobi's formula**: `(det B)' = det B · tr(B⁻¹ B')` for invertible `B`. -/
lemma deriv_det (B : Matrix ι ι K⟦X⟧) (hB : IsUnit B.det) :
    d⁄dX K B.det = B.det * (B⁻¹ * dM B).trace := by
  rw [deriv_det_adj, Matrix.nonsing_inv_apply B hB, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, ← mul_assoc]
  simp

end Jacobi

end AvgRS.Formal
