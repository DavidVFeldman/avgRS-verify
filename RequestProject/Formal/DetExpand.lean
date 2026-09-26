module

public import RequestProject.Formal.Minors
public import RequestProject.Formal.DetTrunc

@[expose] public section

/-!
# Expansion of the truncated determinants over pairs of index sets (proof of Lemma 5.4, `lem:durfeedet`)

By the principal-minor expansion and Cauchy–Binet,
`det(1 + diag(ω) H²) = ∑_k ∑_{f, g} (∏ ω ∘ f) det(H_{f,g})²`, and
`det(H_{f,g}) = r^{∑ f + ∑ g + k} det(F(f_i | g_j))` with `F(a|b) = 1/(a! b! (a+b+1))`.
-/

namespace AvgRS.Formal

open PowerSeries Matrix Finset

variable {K : Type*} [Field K]

/-- `F(a|b) = 1/(a! b! (a+b+1))`, the value of `F` on the hook `(a|b)`. -/
noncomputable def hookF (a b : ℕ) : K := ((a.factorial * b.factorial * (a + b + 1) : ℕ) : K)⁻¹

/-- The matrix `(F(f_i | g_j))_{i,j}`. -/
noncomputable def frobMat {k m : ℕ} (f g : Fin k → Fin m) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => hookF (f i : ℕ) (g j : ℕ)

/-- The weight `∑ f + ∑ g + k` (the size of the partition with Frobenius coordinates `(f|g)`). -/
def frobWt {k m : ℕ} (f g : Fin k → Fin m) : ℕ := ∑ i, (f i : ℕ) + ∑ i, (g i : ℕ) + k

lemma hE_eq_hookF (a b : ℕ) : (hE a b : K⟦X⟧) = C (hookF a b) * X ^ (a + b + 1) := by
  simp [hE, hookF]

lemma det_C_mul_X_pow {k : ℕ} (c : Matrix (Fin k) (Fin k) K) (α β : Fin k → ℕ) :
    (Matrix.of fun i j => C (c i j) * (X : K⟦X⟧) ^ (α i + β j + 1)).det
      = C c.det * X ^ (∑ i, α i + ∑ i, β i + k) := by
  have : (Matrix.of fun i j => C (c i j) * (X : K⟦X⟧) ^ (α i + β j + 1))
      = diagonal (fun i => (X : K⟦X⟧) ^ α i) * (C : K →+* K⟦X⟧).mapMatrix c
        * diagonal (fun j => (X : K⟦X⟧) ^ (β j + 1)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, mul_diagonal, diagonal_mul, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    rw [pow_add, pow_add]; ring
  rw [this, det_mul, det_mul, det_diagonal, det_diagonal, ← RingHom.map_det,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [pow_add, pow_add]; ring

lemma det_Hm_submatrix {k m : ℕ} (f g : Fin k → Fin m) :
    ((Hm K m).submatrix f g).det = C (frobMat f g).det * X ^ frobWt f g := by
  have : (Hm K m).submatrix f g
      = Matrix.of fun i j => C (frobMat f g i j) * (X : K⟦X⟧) ^ ((f i : ℕ) + (g j : ℕ) + 1) := by
    refine Matrix.ext fun i j => ?_
    simp [Hm, frobMat, hE_eq_hookF]
  rw [this, det_C_mul_X_pow]
  rfl

lemma frobMat_transpose {k m : ℕ} (f g : Fin k → Fin m) :
    (frobMat (K := K) g f) = (frobMat f g)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [frobMat, Matrix.of_apply, Matrix.transpose_apply, hookF]
  congr 3 <;> ring

lemma frobWt_comm {k m : ℕ} (f g : Fin k → Fin m) : frobWt g f = frobWt f g := by
  simp only [frobWt]; ring

/-- **Expansion of `det(1 + diag(ω) H²)`** over pairs of strictly increasing index maps. -/
theorem det_one_add_diag_HH (m : ℕ) (ω : Fin m → K) :
    (1 + diagonal (fun a => C (ω a)) * (Hm K m * Hm K m)).det
      = ∑ k ∈ Finset.range (m + 1), ∑ f ∈ smono k m, ∑ g ∈ smono k m,
          C ((∏ i, ω (f i)) * (frobMat f g).det ^ 2) * X ^ (2 * frobWt f g) := by
  rw [det_one_add_diagonal_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun f _ => ?_
  have hsub : (Hm K m * Hm K m).submatrix f f = (Hm K m).submatrix f id * (Hm K m).submatrix id f :=
    Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id
  rw [hsub, det_mul_eq_sum_smono, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [submatrix_submatrix, Function.comp_id, Function.id_comp]
  rw [det_Hm_submatrix, det_Hm_submatrix, frobMat_transpose, det_transpose, frobWt_comm,
    ← map_prod, map_mul, map_pow]
  ring

end AvgRS.Formal
