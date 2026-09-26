module

public import RequestProject.Formal.DetTrunc

@[expose] public section

/-!
# Coherence of the truncations

The `(m+1) × (m+1)` truncations agree with the `m × m` ones (extended by a diagonal corner)
up to entries divisible by `r ^ m`.  Consequently the truncated scalars `P, Q, P₁, Q₁`, the
low entries of `p, q, G` and the determinants `D, D_Z` form `X`-adically Cauchy sequences.
-/

namespace AvgRS.Formal

open PowerSeries Matrix

variable {K : Type*} [Field K]

section Block

variable {m : ℕ}

/-- Extension of a vector by a zero last entry. -/
noncomputable def ext0 (u : Fin m → K⟦X⟧) : Fin (m + 1) → K⟦X⟧ := Fin.snoc u 0

@[simp] lemma ext0_castSucc (u : Fin m → K⟦X⟧) (i : Fin m) : ext0 u i.castSucc = u i :=
  Fin.snoc_castSucc (α := fun _ => K⟦X⟧) _ _ _

@[simp] lemma ext0_last (u : Fin m → K⟦X⟧) : ext0 u (Fin.last m) = 0 :=
  Fin.snoc_last (α := fun _ => K⟦X⟧) _ _

/-- The block-diagonal matrix `diag(M, d)`. -/
noncomputable def blk (M : Matrix (Fin m) (Fin m) K⟦X⟧) (d : K⟦X⟧) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K⟦X⟧ :=
  Matrix.of fun i j => Fin.lastCases (motive := fun _ => K⟦X⟧)
    (Fin.lastCases (motive := fun _ => K⟦X⟧) d (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => K⟦X⟧) 0 (fun j' => M i' j') j) i

variable (M N : Matrix (Fin m) (Fin m) K⟦X⟧) (d e : K⟦X⟧)

@[simp] lemma blk_cc (i j : Fin m) : blk M d i.castSucc j.castSucc = M i j := by simp [blk]
@[simp] lemma blk_cl (i : Fin m) : blk M d i.castSucc (Fin.last m) = 0 := by simp [blk]
@[simp] lemma blk_lc (j : Fin m) : blk M d (Fin.last m) j.castSucc = 0 := by simp [blk]
@[simp] lemma blk_ll : blk M d (Fin.last m) (Fin.last m) = d := by simp [blk]

lemma blk_mul : blk M d * blk N e = blk (M * N) (d * e) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

lemma blk_one : blk (1 : Matrix (Fin m) (Fin m) K⟦X⟧) 1 = 1 := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

lemma blk_mulVec (u : Fin m → K⟦X⟧) : blk M d *ᵥ ext0 u = ext0 (M *ᵥ u) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

lemma ext0_dotProduct (u w : Fin m → K⟦X⟧) : ext0 u ⬝ᵥ ext0 w = u ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_castSucc]

lemma det_blk : (blk M d).det = M.det * d := by
  rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
  simp only [blk_lc, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, blk_ll,
    Fin.succAbove_last, Fin.val_last]
  have : (blk M d).submatrix Fin.castSucc Fin.castSucc = M := Matrix.ext fun i j => by simp
  rw [this, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, mul_comm]

lemma blk_inv (hM : IsUnit M.det) : (blk M 1)⁻¹ = blk M⁻¹ 1 :=
  Matrix.inv_eq_left_inv (by rw [blk_mul, Matrix.nonsing_inv_mul _ hM, one_mul, blk_one])

end Block

section Congr

variable {ι : Type*} [Fintype ι] {k : ℕ}

omit [Fintype ι] in
lemma DvdM.mono {M : Matrix ι ι K⟦X⟧} {k' : ℕ} (h : DvdM k M) (hk : k' ≤ k) : DvdM k' M :=
  fun i j => (pow_dvd_pow _ hk).trans (h i j)

lemma DvdM.sub_mul {A A' B B' : Matrix ι ι K⟦X⟧} (h1 : DvdM k (A - A')) (h2 : DvdM k (B - B')) :
    DvdM k (A * B - A' * B') := by
  have : A * B - A' * B' = (A - A') * B + A' * (B - B') := by
    rw [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [this]; exact (h1.mul_right B).add (h2.mul_left A')

lemma DvdV.sub_mulVec {A A' : Matrix ι ι K⟦X⟧} {u u' : ι → K⟦X⟧} (h1 : DvdM k (A - A'))
    (h2 : DvdV k (u - u')) : DvdV k (A *ᵥ u - A' *ᵥ u') := by
  have : A *ᵥ u - A' *ᵥ u' = (A - A') *ᵥ u + A' *ᵥ (u - u') := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub]; abel
  rw [this]; exact (h1.mulVec u).add (h2.mulVec A')

lemma DvdV.sub_dot {u u' w w' : ι → K⟦X⟧} (h1 : DvdV k (u - u')) (h2 : DvdV k (w - w')) :
    (X : K⟦X⟧) ^ k ∣ u ⬝ᵥ w - u' ⬝ᵥ w' := by
  have : u ⬝ᵥ w - u' ⬝ᵥ w' = w ⬝ᵥ (u - u') + u' ⬝ᵥ (w - w') := by
    rw [dotProduct_sub, dotProduct_sub, dotProduct_comm w u, dotProduct_comm w u']; abel
  rw [this]; exact dvd_add (h1.dot w) (h2.dot u')

variable [DecidableEq ι]

lemma DvdM.sub_inv {A B : Matrix ι ι K⟦X⟧} (hA : IsUnit A.det) (hB : IsUnit B.det)
    (h : DvdM k (A - B)) : DvdM k (A⁻¹ - B⁻¹) := by
  have : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hA, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, Matrix.one_mul]
  rw [this, ← neg_sub]
  exact ((h.neg.mul_left _).mul_right _)

lemma DvdM.sub_det {A B : Matrix ι ι K⟦X⟧} (h : DvdM k (A - B)) :
    (X : K⟦X⟧) ^ k ∣ A.det - B.det := by
  let f := Ideal.Quotient.mk (Ideal.span {(X : K⟦X⟧) ^ k})
  have hAB : f.mapMatrix A = f.mapMatrix B := Matrix.ext fun i j => by
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h i j))
  have : f A.det = f B.det := by rw [RingHom.map_det, RingHom.map_det, hAB]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp this)

end Congr

section Specific

variable {m : ℕ} {z : K}

lemma Hm_succ : DvdM (m + 1) (Hm K (m + 1) - blk (Hm K m) 0) := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [Matrix.sub_apply, blk_cc, blk_cl, blk_lc, blk_ll, sub_zero, Hm, Matrix.of_apply,
      Fin.val_last, Fin.val_castSucc]
  · exact (pow_dvd_pow _ (by omega)).trans (X_pow_dvd_hE m m)
  · exact (pow_dvd_pow _ (by omega)).trans (X_pow_dvd_hE m j)
  · exact (pow_dvd_pow _ (by omega)).trans (X_pow_dvd_hE i m)
  · simp

lemma vm_succ : DvdV m (vm K (m + 1) - ext0 (vm K m)) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [vm, X_pow_dvd_vE]

lemma Am_succ : Am K (m + 1) = blk (Am K m) (m : K⟦X⟧) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Am, Matrix.diagonal_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

lemma Zm_succ : Zm K (m + 1) z = blk (Zm K m z) (if m < 2 then 1 else C z) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Zm, Matrix.diagonal_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

lemma HH_succ : DvdM (m + 1) (Hm K (m + 1) * Hm K (m + 1) - blk (Hm K m * Hm K m) 0) := by
  have := DvdM.sub_mul (Hm_succ (K := K) (m := m)) Hm_succ
  rwa [blk_mul, mul_zero] at this

lemma Bm_succ : DvdM (m + 1) (Bm K (m + 1) z - blk (Bm K m z) 1) := by
  have e : blk (Bm K m z) 1 = 1 + C z • blk (Hm K m * Hm K m) 0 := by
    refine Matrix.ext fun i j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Bm, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  rw [e, Bm, add_sub_add_left_eq_sub, ← smul_sub]
  exact HH_succ.smul _

lemma Gm_succ : DvdM (m + 1) (Gm K (m + 1) z - blk (Gm K m z) 1) := by
  rw [Gm, Gm, ← blk_inv _ isUnit_det_Bm]
  exact DvdM.sub_inv isUnit_det_Bm (by rw [det_blk, mul_one]; exact isUnit_det_Bm) Bm_succ

lemma Hv_succ : DvdV m (Hm K (m + 1) *ᵥ vm K (m + 1) - ext0 (Hm K m *ᵥ vm K m)) := by
  rw [← blk_mulVec _ 0]
  exact DvdV.sub_mulVec (Hm_succ.mono (Nat.le_succ m)) vm_succ

lemma Av_succ : DvdV m (Am K (m + 1) *ᵥ vm K (m + 1) - ext0 (Am K m *ᵥ vm K m)) := by
  rw [← blk_mulVec _ (m : K⟦X⟧), ← Am_succ]
  have : DvdM m (Am K (m + 1) - Am K (m + 1)) := fun i j => by simp
  exact DvdV.sub_mulVec this vm_succ

lemma pm_succ : DvdV m (pm K (m + 1) z - ext0 (pm K m z)) := by
  rw [pm, pm, ← blk_mulVec _ 1]
  exact DvdV.sub_mulVec (Gm_succ.mono (Nat.le_succ m)) vm_succ

lemma qm_succ : DvdV m (qm K (m + 1) z - ext0 (qm K m z)) := by
  rw [qm, qm, ← blk_mulVec _ 1]
  exact DvdV.sub_mulVec (Gm_succ.mono (Nat.le_succ m)) Hv_succ

lemma Pm_succ : (X : K⟦X⟧) ^ m ∣ Pm K (m + 1) z - Pm K m z := by
  have := DvdV.sub_dot (vm_succ (K := K) (m := m)) (pm_succ (m := m) (z := z))
  rwa [ext0_dotProduct] at this

lemma Qm_succ : (X : K⟦X⟧) ^ m ∣ Qm K (m + 1) z - Qm K m z := by
  have := DvdV.sub_dot (vm_succ (K := K) (m := m)) (qm_succ (m := m) (z := z))
  rwa [ext0_dotProduct] at this

lemma P1m_succ : (X : K⟦X⟧) ^ m ∣ P1m K (m + 1) z - P1m K m z := by
  have := DvdV.sub_dot (Av_succ (K := K) (m := m)) (pm_succ (m := m) (z := z))
  rwa [ext0_dotProduct] at this

lemma Q1m_succ : (X : K⟦X⟧) ^ m ∣ Q1m K (m + 1) z - Q1m K m z := by
  have := DvdV.sub_dot (Av_succ (K := K) (m := m)) (qm_succ (m := m) (z := z))
  rwa [ext0_dotProduct] at this

lemma Gm_succ_apply (a b : Fin m) :
    (X : K⟦X⟧) ^ m ∣ Gm K (m + 1) z a.castSucc b.castSucc - Gm K m z a b := by
  have := (Gm_succ (K := K) (m := m) (z := z)).mono (Nat.le_succ m) a.castSucc b.castSucc
  simpa using this

lemma pm_succ_apply (a : Fin m) : (X : K⟦X⟧) ^ m ∣ pm K (m + 1) z a.castSucc - pm K m z a := by
  simpa using pm_succ (K := K) (m := m) (z := z) a.castSucc

lemma qm_succ_apply (a : Fin m) : (X : K⟦X⟧) ^ m ∣ qm K (m + 1) z a.castSucc - qm K m z a := by
  simpa using qm_succ (K := K) (m := m) (z := z) a.castSucc

lemma Dm_succ : (X : K⟦X⟧) ^ m ∣ Dm K (m + 1) z - Dm K m z := by
  have := (Bm_succ (K := K) (m := m) (z := z)).sub_det
  rw [det_blk, mul_one] at this
  exact (pow_dvd_pow _ (Nat.le_succ m)).trans this

lemma DZm_succ : (X : K⟦X⟧) ^ m ∣ DZm K (m + 1) z - DZm K m z := by
  have e : blk (1 + Zm K m z * (Hm K m * Hm K m)) 1
      = 1 + Zm K (m + 1) z * blk (Hm K m * Hm K m) 0 := by
    rw [Zm_succ, blk_mul, mul_zero]
    refine Matrix.ext fun i j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  have h : DvdM (m + 1) ((1 + Zm K (m + 1) z * (Hm K (m + 1) * Hm K (m + 1)))
      - blk (1 + Zm K m z * (Hm K m * Hm K m)) 1) := by
    rw [e, add_sub_add_left_eq_sub, ← Matrix.mul_sub]
    exact HH_succ.mul_left _
  have := h.sub_det
  rw [det_blk, mul_one] at this
  exact (pow_dvd_pow _ (Nat.le_succ m)).trans this

end Specific

end AvgRS.Formal
