module

public import RequestProject.Formal.Hook
public import RequestProject.Formal.MatDeriv

@[expose] public section

/-!
# Finite truncations of the hook matrix

For each size `m` we consider the `m × m` truncations `H`, `v`, `A`, `X` of the hook matrix,
the vector `v`, the Euler operator and the weighted shift of Section 5, and prove the
identities (H1)–(H5) for them: all hold exactly except (H3) and `Xᵀ v = r v`, which hold up
to boundary terms divisible by `r ^ m`.
-/

namespace AvgRS.Formal

open PowerSeries Matrix

variable (K : Type*) [Field K]

/-- The truncated hook matrix. -/
noncomputable def Hm (m : ℕ) : Matrix (Fin m) (Fin m) K⟦X⟧ := Matrix.of fun a b => hE a b

/-- The truncated vector `v`. -/
noncomputable def vm (m : ℕ) : Fin m → K⟦X⟧ := fun a => vE a

/-- The Euler operator `A = diag(0,1,2,…)`. -/
noncomputable def Am (m : ℕ) : Matrix (Fin m) (Fin m) K⟦X⟧ :=
  Matrix.diagonal fun a => ((a : ℕ) : K⟦X⟧)

/-- The weighted shift `(X f)_a = a f_{a-1}`. -/
noncomputable def Xm (m : ℕ) : Matrix (Fin m) (Fin m) K⟦X⟧ :=
  Matrix.of fun a b => if (a : ℕ) = b + 1 then ((a : ℕ) : K⟦X⟧) else 0

variable {K} {m : ℕ}

section Entries

variable {R : Type*} [CommRing R]

/-- Entries of `X * M` for `M` given by a function on `ℕ × ℕ`. -/
lemma Xm_mul_of (f : ℕ → ℕ → K⟦X⟧) (a b : Fin m) :
    (Xm K m * Matrix.of (fun a b : Fin m => f a b)) a b
      = if (a : ℕ) = 0 then 0 else ((a : ℕ) : K⟦X⟧) * f (a - 1) b := by
  rw [Matrix.mul_apply]
  split_ifs with ha
  · refine Finset.sum_eq_zero fun c _ => ?_
    simp [Xm, ha]
  · rw [Finset.sum_eq_single ⟨(a : ℕ) - 1, by omega⟩]
    · simp only [Xm, Matrix.of_apply]
      rw [if_pos (by omega)]
    · intro c _ hc
      simp only [Xm, Matrix.of_apply]
      rw [if_neg, zero_mul]
      intro h; apply hc; ext; simp; omega
    · simp

lemma of_mul_XmT (f : ℕ → ℕ → K⟦X⟧) (a b : Fin m) :
    (Matrix.of (fun a b : Fin m => f a b) * (Xm K m)ᵀ) a b
      = if (b : ℕ) = 0 then 0 else ((b : ℕ) : K⟦X⟧) * f a (b - 1) := by
  rw [Matrix.mul_apply]
  split_ifs with hb
  · refine Finset.sum_eq_zero fun c _ => ?_
    simp [Xm, hb]
  · rw [Finset.sum_eq_single ⟨(b : ℕ) - 1, by omega⟩]
    · simp only [Xm, Matrix.of_apply, Matrix.transpose_apply]
      rw [if_pos (by omega), mul_comm]
    · intro c _ hc
      simp only [Xm, Matrix.of_apply, Matrix.transpose_apply]
      rw [if_neg, mul_zero]
      intro h; apply hc; ext; simp; omega
    · simp

lemma XmT_mul_of (f : ℕ → ℕ → K⟦X⟧) (a b : Fin m) :
    ((Xm K m)ᵀ * Matrix.of (fun a b : Fin m => f a b)) a b
      = if (a : ℕ) + 1 < m then (((a : ℕ) : K⟦X⟧) + 1) * f (a + 1) b else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with ha
  · rw [Finset.sum_eq_single ⟨(a : ℕ) + 1, ha⟩]
    · simp [Xm]
    · intro c _ hc
      simp only [Xm, Matrix.of_apply, Matrix.transpose_apply]
      rw [if_neg, zero_mul]
      intro h; apply hc; ext; simp; omega
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    simp only [Xm, Matrix.of_apply, Matrix.transpose_apply]
    rw [if_neg, zero_mul]
    omega

lemma of_mul_Xm (f : ℕ → ℕ → K⟦X⟧) (a b : Fin m) :
    (Matrix.of (fun a b : Fin m => f a b) * Xm K m) a b
      = if (b : ℕ) + 1 < m then (((b : ℕ) : K⟦X⟧) + 1) * f a (b + 1) else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hb
  · rw [Finset.sum_eq_single ⟨(b : ℕ) + 1, hb⟩]
    · simp [Xm, mul_comm]
    · intro c _ hc
      simp only [Xm, Matrix.of_apply]
      rw [if_neg, mul_zero]
      intro h; apply hc; ext; simp; omega
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    simp only [Xm, Matrix.of_apply]
    rw [if_neg, mul_zero]
    omega

lemma Xm_mulVec_of (g : ℕ → K⟦X⟧) (a : Fin m) :
    (Xm K m *ᵥ fun a : Fin m => g a) a
      = if (a : ℕ) = 0 then 0 else ((a : ℕ) : K⟦X⟧) * g (a - 1) := by
  have := Xm_mul_of (m := m) (fun a _ => g a) a a
  rw [Matrix.mul_apply] at this
  rw [Matrix.mulVec, dotProduct, ← this]
  rfl

lemma XmT_mulVec_of (g : ℕ → K⟦X⟧) (a : Fin m) :
    ((Xm K m)ᵀ *ᵥ fun a : Fin m => g a) a
      = if (a : ℕ) + 1 < m then (((a : ℕ) : K⟦X⟧) + 1) * g (a + 1) else 0 := by
  have := XmT_mul_of (m := m) (fun a _ => g a) a a
  rw [Matrix.mul_apply] at this
  rw [Matrix.mulVec, dotProduct, ← this]
  rfl

lemma Xm_mulVec_zero (u : Fin (m + 1) → K⟦X⟧) : (Xm K (m + 1) *ᵥ u) 0 = 0 := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp [Xm]

lemma Xm_mulVec_one (u : Fin (m + 2) → K⟦X⟧) : (Xm K (m + 2) *ᵥ u) 1 = u 0 := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single 0]
  · simp [Xm]
  · intro c _ hc
    simp only [Xm, Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro h; apply hc; ext; simp at h ⊢; omega
  · simp

lemma Am_mulVec (u : Fin m → K⟦X⟧) (a : Fin m) : (Am K m *ᵥ u) a = ((a : ℕ) : K⟦X⟧) * u a := by
  simp [Am, Matrix.mulVec_diagonal]

lemma mul_Am_apply (M : Matrix (Fin m) (Fin m) K⟦X⟧) (a b : Fin m) :
    (M * Am K m) a b = M a b * ((b : ℕ) : K⟦X⟧) := by
  simp [Am, Matrix.mul_diagonal]

lemma Am_mul_apply (M : Matrix (Fin m) (Fin m) K⟦X⟧) (a b : Fin m) :
    (Am K m * M) a b = ((a : ℕ) : K⟦X⟧) * M a b := by
  simp [Am, Matrix.diagonal_mul]

end Entries

lemma Hm_transpose : (Hm K m)ᵀ = Hm K m := by
  refine Matrix.ext fun a b => ?_
  simp [Hm, hE_symm]

lemma Am_transpose : (Am K m)ᵀ = Am K m := by
  simp [Am]

lemma X_dvd_Hm (a b : Fin m) : (X : K⟦X⟧) ∣ Hm K m a b :=
  (dvd_pow_self X (Nat.succ_ne_zero _)).trans (X_pow_dvd_hE (K := K) a b)

variable [CharZero K]

/-- (H1): `H' = v ⊗ v`. -/
lemma dM_Hm : dM (Hm K m) = vecMulVec (vm K m) (vm K m) := by
  refine Matrix.ext fun a b => ?_
  simp [Hm, vm, vecMulVec_apply, deriv_hE]

omit [CharZero K] in
/-- (H1): `r v' = A v`. -/
lemma X_smul_dV_vm : (X : K⟦X⟧) • dV (vm K m) = Am K m *ᵥ vm K m := by
  funext a
  simp [Am_mulVec, vm, X_mul_deriv_vE]

/-- (H2): `HA + (A+1)H = r v ⊗ v`. -/
lemma Hm_H2 : Hm K m * Am K m + (Am K m + 1) * Hm K m = (X : K⟦X⟧) • vecMulVec (vm K m) (vm K m) := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.add_apply, mul_Am_apply, Matrix.add_mul, Matrix.add_apply, Am_mul_apply,
    Matrix.one_mul]
  simp only [Hm, vm, Matrix.of_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  linear_combination hE_H2 (K := K) a b

/-- (H4): `XH - HXᵀ = Av ⊗ v - v ⊗ Av`. -/
lemma Hm_H4 : Xm K m * Hm K m - Hm K m * (Xm K m)ᵀ
    = vecMulVec (Am K m *ᵥ vm K m) (vm K m) - vecMulVec (vm K m) (Am K m *ᵥ vm K m) := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.sub_apply, Hm, Xm_mul_of, of_mul_XmT, Matrix.sub_apply, vecMulVec_apply,
    vecMulVec_apply, Am_mulVec, Am_mulVec]
  simp only [vm]
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only
  rcases a with _ | a <;> rcases b with _ | b
  · simp
  · simp only [if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, zero_sub,
      Nat.cast_zero, zero_mul, vE_zero]
    rw [hE_symm, hE_zero_right]; push_cast; ring
  · simp only [if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, sub_zero,
      Nat.cast_zero, zero_mul, mul_zero, vE_zero]
    rw [hE_zero_right]; push_cast; ring
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have := hE_H4 (K := K) a b
    push_cast
    linear_combination this

/-- (H3) up to boundary terms: `XᵀH - HX ≡ 0 (mod r^m)`. -/
lemma Hm_H3 : DvdM m ((Xm K m)ᵀ * Hm K m - Hm K m * Xm K m) := by
  intro a b
  rw [Matrix.sub_apply, Hm, XmT_mul_of, of_mul_Xm]
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only
  have d1 : (X : K⟦X⟧) ^ m ∣ hE (a + 1) b ∨ a + 1 < m := by
    by_cases h : a + 1 < m
    · exact Or.inr h
    · exact Or.inl ((pow_dvd_pow _ (by omega)).trans (X_pow_dvd_hE _ _))
  split_ifs with h1 h2 h2
  · rw [hE_H3, sub_self]; exact dvd_zero _
  · rw [sub_zero]
    exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans (X_pow_dvd_hE _ _)) _
  · rw [zero_sub, dvd_neg]
    exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans (X_pow_dvd_hE _ _)) _
  · simp

/-- (H5) up to boundary terms: `Xᵀ v ≡ r v (mod r^m)`. -/
lemma vm_H5a : DvdV m ((Xm K m)ᵀ *ᵥ vm K m - (X : K⟦X⟧) • vm K m) := by
  intro a
  rw [show vm K m = fun a : Fin m => (vE (a : ℕ) : K⟦X⟧) from rfl, Pi.sub_apply, XmT_mulVec_of]
  obtain ⟨a, ha⟩ := a
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [vE_H5a, sub_self]; exact dvd_zero _
  · rw [zero_sub, dvd_neg]
    have : m = a + 1 := by omega
    subst this
    rw [pow_succ']
    exact mul_dvd_mul_left _ (X_pow_dvd_vE a)

/-- (H5): `A² v = r X v`. -/
lemma vm_H5b : Am K m *ᵥ (Am K m *ᵥ vm K m) = (X : K⟦X⟧) • (Xm K m *ᵥ vm K m) := by
  funext a
  rw [show vm K m = fun a : Fin m => (vE (a : ℕ) : K⟦X⟧) from rfl, Am_mulVec, Am_mulVec,
    Pi.smul_apply, Xm_mulVec_of, smul_eq_mul]
  obtain ⟨a, ha⟩ := a
  simp only
  rcases a with _ | a
  · simp
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    push_cast
    rw [← mul_assoc, ← pow_two, vE_H5b]

end AvgRS.Formal
