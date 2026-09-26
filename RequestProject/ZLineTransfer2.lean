module

public import RequestProject.ZLineTransfer

@[expose] public section

/-!
# The z-line resolvent: the truncated identities needed for the closed system

For the `m × m` truncations: the differential equation for `P₁` (paired with the recurrence
(P2q)), the differential equations of the low entries of `p, q, 𝒢`, Jacobi's formula for
`det(1 + ω C₁)`, the rank-two formula for `det(1 + Ω C₁)`, the index-0 and index-1 components of
the recurrences (RXp), (RZp), and the constant terms.
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

section General

variable {m : ℕ} {w : ℚ} {l μ : ℕ → ℚ}

/-- `r P₁' = 2 P₂ − 2 ω r P Q₁`, `P₂ = ⟨diag(μ) A² v, p⟩`. -/
lemma ode_P1g : X * d⁄dX ℚ (P1g w l μ m)
    = 2 * ((Dg μ m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pg w l μ m)
      - 2 * C w * X * Pg w l μ m * Q1g w l μ m := by
  rw [P1g, X_mul_deriv_dot, X_smul_dV_Dg_Am_vm, ode_pg, dotProduct_sub, dotProduct_smul,
    dot_A_symm (u := Dg μ m *ᵥ (Am ℚ m *ᵥ vm ℚ m)), ← Dg_Am_mulVec, ← Q1g, smul_eq_mul]
  ring

/-- Jacobi's formula: `(det B)' = 2 ω Q det B`. -/
lemma deriv_detBg : d⁄dX ℚ (Bg w l μ m).det = 2 * C w * Qg w l μ m * (Bg w l μ m).det := by
  rw [deriv_det _ isUnit_det_Bg, ← Gg]
  have hB : dM (Bg w l μ m) = C w • (vecMulVec (vm ℚ m) (Dg μ m *ᵥ cg l m)
      + vecMulVec (cg l m) (Dg μ m *ᵥ vm ℚ m)) := by
    rw [Bg, dM_add, dM_one, zero_add, dM_C_smul, dM_Cg]
  rw [hB, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
    Gg_mulVec_vm, Gg_mulVec_cg, smul_eq_mul]
  have h1 : (Dg μ m *ᵥ cg l m) ⬝ᵥ pg w l μ m = Qg w l μ m := by
    rw [← dot_Dp_cg, dotProduct_comm, dot_Dg_symm]
  have h2 : (Dg μ m *ᵥ vm ℚ m) ⬝ᵥ qg w l μ m = Qg w l μ m := rfl
  rw [dotProduct_comm (pg w l μ m), dotProduct_comm (qg w l μ m), h1, h2]
  ring

lemma c_CG : C w • (Cg l μ m * Gg w l μ m) = 1 - Gg w l μ m := by
  have h := Bg_mul_Gg (w := w) (l := l) (μ := μ) (m := m)
  rw [Bg, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
  rw [← h]; abel

/-- The rank-two perturbation formula for `det(1 + Ω C)`, `Ω = diag(1, 1, ω, ω, …)`. -/
lemma detZg_eq (n : ℕ) :
    (C w : ℚ⟦X⟧) ^ 2 * (1 + Zm ℚ (n + 2) w * Cg l μ (n + 2)).det = (Bg w l μ (n + 2)).det *
      ((1 - (1 - C w) * Gg w l μ (n + 2) 0 0) * (1 - (1 - C w) * Gg w l μ (n + 2) 1 1)
        - (1 - C w) ^ 2 * (Gg w l μ (n + 2) 0 1 * Gg w l μ (n + 2) 1 0)) := by
  let ι : Fin 2 → Fin (n + 2) := fun j => ⟨j, by omega⟩
  let U : Matrix (Fin (n + 2)) (Fin 2) ℚ⟦X⟧ :=
    Matrix.of fun a j => if (a : ℕ) = (j : ℕ) then 1 - (C w : ℚ⟦X⟧) else 0
  let V : Matrix (Fin 2) (Fin (n + 2)) ℚ⟦X⟧ := Matrix.of fun j b => Cg l μ (n + 2) (ι j) b
  have hZ : 1 + Zm ℚ (n + 2) w * Cg l μ (n + 2) = Bg w l μ (n + 2) + U * V := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.add_apply, Zm, Matrix.diagonal_mul, Bg, Matrix.add_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply (M := U), Fin.sum_univ_two]
    simp only [U, V, Matrix.of_apply]
    obtain ⟨a, ha⟩ := a
    rcases a with _ | _ | a
    · simp [ι]; ring
    · simp [ι]; ring
    · simp [ι]
  have hUV : ∀ i j, (V * Gg w l μ (n + 2) * U) i j
      = (1 - (C w : ℚ⟦X⟧)) * (Cg l μ (n + 2) * Gg w l μ (n + 2)) (ι i) (ι j) := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (ι j)]
    · simp only [U, Matrix.of_apply, ι, V]
      rw [mul_comm]
      congr 1
    · intro b _ hb
      simp only [U, Matrix.of_apply]
      rw [if_neg, mul_zero]
      intro h; apply hb; ext; simp [ι, h]
    · simp
  have hc : ∀ x y, (C w : ℚ⟦X⟧) * (Cg l μ (n + 2) * Gg w l μ (n + 2)) x y
      = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ⟦X⟧) x y - Gg w l μ (n + 2) x y := by
    intro x y
    have := congrFun (congrFun (c_CG (w := w) (l := l) (μ := μ) (m := n + 2)) x) y
    simpa using this
  have hdet : (C w : ℚ⟦X⟧) ^ 2 * (1 + V * Gg w l μ (n + 2) * U).det
      = (1 - (1 - (C w : ℚ⟦X⟧)) * Gg w l μ (n + 2) 0 0)
          * (1 - (1 - (C w : ℚ⟦X⟧)) * Gg w l μ (n + 2) 1 1)
        - (1 - (C w : ℚ⟦X⟧)) ^ 2 * (Gg w l μ (n + 2) 0 1 * Gg w l μ (n + 2) 1 0) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, hUV, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide :
      (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    have h00 := hc 0 0
    have h11 := hc 1 1
    have h01 := hc 0 1
    have h10 := hc 1 0
    have e0 : ι 0 = 0 := rfl
    have e1 : ι 1 = 1 := by ext; simp [ι]
    rw [e0, e1]
    rw [Matrix.one_apply_eq] at h00 h11
    rw [Matrix.one_apply_ne (by simp)] at h01 h10
    linear_combination (1 - C w) * (C w + (1 - C w) * C w *
        (Cg l μ (n + 2) * Gg w l μ (n + 2)) 1 1) * h00
      + (1 - C w) * (C w + (1 - C w) * (1 - Gg w l μ (n + 2) 0 0)) * h11
      - (1 - C w) ^ 2 * C w * (Cg l μ (n + 2) * Gg w l μ (n + 2)) 1 0 * h01
      + (1 - C w) ^ 2 * Gg w l μ (n + 2) 0 1 * h10
  rw [hZ, Matrix.det_add_mul U V isUnit_det_Bg, ← Gg, ← hdet]
  ring

/-! ### Constant terms -/

lemma one_sub_Gg_dvd : DvdM 1 (1 - Gg w l μ m) := by
  have e : 1 - Gg w l μ m = Gg w l μ m * (C w • Cg l μ m) := by
    have h := Gg_mul_Bg (w := w) (l := l) (μ := μ) (m := m)
    rw [Bg, Matrix.mul_add, Matrix.mul_one] at h
    rw [← h]; abel
  rw [e]
  have hC : DvdM 1 (Cg l μ m) := by
    have := ((Hm_dvd (K := ℚ) (m := m)).mul_right (Dg l m * Hm ℚ m * Dg μ m))
    simpa [Cg, Matrix.mul_assoc] using this
  exact (hC.smul _).mul_left _

lemma pg_sub_e0 (n : ℕ) : DvdV 1 (pg w l μ (n + 1) - e0 n) := by
  have e : pg w l μ (n + 1) - e0 n = Gg w l μ (n + 1) *ᵥ (vm ℚ (n + 1) - e0 n)
      - (1 - Gg w l μ (n + 1)) *ᵥ e0 n := by
    rw [pg, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [e]
  exact ((vm_sub_e0 n).mulVec _).sub (one_sub_Gg_dvd.mulVec _)

lemma Dv_sub_e0 (n : ℕ) : DvdV 1 (Dg μ (n + 1) *ᵥ vm ℚ (n + 1) - C (μ 0) • e0 n) := by
  have e : C (μ 0) • e0 n = Dg μ (n + 1) *ᵥ (e0 n : Fin (n + 1) → ℚ⟦X⟧) := by
    ext a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp [e0, Dg, Matrix.mulVec_diagonal]
  rw [e, ← Matrix.mulVec_sub]
  exact (vm_sub_e0 n).mulVec _

lemma e0_dot_e0 (n : ℕ) : (e0 n : Fin (n + 1) → ℚ⟦X⟧) ⬝ᵥ e0 n = 1 := by
  simp [e0]

lemma Pg_sub_dvd (n : ℕ) : (X : ℚ⟦X⟧) ∣ Pg w l μ (n + 1) - C (μ 0) := by
  have := DvdV.sub_dot (Dv_sub_e0 (μ := μ) n) (pg_sub_e0 (w := w) (l := l) (μ := μ) n)
  rw [smul_dotProduct, e0_dot_e0, smul_eq_mul, mul_one, pow_one] at this
  exact this

lemma P1g_dvd : (X : ℚ⟦X⟧) ∣ P1g w l μ m := by
  have := ((Av_dvd (K := ℚ) (m := m)).mulVec (Dg μ m)).dot (pg w l μ m)
  rw [pow_one, dotProduct_comm] at this
  exact this

lemma detBg_sub_one_dvd : (X : ℚ⟦X⟧) ∣ (Bg w l μ m).det - 1 := by
  have h : DvdM 1 (Bg w l μ m - 1) := by
    have hC : DvdM 1 (Cg l μ m) := by
      have := ((Hm_dvd (K := ℚ) (m := m)).mul_right (Dg l m * Hm ℚ m * Dg μ m))
      simpa [Cg, Matrix.mul_assoc] using this
    rw [Bg, add_sub_cancel_left]; exact hC.smul _
  have := h.sub_det
  rwa [Matrix.det_one, pow_one] at this

end General

end AvgRS
