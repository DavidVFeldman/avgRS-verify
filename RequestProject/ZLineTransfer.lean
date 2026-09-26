module

public import RequestProject.ZLineRec

@[expose] public section

/-!
# The z-line resolvent: coherence of the truncations and the limit scalars

The `(m+1) × (m+1)` truncations of `C₁ = H Λ H M` agree with the `m × m` ones (extended by a
zero corner) up to entries divisible by `r ^ m`.  Consequently the truncated scalars
`P, P̂, Q, P₁, P̂₁, Q₁, Q̂₁`, the low entries of `p, q, 𝒢` and the determinants
`det(1 + ω C₁)`, `det(1 + Ω C₁)` form `X`-adically Cauchy sequences; their limits are the formal
power series of `zline_closed_system.md`.
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

section Coh

variable {m : ℕ} {w : ℚ} {l μ : ℕ → ℚ}

lemma Dg_succ (l : ℕ → ℚ) : Dg l (m + 1) = blk (Dg l m) (C (l m)) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Dg, Matrix.diagonal_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

lemma DvdM_sub_self {k : ℕ} (M : Matrix (Fin m) (Fin m) ℚ⟦X⟧) : DvdM k (M - M) :=
  fun i j => by simp

lemma Dg_succ' (l : ℕ → ℚ) {k : ℕ} : DvdM k (Dg l (m + 1) - blk (Dg l m) (C (l m))) := by
  rw [← Dg_succ l]; exact DvdM_sub_self _

lemma HD_succ (l : ℕ → ℚ) :
    DvdM (m + 1) (Hm ℚ (m + 1) * Dg l (m + 1) - blk (Hm ℚ m * Dg l m) 0) := by
  have := DvdM.sub_mul (Hm_succ (K := ℚ) (m := m)) (Dg_succ' (m := m) l)
  rwa [blk_mul, zero_mul] at this

lemma Cg_succ : DvdM (m + 1) (Cg l μ (m + 1) - blk (Cg l μ m) 0) := by
  have h1 := DvdM.sub_mul (HD_succ (m := m) l) (Hm_succ (K := ℚ) (m := m))
  rw [blk_mul, zero_mul] at h1
  have h2 := DvdM.sub_mul h1 (Dg_succ' (m := m) μ)
  rwa [blk_mul, zero_mul] at h2

lemma Bg_succ : DvdM (m + 1) (Bg w l μ (m + 1) - blk (Bg w l μ m) 1) := by
  have e : blk (Bg w l μ m) 1 = 1 + C w • blk (Cg l μ m) 0 := by
    refine Matrix.ext fun i j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Bg, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  rw [e, Bg, add_sub_add_left_eq_sub, ← smul_sub]
  exact Cg_succ.smul _

lemma Gg_succ : DvdM (m + 1) (Gg w l μ (m + 1) - blk (Gg w l μ m) 1) := by
  rw [Gg, Gg, ← blk_inv _ isUnit_det_Bg]
  exact DvdM.sub_inv isUnit_det_Bg (by rw [det_blk, mul_one]; exact isUnit_det_Bg) Bg_succ

lemma pg_succ : DvdV m (pg w l μ (m + 1) - ext0 (pg w l μ m)) := by
  rw [pg, pg, ← blk_mulVec _ 1]
  exact DvdV.sub_mulVec (Gg_succ.mono (Nat.le_succ m)) vm_succ

lemma qg_succ : DvdV m (qg w l μ (m + 1) - ext0 (qg w l μ m)) := by
  rw [qg, qg, ← blk_mulVec _ 0]
  exact DvdV.sub_mulVec ((HD_succ l).mono (Nat.le_succ m)) pg_succ

lemma Dv_succ (μ : ℕ → ℚ) :
    DvdV m (Dg μ (m + 1) *ᵥ vm ℚ (m + 1) - ext0 (Dg μ m *ᵥ vm ℚ m)) := by
  rw [← blk_mulVec _ (C (μ m)), ← Dg_succ μ]
  exact DvdV.sub_mulVec (DvdM_sub_self _) vm_succ

lemma DAv_succ (μ : ℕ → ℚ) :
    DvdV m (Dg μ (m + 1) *ᵥ (Am ℚ (m + 1) *ᵥ vm ℚ (m + 1))
      - ext0 (Dg μ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) := by
  rw [← blk_mulVec _ (C (μ m)), ← Dg_succ μ]
  exact DvdV.sub_mulVec (DvdM_sub_self _) Av_succ

lemma Pg_succ : (X : ℚ⟦X⟧) ^ m ∣ Pg w l μ (m + 1) - Pg w l μ m := by
  have := DvdV.sub_dot (Dv_succ (m := m) μ) (pg_succ (m := m) (w := w) (l := l) (μ := μ))
  rwa [ext0_dotProduct] at this

lemma Qg_succ : (X : ℚ⟦X⟧) ^ m ∣ Qg w l μ (m + 1) - Qg w l μ m := by
  have := DvdV.sub_dot (Dv_succ (m := m) μ) (qg_succ (m := m) (w := w) (l := l) (μ := μ))
  rwa [ext0_dotProduct] at this

lemma P1g_succ : (X : ℚ⟦X⟧) ^ m ∣ P1g w l μ (m + 1) - P1g w l μ m := by
  have := DvdV.sub_dot (DAv_succ (m := m) μ) (pg_succ (m := m) (w := w) (l := l) (μ := μ))
  rwa [ext0_dotProduct] at this

lemma Q1g_succ : (X : ℚ⟦X⟧) ^ m ∣ Q1g w l μ (m + 1) - Q1g w l μ m := by
  have := DvdV.sub_dot (DAv_succ (m := m) μ) (qg_succ (m := m) (w := w) (l := l) (μ := μ))
  rwa [ext0_dotProduct] at this

lemma Gg_succ_apply (a b : Fin m) :
    (X : ℚ⟦X⟧) ^ m ∣ Gg w l μ (m + 1) a.castSucc b.castSucc - Gg w l μ m a b := by
  have := (Gg_succ (w := w) (l := l) (μ := μ) (m := m)).mono (Nat.le_succ m) a.castSucc b.castSucc
  simpa using this

lemma pg_succ_apply (a : Fin m) :
    (X : ℚ⟦X⟧) ^ m ∣ pg w l μ (m + 1) a.castSucc - pg w l μ m a := by
  simpa using pg_succ (w := w) (l := l) (μ := μ) (m := m) a.castSucc

lemma qg_succ_apply (a : Fin m) :
    (X : ℚ⟦X⟧) ^ m ∣ qg w l μ (m + 1) a.castSucc - qg w l μ m a := by
  simpa using qg_succ (w := w) (l := l) (μ := μ) (m := m) a.castSucc

lemma detBg_succ : (X : ℚ⟦X⟧) ^ m ∣ (Bg w l μ (m + 1)).det - (Bg w l μ m).det := by
  have := (Bg_succ (w := w) (l := l) (μ := μ) (m := m)).sub_det
  rw [det_blk, mul_one] at this
  exact (pow_dvd_pow _ (Nat.le_succ m)).trans this

lemma detZg_succ : (X : ℚ⟦X⟧) ^ m ∣ (1 + Zm ℚ (m + 1) w * Cg l μ (m + 1)).det
    - (1 + Zm ℚ m w * Cg l μ m).det := by
  have e : blk (1 + Zm ℚ m w * Cg l μ m) 1 = 1 + Zm ℚ (m + 1) w * blk (Cg l μ m) 0 := by
    rw [Zm_succ, blk_mul, mul_zero]
    refine Matrix.ext fun i j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  have h : DvdM (m + 1) ((1 + Zm ℚ (m + 1) w * Cg l μ (m + 1))
      - blk (1 + Zm ℚ m w * Cg l μ m) 1) := by
    rw [e, add_sub_add_left_eq_sub, ← Matrix.mul_sub]
    exact Cg_succ.mul_left _
  have := h.sub_det
  rw [det_blk, mul_one] at this
  exact (pow_dvd_pow _ (Nat.le_succ m)).trans this

end Coh

end AvgRS
