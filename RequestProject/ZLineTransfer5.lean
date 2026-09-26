module

public import RequestProject.ZLineTransfer4

@[expose] public section

/-!
# The z-line resolvent: the limit scalars form a `ZAlgData`
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

variable (t w : ℚ)

theorem zl_hP :
    X * d⁄dX ℚ (zlP t w) = 2 * (zlP1 t w) - 2 * C w * X * (zlP t w) * (zlQ t w) :=
  IsLim.eq_of_dvd (f := fun n => X * d⁄dX ℚ (Pzz t w (n + 2)))
      (g := fun n => 2 * P1zz t w (n + 2) - 2 * C w * X * Pzz t w (n + 2) * Qzz t w (n + 2))
      (by zislim) (by zislim) (fun n => dvd_of_eq' ode_Pzz n)

theorem zl_hPh :
    X * d⁄dX ℚ (zlPh t w) = 2 * (zlPh1 t w) - 2 * C w * X * (zlPh t w) * (zlQ t w) :=
  IsLim.eq_of_dvd (f := fun n => X * d⁄dX ℚ (Phzz t w (n + 2)))
      (g := fun n => 2 * Ph1zz t w (n + 2) - 2 * C w * X * Phzz t w (n + 2) * Qzz t w (n + 2))
      (by zislim) (by zislim) (fun n => dvd_of_eq' ode_Phzz n)

theorem zl_hQ :
    X * d⁄dX ℚ (zlQ t w) = 2 * X * (zlP t w) * (zlPh t w) - (zlQ t w) :=
  IsLim.eq_of_dvd (f := fun n => X * d⁄dX ℚ (Qzz t w (n + 2)))
      (g := fun n => 2 * X * Pzz t w (n + 2) * Phzz t w (n + 2) - Qzz t w (n + 2))
      (by zislim) (by zislim) (fun n => dvd_of_eq' ode_Qzz n)

theorem zl_hQ1 :
    X * d⁄dX ℚ (zlQ1 t w) = 2 * X * (zlPh t w) * (zlP1 t w) - (zlQ1 t w) :=
  IsLim.eq_of_dvd (f := fun n => X * d⁄dX ℚ (Q1zz t w (n + 2)))
      (g := fun n => 2 * X * Phzz t w (n + 2) * P1zz t w (n + 2) - Q1zz t w (n + 2))
      (by zislim) (by zislim) (fun n => dvd_of_eq' ode_Q1zz n)

theorem zl_hQh1 :
    X * d⁄dX ℚ (zlQh1 t w) = 2 * X * (zlP t w) * (zlPh1 t w) - (zlQh1 t w) :=
  IsLim.eq_of_dvd (f := fun n => X * d⁄dX ℚ (Qh1zz t w (n + 2)))
      (g := fun n => 2 * X * Pzz t w (n + 2) * Ph1zz t w (n + 2) - Qh1zz t w (n + 2))
      (by zislim) (by zislim) (fun n => dvd_of_eq' ode_Qh1zz n)

theorem zl_hP1 :
    X * (1 - X ^ 2) * d⁄dX ℚ (zlP1 t w)
      = 2 * (C w * X * (1 - X ^ 2) * ((zlP t w) * (zlQ1 t w) + (zlP1 t w) * (zlQ t w) - C w * X * (zlP t w) * (zlQ t w) ^ 2)
        + C w * X * (1 + X ^ 2) * (zlP t w) * (zlQ t w) - X ^ 2 * C t * (zlP t w) - C w * X ^ 2 * (1 - X ^ 2) * (zlP t w) ^ 2 * (zlPh t w))
        - 2 * C w * X * (1 - X ^ 2) * (zlP t w) * (zlQ1 t w) :=
  IsLim.eq_of_dvd (f := fun n => X * (1 - X ^ 2) * d⁄dX ℚ (P1zz t w (n + 2)))
      (g := fun n => 2 * (C w * X * (1 - X ^ 2) * (Pzz t w (n + 2) * Q1zz t w (n + 2)
          + P1zz t w (n + 2) * Qzz t w (n + 2) - C w * X * Pzz t w (n + 2) * Qzz t w (n + 2) ^ 2)
        + C w * X * (1 + X ^ 2) * Pzz t w (n + 2) * Qzz t w (n + 2) - X ^ 2 * C t * Pzz t w (n + 2)
        - C w * X ^ 2 * (1 - X ^ 2) * Pzz t w (n + 2) ^ 2 * Phzz t w (n + 2))
        - 2 * C w * X * (1 - X ^ 2) * Pzz t w (n + 2) * Q1zz t w (n + 2))
      (by zislim) (by zislim) (fun n => by
        obtain ⟨e, he, h⟩ := zP1_trunc (t := t) (w := w) n
        exact dvd_of_eq_err h he (by omega))

theorem zl_hPh1 :
    X * (1 - X ^ 2) * d⁄dX ℚ (zlPh1 t w)
      = 2 * (4 * X ^ 2 * (zlPh1 t w) + C w * X * (1 - X ^ 2) * ((zlPh t w) * (zlQh1 t w) + (zlPh1 t w) * (zlQ t w) - C w * X * (zlPh t w) * (zlQ t w) ^ 2)
        + C w * X * (1 - 3 * X ^ 2) * (zlPh t w) * (zlQ t w) + (4 - C t) * X ^ 2 * (zlPh t w)
        - C w * X ^ 2 * (1 - X ^ 2) * (zlP t w) * (zlPh t w) ^ 2)
        - 2 * C w * X * (1 - X ^ 2) * (zlPh t w) * (zlQh1 t w) :=
  IsLim.eq_of_dvd (f := fun n => X * (1 - X ^ 2) * d⁄dX ℚ (Ph1zz t w (n + 2)))
      (g := fun n => 2 * (4 * X ^ 2 * Ph1zz t w (n + 2) + C w * X * (1 - X ^ 2)
          * (Phzz t w (n + 2) * Qh1zz t w (n + 2) + Ph1zz t w (n + 2) * Qzz t w (n + 2)
            - C w * X * Phzz t w (n + 2) * Qzz t w (n + 2) ^ 2)
        + C w * X * (1 - 3 * X ^ 2) * Phzz t w (n + 2) * Qzz t w (n + 2)
        + (4 - C t) * X ^ 2 * Phzz t w (n + 2)
        - C w * X ^ 2 * (1 - X ^ 2) * Pzz t w (n + 2) * Phzz t w (n + 2) ^ 2)
        - 2 * C w * X * (1 - X ^ 2) * Phzz t w (n + 2) * Qh1zz t w (n + 2))
      (by zislim) (by zislim) (fun n => by
        obtain ⟨e, he, h⟩ := zPh1_trunc (t := t) (w := w) n
        exact dvd_of_eq_err h he (by omega))

theorem zl_hp0 :
    d⁄dX ℚ (zlp0 t w) = -(2 * C w * (zlP t w) * (zlq0 t w)) :=
  IsLim.eq_of_dvd (f := fun n => d⁄dX ℚ (pzz t w (n + 2) 0))
      (g := fun n => -(2 * C w * Pzz t w (n + 2) * qzz t w (n + 2) 0))
      (by zislim) (by zislim) (fun n => dvd_of_eq' (zp0_ode_trunc n) n)

theorem zl_hq0 :
    X * d⁄dX ℚ (zlq0 t w) = 2 * X * (zlPh t w) * (zlp0 t w) - (zlq0 t w) :=
  IsLim.eq_of_dvd (f := fun n => X * d⁄dX ℚ (qzz t w (n + 2) 0))
      (g := fun n => 2 * X * Phzz t w (n + 2) * pzz t w (n + 2) 0 - qzz t w (n + 2) 0)
      (by zislim) (by zislim) (fun n => dvd_of_eq' (zq0_ode_trunc n) n)

theorem zl_hp1 :
    X * d⁄dX ℚ (zlp1 t w) = (zlp1 t w) - 2 * C w * X * (zlP t w) * (zlq1 t w) :=
  IsLim.eq_of_dvd (f := fun n => X * d⁄dX ℚ (pzz t w (n + 2) 1))
      (g := fun n => pzz t w (n + 2) 1 - 2 * C w * X * Pzz t w (n + 2) * qzz t w (n + 2) 1)
      (by zislim) (by zislim) (fun n => dvd_of_eq' (zp1_ode_trunc n) n)

theorem zl_hG00 :
    d⁄dX ℚ (zlG00 t w) = -(2 * C w * (1 - C t) * (zlp0 t w) * (zlq0 t w)) := by
    have h := IsLim.eq_of_dvd (f := fun n => d⁄dX ℚ (Gzz t w (n + 2) 0 0))
      (g := fun n => -(C w * (pzz t w (n + 2) 0 * (C (muW t 0) * qzz t w (n + 2) 0)
        + qzz t w (n + 2) 0 * (C (muW t 0) * pzz t w (n + 2) 0))))
      (L := d⁄dX ℚ (zlG00 t w))
      (M := -(C w * (zlp0 t w * (C (muW t 0) * zlq0 t w) + zlq0 t w * (C (muW t 0) * zlp0 t w))))
      (by zislim) (by zislim) (fun n => dvd_of_eq' (zG_ode_trunc n 0 0) n)
    rw [h, muW_zero', map_sub, map_one]; ring

theorem zl_hG01 :
    d⁄dX ℚ (zlG01 t w) = C w * C t * (1 - C t) * ((zlp0 t w) * (zlq1 t w) + (zlq0 t w) * (zlp1 t w)) := by
    have h := IsLim.eq_of_dvd (f := fun n => d⁄dX ℚ (Gzz t w (n + 2) 0 1))
      (g := fun n => -(C w * (pzz t w (n + 2) 0 * (C (muW t 1) * qzz t w (n + 2) 1)
        + qzz t w (n + 2) 0 * (C (muW t 1) * pzz t w (n + 2) 1))))
      (L := d⁄dX ℚ (zlG01 t w))
      (M := -(C w * (zlp0 t w * (C (muW t 1) * zlq1 t w) + zlq0 t w * (C (muW t 1) * zlp1 t w))))
      (by zislim) (by zislim)
      (fun n => dvd_of_eq' (by beta_reduce; rw [zG_ode_trunc]; simp only [fin_one_val2]) n)
    rw [h, muW_one', map_neg, map_mul, map_sub, map_one]; ring

theorem zl_hG10 :
    d⁄dX ℚ (zlG10 t w) = -(C w * (1 - C t) * ((zlp1 t w) * (zlq0 t w) + (zlq1 t w) * (zlp0 t w))) := by
    have h := IsLim.eq_of_dvd (f := fun n => d⁄dX ℚ (Gzz t w (n + 2) 1 0))
      (g := fun n => -(C w * (pzz t w (n + 2) 1 * (C (muW t 0) * qzz t w (n + 2) 0)
        + qzz t w (n + 2) 1 * (C (muW t 0) * pzz t w (n + 2) 0))))
      (L := d⁄dX ℚ (zlG10 t w))
      (M := -(C w * (zlp1 t w * (C (muW t 0) * zlq0 t w) + zlq1 t w * (C (muW t 0) * zlp0 t w))))
      (by zislim) (by zislim)
      (fun n => dvd_of_eq' (by beta_reduce; rw [zG_ode_trunc]; simp only [Fin.val_zero]) n)
    rw [h, muW_zero', map_sub, map_one]; ring

theorem zl_hG11 :
    d⁄dX ℚ (zlG11 t w) = 2 * C w * C t * (1 - C t) * (zlp1 t w) * (zlq1 t w) := by
    have h := IsLim.eq_of_dvd (f := fun n => d⁄dX ℚ (Gzz t w (n + 2) 1 1))
      (g := fun n => -(C w * (pzz t w (n + 2) 1 * (C (muW t 1) * qzz t w (n + 2) 1)
        + qzz t w (n + 2) 1 * (C (muW t 1) * pzz t w (n + 2) 1))))
      (L := d⁄dX ℚ (zlG11 t w))
      (M := -(C w * (zlp1 t w * (C (muW t 1) * zlq1 t w) + zlq1 t w * (C (muW t 1) * zlp1 t w))))
      (by zislim) (by zislim)
      (fun n => dvd_of_eq' (by beta_reduce; rw [zG_ode_trunc]; simp only [fin_one_val2]) n)
    rw [h, muW_one', map_neg, map_mul, map_sub, map_one]; ring

theorem zl_hD :
    d⁄dX ℚ (zlD t w) = 2 * C w * (zlQ t w) * (zlD t w) :=
  IsLim.eq_of_dvd (f := fun n => d⁄dX ℚ (Bg w (lamW t) (muW t) (n + 2)).det)
      (g := fun n => 2 * C w * Qzz t w (n + 2) * (Bg w (lamW t) (muW t) (n + 2)).det)
      (by zislim) (by zislim) (fun n => dvd_of_eq' deriv_detBg n)

theorem zl_hDZ :
    C w ^ 2 * (zlDZ t w)
      = (zlD t w) * ((1 - (1 - C w) * (zlG00 t w)) * (1 - (1 - C w) * (zlG11 t w)) - (1 - C w) ^ 2 * (zlG01 t w) * (zlG10 t w)) :=
  IsLim.eq_of_dvd
      (f := fun n => C w ^ 2 * (1 + Zm ℚ (n + 2) w * Cg (lamW t) (muW t) (n + 2)).det)
      (g := fun n => (Bg w (lamW t) (muW t) (n + 2)).det * ((1 - (1 - C w) * Gzz t w (n + 2) 0 0)
        * (1 - (1 - C w) * Gzz t w (n + 2) 1 1)
        - (1 - C w) ^ 2 * Gzz t w (n + 2) 0 1 * Gzz t w (n + 2) 1 0))
      (by zislim) (by zislim) (fun n => by
        have e : C w ^ 2 * (1 + Zm ℚ (n + 2) w * Cg (lamW t) (muW t) (n + 2)).det
            = (Bg w (lamW t) (muW t) (n + 2)).det * ((1 - (1 - C w) * Gzz t w (n + 2) 0 0)
              * (1 - (1 - C w) * Gzz t w (n + 2) 1 1)
              - (1 - C w) ^ 2 * (Gzz t w (n + 2) 0 1 * Gzz t w (n + 2) 1 0)) := detZg_eq n
        exact dvd_of_eq' (by linear_combination e) n)

theorem zl_hR2 :
    (zlQ1 t w) + (zlQh1 t w) + (zlQ t w) = X * (zlP t w) * (zlPh t w) + C w * X * (zlQ t w) ^ 2 :=
  IsLim.eq_of_dvd (f := fun n => Q1zz t w (n + 2) + Qh1zz t w (n + 2) + Qzz t w (n + 2))
      (g := fun n => X * Pzz t w (n + 2) * Phzz t w (n + 2) + C w * X * Qzz t w (n + 2) ^ 2)
      (by zislim) (by zislim) (fun n => dvd_of_eq' first_integral_R2 n)

theorem zl_hL0 (hw : w ≠ 0) :
    ((1 - X ^ 2) * ((zlP1 t w) - C w * X * (zlP t w) * (zlQ t w)) + X ^ 2 * (zlP t w)) * (zlq0 t w)
      = (X * (1 - X ^ 2) * (zlP t w) * (zlPh t w) - (zlQ t w)) * (zlp0 t w) := by
    have h := IsLim.eq_of_dvd (f := fun _ => 0)
      (g := fun n => C w * X * ((X * (1 - X ^ 2) * Pzz t w (n + 2) * Phzz t w (n + 2)
          - Qzz t w (n + 2)) * pzz t w (n + 2) 0
        - ((1 - X ^ 2) * (P1zz t w (n + 2) - C w * X * Pzz t w (n + 2) * Qzz t w (n + 2))
          + X ^ 2 * Pzz t w (n + 2)) * qzz t w (n + 2) 0))
      (M := C w * X * ((X * (1 - X ^ 2) * zlP t w * zlPh t w - zlQ t w) * zlp0 t w
        - ((1 - X ^ 2) * (zlP1 t w - C w * X * zlP t w * zlQ t w) + X ^ 2 * zlP t w) * zlq0 t w))
      (IsLim.const 0) (by zislim) (fun n => by
        obtain ⟨e, he, h⟩ := zRX0_trunc (t := t) (w := w) n
        exact dvd_of_eq_err h he (by omega))
    have hwX : (C w * X : ℚ⟦X⟧) ≠ 0 := mul_ne_zero (zps_C_ne_zero hw) X_ne_zero
    have := (mul_eq_zero.mp h.symm).resolve_left hwX
    linear_combination -this

theorem zl_hF1 :
    C t * (zlp1 t w) + C w * ((1 - X ^ 2) * ((zlP1 t w) - C w * X * (zlP t w) * (zlQ t w)) + (zlP t w)) * (zlq0 t w)
      + (C w * X ^ 2 * (zlQ t w) - X * C t - C w * X * (1 - X ^ 2) * (zlP t w) * (zlPh t w)) * (zlp0 t w) = 0 :=
  IsLim.eq_of_dvd
      (f := fun n => C t * pzz t w (n + 2) 1 + C w * ((1 - X ^ 2) * (P1zz t w (n + 2)
          - C w * X * Pzz t w (n + 2) * Qzz t w (n + 2)) + Pzz t w (n + 2)) * qzz t w (n + 2) 0
        + (C w * X ^ 2 * Qzz t w (n + 2) - X * C t
          - C w * X * (1 - X ^ 2) * Pzz t w (n + 2) * Phzz t w (n + 2)) * pzz t w (n + 2) 0)
      (g := fun _ => 0)
      (by zislim) (IsLim.const 0) (fun n => by
        obtain ⟨e, he, h⟩ := zRZ0_trunc (t := t) (w := w) n
        exact dvd_of_eq_err (e := -e) (by linear_combination -h) (dvd_neg.mpr he) (by omega))

theorem zl_hF2 :
    X * (zlp0 t w) = (zlp1 t w) * (1 + C w * X * (X * (1 - X ^ 2) * (zlP t w) * (zlPh t w) - (zlQ t w)))
      - C w * X * ((zlP t w) + (1 - X ^ 2) * ((zlP1 t w) - C w * X * (zlP t w) * (zlQ t w))) * (zlq1 t w) :=
  IsLim.eq_of_dvd (f := fun n => X * pzz t w (n + 2) 0)
      (g := fun n => pzz t w (n + 2) 1 * (1 + C w * X * (X * (1 - X ^ 2) * Pzz t w (n + 2)
          * Phzz t w (n + 2) - Qzz t w (n + 2)))
        - C w * X * (Pzz t w (n + 2) + (1 - X ^ 2) * (P1zz t w (n + 2)
          - C w * X * Pzz t w (n + 2) * Qzz t w (n + 2))) * qzz t w (n + 2) 1)
      (by zislim) (by zislim) (fun n => by
        obtain ⟨e, he, h⟩ := zRX1_trunc (t := t) (w := w) n
        exact dvd_of_eq_err h he (by omega))

theorem zl_hcP :
    constantCoeff (zlP t w) = 1 - t := by
    have h := (isLim_zlP t w).dvd_sub_of (k := 1) (a := C (1 - t)) fun n => by
      have := Pg_sub_dvd (w := w) (l := lamW t) (μ := muW t) (n + 1)
      rw [muW_zero'] at this
      rw [pow_one]; exact this
    rw [pow_one, X_dvd_iff, map_sub, constantCoeff_C, sub_eq_zero] at h
    exact h

theorem zl_hcPh :
    constantCoeff (zlPh t w) = 1 := by
    have h := (isLim_zlPh t w).dvd_sub_of (k := 1) (a := C 1) fun n => by
      have := Pg_sub_dvd (w := w) (l := muW t) (μ := lamW t) (n + 1)
      rw [lamW_zero'] at this
      rw [pow_one]; exact this
    rw [pow_one, X_dvd_iff, map_sub, constantCoeff_C, sub_eq_zero] at h
    exact h

theorem zl_hP1X :
    X ∣ (zlP1 t w) := by
    have h := (isLim_zlP1 t w).dvd_sub_of (k := 1) (a := 0) fun n => by
      rw [pow_one, sub_zero]; exact P1g_dvd
    simpa using h

theorem zl_hPh1X :
    X ∣ (zlPh1 t w) := by
    have h := (isLim_zlPh1 t w).dvd_sub_of (k := 1) (a := 0) fun n => by
      rw [pow_one, sub_zero]; exact P1g_dvd
    simpa using h

theorem zl_hcp0 :
    constantCoeff (zlp0 t w) = 1 := by
    have h := (isLim_zlp0 t w).dvd_sub_of (k := 1) (a := 1) fun n => by
      have := pg_sub_e0 (w := w) (l := lamW t) (μ := muW t) (n + 1) 0
      simpa [e0] using this
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at h
    exact h

theorem zl_hcG00 :
    constantCoeff (zlG00 t w) = 1 := by
    have h := (isLim_zlG00 t w).dvd_sub_of (k := 1) (a := 1) fun n => by
      have := one_sub_Gg_dvd (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 0 0
      rw [← dvd_neg]; simpa using this
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at h
    exact h

theorem zl_hcG11 :
    constantCoeff (zlG11 t w) = 1 := by
    have h := (isLim_zlG11 t w).dvd_sub_of (k := 1) (a := 1) fun n => by
      have := one_sub_Gg_dvd (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 1 1
      rw [← dvd_neg]; simpa using this
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at h
    exact h

theorem zl_hcG01 :
    constantCoeff (zlG01 t w) = 0 := by
    have h := (isLim_zlG01 t w).dvd_sub_of (k := 1) (a := 0) fun n => by
      have := one_sub_Gg_dvd (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 0 1
      rw [← dvd_neg]; simpa [Matrix.one_apply] using this
    rw [pow_one, sub_zero, X_dvd_iff] at h
    exact h

theorem zl_hcG10 :
    constantCoeff (zlG10 t w) = 0 := by
    have h := (isLim_zlG10 t w).dvd_sub_of (k := 1) (a := 0) fun n => by
      have := one_sub_Gg_dvd (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 1 0
      rw [← dvd_neg]; simpa [Matrix.one_apply] using this
    rw [pow_one, sub_zero, X_dvd_iff] at h
    exact h

theorem zl_hcD :
    constantCoeff (zlD t w) = 1 := by
    have h := (isLim_zlD t w).dvd_sub_of (k := 1) (a := 1) fun n => by
      rw [pow_one]; exact detBg_sub_one_dvd
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at h
    exact h

/-- The limit scalars of the two-matrix resolvent on the line `z + z' = −2`. -/
noncomputable def zdata (hw : w ≠ 0) : ZAlgData t w :=
  ⟨(zlP t w), (zlPh t w), (zlQ t w), (zlP1 t w), (zlPh1 t w), (zlQ1 t w), (zlQh1 t w), (zlp0 t w), (zlq0 t w), (zlp1 t w), (zlq1 t w), (zlG00 t w), (zlG01 t w), (zlG10 t w), (zlG11 t w), (zlD t w), (zlDZ t w), (zl_hP t w), (zl_hPh t w), (zl_hQ t w), (zl_hQ1 t w), (zl_hQh1 t w), (zl_hP1 t w), (zl_hPh1 t w), (zl_hp0 t w), (zl_hq0 t w), (zl_hp1 t w), (zl_hG00 t w), (zl_hG01 t w), (zl_hG10 t w), (zl_hG11 t w), (zl_hD t w), (zl_hDZ t w), (zl_hR2 t w), (zl_hL0 t w hw), (zl_hF1 t w), (zl_hF2 t w), (zl_hcP t w), (zl_hcPh t w), (zl_hP1X t w), (zl_hPh1X t w), (zl_hcp0 t w), (zl_hcG00 t w), (zl_hcG11 t w), (zl_hcG01 t w), (zl_hcG10 t w), (zl_hcD t w)⟩

end AvgRS
