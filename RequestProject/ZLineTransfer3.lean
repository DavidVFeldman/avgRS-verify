module

public import RequestProject.ZLineTransfer2

@[expose] public section

/-!
# The z-line resolvent: components of the recurrences and of the differential equations

The index-0 and index-1 components of (RXp), (RZp), the differential equations for the low
entries of `p, q, 𝒢`, and the equations for `P₁, P̂₁` closed by (P2q), (P̂2q), all for the
`(n+2) × (n+2)` truncations (exactly, or up to an error divisible by `X ^ (n+2)`).
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

section Components

variable {t w : ℚ} (n : ℕ)

local notation "PP" => Pzz t w (n + 2)
local notation "QQ" => Qzz t w (n + 2)
local notation "PPh" => Phzz t w (n + 2)
local notation "PP1" => P1zz t w (n + 2)
local notation "PPh1" => Ph1zz t w (n + 2)
local notation "QQ1" => Q1zz t w (n + 2)
local notation "QQh1" => Qh1zz t w (n + 2)
local notation "pp" => pzz t w (n + 2)
local notation "qq" => qzz t w (n + 2)
local notation "GG" => Gzz t w (n + 2)
local notation "ww" => (C w : ℚ⟦X⟧)
local notation "tt" => (C t : ℚ⟦X⟧)

lemma fin_one_val2 : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp

lemma zRX0_trunc : ∃ e : ℚ⟦X⟧, (X : ℚ⟦X⟧) ^ (n + 2) ∣ e ∧
    0 = ww * X * ((X * (1 - X ^ 2) * PP * PPh - QQ) * pp 0
      - ((1 - X ^ 2) * (PP1 - ww * X * PP * QQ) + X ^ 2 * PP) * qq 0) + e := by
  obtain ⟨err, herr, h⟩ := RXp_trunc (t := t) (w := w) (m := n + 2)
  refine ⟨err 0, herr 0, ?_⟩
  have := congrFun h 0
  simp only [Xm_mulVec_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Am_mulVec, Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero, sigzz] at this
  linear_combination this

lemma zRX1_trunc : ∃ e : ℚ⟦X⟧, (X : ℚ⟦X⟧) ^ (n + 2) ∣ e ∧
    X * pp 0 = pp 1 * (1 + ww * X * (X * (1 - X ^ 2) * PP * PPh - QQ))
      - ww * X * (PP + (1 - X ^ 2) * (PP1 - ww * X * PP * QQ)) * qq 1 + e := by
  obtain ⟨err, herr, h⟩ := RXp_trunc (t := t) (w := w) (m := n + 2)
  refine ⟨err 1, herr 1, ?_⟩
  have := congrFun h 1
  simp only [Xm_mulVec_one, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Am_mulVec, fin_one_val2, Nat.cast_one, one_mul, sigzz] at this
  linear_combination this

lemma zRZ0_trunc : ∃ e : ℚ⟦X⟧, (X : ℚ⟦X⟧) ^ (n + 2) ∣ e ∧
    0 = tt * pp 1 + ww * ((1 - X ^ 2) * (PP1 - ww * X * PP * QQ) + PP) * qq 0
      + (ww * X ^ 2 * QQ - X * tt - ww * X * (1 - X ^ 2) * PP * PPh) * pp 0 + e := by
  obtain ⟨err, herr, h⟩ := RZp_trunc (t := t) (w := w) (m := n + 2)
  refine ⟨err 0, herr 0, ?_⟩
  have := congrFun h 0
  have hX : ((Xm ℚ (n + 2))ᵀ *ᵥ pp) 0 = pp 1 := by
    have := XmT_mulVec_of (K := ℚ) (m := n + 2) (fun a => if h : a < n + 2 then pp ⟨a, h⟩ else 0) 0
    simp only [Fin.val_zero, zero_add, Nat.cast_zero] at this
    rw [if_pos (by omega)] at this
    convert this using 2
    · ext a; simp [a.isLt]
    · simp
  simp only [Dmz, Matrix.mulVec_diagonal, hX, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Am_mulVec, Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero, sigzz] at this
  simp only [Nat.cast_zero, add_zero, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_sub, map_neg] at this
  linear_combination this

lemma zp0_ode_trunc : d⁄dX ℚ (pp 0) = -(2 * ww * PP * qq 0) := by
  have := congrFun (ode_pzz (t := t) (w := w) (m := n + 2)) 0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Am_mulVec, Fin.val_zero, Nat.cast_zero,
    zero_mul, dV] at this
  exact mul_left_cancel₀ X_ne_zero (by linear_combination this)

lemma zq0_ode_trunc : X * d⁄dX ℚ (qq 0) = 2 * X * PPh * pp 0 - qq 0 := by
  have := congrFun (ode_qzz (t := t) (w := w) (m := n + 2)) 0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply, Am_mulVec, Fin.val_zero,
    Nat.cast_zero, zero_mul, zero_add, dV] at this
  linear_combination this

lemma zp1_ode_trunc : X * d⁄dX ℚ (pp 1) = pp 1 - 2 * ww * X * PP * qq 1 := by
  have := congrFun (ode_pzz (t := t) (w := w) (m := n + 2)) 1
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Am_mulVec, fin_one_val2, Nat.cast_one,
    one_mul, dV] at this
  linear_combination this

lemma muW_zero' (t : ℚ) : muW t 0 = 1 - t := by simp [muW]
lemma muW_one' (t : ℚ) : muW t 1 = -(t * (1 - t)) := by simp [muW]; ring
lemma lamW_zero' (t : ℚ) : lamW t 0 = 1 := by simp [lamW]

lemma zG_ode_trunc (a b : Fin (n + 2)) :
    d⁄dX ℚ (GG a b) = -(ww * (pp a * (C (muW t b) * qq b) + qq a * (C (muW t b) * pp b))) := by
  have := congrFun (congrFun (dM_Gg (w := w) (l := lamW t) (μ := muW t) (m := n + 2)) a) b
  simp only [dM_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply,
    Dg, Matrix.mulVec_diagonal, smul_eq_mul] at this
  exact this

lemma zP1_trunc : ∃ e : ℚ⟦X⟧, (X : ℚ⟦X⟧) ^ (n + 2) ∣ e ∧
    X * (1 - X ^ 2) * d⁄dX ℚ PP1
      = 2 * (ww * X * (1 - X ^ 2) * (PP * QQ1 + PP1 * QQ - ww * X * PP * QQ ^ 2)
        + ww * X * (1 + X ^ 2) * PP * QQ - X ^ 2 * tt * PP
        - ww * X ^ 2 * (1 - X ^ 2) * PP ^ 2 * PPh)
        - 2 * ww * X * (1 - X ^ 2) * PP * QQ1 + e := by
  obtain ⟨e, he, h⟩ := P2_of_RZp_trunc (t := t) (w := w) (m := n + 2)
  refine ⟨2 * e, dvd_mul_of_dvd_right he _, ?_⟩
  have h1 := ode_P1g (w := w) (l := lamW t) (μ := muW t) (m := n + 2)
  have h1' : X * d⁄dX ℚ PP1 = 2 * ((Mum t (n + 2) *ᵥ (Am ℚ (n + 2) *ᵥ (Am ℚ (n + 2) *ᵥ vm ℚ (n + 2))))
      ⬝ᵥ pp) - 2 * ww * X * PP * QQ1 := h1
  linear_combination (1 - X ^ 2) * h1' + 2 * h

lemma zPh1_trunc : ∃ e : ℚ⟦X⟧, (X : ℚ⟦X⟧) ^ (n + 2) ∣ e ∧
    X * (1 - X ^ 2) * d⁄dX ℚ PPh1
      = 2 * (4 * X ^ 2 * PPh1 + ww * X * (1 - X ^ 2) * (PPh * QQh1 + PPh1 * QQ - ww * X * PPh * QQ ^ 2)
        + ww * X * (1 - 3 * X ^ 2) * PPh * QQ + (4 - tt) * X ^ 2 * PPh
        - ww * X ^ 2 * (1 - X ^ 2) * PP * PPh ^ 2)
        - 2 * ww * X * (1 - X ^ 2) * PPh * QQh1 + e := by
  obtain ⟨e, he, h⟩ := Ph2_of_RZph_trunc (t := t) (w := w) (m := n + 2)
  refine ⟨2 * e, dvd_mul_of_dvd_right he _, ?_⟩
  have h1 := ode_P1g (w := w) (l := muW t) (μ := lamW t) (m := n + 2)
  have hQ : Qg w (muW t) (lamW t) (n + 2) = QQ := (Qg_symm).symm
  have h1' : X * d⁄dX ℚ PPh1 = 2 * ((Lamm t (n + 2) *ᵥ (Am ℚ (n + 2) *ᵥ (Am ℚ (n + 2) *ᵥ vm ℚ (n + 2))))
      ⬝ᵥ phzz t w (n + 2)) - 2 * ww * X * PPh * QQh1 := h1
  have h4 : (C (4 - t) : ℚ⟦X⟧) = 4 - tt := by simp [map_sub, map_ofNat]
  rw [h4] at h
  linear_combination (1 - X ^ 2) * h1' + 2 * h

end Components

end AvgRS
