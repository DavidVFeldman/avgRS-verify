module

public import RequestProject.Formal.Resolvent

@[expose] public section

/-!
# Recurrences and differential equations for the truncated resolvent

(G3), (G4), the recurrences (Rq), (Rp) of Lemma 5.10 (`lem:rec`) and the differential equations of
Lemma 5.11 (`lem:odes`), for the finite truncations (the non-exact ones up to terms divisible by `r ^ m`).
-/

namespace AvgRS.Formal

open PowerSeries Matrix

variable {K : Type*} [Field K] [CharZero K]

variable {m : ℕ} {z : K}

local notation "HH" => Hm K m
local notation "vv" => vm K m
local notation "AA" => Am K m
local notation "XX" => Xm K m
local notation "BB" => Bm K m z
local notation "GG" => Gm K m z
local notation "cc" => (C z : K⟦X⟧)
local notation "rr" => (X : K⟦X⟧)
local notation "pp" => pm K m z
local notation "qq" => qm K m z
local notation "tt" => tm K m z
local notation "ss" => sm K m z
local notation "PP" => Pm K m z
local notation "QQ" => Qm K m z
local notation "PP1" => P1m K m z
local notation "QQ1" => Q1m K m z

variable (K) in
/-- The boundary defect of (H3). -/
noncomputable def E3m (m : ℕ) : Matrix (Fin m) (Fin m) K⟦X⟧ := (Xm K m)ᵀ * Hm K m - Hm K m * Xm K m

local notation "EE" => E3m K m

lemma E3m_dvd : DvdM m (E3m K m) := Hm_H3

lemma Hm_Am_pm : HH *ᵥ (AA *ᵥ pp) = (rr * PP) • vv - (AA *ᵥ qq + qq) := by
  have h2 := Hm_H2 (K := K) (m := m)
  have : HH * AA = rr • vecMulVec vv vv - (AA + 1) * HH := by rw [← h2]; abel
  rw [Matrix.mulVec_mulVec, this, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec',
    ← Matrix.mulVec_mulVec, Hm_mulVec_pm, Matrix.add_mulVec, Matrix.one_mulVec, smul_smul]
  rfl

omit [CharZero K] in
lemma conj_Bm (M N : Matrix (Fin m) (Fin m) K⟦X⟧) :
    M * GG * HH - GG * HH * N = GG * (BB * M * HH - HH * N * BB) * GG := by
  have k1 : GG * (BB * M * HH) * GG = M * GG * HH := by
    calc GG * (BB * M * HH) * GG = (GG * BB) * M * (HH * GG) := by simp only [Matrix.mul_assoc]
      _ = M * GG * HH := by rw [Gm_mul_Bm, Matrix.one_mul, Hm_mul_Gm, Matrix.mul_assoc]
  have k2 : GG * (HH * N * BB) * GG = GG * HH * N := by
    calc GG * (HH * N * BB) * GG = GG * HH * N * (BB * GG) := by simp only [Matrix.mul_assoc]
      _ = GG * HH * N := by rw [Bm_mul_Gm, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, k1, k2]

omit [CharZero K] in
lemma Bm_sandwich (M N : Matrix (Fin m) (Fin m) K⟦X⟧) :
    BB * M * HH - HH * N * BB = (M * HH - HH * N) + cc • (HH * (HH * M - N * HH) * HH) := by
  simp only [Bm, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [smul_sub]
  abel

/-- (G4) up to boundary terms. -/
lemma Gm_G4 : XX * GG * HH - GG * HH * XXᵀ
    = vecMulVec tt pp - vecMulVec pp tt - cc • (GG * HH * EE * HH * GG) := by
  rw [conj_Bm, Bm_sandwich, Hm_H4]
  have : HH * XX - XXᵀ * HH = -EE := by rw [E3m]; abel
  rw [this, Matrix.mul_neg, Matrix.neg_mul, smul_neg, ← sub_eq_add_neg, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, Gm_vecMulVec_Gm, Gm_vecMulVec_Gm,
    Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc]
  rfl

/-- (G3) up to boundary terms. -/
lemma Gm_G3 : XXᵀ * GG * HH - GG * HH * XX
    = -(cc • (vecMulVec ss qq - vecMulVec qq ss)) + GG * EE * GG := by
  rw [conj_Bm, Bm_sandwich]
  have h1 : XXᵀ * HH - HH * XX = EE := rfl
  have h2 : HH * XXᵀ - XX * HH = -(vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) := by
    rw [← Hm_H4]; abel
  have hGH : (GG * HH)ᵀ = GG * HH := by
    rw [Matrix.transpose_mul, Hm_transpose, Gm_transpose, Hm_mul_Gm]
  have e : GG * (HH * (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * HH) * GG
      = vecMulVec ss qq - vecMulVec qq ss := by
    have : GG * (HH * (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * HH) * GG
        = (GG * HH) * (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * (GG * HH) := by
      calc _ = (GG * HH) * (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * (HH * GG) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Hm_mul_Gm]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, mul_vecMulVec_mul hGH, mul_vecMulVec_mul hGH]
    simp only [← Matrix.mulVec_mulVec]
    rfl
  rw [h1, h2, Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, e]
  abel

end AvgRS.Formal
