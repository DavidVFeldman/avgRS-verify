module

public import RequestProject.Formal.ResolventRec

@[expose] public section

/-!
# The recurrences (Rq), (Rp) and the differential equations (Lemmas 5.10, 5.11), truncated
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
local notation "EE" => E3m K m
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

/-- (Rq) up to boundary terms: `X q = P A p - σ p + β q`. -/
lemma Rq_trunc : ∃ err : Fin m → K⟦X⟧, DvdV m err ∧
    XX *ᵥ qq = PP • (AA *ᵥ pp) - (PP1 - cc * rr * PP * QQ) • pp
      + (rr * (1 - cc * PP ^ 2)) • qq + err := by
  have h4 := congrArg (· *ᵥ vv) (Gm_G4 (K := K) (m := m) (z := z))
  have e5 := vm_H5a (K := K) (m := m)
  obtain ⟨e, he, hX⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ vv = rr • vv + e :=
    ⟨_, e5, by abel⟩
  have a1 : (XX * GG * HH) *ᵥ vv = XX *ᵥ qq := by
    rw [qm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have a2 : (GG * HH * XXᵀ) *ᵥ vv = rr • qq + GG *ᵥ (HH *ᵥ e) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
    rfl
  have a3 : (vecMulVec tt pp - vecMulVec pp tt) *ᵥ vv = PP • tt - PP1 • pp := by
    rw [Matrix.sub_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', dotProduct_comm pp,
      dotProduct_comm tt, dot_vm_tm]
    rfl
  have h4' : XX *ᵥ qq - (rr • qq + GG *ᵥ (HH *ᵥ e))
      = PP • tt - PP1 • pp - cc • ((GG * HH * EE * HH * GG) *ᵥ vv) := by
    rw [← a1, ← a2, ← a3, ← Matrix.smul_mulVec, ← Matrix.sub_mulVec, ← Matrix.sub_mulVec]
    exact h4
  rw [tm_eq] at h4'
  refine ⟨GG *ᵥ (HH *ᵥ e) - cc • ((GG * HH * EE * HH * GG) *ᵥ vv), ?_, ?_⟩
  · exact ((he.mulVec _).mulVec _).sub
      (((((E3m_dvd (K := K)).mul_left (GG * HH)).mul_right HH).mul_right GG).mulVec vv |>.smul _)
  · generalize XX *ᵥ qq = a at h4' ⊢
    generalize AA *ᵥ pp = b at h4' ⊢
    generalize GG *ᵥ (HH *ᵥ e) = c at h4' ⊢
    generalize (GG * HH * EE * HH * GG) *ᵥ vv = d at h4' ⊢
    generalize pp = p at h4' ⊢
    generalize qq = q at h4' ⊢
    linear_combination (norm := module) h4'

omit [CharZero K] in
lemma c_Hm_Gm_Hm (w : Fin m → K⟦X⟧) : cc • (HH *ᵥ (GG *ᵥ (HH *ᵥ w))) = w - GG *ᵥ w := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec,
    c_HGH, Matrix.sub_mulVec, Matrix.one_mulVec]

lemma Gm_Am_mulVec (w : Fin m → K⟦X⟧) : GG *ᵥ (AA *ᵥ w)
    = AA *ᵥ (GG *ᵥ w) + (cc * rr) • ((qq ⬝ᵥ w) • pp - (pp ⬝ᵥ w) • qq) := by
  have h : GG * AA = AA * GG + (cc * rr) • (vecMulVec pp qq - vecMulVec qq pp) := by
    rw [← sub_eq_iff_eq_add', ← neg_sub, Am_comm_Gm, neg_neg]
  rw [Matrix.mulVec_mulVec, h, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, vecMulVec_mulVec', vecMulVec_mulVec']

lemma Gm_Am_Am_vm : GG *ᵥ (AA *ᵥ (AA *ᵥ vv)) = AA *ᵥ (AA *ᵥ pp)
    + (cc * rr) • (QQ1 • pp - PP1 • qq) + (cc * rr) • (QQ • (AA *ᵥ pp) - PP • (AA *ᵥ qq)) := by
  rw [Gm_Am_mulVec, Gm_Am_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul, ← pm, dotProduct_comm qq, dotProduct_comm pp,
    dotProduct_comm qq, dotProduct_comm pp]
  simp only [Qm, Pm, Q1m, P1m]
  module

/-- (Rp) up to boundary terms (multiplied by `r`):
`r X p = A² p - z r P A q + z r W p - z r σ q + r ε v`. -/
lemma Rp_trunc : ∃ err : Fin m → K⟦X⟧, DvdV m err ∧
    rr • (XX *ᵥ pp) = AA *ᵥ (AA *ᵥ pp) - (cc * rr * PP) • (AA *ᵥ qq)
      + (cc * rr * (rr * PP ^ 2 - QQ)) • pp - (cc * rr * (PP1 - cc * rr * PP * QQ)) • qq
      + (rr * (cc * (2 * QQ1 + QQ - rr * cc * QQ ^ 2 - rr * PP ^ 2))) • vv + err := by
  have E1 : XX *ᵥ pp = XX *ᵥ vv - cc • (XX *ᵥ (HH *ᵥ qq)) := by
    conv_lhs => rw [pm_eq]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have E2 : XX *ᵥ (HH *ᵥ qq) = HH *ᵥ (XXᵀ *ᵥ qq) + QQ • (AA *ᵥ vv) - QQ1 • vv := by
    have h := Hm_H4 (K := K) (m := m)
    have : XX * HH = HH * XXᵀ + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) := by
      rw [← h]; abel
    rw [Matrix.mulVec_mulVec, this, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      vecMulVec_mulVec', vecMulVec_mulVec']
    simp only [Qm, Q1m]
    abel
  have s3 : XXᵀ *ᵥ qq = GG *ᵥ (HH *ᵥ (XX *ᵥ vv)) - cc • (QQ • ss - (vv ⬝ᵥ ss) • qq)
      + (GG * EE * GG) *ᵥ vv := by
    have h3 := congrArg (· *ᵥ vv) (Gm_G3 (K := K) (m := m) (z := z))
    have b1 : (XXᵀ * GG * HH) *ᵥ vv = XXᵀ *ᵥ qq := by
      rw [qm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have b2 : (GG * HH * XX) *ᵥ vv = GG *ᵥ (HH *ᵥ (XX *ᵥ vv)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have b3 : (vecMulVec ss qq - vecMulVec qq ss) *ᵥ vv = QQ • ss - (vv ⬝ᵥ ss) • qq := by
      rw [Matrix.sub_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', dotProduct_comm qq,
        dotProduct_comm ss]
      rfl
    simp only at h3
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, b1, b2,
      b3] at h3
    rw [sub_eq_iff_eq_add] at h3
    rw [h3]
    abel
  have E3 : cc • (HH *ᵥ (XXᵀ *ᵥ qq)) = (XX *ᵥ vv - GG *ᵥ (XX *ᵥ vv))
      - cc • (QQ • (AA *ᵥ vv - tt) - (vv ⬝ᵥ ss) • (vv - pp))
      + cc • (HH *ᵥ ((GG * EE * GG) *ᵥ vv)) := by
    rw [s3, Matrix.mulVec_add, Matrix.mulVec_sub, smul_add, smul_sub, c_Hm_Gm_Hm,
      ← c_Hm_mulVec_sm, ← c_Hm_mulVec_qm, Matrix.mulVec_smul, Matrix.mulVec_sub,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
    module
  have E4 : rr • (GG *ᵥ (XX *ᵥ vv)) = GG *ᵥ (AA *ᵥ (AA *ᵥ vv)) := by
    rw [← Matrix.mulVec_smul, ← vm_H5b]
  have E5 := Gm_Am_Am_vm (K := K) (m := m) (z := z)
  have E6 := tm_eq (K := K) (m := m) (z := z)
  rw [dot_vm_sm] at E3
  refine ⟨-(rr * cc) • (HH *ᵥ ((GG * EE * GG) *ᵥ vv)), ?_, ?_⟩
  · exact (((((E3m_dvd (K := K)).mul_left GG).mul_right GG).mulVec vv).mulVec HH).smul _
  · generalize XX *ᵥ pp = a1 at *
    generalize XX *ᵥ (HH *ᵥ qq) = a2 at *
    generalize HH *ᵥ (XXᵀ *ᵥ qq) = a3 at *
    generalize GG *ᵥ (AA *ᵥ (AA *ᵥ vv)) = a4 at *
    generalize GG *ᵥ (XX *ᵥ vv) = a5 at *
    generalize HH *ᵥ ((GG * EE * GG) *ᵥ vv) = a6 at *
    generalize XX *ᵥ vv = a7 at *
    generalize AA *ᵥ (AA *ᵥ pp) = a8 at *
    generalize AA *ᵥ pp = a9 at *
    generalize AA *ᵥ qq = a10 at *
    generalize AA *ᵥ vv = a11 at *
    generalize tt = t at *
    generalize pp = p at *
    generalize qq = q at *
    linear_combination (norm := module) rr • E1 - (rr * cc) • E2 - rr • E3 + E4 + E5
      - (rr * cc * QQ) • E6

omit [CharZero K] in
lemma dM_Am : dM AA = 0 := by
  refine Matrix.ext fun a b => ?_
  by_cases h : a = b
  · subst h; simp [Am, Matrix.diagonal_apply_eq]
  · simp [Am, Matrix.diagonal_apply_ne _ h]

/-- (7.18): `r p' = A p - 2 z r P q`. -/
lemma ode_p : rr • dV pp = AA *ᵥ pp - (2 * cc * rr * PP) • qq := by
  have h1 : dV pp = dM GG *ᵥ vv + GG *ᵥ dV vv := dV_mulVec _ _
  have h2 : rr • (GG *ᵥ dV vv) = tt := by
    rw [← Matrix.mulVec_smul, X_smul_dV_vm]; rfl
  rw [h1, smul_add, h2, dM_Gm, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    vecMulVec_mulVec', vecMulVec_mulVec', tm_eq, dotProduct_comm qq, dotProduct_comm pp]
  simp only [Qm, Pm]
  module

/-- (7.18): `r q' = 2 r P p - (A+1) q`. -/
lemma ode_q : rr • dV qq = (2 * rr * PP) • pp - (AA *ᵥ qq + qq) := by
  have h0 : qq = HH *ᵥ pp := Hm_mulVec_pm.symm
  have h1 : dV qq = dM HH *ᵥ pp + HH *ᵥ dV pp := by rw [h0]; exact dV_mulVec _ _
  have h2 : rr • (HH *ᵥ dV pp) = HH *ᵥ (AA *ᵥ pp) - (2 * rr * PP) • (cc • (HH *ᵥ qq)) := by
    rw [← Matrix.mulVec_smul, ode_p, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_smul]
    congr 2; ring
  rw [h1, smul_add, h2, dM_Hm, vecMulVec_mulVec', Hm_Am_pm, c_Hm_mulVec_qm]
  simp only [Pm]
  module

/-- (7.19): `r P' = 2 P₁ - 2 z r P Q`. -/
lemma ode_P : rr * d⁄dX K PP = 2 * PP1 - 2 * cc * rr * PP * QQ := by
  have a1 : rr * (dV vv ⬝ᵥ pp) = (AA *ᵥ vv) ⬝ᵥ pp := by
    rw [← X_smul_dV_vm, smul_dotProduct, smul_eq_mul]
  have a2 : rr * (vv ⬝ᵥ dV pp) = vv ⬝ᵥ (AA *ᵥ pp - (2 * cc * rr * PP) • qq) := by
    rw [← ode_p, dotProduct_smul, smul_eq_mul]
  have e : d⁄dX K PP = dV vv ⬝ᵥ pp + vv ⬝ᵥ dV pp := d_dotProduct _ _
  rw [e, mul_add, a1, a2, dotProduct_sub, dotProduct_smul, dot_A_symm]
  simp only [P1m, Qm, smul_eq_mul]
  ring

/-- (7.19): `r Q' = 2 r P² - Q`. -/
lemma ode_Q : rr * d⁄dX K QQ = 2 * rr * PP ^ 2 - QQ := by
  have a1 : rr * (dV vv ⬝ᵥ qq) = (AA *ᵥ vv) ⬝ᵥ qq := by
    rw [← X_smul_dV_vm, smul_dotProduct, smul_eq_mul]
  have a2 : rr * (vv ⬝ᵥ dV qq) = vv ⬝ᵥ ((2 * rr * PP) • pp - (AA *ᵥ qq + qq)) := by
    rw [← ode_q, dotProduct_smul, smul_eq_mul]
  have e : d⁄dX K QQ = dV vv ⬝ᵥ qq + vv ⬝ᵥ dV qq := d_dotProduct _ _
  rw [e, mul_add, a1, a2, dotProduct_sub, dotProduct_smul, dotProduct_add, dot_A_symm]
  simp only [Qm, Pm, smul_eq_mul]
  ring

/-- (7.18): `G'_{ab} = -z (p_a q_b + q_a p_b)`. -/
lemma ode_G (a b : Fin m) :
    d⁄dX K (GG a b) = -(cc * (pp a * qq b + qq a * pp b)) := by
  have := congrFun (congrFun (dM_Gm (K := K) (m := m) (z := z)) a) b
  simp [vecMulVec_apply] at this
  rw [this]; ring

/-- (7.19) up to boundary terms: `P₁' = 2 β P + 2 z Q (P + σ)`. -/
lemma ode_P1 : ∃ e : K⟦X⟧, (X : K⟦X⟧) ^ m ∣ e ∧
    d⁄dX K PP1 = 2 * (rr * (1 - cc * PP ^ 2)) * PP
      + 2 * cc * QQ * (PP + (PP1 - cc * rr * PP * QQ)) + e := by
  obtain ⟨errq, herrq, hRq⟩ := Rq_trunc (K := K) (m := m) (z := z)
  obtain ⟨e5, he5, hX⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ vv = rr • vv + e := ⟨_, vm_H5a, by abel⟩
  -- `r P₁' = 2 ⟨A² v, p⟩ - 2 z r P Q₁`
  have hd : rr * d⁄dX K PP1 = 2 * ((AA *ᵥ (AA *ᵥ vv)) ⬝ᵥ pp) - 2 * cc * rr * PP * QQ1 := by
    have e : d⁄dX K PP1 = dV (AA *ᵥ vv) ⬝ᵥ pp + (AA *ᵥ vv) ⬝ᵥ dV pp := d_dotProduct _ _
    have hAv : rr • dV (AA *ᵥ vv) = AA *ᵥ (AA *ᵥ vv) := by
      rw [dV_mulVec, dM_Am, Matrix.zero_mulVec, zero_add, ← Matrix.mulVec_smul, X_smul_dV_vm]
    have a1 : rr * (dV (AA *ᵥ vv) ⬝ᵥ pp) = (AA *ᵥ (AA *ᵥ vv)) ⬝ᵥ pp := by
      rw [← hAv, smul_dotProduct, smul_eq_mul]
    have a2 : rr * ((AA *ᵥ vv) ⬝ᵥ dV pp) = (AA *ᵥ vv) ⬝ᵥ (AA *ᵥ pp - (2 * cc * rr * PP) • qq) := by
      rw [← ode_p, dotProduct_smul, smul_eq_mul]
    rw [e, mul_add, a1, a2, dotProduct_sub, dotProduct_smul, dot_A_symm]
    simp only [Q1m, smul_eq_mul]
    ring
  -- `⟨A² v, p⟩ = r ⟨v, Xᵀ p⟩`
  have hA2 : (AA *ᵥ (AA *ᵥ vv)) ⬝ᵥ pp = rr * (vv ⬝ᵥ (XXᵀ *ᵥ pp)) := by
    rw [vm_H5b, smul_dotProduct, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  -- `Xᵀ p`
  have hXp : XXᵀ *ᵥ pp = (cc * PP) • (AA *ᵥ qq + qq) + (cc * (PP1 - cc * rr * PP * QQ)) • qq
      + (rr * (1 - cc * PP ^ 2)) • pp
      + (e5 - cc • (HH *ᵥ errq) - cc • (EE *ᵥ qq)) := by
    have h1 : XXᵀ *ᵥ pp = XXᵀ *ᵥ vv - cc • ((XXᵀ * HH) *ᵥ qq) := by
      conv_lhs => rw [pm_eq]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    have h2 : XXᵀ * HH = HH * XX + EE := by rw [E3m]; abel
    have h3 : cc • (HH *ᵥ (XX *ᵥ qq)) = PP • (cc • (HH *ᵥ (AA *ᵥ pp)))
        - (PP1 - cc * rr * PP * QQ) • (cc • qq) + (rr * (1 - cc * PP ^ 2)) • (vv - pp)
        + cc • (HH *ᵥ errq) := by
      rw [hRq, ← c_Hm_mulVec_qm, ← Hm_mulVec_pm]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
      module
    rw [h1, h2, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hX, smul_add, h3, Hm_Am_pm]
    simp only [Pm]
    module
  have hv : vv ⬝ᵥ (XXᵀ *ᵥ pp) = cc * PP * (QQ1 + QQ) + cc * (PP1 - cc * rr * PP * QQ) * QQ
      + rr * (1 - cc * PP ^ 2) * PP + vv ⬝ᵥ (e5 - cc • (HH *ᵥ errq) - cc • (EE *ᵥ qq)) := by
    rw [hXp]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dot_A_symm]
    simp only [Q1m, Qm, Pm]
  refine ⟨2 * (vv ⬝ᵥ (e5 - cc • (HH *ᵥ errq) - cc • (EE *ᵥ qq))), ?_, ?_⟩
  · refine dvd_mul_of_dvd_right (DvdV.dot ?_ _) _
    exact (he5.sub ((herrq.mulVec _).smul _)).sub (((E3m_dvd (K := K)).mulVec _).smul _)
  · apply mul_left_cancel₀ (X_ne_zero (R := K))
    rw [hd, hA2, hv]
    ring

end AvgRS.Formal
