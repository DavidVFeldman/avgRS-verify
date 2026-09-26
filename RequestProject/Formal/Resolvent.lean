module

public import RequestProject.Formal.TruncMat

@[expose] public section

/-!
# The truncated resolvent `G = (1 + z H²)⁻¹` and its commutation relations

Lemma 5.9 (`lem:Gids`: (G1)–(G4) and equation `eq:ts`) for the finite truncations; (G3), (G4) hold up to boundary
terms divisible by `r ^ m`.
-/

namespace AvgRS.Formal

open PowerSeries Matrix

variable {K : Type*} [Field K]

section General

variable {ι : Type*} [Fintype ι]

lemma vecMulVec_mulVec' (u w y : ι → K⟦X⟧) : vecMulVec u w *ᵥ y = (w ⬝ᵥ y) • u := by
  funext i
  simp [vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

lemma dotProduct_mulVec_symm {M : Matrix ι ι K⟦X⟧} (hM : Mᵀ = M) (u w : ι → K⟦X⟧) :
    u ⬝ᵥ (M *ᵥ w) = (M *ᵥ u) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM]

lemma mul_vecMulVec_mul {M N : Matrix ι ι K⟦X⟧} (hN : Nᵀ = N) (u w : ι → K⟦X⟧) :
    M * vecMulVec u w * N = vecMulVec (M *ᵥ u) (N *ᵥ w) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, hN]

end General

variable (K) in
/-- `B = 1 + z H²` (truncated). -/
noncomputable def Bm (m : ℕ) (z : K) : Matrix (Fin m) (Fin m) K⟦X⟧ :=
  1 + C z • (Hm K m * Hm K m)

variable (K) in
/-- The truncated resolvent `G = (1 + z H²)⁻¹`. -/
noncomputable def Gm (m : ℕ) (z : K) : Matrix (Fin m) (Fin m) K⟦X⟧ := (Bm K m z)⁻¹

variable (K) in
/-- `p = G v`. -/
noncomputable def pm (m : ℕ) (z : K) : Fin m → K⟦X⟧ := Gm K m z *ᵥ vm K m

variable (K) in
/-- `q = G H v`. -/
noncomputable def qm (m : ℕ) (z : K) : Fin m → K⟦X⟧ := Gm K m z *ᵥ (Hm K m *ᵥ vm K m)

variable (K) in
/-- `t = G A v`. -/
noncomputable def tm (m : ℕ) (z : K) : Fin m → K⟦X⟧ := Gm K m z *ᵥ (Am K m *ᵥ vm K m)

variable (K) in
/-- `s = G H A v`. -/
noncomputable def sm (m : ℕ) (z : K) : Fin m → K⟦X⟧ :=
  Gm K m z *ᵥ (Hm K m *ᵥ (Am K m *ᵥ vm K m))

variable (K) in
/-- `P = ⟨v, p⟩`. -/
noncomputable def Pm (m : ℕ) (z : K) : K⟦X⟧ := vm K m ⬝ᵥ pm K m z

variable (K) in
/-- `Q = ⟨v, q⟩`. -/
noncomputable def Qm (m : ℕ) (z : K) : K⟦X⟧ := vm K m ⬝ᵥ qm K m z

variable (K) in
/-- `P₁ = ⟨A v, p⟩`. -/
noncomputable def P1m (m : ℕ) (z : K) : K⟦X⟧ := (Am K m *ᵥ vm K m) ⬝ᵥ pm K m z

variable (K) in
/-- `Q₁ = ⟨A v, q⟩`. -/
noncomputable def Q1m (m : ℕ) (z : K) : K⟦X⟧ := (Am K m *ᵥ vm K m) ⬝ᵥ qm K m z

variable {m : ℕ} {z : K}

local notation "HH" => Hm K m
local notation "vv" => vm K m
local notation "AA" => Am K m
local notation "XX" => Xm K m
local notation "BB" => Bm K m z
local notation "GG" => Gm K m z
local notation "cc" => (C z : K⟦X⟧)
local notation "rr" => (X : K⟦X⟧)

lemma constantCoeff_Hm (a b : Fin m) : constantCoeff (Hm K m a b) = 0 :=
  (PowerSeries.X_dvd_iff).mp (X_dvd_Hm a b)

lemma isUnit_det_Bm : IsUnit (Bm K m z).det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff : K⟦X⟧ →+* K).mapMatrix (Bm K m z) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [Bm, Matrix.mul_apply, constantCoeff_Hm, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact isUnit_one

lemma Gm_mul_Bm : GG * BB = 1 := Matrix.nonsing_inv_mul _ isUnit_det_Bm

lemma Bm_mul_Gm : BB * GG = 1 := Matrix.mul_nonsing_inv _ isUnit_det_Bm

lemma Hm_mul_Gm : HH * GG = GG * HH := by
  have hHB : HH * BB = BB * HH := by
    simp only [Bm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  calc HH * GG = GG * BB * (HH * GG) := by rw [Gm_mul_Bm, Matrix.one_mul]
    _ = GG * (BB * HH) * GG := by simp only [Matrix.mul_assoc]
    _ = GG * (HH * BB) * GG := by rw [hHB]
    _ = GG * HH * (BB * GG) := by simp only [Matrix.mul_assoc]
    _ = GG * HH := by rw [Bm_mul_Gm, Matrix.mul_one]

lemma Bm_transpose : (Bm K m z)ᵀ = Bm K m z := by
  simp [Bm, Matrix.transpose_mul, Hm_transpose]

lemma Gm_transpose : (Gm K m z)ᵀ = Gm K m z := by
  rw [Gm, Matrix.transpose_nonsing_inv, Bm_transpose]

/-- `z H G H = 1 - G`. -/
lemma c_HGH : cc • (HH * GG * HH) = 1 - GG := by
  have h := Gm_mul_Bm (K := K) (m := m) (z := z)
  rw [Bm, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at h
  calc cc • (HH * GG * HH) = cc • (GG * (HH * HH)) := by rw [Hm_mul_Gm, Matrix.mul_assoc]
    _ = 1 - GG := by rw [← h]; abel

lemma Hm_mulVec_pm : HH *ᵥ pm K m z = qm K m z := by
  rw [pm, qm, Matrix.mulVec_mulVec, Hm_mul_Gm, ← Matrix.mulVec_mulVec]

lemma c_Hm_mulVec_qm : cc • (HH *ᵥ qm K m z) = vv - pm K m z := by
  rw [qm, pm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, c_HGH,
    Matrix.sub_mulVec, Matrix.one_mulVec]

lemma Hm_mulVec_tm : HH *ᵥ tm K m z = sm K m z := by
  rw [tm, sm, Matrix.mulVec_mulVec, Hm_mul_Gm, ← Matrix.mulVec_mulVec]

lemma c_Hm_mulVec_sm : cc • (HH *ᵥ sm K m z) = AA *ᵥ vv - tm K m z := by
  rw [sm, tm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, c_HGH,
    Matrix.sub_mulVec, Matrix.one_mulVec]

lemma pm_eq : pm K m z = vv - cc • (HH *ᵥ qm K m z) := by
  rw [c_Hm_mulVec_qm]; abel

lemma dot_G_symm (u w : Fin m → K⟦X⟧) : u ⬝ᵥ (GG *ᵥ w) = (GG *ᵥ u) ⬝ᵥ w :=
  dotProduct_mulVec_symm Gm_transpose u w

lemma dot_A_symm (u w : Fin m → K⟦X⟧) : u ⬝ᵥ (AA *ᵥ w) = (AA *ᵥ u) ⬝ᵥ w :=
  dotProduct_mulVec_symm Am_transpose u w

lemma dot_H_symm (u w : Fin m → K⟦X⟧) : u ⬝ᵥ (HH *ᵥ w) = (HH *ᵥ u) ⬝ᵥ w :=
  dotProduct_mulVec_symm Hm_transpose u w

lemma Gm_vecMulVec_Gm (u w : Fin m → K⟦X⟧) :
    GG * vecMulVec u w * GG = vecMulVec (GG *ᵥ u) (GG *ᵥ w) :=
  mul_vecMulVec_mul Gm_transpose u w

/-- `G B' G`-type identity: `[M, G] = G [B, M] G`. -/
lemma comm_Gm (M : Matrix (Fin m) (Fin m) K⟦X⟧) :
    M * GG - GG * M = GG * (BB * M - M * BB) * GG := by
  rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Gm_mul_Bm, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, Bm_mul_Gm, Matrix.mul_one]

variable [CharZero K]

/-- (G1): `G' = -z (p ⊗ q + q ⊗ p)`. -/
lemma dM_Gm : dM GG = -(cc • (vecMulVec (pm K m z) (qm K m z) + vecMulVec (qm K m z) (pm K m z))) := by
  rw [Gm, dM_inv _ isUnit_det_Bm, ← Gm]
  have hB : dM BB = cc • (vecMulVec vv (HH *ᵥ vv) + vecMulVec (HH *ᵥ vv) vv) := by
    rw [Bm, dM_add, dM_one, zero_add, dM_C_smul, dM_mul, dM_Hm, Matrix.vecMulVec_mul,
      Matrix.mul_vecMulVec, ← Matrix.mulVec_transpose, Hm_transpose]
  rw [hB, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Gm_vecMulVec_Gm,
    Gm_vecMulVec_Gm]
  rfl

/-- (H6): `[A, H²] = r (v ⊗ Hv - Hv ⊗ v)`. -/
lemma Hm_H6 : AA * (HH * HH) - HH * HH * AA
    = rr • (vecMulVec vv (HH *ᵥ vv) - vecMulVec (HH *ᵥ vv) vv) := by
  have h2 := Hm_H2 (K := K) (m := m)
  have hAH : AA * HH = rr • vecMulVec vv vv - HH * AA - HH := by
    rw [← h2, Matrix.add_mul, Matrix.one_mul]; abel
  have e1 : vecMulVec vv vv * HH = vecMulVec vv (HH *ᵥ vv) := by
    rw [Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, Hm_transpose]
  have e2 : HH * vecMulVec vv vv = vecMulVec (HH *ᵥ vv) vv := Matrix.mul_vecMulVec _ _ _
  calc AA * (HH * HH) - HH * HH * AA = (AA * HH) * HH - HH * (HH * AA) := by
        simp only [Matrix.mul_assoc]
    _ = (rr • vecMulVec vv vv - HH * AA - HH) * HH
        - HH * (rr • vecMulVec vv vv - AA * HH - HH) := by
        rw [← hAH]; congr 2; rw [hAH]; abel
    _ = _ := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, e1, e2,
          Matrix.mul_assoc, smul_sub]
        abel

/-- (G2): `[A, G] = -z r (p ⊗ q - q ⊗ p)`. -/
lemma Am_comm_Gm : AA * GG - GG * AA
    = -((cc * rr) • (vecMulVec (pm K m z) (qm K m z) - vecMulVec (qm K m z) (pm K m z))) := by
  rw [comm_Gm]
  have : BB * AA - AA * BB = -(cc • (AA * (HH * HH) - HH * HH * AA)) := by
    simp only [Bm, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  rw [this, Hm_H6, Matrix.mul_neg, Matrix.neg_mul, smul_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Gm_vecMulVec_Gm, Gm_vecMulVec_Gm]
  rfl

/-- (`eq:ts`): `t = A p + z r (Q p - P q)`. -/
lemma tm_eq : tm K m z
    = AA *ᵥ pm K m z + (cc * rr) • (Qm K m z • pm K m z - Pm K m z • qm K m z) := by
  have h : GG * AA = AA * GG + (cc * rr) • (vecMulVec (pm K m z) (qm K m z)
      - vecMulVec (qm K m z) (pm K m z)) := by
    rw [← sub_eq_iff_eq_add', ← neg_sub, Am_comm_Gm, neg_neg]
  rw [tm, Matrix.mulVec_mulVec, h, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', Qm, Pm, dotProduct_comm (qm K m z),
    dotProduct_comm (pm K m z)]
  rfl

/-- (`eq:ts`): `s = -(A+1) q + r (z Q q + P p)`. -/
lemma sm_eq : sm K m z = rr • ((cc * Qm K m z) • qm K m z + Pm K m z • pm K m z)
    - (AA *ᵥ qm K m z + qm K m z) := by
  rw [← Hm_mulVec_tm, tm_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Hm_mulVec_pm]
  have hHA : HH *ᵥ (AA *ᵥ pm K m z) = (rr * Pm K m z) • vv - (AA *ᵥ qm K m z + qm K m z) := by
    have h2 := Hm_H2 (K := K) (m := m)
    have : HH * AA = rr • vecMulVec vv vv - (AA + 1) * HH := by rw [← h2]; abel
    rw [Matrix.mulVec_mulVec, this, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec',
      ← Matrix.mulVec_mulVec, Hm_mulVec_pm, Matrix.add_mulVec, Matrix.one_mulVec, smul_smul]
    rfl
  have hq := c_Hm_mulVec_qm (K := K) (m := m) (z := z)
  rw [hHA]
  have e : (cc * rr) • (Pm K m z • (HH *ᵥ qm K m z)) = (rr * Pm K m z) • (vv - pm K m z) := by
    rw [← hq, smul_smul, smul_smul]; congr 1; ring
  rw [smul_sub, e]
  module

omit [CharZero K] in
/-- (7.15): `⟨v, t⟩ = P₁`. -/
lemma dot_vm_tm : vv ⬝ᵥ tm K m z = P1m K m z := by
  rw [tm, dot_G_symm, dotProduct_comm, P1m, pm]

/-- (7.15): `⟨v, s⟩ = -Q₁ - Q + r(z Q² + P²)`. -/
lemma dot_vm_sm : vv ⬝ᵥ sm K m z
    = -Q1m K m z - Qm K m z + rr * (cc * Qm K m z ^ 2 + Pm K m z ^ 2) := by
  rw [sm_eq, dotProduct_sub, dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_add, dot_A_symm]
  simp only [Qm, Pm, Q1m, smul_eq_mul]
  ring

end AvgRS.Formal
