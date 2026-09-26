module

public import RequestProject.Formal.RecODE
public import RequestProject.ZLineDet
public import RequestProject.ZLineGenODE

@[expose] public section

/-!
# Batch 5: the operator layer and the recurrences on the line `z + z' = −2`

The determinants of `ZLineDet.lean` are built from `H_z H_{z'}ᵀ`.  Conjugating by the diagonal
matrix `diag(z (z+1)_a)` turns that product into `C₁ = H Λ H M`, where `H` is the Plancherel hook
matrix of `Formal/Hook.lean` and

    λ_b = ∏_{j<b} ((j+2)² − t),    μ_a = (1 − t) ∏_{j<a} (j² − t),    t = (z+1)².

This file sets up `C₁`, its resolvent, the two families of vectors and the eight scalars, and states
the identities of COMMISSION.md (batch 5), items A0–C3.  Items W1–W5, A1–A4 and B1–B9 are exact
identities of truncated matrices; item A5 and the three recurrences C1–C3 hold up to an error
divisible by `X ^ m`, as in `Formal/ResolventRec.lean` and `Formal/RecODE.lean`.

Everything here concerns Section 3 of `avgRS.tex` (`sec:zline`, Conjecture 3.2 `conj:zline`) and is
the z-line analogue of Lemmas 5.6, 5.9, 5.10, 5.11 (`lem:Hids`, `lem:Gids`, `lem:rec`, `lem:odes`).
The first integrals beyond B9, the closed forms and the proof of Conjecture 3.2 are **not** part of
this batch.

`COMMISSION.md` has a plain-English proof of every statement below, and
`zline_recurrences_check.py` verifies all of them coefficientwise in exact rational arithmetic.
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

/-! ### Weights -/

/-- `λ_b = ∏_{j<b} ((j+2)² − t)`. -/
noncomputable def lamW (t : ℚ) (b : ℕ) : ℚ := ∏ j ∈ range b, (((j : ℚ) + 2) ^ 2 - t)

/-- `μ_a = (1 − t) ∏_{j<a} (j² − t)`. -/
noncomputable def muW (t : ℚ) (a : ℕ) : ℚ := (1 - t) * ∏ j ∈ range a, ((j : ℚ) ^ 2 - t)

/-- `ν_b = ∏_{j<b} ((j+1)² − t)`; this is `(1 − t) λ_{b−1}`, the division-free form of the shifted
weight `Λ⁻` of item A3. -/
noncomputable def nuW (t : ℚ) (b : ℕ) : ℚ := ∏ j ∈ range b, (((j : ℚ) + 1) ^ 2 - t)

/-- `Λ = diag(λ_b)`, truncated. -/
noncomputable def Lamm (t : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Matrix.diagonal fun b => C (lamW t b)

/-- `M = diag(μ_a)`, truncated. -/
noncomputable def Mum (t : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Matrix.diagonal fun a => C (muW t a)

/-- `μ⁻_a = μ_{a−1}`, with `μ⁻_0 = 1`; the shifted weight of items A3h and W3. -/
noncomputable def muMW (t : ℚ) : ℕ → ℚ
  | 0 => 1
  | (a + 1) => muW t a

/-- `N = diag(ν_b)`, truncated. -/
noncomputable def Num (t : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Matrix.diagonal fun b => C (nuW t b)

/-- `M⁻ = diag(μ⁻_a)`, truncated. -/
noncomputable def Mumm (t : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Matrix.diagonal fun a => C (muMW t a)

/-- `D_k = (A + k)² − t`, truncated (`k : ℤ`, used with `k = −1, 0, 1, 2`). -/
noncomputable def Dmz (t : ℚ) (k : ℤ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Matrix.diagonal fun a => C ((((a : ℤ) + k : ℤ) : ℚ) ^ 2 - t)

/-! ### The two resolvents -/

/-- `C₁ = H Λ H M`. -/
noncomputable def Czz (t : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Hm ℚ m * Lamm t m * Hm ℚ m * Mum t m

/-- `Ĉ₁ = H M H Λ`. -/
noncomputable def Chzz (t : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Hm ℚ m * Mum t m * Hm ℚ m * Lamm t m

/-- `B = 1 + ω C₁`. -/
noncomputable def Bzz (t w : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ := 1 + C w • Czz t m

/-- `B̂ = 1 + ω Ĉ₁`. -/
noncomputable def Bhzz (t w : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ := 1 + C w • Chzz t m

/-- `𝒢 = (1 + ω C₁)⁻¹`. -/
noncomputable def Gzz (t w : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ := (Bzz t w m)⁻¹

/-- `𝒢̂ = (1 + ω Ĉ₁)⁻¹`. -/
noncomputable def Ghzz (t w : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ := (Bhzz t w m)⁻¹

/-- Both `B` and `B̂` are invertible: their entries off the diagonal have zero constant term. -/
lemma isUnit_det_Bzz (t w : ℚ) (m : ℕ) : IsUnit (Bzz t w m).det := by
  exact isUnit_det_Bg

lemma isUnit_det_Bhzz (t w : ℚ) (m : ℕ) : IsUnit (Bhzz t w m).det := by
  exact isUnit_det_Bg

/-! ### Vectors and scalars -/

/-- `p = 𝒢 v`. -/
noncomputable def pzz (t w : ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ := Gzz t w m *ᵥ vm ℚ m

/-- `p̂ = 𝒢̂ v`. -/
noncomputable def phzz (t w : ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ := Ghzz t w m *ᵥ vm ℚ m

/-- `q = H Λ p̂`. -/
noncomputable def qzz (t w : ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ :=
  (Hm ℚ m * Lamm t m) *ᵥ phzz t w m

/-- `q̂ = H M p`. -/
noncomputable def qhzz (t w : ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ :=
  (Hm ℚ m * Mum t m) *ᵥ pzz t w m

/-- `c = H Λ v`. -/
noncomputable def czz (t : ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ := (Hm ℚ m * Lamm t m) *ᵥ vm ℚ m

noncomputable def Pzz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ := (Mum t m *ᵥ vm ℚ m) ⬝ᵥ pzz t w m
noncomputable def Qzz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ := (Mum t m *ᵥ vm ℚ m) ⬝ᵥ qzz t w m
noncomputable def Phzz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ := (Lamm t m *ᵥ vm ℚ m) ⬝ᵥ phzz t w m
noncomputable def Qhzz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ := (Lamm t m *ᵥ vm ℚ m) ⬝ᵥ qhzz t w m
noncomputable def P1zz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (Mum t m *ᵥ (Am ℚ m *ᵥ vm ℚ m)) ⬝ᵥ pzz t w m
noncomputable def Q1zz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (Mum t m *ᵥ (Am ℚ m *ᵥ vm ℚ m)) ⬝ᵥ qzz t w m
noncomputable def Ph1zz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (Lamm t m *ᵥ (Am ℚ m *ᵥ vm ℚ m)) ⬝ᵥ phzz t w m
noncomputable def Qh1zz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (Lamm t m *ᵥ (Am ℚ m *ᵥ vm ℚ m)) ⬝ᵥ qhzz t w m

/-- `σ = (1 − r²)(P₁ − ω r P Q)`. -/
noncomputable def sigzz (t w : ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (1 - X ^ 2) * (P1zz t w m - C w * X * Pzz t w m * Qzz t w m)

section
variable {t w : ℚ} {m : ℕ}

local notation "HH" => Hm ℚ m
local notation "vv" => vm ℚ m
local notation "AA" => Am ℚ m
local notation "XX" => Xm ℚ m
local notation "LL" => Lamm t m
local notation "MM" => Mum t m
local notation "NN" => Num t m
local notation "MMm" => Mumm t m
local notation "GG" => Gzz t w m
local notation "GGh" => Ghzz t w m
local notation "pp" => pzz t w m
local notation "qq" => qzz t w m
local notation "pph" => phzz t w m
local notation "qqh" => qhzz t w m
local notation "cc" => czz t m
local notation "ww" => (C w : ℚ⟦X⟧)
local notation "tt" => (C t : ℚ⟦X⟧)
local notation "rr" => (X : ℚ⟦X⟧)
local notation "uu" => (1 - X ^ 2 : ℚ⟦X⟧)
local notation "PP" => Pzz t w m
local notation "QQ" => Qzz t w m
local notation "PPh" => Phzz t w m
local notation "QQh" => Qhzz t w m
local notation "PP1" => P1zz t w m
local notation "QQ1" => Q1zz t w m
local notation "PPh1" => Ph1zz t w m
local notation "QQh1" => Qh1zz t w m
local notation "ss" => sigzz t w m

lemma Dmz_eq (k : ℤ) : Dmz t k m = Dg (fun a => ((a : ℚ) + k) ^ 2 - t) m := by
  simp [Dmz, Dg]

/-- The second half of item A2: `D₂ H = H D₋₁ + r ((A+3)v ⊗ v − v ⊗ Av)`. -/
lemma Dmz_two_mul_Hm : Dmz t 2 m * HH
    = HH * Dmz t (-1) m + rr • (vecMulVec (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv) vv
        - vecMulVec vv (AA *ᵥ vv)) := by
  rw [Dmz_eq, Dmz_eq]
  refine Matrix.ext fun a b => ?_
  simp only [Dg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Am_mulVec, smul_eq_mul, Hm,
    vm, Matrix.of_apply]
  have h := hE_H2 (K := ℚ) a b
  simp only [map_sub, map_pow, map_add, map_natCast, map_intCast]
  push_cast
  linear_combination ((a : ℚ⟦X⟧) - b + 3) * h

/-! ### A0: the bridge to `ZLineDet.lean` -/

/-- **Item A0.**  For every diagonal `diag(d)`, the determinant of `1 + diag(d) H_z H_{z'}ᵀ` is
unchanged when `H_z H_{z'}ᵀ` is replaced by `C₁ = H Λ H M` at `t = (z+1)²`.  With `d` constant this
is `G0m`, and with `d = (1,1,ω,ω,…)` it is `G2m` (`ZLineDet.lean`).  Proof: conjugation by
`diag(z (z+1)_a)` for `z ∉ {0, −1, −2, …}`, then equality of polynomials in `z`. -/
theorem det_one_add_diag_Czz (z : ℚ) (d : Fin m → ℚ) :
    (1 + Matrix.diagonal (fun a => C (d a)) * Czm z m).det
      = (1 + Matrix.diagonal (fun a => C (d a)) * Czz ((z + 1) ^ 2) m).det := by
  have hHz : ∀ z' : ℚ, Hzm z' m = Dg (armProd z') m * HH * Dg (legProd z') m := by
    intro z'
    refine Matrix.ext fun a b => ?_
    simp only [Dg, Matrix.diagonal_mul, Matrix.mul_diagonal, Hzm, Hm, Matrix.of_apply,
      hE_eq_hookF, hookFz, hookContentProd_eq, map_mul]
    ring
  have hL : Dg (legProd z) m * Dg (legProd (-z - 2)) m = Lamm ((z + 1) ^ 2) m := by
    rw [Dg_mul_Dg]
    refine Dg_congr fun b => ?_
    simp only [legProd, lamW, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hM : Dg (armProd z) m * Dg (armProd (-z - 2)) m = Mum ((z + 1) ^ 2) m := by
    rw [Dg_mul_Dg]
    refine Dg_congr fun a => ?_
    simp only [armProd, muW, Finset.prod_range_succ']
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    push_cast
    rw [mul_comm]
    congr 1
    · ring
    · exact Finset.prod_congr rfl fun j _ => by ring
  set K := HH * Lamm ((z + 1) ^ 2) m * HH with hK
  set D := Matrix.diagonal (fun a => C (d a)) with hD
  have e1 : Czm z m = Dg (armProd z) m * K * Dg (armProd (-z - 2)) m := by
    calc Czm z m = Dg (armProd z) m * HH * Dg (legProd z) m
          * (Dg (legProd (-z - 2)) m * HH * Dg (armProd (-z - 2)) m) := by
          rw [Czm, hHz, hHz, Matrix.transpose_mul, Matrix.transpose_mul, Dg_transpose,
            Dg_transpose, Hm_transpose]
          simp only [Matrix.mul_assoc]
      _ = Dg (armProd z) m * (HH * (Dg (legProd z) m * Dg (legProd (-z - 2)) m) * HH)
          * Dg (armProd (-z - 2)) m := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL]
  have hDc : ∀ f : ℕ → ℚ, Dg f m * D = D * Dg f m := fun f => by
    simp only [hD, Dg, Matrix.diagonal_mul_diagonal, mul_comm]
  have hCz : Czz ((z + 1) ^ 2) m = K * Mum ((z + 1) ^ 2) m := rfl
  clear_value K D
  have key : Dg (armProd (-z - 2)) m * (D * Dg (armProd z) m * K)
      = D * (Dg (armProd z) m * Dg (armProd (-z - 2)) m) * K := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDc, Matrix.mul_assoc D,
      Dg_comm_Dg (armProd (-z - 2))]
  calc (1 + D * Czm z m).det
      = (1 + (D * Dg (armProd z) m * K) * Dg (armProd (-z - 2)) m).det := by
        rw [e1]; simp only [Matrix.mul_assoc]
    _ = (1 + Dg (armProd (-z - 2)) m * (D * Dg (armProd z) m * K)).det :=
        Matrix.det_one_add_mul_comm _ _
    _ = (1 + (D * Mum ((z + 1) ^ 2) m) * K).det := by
        rw [key, hM]
    _ = (1 + Mum ((z + 1) ^ 2) m * (D * K)).det := by
        rw [show Mum ((z + 1) ^ 2) m * (D * K) = (Mum ((z + 1) ^ 2) m * D) * K from
          (Matrix.mul_assoc _ _ _).symm, show Mum ((z + 1) ^ 2) m * D = D * Mum ((z + 1) ^ 2) m
          from hDc _]
    _ = (1 + (D * K) * Mum ((z + 1) ^ 2) m).det := Matrix.det_one_add_mul_comm _ _
    _ = (1 + D * Czz ((z + 1) ^ 2) m).det := by rw [hCz, Matrix.mul_assoc]

/-! ### W: the weight-shift identities (exact) -/

/-- **W1.** `μ_{a+1} = (a² − t) μ_a` and `λ_{a+1} = ((a+2)² − t) λ_a`; also `ν_{b+1} = ((b+1)² − t) ν_b`
and `(1 − t) λ_{b−1} = ν_b` (`nuW_succ`, `muW_succ`, `lamW_succ`, `lamW_pred`). -/
lemma muW_succ (t : ℚ) (a : ℕ) : muW t (a + 1) = ((a : ℚ) ^ 2 - t) * muW t a := by
  simp only [muW, Finset.prod_range_succ]; ring

lemma lamW_succ (t : ℚ) (b : ℕ) : lamW t (b + 1) = (((b : ℚ) + 2) ^ 2 - t) * lamW t b := by
  simp only [lamW, Finset.prod_range_succ]; ring

lemma nuW_succ (t : ℚ) (b : ℕ) : nuW t (b + 1) = (((b : ℚ) + 1) ^ 2 - t) * nuW t b := by
  simp only [nuW, Finset.prod_range_succ]; ring

lemma one_sub_mul_lamW (t : ℚ) (b : ℕ) : (1 - t) * lamW t b = nuW t (b + 1) := by
  induction b with
  | zero => simp [lamW, nuW]
  | succ b ih => rw [lamW_succ, nuW_succ, ← mul_assoc, mul_comm (1 - t), mul_assoc, ih]; push_cast; ring

/-- **W2.** `Xᵀ M = M D₀ Xᵀ`. -/
lemma XT_mul_Mum : XXᵀ * MM = MM * Dmz t 0 m * XXᵀ := by
  rw [Dmz_eq]
  show (Xm ℚ m)ᵀ * Dg (muW t) m = Dg (muW t) m * Dg _ m * (Xm ℚ m)ᵀ
  rw [Dg_mul_Dg]
  exact XmT_mul_Dg _ _ fun a => by rw [muW_succ]; push_cast; ring

/-- **W3.** `X M = M⁻ X`. -/
lemma Xm_mul_Mum : XX * MM = MMm * XX := by
  exact Xm_mul_Dg _ _ fun b => rfl

/-- **W4.** `(1 − t) X Λ = N X`. -/
lemma Xm_mul_Lamm : C (1 - t) • (XX * LL) = NN * XX := by
  rw [← Matrix.mul_smul]
  show Xm ℚ m * (C (1 - t) • Dg (lamW t) m) = Dg (nuW t) m * Xm ℚ m
  rw [C_smul_Dg]
  exact Xm_mul_Dg _ _ fun b => one_sub_mul_lamW t b

/-- **W5.** `Xᵀ Λ = Λ D₂ Xᵀ`. -/
lemma XT_mul_Lamm : XXᵀ * LL = LL * Dmz t 2 m * XXᵀ := by
  rw [Dmz_eq]
  show (Xm ℚ m)ᵀ * Dg (lamW t) m = Dg (lamW t) m * Dg _ m * (Xm ℚ m)ᵀ
  rw [Dg_mul_Dg]
  exact XmT_mul_Dg _ _ fun a => by rw [lamW_succ]; push_cast; ring

/-- **W6.** `D₁ N = (1 − t) Λ` and `D₋₁ M⁻ = M`. -/
lemma Dmz_one_mul_Num : Dmz t 1 m * NN = C (1 - t) • LL := by
  rw [Dmz_eq]
  show Dg _ m * Dg (nuW t) m = C (1 - t) • Dg (lamW t) m
  rw [Dg_mul_Dg, C_smul_Dg]
  exact Dg_congr fun a => by rw [one_sub_mul_lamW, nuW_succ]; push_cast; ring

lemma Dmz_neg_one_mul_Mumm : Dmz t (-1) m * MMm = MM := by
  rw [Dmz_eq]
  show Dg _ m * Dg (muMW t) m = Dg (muW t) m
  rw [Dg_mul_Dg]
  refine Dg_congr fun a => ?_
  cases a with
  | zero => norm_num [muMW, muW]
  | succ a => simp only [muMW]; rw [muW_succ]; push_cast; ring

/-! ### A: the operator layer (exact) -/

/-- **A1.**  (H2) dressed by `Λ`: `(HΛ) A + (A+1)(HΛ) = r v ⊗ Λv`. -/
lemma HLam_H2 : (HH * LL) * AA + (AA + 1) * (HH * LL)
    = rr • vecMulVec vv (LL *ᵥ vv) := by
  exact HD_H2

/-- **A2.**  `D₀ H = H D₁ − r (v ⊗ (A+1)v − Av ⊗ v)`. -/
lemma Dmz_zero_mul_Hm : Dmz t 0 m * HH
    = HH * Dmz t 1 m - rr • (vecMulVec vv (AA *ᵥ vv + vv) - vecMulVec (AA *ᵥ vv) vv) := by
  rw [Dmz_eq, Dmz_eq]
  refine Matrix.ext fun a b => ?_
  simp only [Dg, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply,
    Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Am_mulVec, smul_eq_mul, Hm,
    vm, Matrix.of_apply]
  have h := hE_H2 (K := ℚ) a b
  simp only [map_sub, map_pow, map_add, map_natCast, map_intCast]
  push_cast
  linear_combination ((a : ℚ⟦X⟧) - b - 1) * h

/-- **A3.**  The crux of C2/C3: `D₀ H N H = (1 − t) H Λ H − r (v ⊗ H N (A+1)v − Av ⊗ H N v)`,
so `D₀ H N H` differs from a multiple of `H Λ H` by a matrix of rank two.  (This is A2 multiplied
by `N H` on the right, together with W6.) -/
lemma Dmz_zero_HNH : Dmz t 0 m * HH * NN * HH
    = C (1 - t) • (HH * LL * HH)
      - rr • (vecMulVec vv ((HH * NN) *ᵥ (AA *ᵥ vv + vv))
              - vecMulVec (AA *ᵥ vv) ((HH * NN) *ᵥ vv)) := by
  have h2 := Dmz_zero_mul_Hm (t := t) (m := m)
  have h6 := Dmz_one_mul_Num (t := t) (m := m)
  have hNt : (Num t m)ᵀ = Num t m := Dg_transpose
  have e : Dmz t 0 m * HH * NN * HH = (Dmz t 0 m * HH) * (NN * HH) := by
    simp only [Matrix.mul_assoc]
  have e2 : HH * Dmz t 1 m * (NN * HH) = C (1 - t) • (HH * LL * HH) := by
    rw [show HH * Dmz t 1 m * (NN * HH) = HH * (Dmz t 1 m * NN) * HH by
      simp only [Matrix.mul_assoc], h6, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, h2, Matrix.sub_mul, e2, Matrix.smul_mul, Matrix.sub_mul, vecMulVec_mul_eq,
    vecMulVec_mul_eq, Matrix.transpose_mul, Hm_transpose, hNt]

/-- **A3h.**  The hatted crux, for C3: `D₂ H M⁻ H = H M H + r ((A+3)v ⊗ H M⁻ v − v ⊗ H M⁻ A v)`.
(This is `D₂ H = H D₋₁ + r ((A+3)v ⊗ v − v ⊗ Av)` multiplied by `M⁻ H` on the right, with W6.) -/
lemma Dmz_two_HMmH : Dmz t 2 m * HH * MMm * HH
    = HH * MM * HH
      + rr • (vecMulVec (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv) ((HH * MMm) *ᵥ vv)
              - vecMulVec vv ((HH * MMm) *ᵥ (AA *ᵥ vv))) := by
  have h2 := Dmz_two_mul_Hm (t := t) (m := m)
  have h6 := Dmz_neg_one_mul_Mumm (t := t) (m := m)
  have hNt : (Mumm t m)ᵀ = Mumm t m := Dg_transpose
  have e : Dmz t 2 m * HH * MMm * HH = (Dmz t 2 m * HH) * (MMm * HH) := by
    simp only [Matrix.mul_assoc]
  have e2 : HH * Dmz t (-1) m * (MMm * HH) = HH * MM * HH := by
    rw [show HH * Dmz t (-1) m * (MMm * HH) = HH * (Dmz t (-1) m * MMm) * HH by
      simp only [Matrix.mul_assoc], h6]
  rw [e, h2, Matrix.add_mul, e2, Matrix.smul_mul, Matrix.sub_mul, vecMulVec_mul_eq,
    vecMulVec_mul_eq, Matrix.transpose_mul, Hm_transpose, hNt]

/-- **A4.**  `[A, C₁] = r (v ⊗ Mc − c ⊗ Mv)`. -/
lemma Am_comm_Czz : AA * Czz t m - Czz t m * AA
    = rr • (vecMulVec vv (MM *ᵥ cc) - vecMulVec cc (MM *ᵥ vv)) := by
  exact Am_comm_Cg

/-- **A5.**  `[X, C₁] = Av ⊗ Mc + v ⊗ (A+1)Mc − r²(A−1)c ⊗ Mv − r² c ⊗ AMv − r(1−r²)⟨Λv,v⟩ v ⊗ Mv`,
up to an error divisible by `X ^ m` (the boundary defect of (H3)). -/
lemma Xm_comm_Czz : ∃ err : Matrix (Fin m) (Fin m) ℚ⟦X⟧, DvdM m err ∧
    XX * Czz t m - Czz t m * XX
      = vecMulVec (AA *ᵥ vv) (MM *ᵥ cc) + vecMulVec vv (AA *ᵥ (MM *ᵥ cc) + MM *ᵥ cc)
        - (rr ^ 2) • vecMulVec (AA *ᵥ cc - cc) (MM *ᵥ vv)
        - (rr ^ 2) • vecMulVec cc (AA *ᵥ (MM *ᵥ vv))
        - (rr * uu * ((LL *ᵥ vv) ⬝ᵥ vv)) • vecMulVec vv (MM *ᵥ vv) + err := by
  have hXH : XX * HH = HH * XXᵀ + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) := by
    rw [← Hm_H4 (K := ℚ)]; abel
  have hXtH : XXᵀ * HH = HH * XX + E3m ℚ m := by rw [E3m]; abel
  have hXtL : XXᵀ * LL = LL * (Dmz t 2 m * XXᵀ) := by rw [XT_mul_Lamm, Matrix.mul_assoc]
  have hMX : MM * XX = Dmz t (-1) m * (XX * MM) := by
    rw [Xm_mul_Mum, ← Matrix.mul_assoc, Dmz_neg_one_mul_Mumm]
  have hD2 := Dmz_two_mul_Hm (t := t) (m := m)
  obtain ⟨e5, he5, h5⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ vv = rr • vv + e := ⟨_, vm_H5a, by abel⟩
  obtain ⟨e6, he6, h6⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ (AA *ᵥ vv) = rr • (AA *ᵥ vv + vv) + e :=
    ⟨_, vm_H5a_A, by abel⟩
  have hMt : (Mum t m)ᵀ = Mum t m := Dg_transpose
  have hLt : (Lamm t m)ᵀ = Lamm t m := Dg_transpose
  have hA1 : (HH * LL) * AA = rr • vecMulVec vv (LL *ᵥ vv) - (AA + 1) * (HH * LL) := HD_mul_Am
  have hMA : ∀ u, MM *ᵥ (AA *ᵥ u) = AA *ᵥ (MM *ᵥ u) := fun u => Dg_Am_mulVec u
  have hHLA : (HH * LL) *ᵥ (AA *ᵥ vv) = (rr * ((LL *ᵥ vv) ⬝ᵥ vv)) • vv - (AA *ᵥ cc + cc) := by
    rw [Matrix.mulVec_mulVec, hA1, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec',
      ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, smul_smul]
    rfl
  have k1 : XX * Czz t m = HH * (LL * (Dmz t 2 m * (HH * (XX * MM))))
      + HH * (LL * (Dmz t 2 m * (E3m ℚ m * MM)))
      + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * (LL * (HH * MM)) := by
    calc XX * Czz t m = (XX * HH) * (LL * (HH * MM)) := by simp only [Czz, Matrix.mul_assoc]
      _ = HH * ((XXᵀ * LL) * (HH * MM))
          + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * (LL * (HH * MM)) := by
        rw [hXH, Matrix.add_mul]; simp only [Matrix.mul_assoc]
      _ = HH * (LL * (Dmz t 2 m * ((XXᵀ * HH) * MM)))
          + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * (LL * (HH * MM)) := by
        rw [hXtL]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hXtH]; simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  have k2 : Czz t m * XX = HH * (LL * (HH * (Dmz t (-1) m * (XX * MM)))) := by
    rw [show Czz t m * XX = HH * (LL * (HH * (MM * XX))) by simp only [Czz, Matrix.mul_assoc], hMX]
  have k3 : HH * (LL * (Dmz t 2 m * (HH * (XX * MM))))
      = HH * (LL * (HH * (Dmz t (-1) m * (XX * MM))))
        + rr • (HH * (LL * ((vecMulVec (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv) vv
            - vecMulVec vv (AA *ᵥ vv)) * (XX * MM)))) := by
    rw [← Matrix.mul_assoc (Dmz t 2 m), hD2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have k4 : (XX * MM)ᵀ = MM * XXᵀ := by rw [Matrix.transpose_mul, hMt]
  have k5 : HH * (LL * ((vecMulVec (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv) vv
            - vecMulVec vv (AA *ᵥ vv)) * (XX * MM)))
      = vecMulVec ((HH * LL) *ᵥ (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv)) (MM *ᵥ (XXᵀ *ᵥ vv))
        - vecMulVec ((HH * LL) *ᵥ vv) (MM *ᵥ (XXᵀ *ᵥ (AA *ᵥ vv))) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, vecMulVec_mul_eq, k4, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have k6 : (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) * (LL * (HH * MM))
      = vecMulVec (AA *ᵥ vv) (MM *ᵥ ((HH * LL) *ᵥ vv))
        - vecMulVec vv (MM *ᵥ ((HH * LL) *ᵥ (AA *ᵥ vv))) := by
    simp only [Matrix.sub_mul, vecMulVec_mul_eq, Matrix.transpose_mul, hMt, hLt, Hm_transpose,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hc : (HH * LL) *ᵥ vv = cc := rfl
  refine ⟨HH * (LL * (Dmz t 2 m * (E3m ℚ m * MM)))
    + rr • (vecMulVec ((HH * LL) *ᵥ (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv)) (MM *ᵥ e5)
      - vecMulVec cc (MM *ᵥ e6)), ?_, ?_⟩
  · refine DvdM.add ((((E3m_dvd (K := ℚ)).mul_right _).mul_left _).mul_left _ |>.mul_left _) ?_
    exact (DvdM.sub' (DvdM_vecMulVec _ (he5.mulVec _)) (DvdM_vecMulVec _ (he6.mulVec _))).smul _
  · rw [k1, k2, k3, k5, k6, h5, h6, hc]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hHLA, hc]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hMA,
      Matrix.vecMulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_sub, Matrix.sub_vecMulVec,
      Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_sub, smul_add]
    module

/-! ### B: the resolvent layer (exact) -/

/-- **B1.**  `𝒢 H Λ = H Λ 𝒢̂` and `H M 𝒢 = 𝒢̂ H M`. -/
lemma Gzz_mul_HLam : GG * (HH * LL) = (HH * LL) * GGh := by
  exact Gg_mul_HD

lemma HMum_mul_Gzz : (HH * MM) * GG = GGh * (HH * MM) := by
  exact (Gg_mul_HD (w := w) (l := muW t) (μ := lamW t) (m := m)).symm

/-- **B2.**  `ω H M q = v − p̂`. -/
lemma c_HMum_mulVec_qzz : ww • ((HH * MM) *ᵥ qq) = vv - pph := by
  exact C_smul_HD_qg

/-- **B3.**  `Q = Q̂`. -/
lemma Qzz_eq_Qhzz : QQ = QQh := by
  exact Qg_symm

/-- **B4.**  `𝒢 A v = A p + ω r (Q p − P q)` (the `[A, 𝒢]` identity applied to `v`). -/
lemma Gzz_mulVec_Am_vm : GG *ᵥ (AA *ᵥ vv) = AA *ᵥ pp + (ww * rr * QQ) • pp - (ww * rr * PP) • qq := by
  exact Gg_mulVec_Am_vm

/-- **B5.**  `r p' = A p − 2 ω r P q`. -/
lemma ode_pzz : rr • dV pp = AA *ᵥ pp - (2 * ww * rr * PP) • qq := by
  exact ode_pg

/-- **B6.**  `r q' = 2 r P̂ p − (A+1) q`. -/
lemma ode_qzz : rr • dV qq = (2 * rr * PPh) • pp - (AA *ᵥ qq + qq) := by
  exact ode_qg

/-- **B7.**  `r p̂' = A p̂ − 2 ω r P̂ q̂`. -/
lemma ode_phzz : rr • dV pph = AA *ᵥ pph - (2 * ww * rr * PPh) • qqh := by
  exact ode_pg

/-- **B8.**  `r q̂' = 2 r P p̂ − (A+1) q̂`. -/
lemma ode_qhzz : rr • dV qqh = (2 * rr * PP) • pph - (AA *ᵥ qqh + qqh) := by
  exact ode_qg

/-- The scalar equations that follow from B5–B8 by pairing with `Mv`, `Λv`, `MAv`, `ΛAv`. -/
lemma ode_Pzz : rr * d⁄dX ℚ PP = 2 * PP1 - 2 * ww * rr * PP * QQ := by
  exact ode_Pg

lemma ode_Phzz : rr * d⁄dX ℚ PPh = 2 * PPh1 - 2 * ww * rr * PPh * QQ := by
  have h := ode_Pg (w := w) (l := muW t) (μ := lamW t) (m := m)
  rw [← Qg_symm] at h
  exact h

lemma ode_Qzz : rr * d⁄dX ℚ QQ = 2 * rr * PP * PPh - QQ := by
  exact ode_Qg

lemma ode_Q1zz : rr * d⁄dX ℚ QQ1 = 2 * rr * PPh * PP1 - QQ1 := by
  exact ode_Q1g

lemma ode_Qh1zz : rr * d⁄dX ℚ QQh1 = 2 * rr * PP * PPh1 - QQh1 := by
  exact ode_Q1g

/-- **B9.**  The first integral `Q₁ + Q̂₁ + Q = r P P̂ + ω r Q²`.
Proof: write `F` for the difference; the scalar equations give `r F' = −F`, hence `(r F)' = 0`,
and `F` has zero constant term, so `F = 0`. -/
theorem first_integral_R2 : QQ1 + QQh1 + QQ = rr * PP * PPh + ww * rr * QQ ^ 2 := by
  exact first_integral_g

/-! ### The twisted shifts `D₀ Xᵀ`, `D₂ Xᵀ` against `C₁`, `Ĉ₁` (the rank-four commutators) -/

/-- `Xᵀ M⁻ = M⁻ D₋₁ Xᵀ`. -/
lemma XT_mul_Mumm : XXᵀ * MMm = MMm * Dmz t (-1) m * XXᵀ := by
  rw [Dmz_eq]
  show (Xm ℚ m)ᵀ * Dg (muMW t) m = Dg (muMW t) m * Dg _ m * (Xm ℚ m)ᵀ
  rw [Dg_mul_Dg]
  refine XmT_mul_Dg _ _ fun a => ?_
  cases a with
  | zero => norm_num [muMW, muW]
  | succ a => simp only [muMW]; rw [muW_succ]; push_cast; ring

lemma Mumm_mul_Dmz_neg_one : MMm * Dmz t (-1) m = MM := by
  rw [← Dmz_neg_one_mul_Mumm, Dmz_eq]
  exact Dg_comm_Dg _

/-- `Xᵀ M⁻ u = M⁻ D₋₁ Xᵀ u`, evaluated through `D₋₁ M⁻ = M`: for `u = v`, `Xᵀ M⁻ v ≡ r M v`. -/
lemma XT_Mumm_vm : ∃ e, DvdV m e ∧ XXᵀ *ᵥ (MMm *ᵥ vv) = rr • (MM *ᵥ vv) + e := by
  obtain ⟨e5, he5, h5⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ vv = rr • vv + e := ⟨_, vm_H5a, by abel⟩
  refine ⟨MM *ᵥ e5, he5.mulVec _, ?_⟩
  rw [Matrix.mulVec_mulVec, XT_mul_Mumm, Mumm_mul_Dmz_neg_one, ← Matrix.mulVec_mulVec, h5,
    Matrix.mulVec_add, Matrix.mulVec_smul]

lemma XT_Mumm_Am_vm : ∃ e, DvdV m e ∧
    XXᵀ *ᵥ (MMm *ᵥ (AA *ᵥ vv)) = rr • (MM *ᵥ (AA *ᵥ vv + vv)) + e := by
  obtain ⟨e6, he6, h6⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ (AA *ᵥ vv) = rr • (AA *ᵥ vv + vv) + e :=
    ⟨_, vm_H5a_A, by abel⟩
  refine ⟨MM *ᵥ e6, he6.mulVec _, ?_⟩
  rw [Matrix.mulVec_mulVec, XT_mul_Mumm, Mumm_mul_Dmz_neg_one, ← Matrix.mulVec_mulVec, h6,
    Matrix.mulVec_add, Matrix.mulVec_smul]

/-- `X H u = H Xᵀ u + ⟨v, u⟩ A v − ⟨A v, u⟩ v` (the vector form of (H4)). -/
lemma Xm_Hm_mulVec (u : Fin m → ℚ⟦X⟧) :
    XX *ᵥ (HH *ᵥ u) = HH *ᵥ (XXᵀ *ᵥ u) + (vv ⬝ᵥ u) • (AA *ᵥ vv) - ((AA *ᵥ vv) ⬝ᵥ u) • vv := by
  have h : XX * HH = HH * XXᵀ + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) := by
    rw [← Hm_H4 (K := ℚ)]; abel
  rw [Matrix.mulVec_mulVec, h, Matrix.add_mulVec, Matrix.sub_mulVec, vecMulVec_mulVec',
    vecMulVec_mulVec', ← Matrix.mulVec_mulVec]
  abel

/-- `D₂ H u = H D₋₁ u + r (⟨v,u⟩ (A+3) v − ⟨Av,u⟩ v)`. -/
lemma Dmz_two_Hm_mulVec (u : Fin m → ℚ⟦X⟧) :
    Dmz t 2 m *ᵥ (HH *ᵥ u) = HH *ᵥ (Dmz t (-1) m *ᵥ u)
      + rr • ((vv ⬝ᵥ u) • (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv) - ((AA *ᵥ vv) ⬝ᵥ u) • vv) := by
  rw [Matrix.mulVec_mulVec, Dmz_two_mul_Hm, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', ← Matrix.mulVec_mulVec]

/-- **The C3 commutator.**  `[D₂ Xᵀ, Ĉ₁]` equals, up to `X ^ m`, the rank-four matrix
`r(1−r²)⟨Mv,v⟩ v ⊗ Λv + r² v ⊗ Λ(A+3)ĉ + r² Av ⊗ Λĉ − ĉ ⊗ ΛAv − (A+1)ĉ ⊗ Λv`, `ĉ = H M v`. -/
lemma Yh_comm_Chzz : ∃ err : Matrix (Fin m) (Fin m) ℚ⟦X⟧, DvdM m err ∧
    Dmz t 2 m * XXᵀ * Chzz t m - Chzz t m * (Dmz t 2 m * XXᵀ)
      = (rr * uu * ((MM *ᵥ vv) ⬝ᵥ vv)) • vecMulVec vv (LL *ᵥ vv)
        + (rr ^ 2) • vecMulVec vv (LL *ᵥ (AA *ᵥ ((HH * MM) *ᵥ vv) + (3 : ℚ⟦X⟧) • ((HH * MM) *ᵥ vv)))
        + (rr ^ 2) • vecMulVec (AA *ᵥ vv) (LL *ᵥ ((HH * MM) *ᵥ vv))
        - vecMulVec ((HH * MM) *ᵥ vv) (LL *ᵥ (AA *ᵥ vv))
        - vecMulVec (AA *ᵥ ((HH * MM) *ᵥ vv) + (HH * MM) *ᵥ vv) (LL *ᵥ vv) + err := by
  set ch := (HH * MM) *ᵥ vv with hch
  have hXtH : XXᵀ * HH = HH * XX + E3m ℚ m := by rw [E3m]; abel
  have hXH : XX * HH = HH * XXᵀ + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) := by
    rw [← Hm_H4 (K := ℚ)]; abel
  have hXM : XX * MM = MMm * XX := Xm_mul_Mum
  have hXtL : XXᵀ * LL = LL * (Dmz t 2 m * XXᵀ) := by rw [XT_mul_Lamm, Matrix.mul_assoc]
  have hA3h := Dmz_two_HMmH (t := t) (m := m)
  set R3 := vecMulVec (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv) ((HH * MMm) *ᵥ vv)
    - vecMulVec vv ((HH * MMm) *ᵥ (AA *ᵥ vv)) with hR3
  set EE := vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv) with hEE
  have e1 : Dmz t 2 m * XXᵀ * Chzz t m
      = (Dmz t 2 m * HH * MMm * HH) * (LL * (Dmz t 2 m * XXᵀ))
        + Dmz t 2 m * HH * MMm * EE * LL + Dmz t 2 m * E3m ℚ m * MM * HH * LL := by
    calc Dmz t 2 m * XXᵀ * Chzz t m = Dmz t 2 m * (XXᵀ * HH) * MM * HH * LL := by
          simp only [Chzz, Matrix.mul_assoc]
      _ = Dmz t 2 m * HH * (XX * MM) * HH * LL + Dmz t 2 m * E3m ℚ m * MM * HH * LL := by
          rw [hXtH]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = Dmz t 2 m * HH * MMm * (XX * HH) * LL + Dmz t 2 m * E3m ℚ m * MM * HH * LL := by
          rw [hXM]; simp only [Matrix.mul_assoc]
      _ = Dmz t 2 m * HH * MMm * HH * (XXᵀ * LL) + Dmz t 2 m * HH * MMm * EE * LL
          + Dmz t 2 m * E3m ℚ m * MM * HH * LL := by
          rw [hXH]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [hXtL]
  have e2 : (Dmz t 2 m * HH * MMm * HH) * (LL * (Dmz t 2 m * XXᵀ))
      = Chzz t m * (Dmz t 2 m * XXᵀ) + rr • (R3 * (XXᵀ * LL)) := by
    rw [hA3h, Matrix.add_mul, Matrix.smul_mul]
    simp only [Chzz, Matrix.mul_assoc]
    rw [hXtL]
  have hLt : (Lamm t m)ᵀ = Lamm t m := Dg_transpose
  have e3 : R3 * (XXᵀ * LL) = vecMulVec (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv)
        (LL *ᵥ (XX *ᵥ (HH *ᵥ (MMm *ᵥ vv))))
      - vecMulVec vv (LL *ᵥ (XX *ᵥ (HH *ᵥ (MMm *ᵥ (AA *ᵥ vv))))) := by
    simp only [hR3, Matrix.sub_mul, vecMulVec_mul_eq, Matrix.transpose_mul, hLt,
      Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e4 : Dmz t 2 m * HH * MMm * EE * LL
      = vecMulVec (Dmz t 2 m *ᵥ (HH *ᵥ (MMm *ᵥ (AA *ᵥ vv)))) (LL *ᵥ vv)
        - vecMulVec (Dmz t 2 m *ᵥ (HH *ᵥ (MMm *ᵥ vv))) (LL *ᵥ (AA *ᵥ vv)) := by
    simp only [hEE, Matrix.mul_sub, Matrix.sub_mul, vecMulVec_mul_eq, hLt, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  obtain ⟨e7, he7, h7⟩ := XT_Mumm_vm (t := t) (m := m)
  obtain ⟨e8, he8, h8⟩ := XT_Mumm_Am_vm (t := t) (m := m)
  have hMmD : ∀ u, Dmz t (-1) m *ᵥ (MMm *ᵥ u) = MM *ᵥ u := fun u => by
    rw [Matrix.mulVec_mulVec, Dmz_neg_one_mul_Mumm]
  have hA1 : (HH * MM) * AA = rr • vecMulVec vv (MM *ᵥ vv) - (AA + 1) * (HH * MM) := HD_mul_Am
  have hHMA : HH *ᵥ (MM *ᵥ (AA *ᵥ vv)) = (rr * ((MM *ᵥ vv) ⬝ᵥ vv)) • vv - (AA *ᵥ ch + ch) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA1, Matrix.sub_mulVec, Matrix.smul_mulVec,
      vecMulVec_mulVec', Matrix.add_mul, Matrix.one_mul, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec _ AA, smul_smul]
  have hm1 : (AA *ᵥ vv) ⬝ᵥ (MMm *ᵥ vv) = vv ⬝ᵥ (MMm *ᵥ (AA *ᵥ vv)) :=
    (dot_Dg_symm (l := muMW t) _ _).trans (dotProduct_comm _ _)
  have hHM : HH *ᵥ (MM *ᵥ vv) = ch := by rw [hch, Matrix.mulVec_mulVec]
  refine ⟨Dmz t 2 m * E3m ℚ m * MM * HH * LL
    + rr • (vecMulVec (AA *ᵥ vv + (3 : ℚ⟦X⟧) • vv) (LL *ᵥ (HH *ᵥ e7))
      - vecMulVec vv (LL *ᵥ (HH *ᵥ e8))), ?_, ?_⟩
  · refine DvdM.add (((((E3m_dvd (K := ℚ)).mul_left _).mul_right _).mul_right _).mul_right _) ?_
    exact (DvdM.sub' (DvdM_vecMulVec _ ((he7.mulVec _).mulVec _))
      (DvdM_vecMulVec _ ((he8.mulVec _).mulVec _))).smul _
  · rw [e1, e2, e3, e4, Xm_Hm_mulVec, Xm_Hm_mulVec, h7, h8, Dmz_two_Hm_mulVec,
      Dmz_two_Hm_mulVec, hMmD, hMmD]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hHMA, hHM]
    simp only [Matrix.vecMulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_sub,
      Matrix.sub_vecMulVec, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_sub, smul_add, hm1]
    module

/-- `Xᵀ N = N D₁ Xᵀ`. -/
lemma XT_mul_Num : XXᵀ * NN = NN * Dmz t 1 m * XXᵀ := by
  rw [Dmz_eq]
  show (Xm ℚ m)ᵀ * Dg (nuW t) m = Dg (nuW t) m * Dg _ m * (Xm ℚ m)ᵀ
  rw [Dg_mul_Dg]
  exact XmT_mul_Dg _ _ fun a => by rw [nuW_succ]; push_cast; ring

/-- `D₀ H u = H D₁ u − r (⟨(A+1)v, u⟩ v − ⟨v, u⟩ A v)`. -/
lemma Dmz_zero_Hm_mulVec (u : Fin m → ℚ⟦X⟧) :
    Dmz t 0 m *ᵥ (HH *ᵥ u) = HH *ᵥ (Dmz t 1 m *ᵥ u)
      - rr • (((AA *ᵥ vv + vv) ⬝ᵥ u) • vv - (vv ⬝ᵥ u) • (AA *ᵥ vv)) := by
  rw [Matrix.mulVec_mulVec, Dmz_zero_mul_Hm, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', ← Matrix.mulVec_mulVec]

/-- **The C2 commutator, multiplied by `1 − t`.** -/
lemma Y_comm_Czz_scaled : ∃ err : Matrix (Fin m) (Fin m) ℚ⟦X⟧, DvdM m err ∧
    C (1 - t) • (Dmz t 0 m * XXᵀ * Czz t m - Czz t m * (Dmz t 0 m * XXᵀ))
      = C (1 - t) • ((rr * uu * ((LL *ᵥ vv) ⬝ᵥ vv)) • vecMulVec vv (MM *ᵥ vv)
        + (rr ^ 2) • vecMulVec vv (MM *ᵥ (AA *ᵥ cc - cc))
        + (rr ^ 2) • vecMulVec (AA *ᵥ vv) (MM *ᵥ cc)
        - vecMulVec cc (MM *ᵥ (AA *ᵥ vv))
        - vecMulVec (AA *ᵥ cc + cc) (MM *ᵥ vv)) + err := by
  have hXtH : XXᵀ * HH = HH * XX + E3m ℚ m := by rw [E3m]; abel
  have hXH : XX * HH = HH * XXᵀ + (vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv)) := by
    rw [← Hm_H4 (K := ℚ)]; abel
  have hW4 := Xm_mul_Lamm (t := t) (m := m)
  have hW2 : XXᵀ * MM = MM * (Dmz t 0 m * XXᵀ) := by rw [XT_mul_Mum, Matrix.mul_assoc]
  have hA3 := Dmz_zero_HNH (t := t) (m := m)
  set R2 := vecMulVec vv ((HH * NN) *ᵥ (AA *ᵥ vv + vv))
    - vecMulVec (AA *ᵥ vv) ((HH * NN) *ᵥ vv) with hR2
  set EE := vecMulVec (AA *ᵥ vv) vv - vecMulVec vv (AA *ᵥ vv) with hEE
  have e1 : C (1 - t) • (Dmz t 0 m * XXᵀ * Czz t m)
      = C (1 - t) • (Czz t m * (Dmz t 0 m * XXᵀ)) - rr • (R2 * (XXᵀ * MM))
        + Dmz t 0 m * HH * NN * EE * MM + C (1 - t) • (Dmz t 0 m * E3m ℚ m * LL * HH * MM) := by
    calc C (1 - t) • (Dmz t 0 m * XXᵀ * Czz t m)
        = C (1 - t) • (Dmz t 0 m * (XXᵀ * HH) * LL * HH * MM) := by
          simp only [Czz, Matrix.mul_assoc]
      _ = Dmz t 0 m * HH * (C (1 - t) • (XX * LL)) * HH * MM
          + C (1 - t) • (Dmz t 0 m * E3m ℚ m * LL * HH * MM) := by
          rw [hXtH]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, smul_add, Matrix.mul_smul,
            Matrix.smul_mul]
      _ = Dmz t 0 m * HH * NN * (XX * HH) * MM
          + C (1 - t) • (Dmz t 0 m * E3m ℚ m * LL * HH * MM) := by
          rw [hW4]; simp only [Matrix.mul_assoc]
      _ = (Dmz t 0 m * HH * NN * HH) * (XXᵀ * MM) + Dmz t 0 m * HH * NN * EE * MM
          + C (1 - t) • (Dmz t 0 m * E3m ℚ m * LL * HH * MM) := by
          rw [hXH]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [hA3]
          conv_lhs => rw [hW2]
          simp only [Matrix.sub_mul, Matrix.smul_mul, Czz, Matrix.mul_assoc]
          rw [← hW2]
  have hMt : (Mum t m)ᵀ = Mum t m := Dg_transpose
  have e2 : R2 * (XXᵀ * MM) = vecMulVec vv (MM *ᵥ (XX *ᵥ (HH *ᵥ (NN *ᵥ (AA *ᵥ vv + vv)))))
      - vecMulVec (AA *ᵥ vv) (MM *ᵥ (XX *ᵥ (HH *ᵥ (NN *ᵥ vv)))) := by
    simp only [hR2, Matrix.sub_mul, vecMulVec_mul_eq, Matrix.transpose_mul, hMt,
      Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e3 : Dmz t 0 m * HH * NN * EE * MM
      = vecMulVec (Dmz t 0 m *ᵥ (HH *ᵥ (NN *ᵥ (AA *ᵥ vv)))) (MM *ᵥ vv)
        - vecMulVec (Dmz t 0 m *ᵥ (HH *ᵥ (NN *ᵥ vv))) (MM *ᵥ (AA *ᵥ vv)) := by
    simp only [hEE, Matrix.mul_sub, Matrix.sub_mul, vecMulVec_mul_eq, hMt, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  obtain ⟨e5, he5, h5⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ vv = rr • vv + e := ⟨_, vm_H5a, by abel⟩
  obtain ⟨e6, he6, h6⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ (AA *ᵥ vv) = rr • (AA *ᵥ vv + vv) + e :=
    ⟨_, vm_H5a_A, by abel⟩
  have hXtN : ∀ u, XXᵀ *ᵥ (NN *ᵥ u) = NN *ᵥ (Dmz t 1 m *ᵥ (XXᵀ *ᵥ u)) := fun u => by
    rw [Matrix.mulVec_mulVec, XT_mul_Num, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hND : ∀ u, NN *ᵥ (Dmz t 1 m *ᵥ u) = C (1 - t) • (LL *ᵥ u) := fun u => by
    rw [Matrix.mulVec_mulVec, show NN * Dmz t 1 m = Dmz t 1 m * NN by
      rw [Dmz_eq]; exact Dg_comm_Dg _, Dmz_one_mul_Num, Matrix.smul_mulVec]
  have hDN : ∀ u, Dmz t 1 m *ᵥ (NN *ᵥ u) = C (1 - t) • (LL *ᵥ u) := fun u => by
    rw [Matrix.mulVec_mulVec, Dmz_one_mul_Num, Matrix.smul_mulVec]
  have hA1 : (HH * LL) * AA = rr • vecMulVec vv (LL *ᵥ vv) - (AA + 1) * (HH * LL) := HD_mul_Am
  have hHLA : HH *ᵥ (LL *ᵥ (AA *ᵥ vv)) = (rr * ((LL *ᵥ vv) ⬝ᵥ vv)) • vv - (AA *ᵥ cc + cc) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA1, Matrix.sub_mulVec, Matrix.smul_mulVec,
      vecMulVec_mulVec', Matrix.add_mul, Matrix.one_mul, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec _ AA, smul_smul]
    rfl
  have hHL : HH *ᵥ (LL *ᵥ vv) = cc := by rw [Matrix.mulVec_mulVec]; rfl
  have hn1 : (AA *ᵥ vv) ⬝ᵥ (NN *ᵥ vv) = vv ⬝ᵥ (NN *ᵥ (AA *ᵥ vv)) :=
    (dot_Dg_symm (l := nuW t) _ _).trans (dotProduct_comm _ _)
  refine ⟨-rr • (vecMulVec vv (MM *ᵥ (HH *ᵥ (C (1 - t) • (LL *ᵥ (e6 + e5)))))
      - vecMulVec (AA *ᵥ vv) (MM *ᵥ (HH *ᵥ (C (1 - t) • (LL *ᵥ e5)))))
    + C (1 - t) • (Dmz t 0 m * E3m ℚ m * LL * HH * MM), ?_, ?_⟩
  · refine DvdM.add ?_ ((((((E3m_dvd (K := ℚ)).mul_left _).mul_right _).mul_right _).mul_right
      _).smul _)
    refine (DvdM.sub' (DvdM_vecMulVec _ ?_) (DvdM_vecMulVec _ ?_)).smul _
    · exact ((((he6.add he5).mulVec _).smul _).mulVec _).mulVec _
    · exact (((he5.mulVec _).smul _).mulVec _).mulVec _
  · rw [smul_sub, e1, e2, e3, Xm_Hm_mulVec, Xm_Hm_mulVec, hXtN, hXtN, Matrix.mulVec_add, h5, h6,
      Dmz_zero_Hm_mulVec, Dmz_zero_Hm_mulVec, hDN, hDN]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hND]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hHLA, hHL,
      dotProduct_add, add_dotProduct]
    simp only [Matrix.vecMulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_sub,
      Matrix.sub_vecMulVec, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_sub, smul_add, hn1]
    module

/-- **The C2 commutator.**  `[D₀ Xᵀ, C₁]` equals, up to `X ^ m`, the rank-four matrix
`r(1−r²)⟨Λv,v⟩ v ⊗ Mv + r² v ⊗ M(A−1)c + r² Av ⊗ Mc − c ⊗ MAv − (A+1)c ⊗ Mv`.  (For `t ≠ 1`
this is `Y_comm_Czz_scaled` divided by `1 − t`; for `t = 1` both sides vanish since `M = 0`.) -/
lemma Y_comm_Czz : ∃ err : Matrix (Fin m) (Fin m) ℚ⟦X⟧, DvdM m err ∧
    Dmz t 0 m * XXᵀ * Czz t m - Czz t m * (Dmz t 0 m * XXᵀ)
      = (rr * uu * ((LL *ᵥ vv) ⬝ᵥ vv)) • vecMulVec vv (MM *ᵥ vv)
        + (rr ^ 2) • vecMulVec vv (MM *ᵥ (AA *ᵥ cc - cc))
        + (rr ^ 2) • vecMulVec (AA *ᵥ vv) (MM *ᵥ cc)
        - vecMulVec cc (MM *ᵥ (AA *ᵥ vv))
        - vecMulVec (AA *ᵥ cc + cc) (MM *ᵥ vv) + err := by
  by_cases ht : t = 1
  · subst ht
    have hM : Mum 1 m = 0 := by
      refine Matrix.ext fun a b => ?_
      simp [Mum, muW, Matrix.diagonal_apply]
    refine ⟨0, fun _ _ => dvd_zero _, ?_⟩
    simp [Czz, hM]
  · obtain ⟨err, herr, h⟩ := Y_comm_Czz_scaled (t := t) (m := m)
    have hu : (C (1 - t) : ℚ⟦X⟧) * C (1 - t)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm ht)), map_one]
    refine ⟨C (1 - t)⁻¹ • err, herr.smul _, ?_⟩
    have := congrArg (fun M => C (1 - t)⁻¹ • M) h
    simp only [smul_add, smul_smul, mul_comm (C (1 - t)⁻¹), hu, one_smul] at this
    rw [this]

/-! ### C: the three recurrences (up to `X ^ m`) -/

/-- **C1 = (RXp).**
`r X p = A² p − ω r (1−r²) P · A q − ω r (σ + r² P) · q + ω r (r(1−r²) P P̂ − Q) · p`. -/
theorem RXp_trunc : ∃ err : Fin m → ℚ⟦X⟧, DvdV m err ∧
    rr • (XX *ᵥ pp) = AA *ᵥ (AA *ᵥ pp)
      - (ww * rr * uu * PP) • (AA *ᵥ qq)
      - (ww * rr * (ss + rr ^ 2 * PP)) • qq
      + (ww * rr * (rr * uu * PP * PPh - QQ)) • pp + err := by
  obtain ⟨E5, hE5, hA5⟩ := Xm_comm_Czz (t := t) (m := m)
  have hcomm : XX * GG - GG * XX
      = -(ww • (GG * (XX * Czz t m - Czz t m * XX) * GG)) := by
    have h : XX * GG - GG * XX = GG * (Bzz t w m * XX - XX * Bzz t w m) * GG := comm_Gg XX
    have hB : Bzz t w m * XX - XX * Bzz t w m = -(ww • (XX * Czz t m - Czz t m * XX)) := by
      simp only [Bzz, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      abel
    rw [h, hB, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  set K := XX * Czz t m - Czz t m * XX with hK
  have hp : GG *ᵥ vv = pp := rfl
  have hXp : XX *ᵥ pp = GG *ᵥ (XX *ᵥ vv) - ww • (GG *ᵥ (K *ᵥ pp)) := by
    have e := congrArg (· *ᵥ vv) hcomm
    simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hp] at e
    linear_combination (norm := module) e
  have hS2 : rr • (GG *ᵥ (XX *ᵥ vv)) = GG *ᵥ (AA *ᵥ (AA *ᵥ vv)) := by
    rw [← Matrix.mulVec_smul, ← vm_H5b]
  have s1 : (MM *ᵥ cc) ⬝ᵥ pp = QQ :=
    calc (MM *ᵥ cc) ⬝ᵥ pp = cc ⬝ᵥ (MM *ᵥ pp) := (dot_Dg_symm (l := muW t) _ _).symm
      _ = (MM *ᵥ pp) ⬝ᵥ cc := dotProduct_comm _ _
      _ = QQ := dot_Dp_cg
  have s2 : (AA *ᵥ (MM *ᵥ cc) + MM *ᵥ cc) ⬝ᵥ pp
      = rr * PP * ((LL *ᵥ vv) ⬝ᵥ vv) - QQh1 := dot_ADc_pg
  have s4 : (AA *ᵥ (MM *ᵥ vv)) ⬝ᵥ pp = PP1 := by
    rw [show AA *ᵥ (MM *ᵥ vv) = MM *ᵥ (AA *ᵥ vv) from (Dg_Am_mulVec _).symm]; rfl
  have s3 : (MM *ᵥ vv) ⬝ᵥ pp = PP := rfl
  have hKp : K *ᵥ pp = QQ • (AA *ᵥ vv) + (rr * PP * ((LL *ᵥ vv) ⬝ᵥ vv) - QQh1) • vv
      - (rr ^ 2 * PP) • (AA *ᵥ cc - cc) - (rr ^ 2 * PP1) • cc
      - (rr * uu * ((LL *ᵥ vv) ⬝ᵥ vv) * PP) • vv + E5 *ᵥ pp := by
    rw [hA5]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec']
    rw [s1, s2, s3, s4]
    module
  have hGc : GG *ᵥ cc = qq := Gg_mulVec_cg
  have hGAv := Gzz_mulVec_Am_vm (t := t) (w := w) (m := m)
  have hGAc : GG *ᵥ (AA *ᵥ cc) = AA *ᵥ qq + (rr * ((LL *ᵥ vv) ⬝ᵥ vv - PPh)) • pp
      - (ww * rr * QQ) • qq := Gg_Am_cg
  have hGA2 : GG *ᵥ (AA *ᵥ (AA *ᵥ vv)) = AA *ᵥ (AA *ᵥ pp)
      + (ww * rr * QQ) • (AA *ᵥ pp) - (ww * rr * PP) • (AA *ᵥ qq)
      + (ww * rr * QQ1) • pp - (ww * rr * PP1) • qq := Gg_Am_Am_vm
  have hB9 := first_integral_R2 (t := t) (w := w) (m := m)
  have hGK : GG *ᵥ (K *ᵥ pp) = QQ • (GG *ᵥ (AA *ᵥ vv))
      + (rr * PP * ((LL *ᵥ vv) ⬝ᵥ vv) - QQh1) • pp
      - (rr ^ 2 * PP) • (GG *ᵥ (AA *ᵥ cc) - qq) - (rr ^ 2 * PP1) • qq
      - (rr * uu * ((LL *ᵥ vv) ⬝ᵥ vv) * PP) • pp + GG *ᵥ (E5 *ᵥ pp) := by
    rw [hKp]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hGc, hp]
  refine ⟨-(ww * rr) • (GG *ᵥ (E5 *ᵥ pp)), ((hE5.mulVec pp).mulVec GG).smul _, ?_⟩
  rw [hXp, smul_sub, hS2, hGA2, hGK, hGAv, hGAc]
  unfold sigzz
  linear_combination (norm := module) hB9 • ((ww * rr) • pp)

/-- **C2 = (RZp).**
`D₀ Xᵀ p = r A² p + ω (1−r²) P · A q + ω (σ + P) · q + (ω r² Q − r t − ω r (1−r²) P P̂) · p`. -/
theorem RZp_trunc : ∃ err : Fin m → ℚ⟦X⟧, DvdV m err ∧
    Dmz t 0 m *ᵥ (XXᵀ *ᵥ pp) = rr • (AA *ᵥ (AA *ᵥ pp))
      + (ww * uu * PP) • (AA *ᵥ qq)
      + (ww * (ss + PP)) • qq
      + (ww * rr ^ 2 * QQ - tt * rr - ww * rr * uu * PP * PPh) • pp + err := by
  obtain ⟨E5, hE5, hC⟩ := Y_comm_Czz (t := t) (m := m)
  have hcomm : Dmz t 0 m * XXᵀ * GG - GG * (Dmz t 0 m * XXᵀ)
      = -(ww • (GG * (Dmz t 0 m * XXᵀ * Czz t m - Czz t m * (Dmz t 0 m * XXᵀ)) * GG)) := by
    have h : Dmz t 0 m * XXᵀ * GG - GG * (Dmz t 0 m * XXᵀ)
        = GG * (Bzz t w m * (Dmz t 0 m * XXᵀ) - (Dmz t 0 m * XXᵀ) * Bzz t w m) * GG :=
      comm_Gg _
    have hB : Bzz t w m * (Dmz t 0 m * XXᵀ) - (Dmz t 0 m * XXᵀ) * Bzz t w m
        = -(ww • (Dmz t 0 m * XXᵀ * Czz t m - Czz t m * (Dmz t 0 m * XXᵀ))) := by
      simp only [Bzz, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      abel
    rw [h, hB, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  set K := Dmz t 0 m * XXᵀ * Czz t m - Czz t m * (Dmz t 0 m * XXᵀ) with hK
  have hp : GG *ᵥ vv = pp := rfl
  have hYp : Dmz t 0 m *ᵥ (XXᵀ *ᵥ pp)
      = GG *ᵥ (Dmz t 0 m *ᵥ (XXᵀ *ᵥ vv)) - ww • (GG *ᵥ (K *ᵥ pp)) := by
    have e := congrArg (· *ᵥ vv) hcomm
    simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hp] at e
    linear_combination (norm := module) e
  obtain ⟨e5, he5, h5⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ vv = rr • vv + e := ⟨_, vm_H5a, by abel⟩
  have hD0v : Dmz t 0 m *ᵥ vv = AA *ᵥ (AA *ᵥ vv) - C t • vv := by
    funext a
    simp only [Dmz_eq, Dg, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, Am_mulVec,
      smul_eq_mul, map_sub, map_pow, map_add, map_natCast, map_intCast]
    push_cast; ring
  have hYv : Dmz t 0 m *ᵥ (XXᵀ *ᵥ vv) = rr • (AA *ᵥ (AA *ᵥ vv)) - (C t * rr) • vv
      + Dmz t 0 m *ᵥ e5 := by
    rw [h5, Matrix.mulVec_add, Matrix.mulVec_smul, hD0v]
    module
  have s1 : (MM *ᵥ cc) ⬝ᵥ pp = QQ :=
    calc (MM *ᵥ cc) ⬝ᵥ pp = cc ⬝ᵥ (MM *ᵥ pp) := (dot_Dg_symm (l := muW t) _ _).symm
      _ = (MM *ᵥ pp) ⬝ᵥ cc := dotProduct_comm _ _
      _ = QQ := dot_Dp_cg
  have s2 : (AA *ᵥ (MM *ᵥ cc) + MM *ᵥ cc) ⬝ᵥ pp
      = rr * PP * ((LL *ᵥ vv) ⬝ᵥ vv) - QQh1 := dot_ADc_pg
  have s2' : (MM *ᵥ (AA *ᵥ cc)) ⬝ᵥ pp = rr * PP * ((LL *ᵥ vv) ⬝ᵥ vv) - QQh1 - QQ := by
    rw [show MM *ᵥ (AA *ᵥ cc) = AA *ᵥ (MM *ᵥ cc) from Dg_Am_mulVec _, ← s1, ← s2,
      add_dotProduct]
    ring
  have s3 : (MM *ᵥ vv) ⬝ᵥ pp = PP := rfl
  have s4 : (MM *ᵥ (AA *ᵥ vv)) ⬝ᵥ pp = PP1 := rfl
  have hKp : K *ᵥ pp = (rr * uu * ((LL *ᵥ vv) ⬝ᵥ vv) * PP) • vv
      + (rr ^ 2 * (rr * PP * ((LL *ᵥ vv) ⬝ᵥ vv) - QQh1 - 2 * QQ)) • vv
      + (rr ^ 2 * QQ) • (AA *ᵥ vv) - PP1 • cc - PP • (AA *ᵥ cc + cc) + E5 *ᵥ pp := by
    rw [hC]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec',
      Matrix.mulVec_sub, sub_dotProduct]
    rw [s1, s2', s3, s4]
    module
  have hGc : GG *ᵥ cc = qq := Gg_mulVec_cg
  have hGAv := Gzz_mulVec_Am_vm (t := t) (w := w) (m := m)
  have hGAc : GG *ᵥ (AA *ᵥ cc) = AA *ᵥ qq + (rr * ((LL *ᵥ vv) ⬝ᵥ vv - PPh)) • pp
      - (ww * rr * QQ) • qq := Gg_Am_cg
  have hGA2 : GG *ᵥ (AA *ᵥ (AA *ᵥ vv)) = AA *ᵥ (AA *ᵥ pp)
      + (ww * rr * QQ) • (AA *ᵥ pp) - (ww * rr * PP) • (AA *ᵥ qq)
      + (ww * rr * QQ1) • pp - (ww * rr * PP1) • qq := Gg_Am_Am_vm
  have hB9 := first_integral_R2 (t := t) (w := w) (m := m)
  have hGK : GG *ᵥ (K *ᵥ pp) = (rr * uu * ((LL *ᵥ vv) ⬝ᵥ vv) * PP) • pp
      + (rr ^ 2 * (rr * PP * ((LL *ᵥ vv) ⬝ᵥ vv) - QQh1 - 2 * QQ)) • pp
      + (rr ^ 2 * QQ) • (GG *ᵥ (AA *ᵥ vv)) - PP1 • qq
      - PP • (GG *ᵥ (AA *ᵥ cc) + qq) + GG *ᵥ (E5 *ᵥ pp) := by
    rw [hKp]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hGc, hp]
  refine ⟨GG *ᵥ (Dmz t 0 m *ᵥ e5) - ww • (GG *ᵥ (E5 *ᵥ pp)),
    ((he5.mulVec _).mulVec _).sub (((hE5.mulVec _).mulVec _).smul _), ?_⟩
  rw [hYp, hYv]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hp]
  rw [hGA2, hGK, hGAc, hGAv]
  unfold sigzz
  linear_combination (norm := module) hB9 • ((ww * rr ^ 2) • pp)

/-- **C3 = (RZp̂).**
`D₂ Xᵀ p̂ = r A² p̂ + 4 r A p̂ + ω (1−r²) P̂ · A q̂
   + ω((1 − 4r²) P̂ + (1−r²) P̂₁ − ω r (1−r²) P̂ Q) · q̂
   + ((4−t) r + ω r² Q − ω r (1−r²) P P̂) · p̂`. -/
theorem RZph_trunc : ∃ err : Fin m → ℚ⟦X⟧, DvdV m err ∧
    Dmz t 2 m *ᵥ (XXᵀ *ᵥ pph) = rr • (AA *ᵥ (AA *ᵥ pph))
      + (4 * rr) • (AA *ᵥ pph)
      + (ww * uu * PPh) • (AA *ᵥ qqh)
      + (ww * ((1 - 4 * rr ^ 2) * PPh + uu * PPh1 - ww * rr * uu * PPh * QQ)) • qqh
      + ((C (4 - t)) * rr + ww * rr ^ 2 * QQ - ww * rr * uu * PP * PPh) • pph + err := by
  obtain ⟨E5, hE5, hC⟩ := Yh_comm_Chzz (t := t) (m := m)
  have hcomm : Dmz t 2 m * XXᵀ * GGh - GGh * (Dmz t 2 m * XXᵀ)
      = -(ww • (GGh * (Dmz t 2 m * XXᵀ * Chzz t m - Chzz t m * (Dmz t 2 m * XXᵀ)) * GGh)) := by
    have h : Dmz t 2 m * XXᵀ * GGh - GGh * (Dmz t 2 m * XXᵀ)
        = GGh * (Bhzz t w m * (Dmz t 2 m * XXᵀ) - (Dmz t 2 m * XXᵀ) * Bhzz t w m) * GGh :=
      comm_Gg _
    have hB : Bhzz t w m * (Dmz t 2 m * XXᵀ) - (Dmz t 2 m * XXᵀ) * Bhzz t w m
        = -(ww • (Dmz t 2 m * XXᵀ * Chzz t m - Chzz t m * (Dmz t 2 m * XXᵀ))) := by
      simp only [Bhzz, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      abel
    rw [h, hB, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  set K := Dmz t 2 m * XXᵀ * Chzz t m - Chzz t m * (Dmz t 2 m * XXᵀ) with hK
  have hp : GGh *ᵥ vv = pph := rfl
  have hYp : Dmz t 2 m *ᵥ (XXᵀ *ᵥ pph)
      = GGh *ᵥ (Dmz t 2 m *ᵥ (XXᵀ *ᵥ vv)) - ww • (GGh *ᵥ (K *ᵥ pph)) := by
    have e := congrArg (· *ᵥ vv) hcomm
    simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hp] at e
    linear_combination (norm := module) e
  obtain ⟨e5, he5, h5⟩ : ∃ e, DvdV m e ∧ XXᵀ *ᵥ vv = rr • vv + e := ⟨_, vm_H5a, by abel⟩
  have hD2v : Dmz t 2 m *ᵥ vv
      = AA *ᵥ (AA *ᵥ vv) + (4 : ℚ⟦X⟧) • (AA *ᵥ vv) + C (4 - t) • vv := by
    funext a
    simp only [Dmz_eq, Dg, Matrix.mulVec_diagonal, Pi.add_apply, Pi.smul_apply, Am_mulVec,
      smul_eq_mul, map_sub, map_pow, map_add, map_natCast, map_intCast, map_ofNat]
    push_cast; ring
  have hYv : Dmz t 2 m *ᵥ (XXᵀ *ᵥ vv) = rr • (AA *ᵥ (AA *ᵥ vv)) + (4 * rr) • (AA *ᵥ vv)
      + (C (4 - t) * rr) • vv + Dmz t 2 m *ᵥ e5 := by
    rw [h5, Matrix.mulVec_add, Matrix.mulVec_smul, hD2v]
    module
  set ch := (HH * MM) *ᵥ vv with hch
  have hQ : QQh = QQ := Qzz_eq_Qhzz.symm
  have t1 : (LL *ᵥ ch) ⬝ᵥ pph = QQ :=
    calc (LL *ᵥ ch) ⬝ᵥ pph = ch ⬝ᵥ (LL *ᵥ pph) := (dot_Dg_symm (l := lamW t) _ _).symm
      _ = (LL *ᵥ pph) ⬝ᵥ ch := dotProduct_comm _ _
      _ = QQh := dot_Dp_cg
      _ = QQ := hQ
  have t2 : (AA *ᵥ (LL *ᵥ ch) + LL *ᵥ ch) ⬝ᵥ pph
      = rr * PPh * ((MM *ᵥ vv) ⬝ᵥ vv) - QQ1 := dot_ADc_pg
  have t2' : (LL *ᵥ (AA *ᵥ ch)) ⬝ᵥ pph = rr * PPh * ((MM *ᵥ vv) ⬝ᵥ vv) - QQ1 - QQ := by
    rw [show LL *ᵥ (AA *ᵥ ch) = AA *ᵥ (LL *ᵥ ch) from Dg_Am_mulVec _, ← t1, ← t2,
      add_dotProduct]
    ring
  have t3 : (LL *ᵥ vv) ⬝ᵥ pph = PPh := rfl
  have t4 : (LL *ᵥ (AA *ᵥ vv)) ⬝ᵥ pph = PPh1 := rfl
  have hKp : K *ᵥ pph = (rr * uu * ((MM *ᵥ vv) ⬝ᵥ vv) * PPh) • vv
      + (rr ^ 2 * (rr * PPh * ((MM *ᵥ vv) ⬝ᵥ vv) - QQ1 + 2 * QQ)) • vv
      + (rr ^ 2 * QQ) • (AA *ᵥ vv) - PPh1 • ch - PPh • (AA *ᵥ ch + ch) + E5 *ᵥ pph := by
    rw [hC]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec',
      Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, smul_dotProduct]
    rw [t1, t2', t3, t4]
    simp only [smul_eq_mul]
    module
  have hGc : GGh *ᵥ ch = qqh := Gg_mulVec_cg
  have hGAv : GGh *ᵥ (AA *ᵥ vv) = AA *ᵥ pph + (ww * rr * QQh) • pph - (ww * rr * PPh) • qqh :=
    Gg_mulVec_Am_vm
  have hGAc : GGh *ᵥ (AA *ᵥ ch) = AA *ᵥ qqh + (rr * ((MM *ᵥ vv) ⬝ᵥ vv - PP)) • pph
      - (ww * rr * QQh) • qqh := Gg_Am_cg
  have hGA2 : GGh *ᵥ (AA *ᵥ (AA *ᵥ vv)) = AA *ᵥ (AA *ᵥ pph)
      + (ww * rr * QQh) • (AA *ᵥ pph) - (ww * rr * PPh) • (AA *ᵥ qqh)
      + (ww * rr * QQh1) • pph - (ww * rr * PPh1) • qqh := Gg_Am_Am_vm
  have hB9 := first_integral_R2 (t := t) (w := w) (m := m)
  have hGK : GGh *ᵥ (K *ᵥ pph) = (rr * uu * ((MM *ᵥ vv) ⬝ᵥ vv) * PPh) • pph
      + (rr ^ 2 * (rr * PPh * ((MM *ᵥ vv) ⬝ᵥ vv) - QQ1 + 2 * QQ)) • pph
      + (rr ^ 2 * QQ) • (GGh *ᵥ (AA *ᵥ vv)) - PPh1 • qqh
      - PPh • (GGh *ᵥ (AA *ᵥ ch) + qqh) + GGh *ᵥ (E5 *ᵥ pph) := by
    rw [hKp]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hGc, hp]
  refine ⟨GGh *ᵥ (Dmz t 2 m *ᵥ e5) - ww • (GGh *ᵥ (E5 *ᵥ pph)),
    ((he5.mulVec _).mulVec _).sub (((hE5.mulVec _).mulVec _).smul _), ?_⟩
  rw [hYp, hYv]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hp]
  rw [hGA2, hGAv, hGK, hGAc, hGAv, hQ]
  linear_combination (norm := module) hB9 • ((ww * rr ^ 2) • pph)

/- **C4, as stated in the skeleton — FALSE for the truncations.**  The exact equality below does
not hold for the `m × m` truncations: pairing C2 with `Mv` gives it only up to `r ⟨Mv, err⟩`,
where `err` is the boundary defect of C2, and that defect does not vanish.  The simplest witness is
`m = 1`, `ω = 0`, `t = 2`: then `p = v`, `A = 0`, so the left side is `0`, while the right side is
`−r² t P = −r² · 2 · (1 − 2) = 2 r²` (formally: `P2_of_RZp_false` below).  For general `m` the
defect first appears at `r^(2m)`.  The corrected statement, with an error divisible by `X ^ m` as for
C1–C3, is `P2_of_RZp_trunc`.

theorem P2_of_RZp :
    (1 - X ^ 2) * ((Mum t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pp)
      = ww * rr * uu * (PP * QQ1 + PP1 * QQ - ww * rr * PP * QQ ^ 2)
        + ww * rr * (1 + rr ^ 2) * PP * QQ - rr ^ 2 * tt * PP
        - ww * rr ^ 2 * uu * PP ^ 2 * PPh := by
  sorry
-/

/-- **C4 (corrected: up to `X ^ m`).**  Pairing C2 with `Mv`:
`(1 − r²) P₂ = ω r (1−r²)(P Q₁ + P₁ Q − ω r P Q²) + ω r (1 + r²) P Q − r² t P − ω r² (1−r²) P² P̂`
up to an error divisible by `X ^ m`, where `P₂ = ⟨M A² v, p⟩`.  The skeleton stated this as an exact
equality, which is false for the truncations (see `P2_of_RZp_false`). -/
theorem P2_of_RZp_trunc : ∃ e : ℚ⟦X⟧, (X : ℚ⟦X⟧) ^ m ∣ e ∧
    (1 - X ^ 2) * ((Mum t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pp)
      = ww * rr * uu * (PP * QQ1 + PP1 * QQ - ww * rr * PP * QQ ^ 2)
        + ww * rr * (1 + rr ^ 2) * PP * QQ - rr ^ 2 * tt * PP
        - ww * rr ^ 2 * uu * PP ^ 2 * PPh + e := by
  obtain ⟨err, herr, h⟩ := RZp_trunc (t := t) (w := w) (m := m)
  have hMt : (Mum t m)ᵀ = Mum t m := Dg_transpose
  have hDt : (Dmz t 0 m)ᵀ = Dmz t 0 m := by rw [Dmz_eq]; exact Dg_transpose
  have hXDM : XX * (Dmz t 0 m * MM) = MM * XX := by
    have e := congrArg Matrix.transpose (XT_mul_Mum (t := t) (m := m))
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hMt, hDt] at e
    exact e.symm
  have hMA : ∀ u, MM *ᵥ (AA *ᵥ u) = AA *ᵥ (MM *ᵥ u) := fun u => Dg_Am_mulVec u
  have k1 : (MM *ᵥ vv) ⬝ᵥ (Dmz t 0 m *ᵥ (XXᵀ *ᵥ pp)) = (MM *ᵥ (XX *ᵥ vv)) ⬝ᵥ pp := by
    calc (MM *ᵥ vv) ⬝ᵥ (Dmz t 0 m *ᵥ (XXᵀ *ᵥ pp))
        = (Dmz t 0 m *ᵥ (MM *ᵥ vv)) ⬝ᵥ (XXᵀ *ᵥ pp) := by
          rw [dot_mulVec_transpose, hDt]
      _ = (XX *ᵥ (Dmz t 0 m *ᵥ (MM *ᵥ vv))) ⬝ᵥ pp := by
          rw [dot_mulVec_transpose, Matrix.transpose_transpose]
      _ = (MM *ᵥ (XX *ᵥ vv)) ⬝ᵥ pp := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hXDM,
            ← Matrix.mulVec_mulVec]
  have k2 : rr * ((MM *ᵥ (XX *ᵥ vv)) ⬝ᵥ pp)
      = (Mum t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pp := by
    rw [← smul_eq_mul, ← smul_dotProduct, ← Matrix.mulVec_smul, ← vm_H5b]
  have k3 : (MM *ᵥ vv) ⬝ᵥ (AA *ᵥ (AA *ᵥ pp))
      = (Mum t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pp := by
    rw [dot_A_symm, dot_A_symm, hMA, hMA]
  have k4 : (MM *ᵥ vv) ⬝ᵥ (AA *ᵥ qq) = QQ1 := by
    rw [dot_A_symm, ← hMA]; rfl
  have k5 : (MM *ᵥ vv) ⬝ᵥ qq = QQ := rfl
  have k6 : (MM *ᵥ vv) ⬝ᵥ pp = PP := rfl
  have hpair := congrArg (fun y => (MM *ᵥ vv) ⬝ᵥ y) h
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hpair
  rw [k1, k3, k4, k5, k6] at hpair
  refine ⟨rr * ((MM *ᵥ vv) ⬝ᵥ err), dvd_mul_of_dvd_right (herr.dot _) _, ?_⟩
  unfold sigzz at hpair
  linear_combination rr * hpair - k2

/-- **The `P̂₂` analogue of C4 (optional item; up to `X ^ m`).**  Pairing C3 with `Λv`:
`(1 − r²) P̂₂ = 4 r² P̂₁ + ω r (1−r²)(P̂ Q̂₁ + P̂₁ Q − ω r P̂ Q²) + ω r (1 − 3r²) P̂ Q + (4 − t) r² P̂
 − ω r² (1−r²) P P̂²` up to an error divisible by `X ^ m`, where `P̂₂ = ⟨Λ A² v, p̂⟩`. -/
theorem Ph2_of_RZph_trunc : ∃ e : ℚ⟦X⟧, (X : ℚ⟦X⟧) ^ m ∣ e ∧
    (1 - X ^ 2) * ((Lamm t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pph)
      = 4 * rr ^ 2 * PPh1 + ww * rr * uu * (PPh * QQh1 + PPh1 * QQ - ww * rr * PPh * QQ ^ 2)
        + ww * rr * (1 - 3 * rr ^ 2) * PPh * QQ + C (4 - t) * rr ^ 2 * PPh
        - ww * rr ^ 2 * uu * PP * PPh ^ 2 + e := by
  obtain ⟨err, herr, h⟩ := RZph_trunc (t := t) (w := w) (m := m)
  have hLt : (Lamm t m)ᵀ = Lamm t m := Dg_transpose
  have hDt : (Dmz t 2 m)ᵀ = Dmz t 2 m := by rw [Dmz_eq]; exact Dg_transpose
  have hXDL : XX * (Dmz t 2 m * LL) = LL * XX := by
    have e := congrArg Matrix.transpose (XT_mul_Lamm (t := t) (m := m))
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hLt, hDt] at e
    exact e.symm
  have hLA : ∀ u, LL *ᵥ (AA *ᵥ u) = AA *ᵥ (LL *ᵥ u) := fun u => Dg_Am_mulVec u
  have k1 : (LL *ᵥ vv) ⬝ᵥ (Dmz t 2 m *ᵥ (XXᵀ *ᵥ pph)) = (LL *ᵥ (XX *ᵥ vv)) ⬝ᵥ pph := by
    calc (LL *ᵥ vv) ⬝ᵥ (Dmz t 2 m *ᵥ (XXᵀ *ᵥ pph))
        = (Dmz t 2 m *ᵥ (LL *ᵥ vv)) ⬝ᵥ (XXᵀ *ᵥ pph) := by
          rw [dot_mulVec_transpose, hDt]
      _ = (XX *ᵥ (Dmz t 2 m *ᵥ (LL *ᵥ vv))) ⬝ᵥ pph := by
          rw [dot_mulVec_transpose, Matrix.transpose_transpose]
      _ = (LL *ᵥ (XX *ᵥ vv)) ⬝ᵥ pph := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hXDL,
            ← Matrix.mulVec_mulVec]
  have k2 : rr * ((LL *ᵥ (XX *ᵥ vv)) ⬝ᵥ pph)
      = (Lamm t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pph := by
    rw [← smul_eq_mul, ← smul_dotProduct, ← Matrix.mulVec_smul, ← vm_H5b]
  have k3 : (LL *ᵥ vv) ⬝ᵥ (AA *ᵥ (AA *ᵥ pph))
      = (Lamm t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pph := by
    rw [dot_A_symm, dot_A_symm, hLA, hLA]
  have k4 : (LL *ᵥ vv) ⬝ᵥ (AA *ᵥ qqh) = QQh1 := by
    rw [dot_A_symm, ← hLA]; rfl
  have k4' : (LL *ᵥ vv) ⬝ᵥ (AA *ᵥ pph) = PPh1 := by
    rw [dot_A_symm, ← hLA]; rfl
  have k5 : (LL *ᵥ vv) ⬝ᵥ qqh = QQ := Qzz_eq_Qhzz.symm
  have k6 : (LL *ᵥ vv) ⬝ᵥ pph = PPh := rfl
  have hpair := congrArg (fun y => (LL *ᵥ vv) ⬝ᵥ y) h
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hpair
  rw [k1, k3, k4, k4', k5, k6] at hpair
  refine ⟨rr * ((LL *ᵥ vv) ⬝ᵥ err), dvd_mul_of_dvd_right (herr.dot _) _, ?_⟩
  linear_combination rr * hpair - k2

end

/-- The skeleton's exact form of item C4 fails for the truncations: at `m = 1`, `ω = 0`, `t = 2`
the left side is `0` and the right side is `2 r²`. -/
theorem P2_of_RZp_false : ¬ ∀ (t w : ℚ) (m : ℕ),
    (1 - X ^ 2) * ((Mum t m *ᵥ (Am ℚ m *ᵥ (Am ℚ m *ᵥ vm ℚ m))) ⬝ᵥ pzz t w m)
      = C w * X * (1 - X ^ 2) * (Pzz t w m * Q1zz t w m + P1zz t w m * Qzz t w m
          - C w * X * Pzz t w m * Qzz t w m ^ 2)
        + C w * X * (1 + X ^ 2) * Pzz t w m * Qzz t w m - X ^ 2 * C t * Pzz t w m
        - C w * X ^ 2 * (1 - X ^ 2) * Pzz t w m ^ 2 * Phzz t w m := by
  intro h
  have h1 := congrArg (coeff 2) (h 2 0 1)
  have hA : Am ℚ 1 *ᵥ vm ℚ 1 = 0 := by
    funext a; fin_cases a; simp [Am_mulVec]
  have hP : Pzz 2 0 1 = -1 := by
    simp [Pzz, pzz, Gzz, Bzz, Mum, muW, vm, Matrix.mulVec_diagonal, dotProduct, vE_zero]
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    norm_num
  rw [hA, hP] at h1
  simp at h1

end AvgRS
