module

public import RequestProject.Formal.RecODE

@[expose] public section

/-!
# The resolvent layer on the line `z + z' = −2`, for general diagonal weights

The objects of `ZLineRec.lean` (`C₁ = H Λ H M`, `Ĉ₁ = H M H Λ`, their resolvents, `p`, `q`, `p̂`,
`q̂` and the scalars) are all instances of one construction with two diagonal weights `l, μ`,
exchanged when passing to the hatted objects.  This file develops the resolvent layer (items A1,
A4 and B1–B9 of batch 5, the z-line analogue of Lemmas 5.6, 5.9, 5.11: `lem:Hids`, `lem:Gids`,
`lem:odes`) once, for arbitrary weights `l, μ : ℕ → ℚ`; `ZLineRec.lean` instantiates it twice.
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

/-- `diag(l_a)`, truncated. -/
noncomputable def Dg (l : ℕ → ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Matrix.diagonal fun a => C (l a)

/-- `C(l, μ) = H diag(l) H diag(μ)`. -/
noncomputable def Cg (l μ : ℕ → ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Hm ℚ m * Dg l m * Hm ℚ m * Dg μ m

/-- `1 + ω C(l, μ)`. -/
noncomputable def Bg (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  1 + C w • Cg l μ m

/-- `(1 + ω C(l, μ))⁻¹`. -/
noncomputable def Gg (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  (Bg w l μ m)⁻¹

/-- `p(l, μ) = G(l, μ) v`. -/
noncomputable def pg (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ := Gg w l μ m *ᵥ vm ℚ m

/-- `q(l, μ) = H diag(l) p(μ, l)`. -/
noncomputable def qg (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ :=
  (Hm ℚ m * Dg l m) *ᵥ pg w μ l m

/-- `c(l) = H diag(l) v`. -/
noncomputable def cg (l : ℕ → ℚ) (m : ℕ) : Fin m → ℚ⟦X⟧ := (Hm ℚ m * Dg l m) *ᵥ vm ℚ m

noncomputable def Pg (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : ℚ⟦X⟧ := (Dg μ m *ᵥ vm ℚ m) ⬝ᵥ pg w l μ m
noncomputable def Qg (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : ℚ⟦X⟧ := (Dg μ m *ᵥ vm ℚ m) ⬝ᵥ qg w l μ m
noncomputable def P1g (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (Dg μ m *ᵥ (Am ℚ m *ᵥ vm ℚ m)) ⬝ᵥ pg w l μ m
noncomputable def Q1g (w : ℚ) (l μ : ℕ → ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (Dg μ m *ᵥ (Am ℚ m *ᵥ vm ℚ m)) ⬝ᵥ qg w l μ m

section General

variable {ι : Type*} [Fintype ι]

lemma vecMulVec_mul_eq (u w : ι → ℚ⟦X⟧) (N : Matrix ι ι ℚ⟦X⟧) :
    vecMulVec u w * N = vecMulVec u (Nᵀ *ᵥ w) := by
  rw [Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]

lemma dot_mulVec_transpose (M : Matrix ι ι ℚ⟦X⟧) (u w : ι → ℚ⟦X⟧) :
    u ⬝ᵥ (M *ᵥ w) = (Mᵀ *ᵥ u) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

end General

variable {w : ℚ} {l μ : ℕ → ℚ} {m : ℕ}

local notation "HH" => Hm ℚ m
local notation "vv" => vm ℚ m
local notation "AA" => Am ℚ m
local notation "rr" => (X : ℚ⟦X⟧)
local notation "ww" => (C w : ℚ⟦X⟧)

lemma Dg_transpose : (Dg l m)ᵀ = Dg l m := by simp [Dg]

lemma Dg_comm_Dg (l' : ℕ → ℚ) : Dg l m * Dg l' m = Dg l' m * Dg l m := by
  simp only [Dg, Matrix.diagonal_mul_diagonal]
  congr 1; funext a; ring

lemma Dg_comm_Am : Dg l m * AA = AA * Dg l m := by
  simp only [Dg, Am, Matrix.diagonal_mul_diagonal]
  congr 1; funext a; ring

lemma dM_Dg : dM (Dg l m) = 0 := by
  refine Matrix.ext fun a b => ?_
  by_cases h : a = b
  · subst h; simp [Dg]
  · simp [Dg, Matrix.diagonal_apply_ne _ h]

lemma Dg_congr {f g : ℕ → ℚ} (h : ∀ a, f a = g a) : Dg f m = Dg g m := by
  simp only [Dg, h]

lemma Dg_mul_Dg (f g : ℕ → ℚ) : Dg f m * Dg g m = Dg (fun a => f a * g a) m := by
  simp only [Dg, Matrix.diagonal_mul_diagonal, map_mul]

lemma C_smul_Dg (c : ℚ) (f : ℕ → ℚ) : C c • Dg f m = Dg (fun a => c * f a) m := by
  refine Matrix.ext fun a b => ?_
  by_cases h : a = b
  · subst h; simp [Dg]
  · simp [Dg, Matrix.diagonal_apply_ne _ h]

lemma XmT_mul_Dg (f g : ℕ → ℚ) (h : ∀ a, f (a + 1) = g a) :
    (Xm ℚ m)ᵀ * Dg f m = Dg g m * (Xm ℚ m)ᵀ := by
  refine Matrix.ext fun a b => ?_
  simp only [Dg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, Xm,
    Matrix.of_apply]
  split_ifs with hb
  · rw [hb, h]; ring
  · simp

lemma Xm_mul_Dg (f g : ℕ → ℚ) (h : ∀ b, f b = g (b + 1)) :
    Xm ℚ m * Dg f m = Dg g m * Xm ℚ m := by
  refine Matrix.ext fun a b => ?_
  simp only [Dg, Matrix.mul_diagonal, Matrix.diagonal_mul, Xm, Matrix.of_apply]
  split_ifs with ha
  · rw [ha, h]; ring
  · simp

lemma dot_Dg_symm (u u' : Fin m → ℚ⟦X⟧) : u ⬝ᵥ (Dg l m *ᵥ u') = (Dg l m *ᵥ u) ⬝ᵥ u' :=
  dotProduct_mulVec_symm Dg_transpose u u'

lemma Cg_transpose : (Cg l μ m)ᵀ = Dg μ m * HH * Dg l m * HH := by
  simp only [Cg, Matrix.transpose_mul, Dg_transpose, Hm_transpose, Matrix.mul_assoc]

lemma X_dvd_Hm_mul (N : Matrix (Fin m) (Fin m) ℚ⟦X⟧) (a b : Fin m) :
    (X : ℚ⟦X⟧) ∣ (HH * N) a b := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun c _ => dvd_mul_of_dvd_left (X_dvd_Hm a c) _

lemma isUnit_det_Bg : IsUnit (Bg w l μ m).det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff : ℚ⟦X⟧ →+* ℚ).mapMatrix (Bg w l μ m) = 1 := by
    refine Matrix.ext fun a b => ?_
    have h : constantCoeff (Cg l μ m a b) = 0 := by
      rw [← PowerSeries.X_dvd_iff, Cg, Matrix.mul_assoc, Matrix.mul_assoc]
      exact X_dvd_Hm_mul _ a b
    simp [Bg, h, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact isUnit_one

lemma Gg_mul_Bg : Gg w l μ m * Bg w l μ m = 1 := Matrix.nonsing_inv_mul _ isUnit_det_Bg

lemma Bg_mul_Gg : Bg w l μ m * Gg w l μ m = 1 := Matrix.mul_nonsing_inv _ isUnit_det_Bg

/-- If `B Y = Y B'`, then `B⁻¹ Y = Y B'⁻¹`. -/
lemma inv_intertwine {B B' Y G G' : Matrix (Fin m) (Fin m) ℚ⟦X⟧} (hG : G * B = 1)
    (hG' : B' * G' = 1) (h : B * Y = Y * B') : G * Y = Y * G' := by
  calc G * Y = G * Y * (B' * G') := by rw [hG', Matrix.mul_one]
    _ = G * (Y * B') * G' := by simp only [Matrix.mul_assoc]
    _ = G * (B * Y) * G' := by rw [h]
    _ = (G * B) * Y * G' := by simp only [Matrix.mul_assoc]
    _ = Y * G' := by rw [hG, Matrix.one_mul]

/-- **B1** (general form): `G(l,μ) H diag(l) = H diag(l) G(μ,l)`. -/
lemma Gg_mul_HD : Gg w l μ m * (HH * Dg l m) = (HH * Dg l m) * Gg w μ l m := by
  refine inv_intertwine Gg_mul_Bg Bg_mul_Gg ?_
  simp only [Bg, Cg, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

lemma Cg_comm_Gg : Cg l μ m * Gg w l μ m = Gg w l μ m * Cg l μ m := by
  refine (inv_intertwine Gg_mul_Bg Bg_mul_Gg ?_).symm
  simp only [Bg, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]

lemma Bg_transpose_mul : (Bg w l μ m)ᵀ * Dg μ m = Dg μ m * Bg w l μ m := by
  simp only [Bg, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_mul, Dg_transpose, Hm_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, Cg, Matrix.mul_assoc]

/-- `G(l,μ)ᵀ diag(μ) = diag(μ) G(l,μ)`: `C(l,μ)` is self-adjoint for `⟨diag(μ)·, ·⟩`. -/
lemma Gg_transpose_mul : (Gg w l μ m)ᵀ * Dg μ m = Dg μ m * Gg w l μ m := by
  have h1 : (Gg w l μ m)ᵀ * (Bg w l μ m)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Bg_mul_Gg, Matrix.transpose_one]
  calc (Gg w l μ m)ᵀ * Dg μ m = (Gg w l μ m)ᵀ * Dg μ m * (Bg w l μ m * Gg w l μ m) := by
        rw [Bg_mul_Gg, Matrix.mul_one]
    _ = (Gg w l μ m)ᵀ * ((Bg w l μ m)ᵀ * Dg μ m) * Gg w l μ m := by
        rw [Bg_transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Dg μ m * Gg w l μ m := by
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

lemma Gg_mulVec_cg : Gg w l μ m *ᵥ cg l m = qg w l μ m := by
  rw [cg, qg, pg, Matrix.mulVec_mulVec, Gg_mul_HD, ← Matrix.mulVec_mulVec]

/-- `ω C(l,μ) p(l,μ) = v − p(l,μ)`. -/
lemma C_smul_Cg_pg : ww • (Cg l μ m *ᵥ pg w l μ m) = vv - pg w l μ m := by
  have h := Bg_mul_Gg (w := w) (l := l) (μ := μ) (m := m)
  rw [Bg, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
  have : ww • (Cg l μ m * Gg w l μ m) = 1 - Gg w l μ m := by rw [← h]; abel
  rw [pg, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, this, Matrix.sub_mulVec,
    Matrix.one_mulVec]

/-- **B2** (general form): `ω H diag(μ) q(l,μ) = v − p(μ,l)`. -/
lemma C_smul_HD_qg : ww • ((HH * Dg μ m) *ᵥ qg w l μ m) = vv - pg w μ l m := by
  rw [qg, Matrix.mulVec_mulVec, ← C_smul_Cg_pg, Cg]
  simp only [Matrix.mul_assoc]

/-- **B3** (general form): `Q(l,μ) = Q(μ,l)`. -/
lemma Qg_symm : Qg w l μ m = Qg w μ l m := by
  have e1 : Qg w μ l m = (Dg l m *ᵥ vv) ⬝ᵥ (Gg w μ l m *ᵥ ((HH * Dg μ m) *ᵥ vv)) := by
    rw [Qg, qg, pg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Gg_mul_HD]
  rw [e1, dot_mulVec_transpose, Matrix.mulVec_mulVec, Gg_transpose_mul, ← Matrix.mulVec_mulVec,
    ← pg, Qg, qg]
  have k1 : (Dg μ m *ᵥ vv) ⬝ᵥ ((HH * Dg l m) *ᵥ pg w μ l m)
      = vv ⬝ᵥ ((Dg μ m * HH * Dg l m) *ᵥ pg w μ l m) := by
    rw [← dot_Dg_symm, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have k2 : (Dg l m *ᵥ pg w μ l m) ⬝ᵥ ((HH * Dg μ m) *ᵥ vv)
      = vv ⬝ᵥ ((Dg μ m * HH * Dg l m) *ᵥ pg w μ l m) := by
    rw [dot_mulVec_transpose, dotProduct_comm, Matrix.transpose_mul, Hm_transpose, Dg_transpose,
      Matrix.mulVec_mulVec]
  rw [k1, k2]

/-- **A1** (general form): `(H diag l) A + (A + 1)(H diag l) = r v ⊗ diag(l) v`. -/
lemma HD_H2 : (HH * Dg l m) * AA + (AA + 1) * (HH * Dg l m)
    = rr • vecMulVec vv (Dg l m *ᵥ vv) := by
  have h2 := Hm_H2 (K := ℚ) (m := m)
  calc (HH * Dg l m) * AA + (AA + 1) * (HH * Dg l m)
      = (HH * AA + (AA + 1) * HH) * Dg l m := by
        simp only [Matrix.add_mul, Matrix.mul_assoc, Dg_comm_Am]
    _ = _ := by rw [h2, Matrix.smul_mul, vecMulVec_mul_eq, Dg_transpose]

/-- `(H diag l) A = r v ⊗ diag(l) v − (A + 1)(H diag l)`. -/
lemma HD_mul_Am : (HH * Dg l m) * AA
    = rr • vecMulVec vv (Dg l m *ᵥ vv) - (AA + 1) * (HH * Dg l m) := by
  rw [← HD_H2]; abel

lemma Am_mul_Hm : AA * HH = rr • vecMulVec vv vv - HH * AA - HH := by
  rw [← Hm_H2 (K := ℚ), Matrix.add_mul, Matrix.one_mul]; abel

/-- **A4** (general form): `[A, C(l,μ)] = r (v ⊗ diag(μ) c(l) − c(l) ⊗ diag(μ) v)`. -/
lemma Am_comm_Cg : AA * Cg l μ m - Cg l μ m * AA
    = rr • (vecMulVec vv (Dg μ m *ᵥ cg l m) - vecMulVec (cg l m) (Dg μ m *ᵥ vv)) := by
  have hμ : Dg μ m * AA = AA * Dg μ m := Dg_comm_Am
  have hl : Dg l m * AA = AA * Dg l m := Dg_comm_Am
  have hAH := Am_mul_Hm (m := m)
  have hHA : HH * AA = rr • vecMulVec vv vv - AA * HH - HH := by
    rw [← Hm_H2 (K := ℚ), Matrix.add_mul, Matrix.one_mul]; abel
  have e1 : vecMulVec vv vv * (Dg l m * (HH * Dg μ m)) = vecMulVec vv (Dg μ m *ᵥ cg l m) := by
    rw [vecMulVec_mul_eq, cg]
    congr 1
    simp only [Matrix.transpose_mul, Dg_transpose, Hm_transpose, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have e2 : HH * (Dg l m * (vecMulVec vv vv * Dg μ m)) = vecMulVec (cg l m) (Dg μ m *ᵥ vv) := by
    rw [vecMulVec_mul_eq, Dg_transpose, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, cg,
      Matrix.mulVec_mulVec]
  have e3 : AA * (Dg l m * (HH * Dg μ m)) = Dg l m * (AA * (HH * Dg μ m)) := by
    rw [← Matrix.mul_assoc, ← hl, Matrix.mul_assoc]
  calc AA * Cg l μ m - Cg l μ m * AA
      = (AA * HH) * (Dg l m * (HH * Dg μ m)) - HH * (Dg l m * ((HH * AA) * Dg μ m)) := by
        simp only [Cg, Matrix.mul_assoc, hμ]
    _ = (rr • vecMulVec vv vv - HH * AA - HH) * (Dg l m * (HH * Dg μ m))
        - HH * (Dg l m * ((rr • vecMulVec vv vv - AA * HH - HH) * Dg μ m)) := by
        rw [← hAH, ← hHA]
    _ = rr • (vecMulVec vv vv * (Dg l m * (HH * Dg μ m)))
        - HH * (AA * (Dg l m * (HH * Dg μ m))) - HH * (Dg l m * (HH * Dg μ m))
        - rr • (HH * (Dg l m * (vecMulVec vv vv * Dg μ m)))
        + HH * (Dg l m * (AA * (HH * Dg μ m))) + HH * (Dg l m * (HH * Dg μ m)) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_assoc]
        abel
    _ = _ := by
        rw [e1, e2, e3, smul_sub]
        abel

/-- `[M, G] = G [B, M] G`. -/
lemma comm_Gg (M : Matrix (Fin m) (Fin m) ℚ⟦X⟧) :
    M * Gg w l μ m - Gg w l μ m * M
      = Gg w l μ m * (Bg w l μ m * M - M * Bg w l μ m) * Gg w l μ m := by
  rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Gg_mul_Bg, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, Bg_mul_Gg, Matrix.mul_one]

/-- `G (f ⊗ diag(μ) g) G = (G f) ⊗ diag(μ) (G g)`. -/
lemma Gg_vecMulVec_D_Gg (f g : Fin m → ℚ⟦X⟧) :
    Gg w l μ m * vecMulVec f (Dg μ m *ᵥ g) * Gg w l μ m
      = vecMulVec (Gg w l μ m *ᵥ f) (Dg μ m *ᵥ (Gg w l μ m *ᵥ g)) := by
  rw [Matrix.mul_vecMulVec, vecMulVec_mul_eq, Matrix.mulVec_mulVec, Gg_transpose_mul,
    ← Matrix.mulVec_mulVec]

lemma Gg_mulVec_vm : Gg w l μ m *ᵥ vv = pg w l μ m := rfl

/-- `[A, G] = −ω r (p ⊗ diag(μ) q − q ⊗ diag(μ) p)`. -/
lemma Am_comm_Gg : AA * Gg w l μ m - Gg w l μ m * AA
    = -((ww * rr) • (vecMulVec (pg w l μ m) (Dg μ m *ᵥ qg w l μ m)
        - vecMulVec (qg w l μ m) (Dg μ m *ᵥ pg w l μ m))) := by
  rw [comm_Gg]
  have : Bg w l μ m * AA - AA * Bg w l μ m = -(ww • (AA * Cg l μ m - Cg l μ m * AA)) := by
    simp only [Bg, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  rw [this, Am_comm_Cg, smul_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Gg_vecMulVec_D_Gg, Gg_vecMulVec_D_Gg,
    Gg_mulVec_cg, Gg_mulVec_vm]

/-- `G A u = A G u + ω r (⟨diag(μ) q, u⟩ p − ⟨diag(μ) p, u⟩ q)`. -/
lemma Gg_Am_mulVec (u : Fin m → ℚ⟦X⟧) : Gg w l μ m *ᵥ (AA *ᵥ u)
    = AA *ᵥ (Gg w l μ m *ᵥ u) + (ww * rr) • (((Dg μ m *ᵥ qg w l μ m) ⬝ᵥ u) • pg w l μ m
        - ((Dg μ m *ᵥ pg w l μ m) ⬝ᵥ u) • qg w l μ m) := by
  have h : Gg w l μ m * AA = AA * Gg w l μ m + (ww * rr) • (vecMulVec (pg w l μ m)
      (Dg μ m *ᵥ qg w l μ m) - vecMulVec (qg w l μ m) (Dg μ m *ᵥ pg w l μ m)) := by
    rw [← sub_eq_iff_eq_add', ← neg_sub, Am_comm_Gg, neg_neg]
  rw [Matrix.mulVec_mulVec, h, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, vecMulVec_mulVec', vecMulVec_mulVec']

/-- **B4** (general form): `G A v = A p + ω r (Q p − P q)`. -/
lemma Gg_mulVec_Am_vm : Gg w l μ m *ᵥ (AA *ᵥ vv)
    = AA *ᵥ pg w l μ m + (ww * rr * Qg w l μ m) • pg w l μ m
      - (ww * rr * Pg w l μ m) • qg w l μ m := by
  rw [Gg_Am_mulVec, Gg_mulVec_vm, ← dot_Dg_symm, ← dot_Dg_symm, dotProduct_comm (qg w l μ m),
    dotProduct_comm (pg w l μ m), ← Qg, ← Pg]
  module

lemma DvdM.sub' {k : ℕ} {M N : Matrix (Fin m) (Fin m) ℚ⟦X⟧} (h : DvdM k M) (h' : DvdM k N) :
    DvdM k (M - N) := fun i j => dvd_sub (h i j) (h' i j)

lemma DvdM_vecMulVec {k : ℕ} (f : Fin m → ℚ⟦X⟧) {g : Fin m → ℚ⟦X⟧} (h : DvdV k g) :
    DvdM k (vecMulVec f g) := fun i j => by
  rw [vecMulVec_apply]; exact dvd_mul_of_dvd_right (h j) _

/-- `Xᵀ A v ≡ r (A + 1) v (mod r^m)`. -/
lemma vm_H5a_A : DvdV m ((Xm ℚ m)ᵀ *ᵥ (Am ℚ m *ᵥ vm ℚ m) - (X : ℚ⟦X⟧) • (Am ℚ m *ᵥ vm ℚ m + vm ℚ m)) := by
  intro a
  have hAv : Am ℚ m *ᵥ vm ℚ m = fun a : Fin m => ((a : ℕ) : ℚ⟦X⟧) * vE (a : ℕ) := by
    funext a; rw [Am_mulVec]; rfl
  rw [hAv, Pi.sub_apply, XmT_mulVec_of (fun a : ℕ => (a : ℚ⟦X⟧) * vE a)]
  obtain ⟨a, ha⟩ := a
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, vm]
  split_ifs with h
  · have := vE_H5a (K := ℚ) a
    push_cast
    rw [show ((a : ℚ⟦X⟧) + 1) * (((a : ℚ⟦X⟧) + 1) * vE (a + 1))
        = ((a : ℚ⟦X⟧) + 1) * (X * vE a) by rw [this]]
    rw [show X * ((a : ℚ⟦X⟧) * vE a + vE a) = ((a : ℚ⟦X⟧) + 1) * (X * vE a) by ring, sub_self]
    exact dvd_zero _
  · rw [zero_sub, dvd_neg]
    have : m = a + 1 := by omega
    subst this
    rw [pow_succ']
    exact mul_dvd_mul_left _ ((X_pow_dvd_vE a).trans (by
      rw [show (a : ℚ⟦X⟧) * vE a + vE a = ((a : ℚ⟦X⟧) + 1) * vE a by ring]
      exact dvd_mul_left _ _))

end AvgRS
