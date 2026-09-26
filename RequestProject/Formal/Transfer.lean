module

public import RequestProject.Formal.Coherence
public import RequestProject.Formal.Sec7Alg
public import RequestProject.Formal.Limits

@[expose] public section

/-!
# Passing to the limit: the formal quantities of Section 5

The truncated scalars form `X`-adically Cauchy sequences (Coherence); their limits are the
formal power series `P, Q, P₁, Q₁, p₀, q₀, p₁, q₁, G₀₀, G₀₁, G₁₁, D, D_Z` of Section 5.  All
identities proved for the truncations (exactly or up to terms divisible by `r ^ m`) pass to
the limit, and the algebra of Section 5 then gives (C): `D' = 2 r z D_Z`.
-/

namespace AvgRS.Formal

open PowerSeries Matrix

variable {K : Type*} [Field K]

section Trunc

variable {m : ℕ} {z : K}

lemma DvdM.mul_of {ι : Type*} [Fintype ι] {a b : ℕ} {M N : Matrix ι ι K⟦X⟧} (h1 : DvdM a M)
    (h2 : DvdM b N) : DvdM (a + b) (M * N) := fun i j => by
  rw [Matrix.mul_apply, pow_add]
  exact Finset.dvd_sum fun l _ => mul_dvd_mul (h1 i l) (h2 l j)

lemma dvd_dot_of {ι : Type*} [Fintype ι] {a b : ℕ} {u w : ι → K⟦X⟧} (h1 : DvdV a u)
    (h2 : DvdV b w) : (X : K⟦X⟧) ^ (a + b) ∣ u ⬝ᵥ w := by
  rw [pow_add]; exact Finset.dvd_sum fun l _ => mul_dvd_mul (h1 l) (h2 l)

lemma Hm_dvd : DvdM 1 (Hm K m) := fun a b => by simpa using X_dvd_Hm (K := K) a b

lemma one_sub_Gm_dvd : DvdM 2 (1 - Gm K m z) := by
  rw [← c_HGH]
  exact ((Hm_dvd.mul_right _).mul_of Hm_dvd).smul _

/-- The first basis vector. -/
noncomputable def e0 (n : ℕ) : Fin (n + 1) → K⟦X⟧ := Pi.single 0 1

lemma vm_sub_e0 (n : ℕ) : DvdV 1 (vm K (n + 1) - e0 n) := by
  intro a
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [vm, e0, vE_zero]
  · simp only [vm, e0, Pi.sub_apply, ne_eq, Fin.succ_ne_zero, not_false_eq_true,
      Pi.single_eq_of_ne, sub_zero, Fin.val_succ]
    exact (pow_dvd_pow _ (by omega)).trans (X_pow_dvd_vE _)

lemma pm_sub_e0 (n : ℕ) : DvdV 1 (pm K (n + 1) z - e0 n) := by
  have : pm K (n + 1) z - e0 n = -((1 - Gm K (n + 1) z) *ᵥ vm K (n + 1)) + (vm K (n + 1) - e0 n) := by
    rw [pm, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [this]
  exact ((one_sub_Gm_dvd.mono (by norm_num)).mulVec _).neg.add (vm_sub_e0 n)

lemma Av_dvd : DvdV 1 (Am K m *ᵥ vm K m) := by
  intro a
  rw [Am_mulVec]
  rcases Nat.eq_zero_or_pos (a : ℕ) with h | h
  · simp [h]
  · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans (X_pow_dvd_vE _)) _

lemma Pm_sub_one_dvd (n : ℕ) : (X : K⟦X⟧) ∣ Pm K (n + 1) z - 1 := by
  have := DvdV.sub_dot (vm_sub_e0 (K := K) n) (pm_sub_e0 (z := z) n)
  have e : e0 (K := K) n ⬝ᵥ e0 n = 1 := by simp [e0]
  rw [e, pow_one] at this
  exact this

lemma pm_zero_sub_one_dvd (n : ℕ) : (X : K⟦X⟧) ∣ pm K (n + 1) z 0 - 1 := by
  simpa [e0] using pm_sub_e0 (K := K) (z := z) n 0

lemma P1m_dvd (n : ℕ) : (X : K⟦X⟧) ^ 2 ∣ P1m K (n + 1) z := by
  have h : P1m K (n + 1) z = (Am K (n + 1) *ᵥ vm K (n + 1)) ⬝ᵥ (pm K (n + 1) z - e0 n)
      + (Am K (n + 1) *ᵥ vm K (n + 1)) ⬝ᵥ e0 n := by
    rw [P1m, dotProduct_sub]; abel
  have h2 : (Am K (n + 1) *ᵥ vm K (n + 1)) ⬝ᵥ e0 n = 0 := by
    simp [e0, Am_mulVec]
  rw [h, h2, add_zero]
  exact dvd_dot_of Av_dvd (pm_sub_e0 n)

lemma Qm_dvd : (X : K⟦X⟧) ∣ Qm K m z := by
  have := ((Hm_dvd (K := K) (m := m)).mulVec (vm K m)).mulVec (Gm K m z)
  simpa [Qm, qm] using this.dot (vm K m)

lemma Gm_apply_sub_dvd (a b : Fin m) :
    (X : K⟦X⟧) ∣ Gm K m z a b - (1 : Matrix (Fin m) (Fin m) K⟦X⟧) a b := by
  have := (one_sub_Gm_dvd (K := K) (m := m) (z := z)).mono (by norm_num : 1 ≤ 2) a b
  rw [pow_one, Matrix.sub_apply] at this
  rw [← neg_sub]; exact this.neg_right

end Trunc

section Components

variable [CharZero K] {z : K} (n : ℕ)

local notation "PP" => Pm K (n + 2) z
local notation "QQ" => Qm K (n + 2) z
local notation "PP1" => P1m K (n + 2) z
local notation "QQ1" => Q1m K (n + 2) z
local notation "pp" => pm K (n + 2) z
local notation "qq" => qm K (n + 2) z
local notation "cc" => (C z : K⟦X⟧)

lemma fin_one_val : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp

lemma R0a_trunc : ∃ e : K⟦X⟧, (X : K⟦X⟧) ^ (n + 2) ∣ e ∧
    0 = -(PP1 - cc * X * PP * QQ) * pp 0 + X * (1 - cc * PP ^ 2) * qq 0 + e := by
  obtain ⟨err, herr, h⟩ := Rq_trunc (K := K) (m := n + 2) (z := z)
  refine ⟨err 0, herr 0, ?_⟩
  have := congrFun h 0
  simp only [Xm_mulVec_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Am_mulVec, Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero] at this
  linear_combination this

lemma R0b_trunc : ∃ e : K⟦X⟧, (X : K⟦X⟧) ^ (n + 2) ∣ e ∧
    0 = cc * X * (X * PP ^ 2 - QQ) * pp 0 - cc * X * (PP1 - cc * X * PP * QQ) * qq 0
      + X * (cc * (2 * QQ1 + QQ - X * cc * QQ ^ 2 - X * PP ^ 2)) + e := by
  obtain ⟨err, herr, h⟩ := Rp_trunc (K := K) (m := n + 2) (z := z)
  refine ⟨err 0, herr 0, ?_⟩
  have := congrFun h 0
  simp only [Xm_mulVec_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Am_mulVec, Fin.val_zero, Nat.cast_zero, zero_mul, mul_zero, vm, vE_zero] at this
  linear_combination this

lemma R1a_trunc : ∃ e : K⟦X⟧, (X : K⟦X⟧) ^ (n + 2) ∣ e ∧
    qq 0 = PP * pp 1 - (PP1 - cc * X * PP * QQ) * pp 1 + X * (1 - cc * PP ^ 2) * qq 1 + e := by
  obtain ⟨err, herr, h⟩ := Rq_trunc (K := K) (m := n + 2) (z := z)
  refine ⟨err 1, herr 1, ?_⟩
  have := congrFun h 1
  simp only [Xm_mulVec_one, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Am_mulVec, fin_one_val, Nat.cast_one, one_mul] at this
  linear_combination this

lemma R1b_trunc : ∃ e : K⟦X⟧, (X : K⟦X⟧) ^ (n + 2) ∣ e ∧
    X * pp 0 = pp 1 - cc * X * PP * qq 1 + cc * X * (X * PP ^ 2 - QQ) * pp 1
      - cc * X * (PP1 - cc * X * PP * QQ) * qq 1
      + X * (cc * (2 * QQ1 + QQ - X * cc * QQ ^ 2 - X * PP ^ 2)) * X + e := by
  obtain ⟨err, herr, h⟩ := Rp_trunc (K := K) (m := n + 2) (z := z)
  refine ⟨err 1, herr 1, ?_⟩
  have := congrFun h 1
  have hv : vm K (n + 2) 1 = X := by simp [vm, vE]
  simp only [Xm_mulVec_one, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Am_mulVec, fin_one_val, Nat.cast_one, one_mul, hv] at this
  linear_combination this

lemma p0_ode_trunc : X * d⁄dX K (pp 0) = -(2 * cc * X * PP * qq 0) := by
  have := congrFun (ode_p (K := K) (m := n + 2) (z := z)) 0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Am_mulVec, Fin.val_zero, Nat.cast_zero,
    zero_mul, dV] at this
  linear_combination this

lemma q0_ode_trunc : X * d⁄dX K (qq 0) = 2 * X * PP * pp 0 - qq 0 := by
  have := congrFun (ode_q (K := K) (m := n + 2) (z := z)) 0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply, Am_mulVec, Fin.val_zero,
    Nat.cast_zero, zero_mul, zero_add, dV] at this
  linear_combination this

omit [CharZero K] in
lemma G10_eq_G01 : Gm K (n + 2) z 1 0 = Gm K (n + 2) z 0 1 := by
  have := congrFun (congrFun (Gm_transpose (K := K) (m := n + 2) (z := z)) 0) 1
  simpa using this

end Components

/-- `IsLim` for polynomial expressions in the base sequences. -/
lemma IsLim.eq_of_dvd {f g : ℕ → K⟦X⟧} {L M : K⟦X⟧} (hf : IsLim f L) (hg : IsLim g M)
    (h : ∀ n, (X : K⟦X⟧) ^ n ∣ f n - g n) : L = M := by
  have := IsLim.eq_zero_of_dvd (hf.sub hg) h
  exact sub_eq_zero.mp this

lemma IsLim.dvd_sub_of {f : ℕ → K⟦X⟧} {L a : K⟦X⟧} {k : ℕ} (hf : IsLim f L)
    (h : ∀ n, (X : K⟦X⟧) ^ k ∣ f n - a) : (X : K⟦X⟧) ^ k ∣ L - a := by
  obtain ⟨N, hN⟩ := hf k
  have := dvd_sub (h N) (hN N le_rfl)
  rwa [sub_sub_sub_cancel_left] at this

/-- The `X`-adic limit of a sequence (meaningful for Cauchy sequences). -/
noncomputable def xlim (f : ℕ → K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun i => coeff i (f (i + 1))

lemma isLim_xlim {f : ℕ → K⟦X⟧} (h : ∀ n, (X : K⟦X⟧) ^ (n + 2) ∣ f (n + 1) - f n) :
    IsLim f (xlim f) :=
  IsLim.of_cauchy fun n => (pow_dvd_pow _ (by omega)).trans (h n)

section Limits

variable (K) (z : K)

/-- The formal series `P = ⟨v, G v⟩`. -/
noncomputable def LP : K⟦X⟧ := xlim fun n => Pm K (n + 2) z
/-- The formal series `Q = ⟨v, G H v⟩`. -/
noncomputable def LQ : K⟦X⟧ := xlim fun n => Qm K (n + 2) z
/-- The formal series `P₁ = ⟨A v, G v⟩`. -/
noncomputable def LP1 : K⟦X⟧ := xlim fun n => P1m K (n + 2) z
/-- The formal series `Q₁ = ⟨A v, G H v⟩`. -/
noncomputable def LQ1 : K⟦X⟧ := xlim fun n => Q1m K (n + 2) z
/-- `p₀`. -/
noncomputable def Lp0 : K⟦X⟧ := xlim fun n => pm K (n + 2) z 0
/-- `q₀`. -/
noncomputable def Lq0 : K⟦X⟧ := xlim fun n => qm K (n + 2) z 0
/-- `p₁`. -/
noncomputable def Lp1 : K⟦X⟧ := xlim fun n => pm K (n + 2) z 1
/-- `q₁`. -/
noncomputable def Lq1 : K⟦X⟧ := xlim fun n => qm K (n + 2) z 1
/-- `G₀₀`. -/
noncomputable def LG00 : K⟦X⟧ := xlim fun n => Gm K (n + 2) z 0 0
/-- `G₀₁`. -/
noncomputable def LG01 : K⟦X⟧ := xlim fun n => Gm K (n + 2) z 0 1
/-- `G₁₁`. -/
noncomputable def LG11 : K⟦X⟧ := xlim fun n => Gm K (n + 2) z 1 1
/-- The formal Fredholm determinant `D = det(1 + z H²)`. -/
noncomputable def LD : K⟦X⟧ := xlim fun n => Dm K (n + 2) z
/-- The formal Fredholm determinant `D_Z = det(1 + Z H²)`. -/
noncomputable def LDZ : K⟦X⟧ := xlim fun n => DZm K (n + 2) z

lemma castSucc_one' (n : ℕ) : (1 : Fin (n + 2)).castSucc = 1 := Fin.ext (by simp)

lemma isLim_P : IsLim (fun n => Pm K (n + 2) z) (LP K z) := isLim_xlim fun _ => Pm_succ
lemma isLim_Q : IsLim (fun n => Qm K (n + 2) z) (LQ K z) := isLim_xlim fun _ => Qm_succ
lemma isLim_P1 : IsLim (fun n => P1m K (n + 2) z) (LP1 K z) := isLim_xlim fun _ => P1m_succ
lemma isLim_Q1 : IsLim (fun n => Q1m K (n + 2) z) (LQ1 K z) := isLim_xlim fun _ => Q1m_succ
lemma isLim_D : IsLim (fun n => Dm K (n + 2) z) (LD K z) := isLim_xlim fun _ => Dm_succ
lemma isLim_DZ : IsLim (fun n => DZm K (n + 2) z) (LDZ K z) := isLim_xlim fun _ => DZm_succ
lemma isLim_p0 : IsLim (fun n => pm K (n + 2) z 0) (Lp0 K z) :=
  isLim_xlim fun n => by simpa using pm_succ_apply (K := K) (m := n + 2) (z := z) 0
lemma isLim_q0 : IsLim (fun n => qm K (n + 2) z 0) (Lq0 K z) :=
  isLim_xlim fun n => by simpa using qm_succ_apply (K := K) (m := n + 2) (z := z) 0
lemma isLim_p1 : IsLim (fun n => pm K (n + 2) z 1) (Lp1 K z) :=
  isLim_xlim fun n => by simpa [castSucc_one'] using pm_succ_apply (K := K) (m := n + 2) (z := z) 1
lemma isLim_q1 : IsLim (fun n => qm K (n + 2) z 1) (Lq1 K z) :=
  isLim_xlim fun n => by simpa [castSucc_one'] using qm_succ_apply (K := K) (m := n + 2) (z := z) 1
lemma isLim_G00 : IsLim (fun n => Gm K (n + 2) z 0 0) (LG00 K z) :=
  isLim_xlim fun n => by simpa using Gm_succ_apply (K := K) (m := n + 2) (z := z) 0 0
lemma isLim_G01 : IsLim (fun n => Gm K (n + 2) z 0 1) (LG01 K z) :=
  isLim_xlim fun n => by
    simpa [castSucc_one'] using Gm_succ_apply (K := K) (m := n + 2) (z := z) 0 1
lemma isLim_G11 : IsLim (fun n => Gm K (n + 2) z 1 1) (LG11 K z) :=
  isLim_xlim fun n => by
    simpa [castSucc_one'] using Gm_succ_apply (K := K) (m := n + 2) (z := z) 1 1

end Limits

/-- Prove `IsLim` of a polynomial expression in the base sequences. -/
macro "islim" : tactic => `(tactic| repeat' (with_reducible first
  | exact isLim_P _ _ | exact isLim_Q _ _ | exact isLim_P1 _ _ | exact isLim_Q1 _ _
  | exact isLim_D _ _ | exact isLim_DZ _ _ | exact isLim_p0 _ _ | exact isLim_q0 _ _
  | exact isLim_p1 _ _ | exact isLim_q1 _ _ | exact isLim_G00 _ _ | exact isLim_G01 _ _
  | exact isLim_G11 _ _
  | apply IsLim.add | apply IsLim.sub | apply IsLim.mul | apply IsLim.neg | apply IsLim.pow
  | apply IsLim.deriv
  | exact IsLim.const _))

section Final

variable [CharZero K] (z : K)

/-- **(C) for the formal Fredholm determinants**: `(1/2r) d/dr det(1 + z H²) = z det(1 + Z H²)`,
i.e. `D' = 2 r z D_Z` in `K⟦r⟧` (Lemma 5.5 and Section 5.8 of the paper, `sec:proofend`). -/
theorem formal_C (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    d⁄dX K (LD K z) = 2 * X * C z * LDZ K z := by
  apply sec7_conclusion z hz0 hz1 (LP K z) (LQ K z) (LP1 K z) (LQ1 K z) (Lp0 K z) (Lq0 K z)
    (Lp1 K z) (Lq1 K z) (LG00 K z) (LG01 K z) (LG11 K z) (LD K z) (LDZ K z)
  · exact IsLim.eq_of_dvd (f := fun n => X * d⁄dX K (Pm K (n + 2) z))
      (g := fun n => 2 * P1m K (n + 2) z - 2 * C z * X * Pm K (n + 2) z * Qm K (n + 2) z)
      (by islim) (by islim) (fun n => by beta_reduce; rw [ode_P, sub_self]; exact dvd_zero _)
  · exact IsLim.eq_of_dvd (f := fun n => X * d⁄dX K (Qm K (n + 2) z))
      (g := fun n => 2 * X * Pm K (n + 2) z ^ 2 - Qm K (n + 2) z)
      (by islim) (by islim) (fun n => by beta_reduce; rw [ode_Q, sub_self]; exact dvd_zero _)
  · refine IsLim.eq_of_dvd (f := fun n => d⁄dX K (P1m K (n + 2) z))
      (g := fun n => 2 * (X * (1 - C z * Pm K (n + 2) z ^ 2)) * Pm K (n + 2) z
        + 2 * C z * Qm K (n + 2) z * (Pm K (n + 2) z
          + (P1m K (n + 2) z - C z * X * Pm K (n + 2) z * Qm K (n + 2) z)))
      (by islim) (by islim) (fun n => ?_)
    beta_reduce
    obtain ⟨e, he, h⟩ := ode_P1 (K := K) (m := n + 2) (z := z)
    rw [h, add_sub_cancel_left]
    exact (pow_dvd_pow _ (by omega)).trans he
  · exact IsLim.eq_of_dvd (f := fun n => X * d⁄dX K (pm K (n + 2) z 0))
      (g := fun n => -(2 * C z * X * Pm K (n + 2) z * qm K (n + 2) z 0))
      (by islim) (by islim) (fun n => by beta_reduce; rw [p0_ode_trunc, sub_self]; exact dvd_zero _)
  · exact IsLim.eq_of_dvd (f := fun n => X * d⁄dX K (qm K (n + 2) z 0))
      (g := fun n => 2 * X * Pm K (n + 2) z * pm K (n + 2) z 0 - qm K (n + 2) z 0)
      (by islim) (by islim) (fun n => by beta_reduce; rw [q0_ode_trunc, sub_self]; exact dvd_zero _)
  · exact IsLim.eq_of_dvd (f := fun n => d⁄dX K (Gm K (n + 2) z 0 0))
      (g := fun n => -(C z * (pm K (n + 2) z 0 * qm K (n + 2) z 0
        + qm K (n + 2) z 0 * pm K (n + 2) z 0)))
      (by islim) (by islim) (fun n => by beta_reduce; rw [ode_G, sub_self]; exact dvd_zero _)
  · exact IsLim.eq_of_dvd (f := fun n => d⁄dX K (Gm K (n + 2) z 0 1))
      (g := fun n => -(C z * (pm K (n + 2) z 0 * qm K (n + 2) z 1
        + qm K (n + 2) z 0 * pm K (n + 2) z 1)))
      (by islim) (by islim) (fun n => by beta_reduce; rw [ode_G, sub_self]; exact dvd_zero _)
  · exact IsLim.eq_of_dvd (f := fun n => d⁄dX K (Gm K (n + 2) z 1 1))
      (g := fun n => -(C z * (pm K (n + 2) z 1 * qm K (n + 2) z 1
        + qm K (n + 2) z 1 * pm K (n + 2) z 1)))
      (by islim) (by islim) (fun n => by beta_reduce; rw [ode_G, sub_self]; exact dvd_zero _)
  · exact IsLim.eq_of_dvd (f := fun n => d⁄dX K (Dm K (n + 2) z))
      (g := fun n => 2 * C z * Qm K (n + 2) z * Dm K (n + 2) z)
      (by islim) (by islim) (fun n => by beta_reduce; rw [deriv_Dm, sub_self]; exact dvd_zero _)
  · exact IsLim.eq_of_dvd (f := fun n => C z ^ 2 * DZm K (n + 2) z)
      (g := fun n => Dm K (n + 2) z * ((1 - (1 - C z) * Gm K (n + 2) z 0 0)
        * (1 - (1 - C z) * Gm K (n + 2) z 1 1)
        - (1 - C z) ^ 2 * (Gm K (n + 2) z 0 1 * Gm K (n + 2) z 0 1)))
      (by islim) (by islim)
      (fun n => by beta_reduce; rw [DZm_eq, G10_eq_G01, sub_self]; exact dvd_zero _)
  · refine IsLim.eq_of_dvd (f := fun _ => 0)
      (g := fun n => -(P1m K (n + 2) z - C z * X * Pm K (n + 2) z * Qm K (n + 2) z)
        * pm K (n + 2) z 0 + X * (1 - C z * Pm K (n + 2) z ^ 2) * qm K (n + 2) z 0)
      (by islim) (by islim) (fun n => ?_)
    beta_reduce
    obtain ⟨e, he, h⟩ := R0a_trunc (K := K) (z := z) n
    rw [show (0 : K⟦X⟧) - _ = e by linear_combination h]
    exact (pow_dvd_pow _ (by omega)).trans he
  · refine IsLim.eq_of_dvd (f := fun _ => 0)
      (g := fun n => C z * X * (X * Pm K (n + 2) z ^ 2 - Qm K (n + 2) z) * pm K (n + 2) z 0
        - C z * X * (P1m K (n + 2) z - C z * X * Pm K (n + 2) z * Qm K (n + 2) z)
          * qm K (n + 2) z 0
        + X * (C z * (2 * Q1m K (n + 2) z + Qm K (n + 2) z - X * C z * Qm K (n + 2) z ^ 2
          - X * Pm K (n + 2) z ^ 2)))
      (by islim) (by islim) (fun n => ?_)
    beta_reduce
    obtain ⟨e, he, h⟩ := R0b_trunc (K := K) (z := z) n
    rw [show (0 : K⟦X⟧) - _ = e by linear_combination h]
    exact (pow_dvd_pow _ (by omega)).trans he
  · refine IsLim.eq_of_dvd (f := fun n => qm K (n + 2) z 0)
      (g := fun n => Pm K (n + 2) z * pm K (n + 2) z 1
        - (P1m K (n + 2) z - C z * X * Pm K (n + 2) z * Qm K (n + 2) z) * pm K (n + 2) z 1
        + X * (1 - C z * Pm K (n + 2) z ^ 2) * qm K (n + 2) z 1)
      (by islim) (by islim) (fun n => ?_)
    beta_reduce
    obtain ⟨e, he, h⟩ := R1a_trunc (K := K) (z := z) n
    rw [show qm K (n + 2) z 0 - _ = e by linear_combination h]
    exact (pow_dvd_pow _ (by omega)).trans he
  · refine IsLim.eq_of_dvd (f := fun n => X * pm K (n + 2) z 0)
      (g := fun n => pm K (n + 2) z 1 - C z * X * Pm K (n + 2) z * qm K (n + 2) z 1
        + C z * X * (X * Pm K (n + 2) z ^ 2 - Qm K (n + 2) z) * pm K (n + 2) z 1
        - C z * X * (P1m K (n + 2) z - C z * X * Pm K (n + 2) z * Qm K (n + 2) z)
          * qm K (n + 2) z 1
        + X * (C z * (2 * Q1m K (n + 2) z + Qm K (n + 2) z - X * C z * Qm K (n + 2) z ^ 2
          - X * Pm K (n + 2) z ^ 2)) * X)
      (by islim) (by islim) (fun n => ?_)
    beta_reduce
    obtain ⟨e, he, h⟩ := R1b_trunc (K := K) (z := z) n
    rw [show X * pm K (n + 2) z 0 - _ = e by linear_combination h]
    exact (pow_dvd_pow _ (by omega)).trans he
  · have := (isLim_P K z).dvd_sub_of (k := 1) (a := 1) fun n => by
      simpa using Pm_sub_one_dvd (K := K) (z := z) (n + 1)
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at this
    exact this
  · have := (isLim_p0 K z).dvd_sub_of (k := 1) (a := 1) fun n => by
      simpa using pm_zero_sub_one_dvd (K := K) (z := z) (n + 1)
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at this
    exact this
  · have := (isLim_G00 K z).dvd_sub_of (k := 1) (a := 1) fun n => by
      simpa using Gm_apply_sub_dvd (K := K) (m := n + 2) (z := z) 0 0
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at this
    exact this
  · have := (isLim_G11 K z).dvd_sub_of (k := 1) (a := 1) fun n => by
      simpa using Gm_apply_sub_dvd (K := K) (m := n + 2) (z := z) 1 1
    rw [pow_one, X_dvd_iff, map_sub, map_one, sub_eq_zero] at this
    exact this
  · have := (isLim_G01 K z).dvd_sub_of (k := 1) (a := 0) fun n => by
      simpa [Matrix.one_apply] using Gm_apply_sub_dvd (K := K) (m := n + 2) (z := z) 0 1
    rw [pow_one, sub_zero, X_dvd_iff] at this
    exact this
  · have := (isLim_P1 K z).dvd_sub_of (k := 2) (a := 0) fun n => by
      simpa using P1m_dvd (K := K) (z := z) (n + 1)
    simpa using this
  · have := (isLim_Q K z).dvd_sub_of (k := 1) (a := 0) fun n => by
      simpa using Qm_dvd (K := K) (m := n + 2) (z := z)
    simpa using this

end Final

end AvgRS.Formal
