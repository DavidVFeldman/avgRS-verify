module

public import RequestProject.ZLine
public import RequestProject.Formal.Transfer

@[expose] public section

/-!
# Batch 4, items B3–B4: the `z`-line identity as an identity of formal determinants

`Hz z` is the hook matrix of the specialization `ρ_z`: `(H_z)_{ab} = X^{a+b+1} · G_z(a|b)` with
`G_z = hookFz` (`ZLine.lean`).  With `z' = −z − 2`, `t = (z+1)²`, the generating functions
`G₀(w) = det(1 + w H_z H_{z'}ᵀ)`, `G₂(w) = det(1 + W H_z H_{z'}ᵀ)`, `W = diag(1,1,w,w,…)`, are
`X`-adic limits of truncations exactly as `LD`, `LDZ` in `Formal/Transfer.lean`, and their
`X^{2N}` coefficients are `∑_{λ ⊢ N} w^{d(λ)} w_t(λ)/N!²` and `∑_{λ ⊢ N} w^{N₂(λ)} w_t(λ)/N!²`
(item B3).  Conjecture 3.2 for all `k` is equivalent to the identity
`d/dX G₀ = 2 X w (z z' G₂ + (X/2) d/dX G₂)` for all rational `w ≠ 0, 1` (item B4); see COMMISSION.md.
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

/-- Truncated hook matrix of `ρ_z`: `(H_z)_{ab} = X^{a+b+1} G_z(a|b)`. -/
noncomputable def Hzm (z : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Matrix.of fun a b => C (hookFz z a b) * X ^ ((a : ℕ) + b + 1)

/-- `C_z = H_z H_{z'}ᵀ`, `z' = −z−2` (truncated). -/
noncomputable def Czm (z : ℚ) (m : ℕ) : Matrix (Fin m) (Fin m) ℚ⟦X⟧ :=
  Hzm z m * (Hzm (-z - 2) m)ᵀ

/-- `G₀ = det(1 + w C_z)` (truncated). -/
noncomputable def G0m (z w : ℚ) (m : ℕ) : ℚ⟦X⟧ := (1 + C w • Czm z m).det

/-- `G₂ = det(1 + W C_z)`, `W = diag(1,1,w,w,…)` (truncated). -/
noncomputable def G2m (z w : ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  (1 + (Matrix.diagonal fun a : Fin m => if (a : ℕ) < 2 then 1 else C w) * Czm z m).det

/-- The matrix `(G_z(f_i | g_j))_{i,j}` for index maps `f, g`. -/
noncomputable def frobMatz (z : ℚ) {k m : ℕ} (f g : Fin k → Fin m) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun i j => hookFz z (f i : ℕ) (g j : ℕ)

lemma det_Hzm_submatrix (z : ℚ) {k m : ℕ} (f g : Fin k → Fin m) :
    ((Hzm z m).submatrix f g).det = C (frobMatz z f g).det * X ^ frobWt f g := by
  have : (Hzm z m).submatrix f g
      = Matrix.of fun i j => C (frobMatz z f g i j) * (X : ℚ⟦X⟧) ^ ((f i : ℕ) + (g j : ℕ) + 1) := by
    ext i j; simp [Hzm, frobMatz]
  rw [this, det_C_mul_X_pow]; rfl

/-- Cauchy–Binet expansion of `det(1 + diag(ω) H_z H_{z'}ᵀ)`. -/
lemma det_one_add_diag_Cz (z : ℚ) (m : ℕ) (ω : Fin m → ℚ) :
    (1 + diagonal (fun a => C (ω a)) * Czm z m).det
      = ∑ k ∈ range (m + 1), ∑ f ∈ smono k m, ∑ g ∈ smono k m,
          C ((∏ i, ω (f i)) * ((frobMatz z f g).det * (frobMatz (-z - 2) f g).det))
            * X ^ (2 * frobWt f g) := by
  rw [Czm, det_one_add_diagonal_mul]
  refine sum_congr rfl fun k _ => sum_congr rfl fun f _ => ?_
  have hsub : (Hzm z m * (Hzm (-z - 2) m)ᵀ).submatrix f f
      = (Hzm z m).submatrix f id * ((Hzm (-z - 2) m)ᵀ).submatrix id f :=
    Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id
  rw [hsub, det_mul_eq_sum_smono, Finset.mul_sum]
  refine sum_congr rfl fun g _ => ?_
  simp only [submatrix_submatrix, Function.comp_id, Function.id_comp]
  rw [← transpose_submatrix, det_transpose, det_Hzm_submatrix, det_Hzm_submatrix, ← map_prod,
    map_mul, map_mul, two_mul, pow_add]
  ring

lemma coeff_det_Cz (z : ℚ) (N m : ℕ) (ω : ℕ → ℚ) :
    coeff (2 * N) (1 + diagonal (fun a : Fin m => C (ω a)) * Czm z m).det
      = ∑ k ∈ range (m + 1), ∑ x ∈ (smono k m ×ˢ smono k m).filter (fun x => frobWt x.1 x.2 = N),
          (∏ t, ω (x.1 t : ℕ)) * ((frobMatz z x.1 x.2).det * (frobMatz (-z - 2) x.1 x.2).det) := by
  rw [det_one_add_diag_Cz z m (fun a => ω a)]
  simp only [map_sum, coeff_C_mul_X_pow]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun f _ => sum_congr rfl fun g _ => ?_
  exact if_congr (by dsimp only; omega) rfl rfl

lemma frobMatz_toFin {N m : ℕ} [NeZero m] (hm : N < m) (z : ℚ) (p : N.Partition) :
    frobMatz z (toFin m (durfee p) (arm p)) (toFin m (durfee p) (leg p))
      = (Matrix.of fun i j : Fin (durfee p) => hookFz z (arm p i) (leg p j)).submatrix
          Fin.revPerm Fin.revPerm := by
  have hv : ∀ t : Fin (durfee p), (toFin m (durfee p) (arm p) t : ℕ) = arm p (Fin.rev t) := by
    intro t; rw [toFin_val t (arm_lt hm (by omega)), Fin.val_rev]; congr 1; omega
  have hv' : ∀ t : Fin (durfee p), (toFin m (durfee p) (leg p) t : ℕ) = leg p (Fin.rev t) := by
    intro t; rw [toFin_val t (leg_lt hm (by omega)), Fin.val_rev]; congr 1; omega
  ext t s
  simp only [frobMatz, Matrix.of_apply, Matrix.submatrix_apply, hv, hv', Fin.revPerm_apply]

lemma summand_eq_z {N m : ℕ} [NeZero m] (hm : N < m) (z : ℚ) (ω : ℕ → ℚ) (p : N.Partition) :
    (∏ i ∈ range (durfee p), ω (arm p i)) *
        (contentWt p ((z + 1) ^ 2) / ((N.factorial : ℚ) ^ 2))
      = (∏ t, ω (toFin m (durfee p) (arm p) t : ℕ)) *
          ((frobMatz z (toFin m (durfee p) (arm p)) (toFin m (durfee p) (leg p))).det *
            (frobMatz (-z - 2) (toFin m (durfee p) (arm p)) (toFin m (durfee p) (leg p))).det) := by
  have hv : ∀ t : Fin (durfee p), (toFin m (durfee p) (arm p) t : ℕ) = arm p (Fin.rev t) := by
    intro t; rw [toFin_val t (arm_lt hm (by omega)), Fin.val_rev]; congr 1; omega
  congr 1
  · rw [← Fin.prod_univ_eq_prod_range (fun i => ω (arm p i))]
    simp only [hv]
    exact Fintype.prod_equiv Fin.revPerm _ _ fun t => by simp
  · rw [frobMatz_toFin hm, frobMatz_toFin hm, det_submatrix_equiv_self, det_submatrix_equiv_self,
      ← giambelli_content, ← giambelli_content, contentWt_eq_prod]
    ring

/-- Item B3 (finite form; adapt `coeff_det_HH_eq_sum_partitions` with two matrices):
the `X^{2N}` coefficient of `det(1 + diag(ω) H_z H_{z'}ᵀ)` for `m > N` is
`∑_{λ ⊢ N} (∏_{i<d} ω(a_i)) · w_t(λ) / N!²`, `t = (z+1)²`. -/
theorem coeff_det_Cz_eq_sum_partitions (z : ℚ) (N m : ℕ) [NeZero m] (hm : N < m) (ω : ℕ → ℚ) :
    coeff (2 * N) (1 + diagonal (fun a : Fin m => C (ω a)) * Czm z m).det
      = ∑ p : N.Partition, (∏ i ∈ range (durfee p), ω (arm p i)) *
          (contentWt p ((z + 1) ^ 2) / ((N.factorial : ℚ) ^ 2)) := by
  rw [coeff_det_Cz, ← sum_fiberwise_of_maps_to (g := durfee) (t := range (m + 1))
    (fun p _ => mem_range.2 (by have := durfee_le p; omega))]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_durfee_eq_sum_smono hm (fun f g => (∏ t, ω (f t : ℕ)) *
    ((frobMatz z f g).det * (frobMatz (-z - 2) f g).det))]
  refine sum_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  subst hp
  exact (summand_eq_z hm z ω p).symm

lemma Hzm_succ (z : ℚ) (m : ℕ) : DvdM (m + 1) (Hzm z (m + 1) - blk (Hzm z m) 0) := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [Matrix.sub_apply, blk_cc, blk_cl, blk_lc, blk_ll, sub_zero, Hzm, Matrix.of_apply,
      Fin.val_last, Fin.val_castSucc, sub_self]
  · exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
  · exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
  · exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
  · simp

lemma blk_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ⟦X⟧) (d : ℚ⟦X⟧) :
    (blk M d)ᵀ = blk Mᵀ d := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp

lemma Czm_succ (z : ℚ) (m : ℕ) : DvdM (m + 1) (Czm z (m + 1) - blk (Czm z m) 0) := by
  have h2 : DvdM (m + 1) ((Hzm (-z - 2) (m + 1))ᵀ - blk (Hzm (-z - 2) m)ᵀ 0) := by
    rw [← blk_transpose, ← Matrix.transpose_sub]
    exact fun i j => Hzm_succ (-z - 2) m j i
  have := DvdM.sub_mul (Hzm_succ z m) h2
  rwa [blk_mul, mul_zero] at this

lemma one_add_blk {m : ℕ} (D M : Matrix (Fin m) (Fin m) ℚ⟦X⟧) (d : ℚ⟦X⟧) :
    1 + blk D d * blk M 0 = blk (1 + D * M) 1 := by
  rw [blk_mul, mul_zero]
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

lemma diag_succ {m : ℕ} (δ : ℕ → ℚ⟦X⟧) :
    (diagonal fun a : Fin (m + 1) => δ a) = blk (diagonal fun a : Fin m => δ a) (δ m) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.diagonal_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

lemma detW_succ (z : ℚ) (m : ℕ) (δ : ℕ → ℚ⟦X⟧) :
    (X : ℚ⟦X⟧) ^ m ∣ (1 + (diagonal fun a : Fin (m + 1) => δ a) * Czm z (m + 1)).det
      - (1 + (diagonal fun a : Fin m => δ a) * Czm z m).det := by
  have h : DvdM (m + 1) ((1 + (diagonal fun a : Fin (m + 1) => δ a) * Czm z (m + 1))
      - blk (1 + (diagonal fun a : Fin m => δ a) * Czm z m) 1) := by
    rw [← one_add_blk, ← diag_succ, add_sub_add_left_eq_sub, ← Matrix.mul_sub]
    exact (Czm_succ z m).mul_left _
  have := h.sub_det
  rw [det_blk, mul_one] at this
  exact (pow_dvd_pow _ (Nat.le_succ m)).trans this

/-- Item B3 (coherence): the truncations are `X`-adically Cauchy, as in `Formal/Coherence.lean`. -/
lemma G0m_succ (z w : ℚ) (m : ℕ) : (X : ℚ⟦X⟧) ^ m ∣ G0m z w (m + 1) - G0m z w m := by
  simpa only [G0m, smul_eq_diagonal_mul] using detW_succ z m (fun _ => C w)

lemma G2m_succ (z w : ℚ) (m : ℕ) : (X : ℚ⟦X⟧) ^ m ∣ G2m z w (m + 1) - G2m z w m :=
  detW_succ z m (fun a => if a < 2 then 1 else C w)

/-- The formal determinants `G₀`, `G₂` (limits of the truncations). -/
noncomputable def LG0 (z w : ℚ) : ℚ⟦X⟧ := xlim fun n => G0m z w (n + 2)
noncomputable def LG2 (z w : ℚ) : ℚ⟦X⟧ := xlim fun n => G2m z w (n + 2)

/-- Item B3: the coefficients of `G₀`, `G₂` are the two generating functions. -/
theorem zlineGF (z w : ℚ) (N : ℕ) :
    coeff (2 * N) (LG0 z w) = ∑ p : N.Partition, w ^ durfee p * (contentWt p ((z + 1) ^ 2) / ((N.factorial : ℚ) ^ 2)) ∧
    coeff (2 * N) (LG2 z w) = ∑ p : N.Partition, w ^ numN2 p * (contentWt p ((z + 1) ^ 2) / ((N.factorial : ℚ) ^ 2)) := by
  have hm : N < 2 * N + 1 + 2 := by omega
  constructor
  · rw [LG0, xlim, coeff_mk, G0m, smul_eq_diagonal_mul]
    refine (coeff_det_Cz_eq_sum_partitions z N _ hm (fun _ => w)).trans ?_
    refine sum_congr rfl fun p _ => ?_
    rw [prod_const, card_range]
  · rw [LG2, xlim, coeff_mk, G2m,
      show (diagonal fun a : Fin (2 * N + 1 + 2) => if (a : ℕ) < 2 then 1 else C w)
        = diagonal fun a : Fin (2 * N + 1 + 2) =>
          C ((fun b : ℕ => if b < 2 then (1 : ℚ) else w) (a : ℕ)) from
        congrArg diagonal (funext fun a => by dsimp only; split_ifs <;> simp)]
    refine (coeff_det_Cz_eq_sum_partitions z N _ hm (fun b => if b < 2 then (1 : ℚ) else w)).trans ?_
    refine sum_congr rfl fun p _ => ?_
    rw [prod_ite, prod_const_one, one_mul, prod_const, numN2_eq]
    congr 3
    exact filter_congr fun i _ => not_lt

lemma coeff_X_mul_derivative (f : ℚ⟦X⟧) (n : ℕ) : coeff n (X * d⁄dX ℚ f) = n * coeff n f := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/-- Coefficient extraction from (B4) at one value of `w`:
`∑_{λ ⊢ N+1} w^{d(λ)} w_t(λ) = (N+1)(N+1−t) w ∑_{λ ⊢ N} w^{N₂(λ)} w_t(λ)`, `t = (z+1)²`. -/
lemma zline_sum_identity (z w : ℚ)
    (h : d⁄dX ℚ (LG0 z w) = 2 * X * C w * (C (z * (-z - 2)) * LG2 z w + (C (1 / 2 : ℚ) * X) * d⁄dX ℚ (LG2 z w)))
    (N : ℕ) :
    ∑ p : (N + 1).Partition, w ^ durfee p * contentWt p ((z + 1) ^ 2)
      = (N + 1) * ((N : ℚ) + 1 - (z + 1) ^ 2) * w *
          ∑ p : N.Partition, w ^ numN2 p * contentWt p ((z + 1) ^ 2) := by
  have hC := congrArg (coeff (2 * N + 1)) h
  rw [show (2 : ℚ⟦X⟧) * X * C w * (C (z * (-z - 2)) * LG2 z w + (C (1 / 2 : ℚ) * X) * d⁄dX ℚ (LG2 z w))
      = X * (C (2 * w * (z * (-z - 2))) * LG2 z w + C w * (X * d⁄dX ℚ (LG2 z w))) by
    simp only [map_mul, map_ofNat]
    have : (C (1 / 2 : ℚ) : ℚ⟦X⟧) * 2 = 1 := by rw [← map_ofNat C 2, ← map_mul]; norm_num
    linear_combination (X * C w * X * d⁄dX ℚ (LG2 z w)) * this] at hC
  rw [coeff_derivative, coeff_succ_X_mul, map_add, coeff_C_mul, coeff_C_mul, coeff_X_mul_derivative,
    show 2 * N + 1 + 1 = 2 * (N + 1) by ring, (zlineGF z w (N + 1)).1, (zlineGF z w N).2] at hC
  have hf : ((N + 1).factorial : ℚ) = (N + 1) * N.factorial := by push_cast [Nat.factorial_succ]; ring
  have hN : (N.factorial : ℚ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have e1 : ∀ (M : ℕ) (g : M.Partition → ℕ), ∑ p : M.Partition, w ^ g p *
      (contentWt p ((z + 1) ^ 2) / ((M.factorial : ℚ) ^ 2))
      = (∑ p : M.Partition, w ^ g p * contentWt p ((z + 1) ^ 2)) / (M.factorial : ℚ) ^ 2 := by
    intro M g; rw [Finset.sum_div]; congr 1; ext p; ring
  rw [e1, e1, hf] at hC
  set A := ∑ p : (N + 1).Partition, w ^ durfee p * contentWt p ((z + 1) ^ 2)
  set B := ∑ p : N.Partition, w ^ numN2 p * contentWt p ((z + 1) ^ 2)
  push_cast at hC
  field_simp at hC
  have h1 : (2 : ℚ) * (N + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ h1
  linear_combination hC

lemma sum_range_coeff_eq_wt {n : ℕ} (c : n.Partition → ℚ) (g : n.Partition → ℕ) (k : ℕ) :
    ∑ j ∈ Finset.range k, (∑ p : n.Partition, Polynomial.C (c p) * Polynomial.X ^ g p).coeff j
      = ∑ p : n.Partition with g p < k, c p := by
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq']
  exact if_congr Finset.mem_range rfl rfl

/-- Item B4 (adapt `shift_identity_of_durfeeGF`): if for all rational `w ≠ 0, 1`
`d/dX G₀ = 2 X w (z z' G₂ + (X/2) d/dX G₂)` with `z' = −z − 2`, then `zline_identity` holds at
`t = (z+1)²`.  Since both sides of `zline_identity` are polynomials in `t` and every rational
`t ≥ 0` is of the form `(z+1)²` for `z = √t − 1` — not rational in general — the passage from
`t = (z+1)²`, `z ∈ ℚ`, to all `t ∈ ℚ` uses that both sides of `zline_identity` are polynomials in
`t` agreeing at the infinitely many values `t = (z+1)²`, `z ∈ ℚ`.

(The skeleton wrote the factor `X/2` as `(X / 2)`, which does not elaborate in `ℚ⟦X⟧` — there
is no division of a power series by a natural number; it is written `C (1/2) * X` here.)

Note that the statement is for the fixed value `t = (z+1)²`, so no interpolation in `t` is
needed for it. -/
theorem zline_identity_of_formal (z : ℚ) (hz : ∀ w : ℚ, w ≠ 0 → w ≠ 1 →
      d⁄dX ℚ (LG0 z w) = 2 * X * C w * (C (z * (-z - 2)) * LG2 z w + (C (1 / 2 : ℚ) * X) * d⁄dX ℚ (LG2 z w)))
    (k N : ℕ) (hk : 2 ≤ k) :
    ∑ p : (N + 1).Partition with ¬ HasBox p k k, contentWt p ((z + 1) ^ 2)
      = (N + 1) * ((N : ℚ) + 1 - (z + 1) ^ 2) *
          ∑ p : N.Partition with ¬ HasBox p (k - 1) (k + 1), contentWt p ((z + 1) ^ 2) := by
  set t := (z + 1) ^ 2
  set A : Polynomial ℚ := ∑ p : (N + 1).Partition, Polynomial.C (contentWt p t) * Polynomial.X ^ durfee p
  set B : Polynomial ℚ := ∑ p : N.Partition, Polynomial.C (contentWt p t) * Polynomial.X ^ numN2 p
  have hAB : A = Polynomial.X * (Polynomial.C (((N : ℚ) + 1) * ((N : ℚ) + 1 - t)) * B) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : ({0, 1}ᶜ : Set ℚ).Infinite := Set.Finite.infinite_compl (by simp)
    refine hinf.mono fun w hw => ?_
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
    have := zline_sum_identity z w (hz w hw.1 hw.2) N
    simp only [Set.mem_setOf_eq, A, B, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [show ∑ p : (N + 1).Partition, contentWt p t * w ^ durfee p
        = ∑ p : (N + 1).Partition, w ^ durfee p * contentWt p t from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, this,
      show ∑ p : N.Partition, contentWt p t * w ^ numN2 p
        = ∑ p : N.Partition, w ^ numN2 p * contentWt p t from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    ring
  have hA : ∑ j ∈ Finset.range k, A.coeff j = _ := sum_range_coeff_eq_wt (n := N + 1) _ durfee k
  have hB : ∑ j ∈ Finset.range (k - 1), B.coeff j = _ := sum_range_coeff_eq_wt (n := N) _ numN2 (k - 1)
  have hXB : ∑ j ∈ Finset.range k,
      (Polynomial.X * (Polynomial.C (((N : ℚ) + 1) * ((N : ℚ) + 1 - t)) * B)).coeff j
      = (((N : ℚ) + 1) * ((N : ℚ) + 1 - t)) * ∑ j ∈ Finset.range (k - 1), B.coeff j := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Finset.sum_range_succ', Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero,
      add_zero, Nat.add_sub_cancel, Finset.mul_sum, Polynomial.coeff_C_mul]
  rw [← hAB, hA, hB] at hXB
  rw [Finset.sum_congr (Finset.filter_congr fun p _ => (durfee_lt_iff p (by omega)).symm)
      (fun _ _ => rfl),
    Finset.sum_congr (Finset.filter_congr fun p _ => (numN2_lt_iff p hk).symm) (fun _ _ => rfl),
    hXB, mul_assoc]

end AvgRS
