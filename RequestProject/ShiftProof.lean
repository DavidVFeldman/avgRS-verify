module

public import RequestProject.Frobenius
public import RequestProject.Formal.DetExpand
public import RequestProject.GiambelliComb

@[expose] public section

/-!
# Proof of the shift identity (Lemma 5.4 via Giambelli's formula, and Theorem 2.1)

The `r^{2N}` coefficient of the truncated determinant `det(1 + diag(ω) H²)` is a sum over pairs of
strictly increasing index maps `(f, g)` with `∑ f + ∑ g + k = N`; these are exactly the Frobenius
coordinates of the partitions of `N`.  Giambelli's formula
`f_λ / |λ|! = det (F(a_i | b_j))_{i,j < d(λ)}` (proved in `GiambelliComb.lean`) then identifies the
coefficients with the Durfee generating functions (Lemma 5.4, `lem:durfeedet`), and the shift identity follows
from the formal identity (C).
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

/-- The Giambelli matrix `(F(a_i | b_j))_{i,j < d(λ)}` of `λ` in Frobenius coordinates, with
`F(a|b) = 1/(a! b! (a+b+1))`. -/
noncomputable def giambelliMat {n : ℕ} (p : n.Partition) :
    Matrix (Fin (durfee p)) (Fin (durfee p)) ℚ :=
  Matrix.of fun i j => hookF (arm p i) (leg p j)

/-- **Giambelli's formula** (in the form used in Section 5): for every partition `λ ⊢ n`,
`F(λ) = f_λ / n! = det (F(a_i | b_j))_{i,j < d(λ)}`, where `(a_0 > ⋯ | b_0 > ⋯)` are the
Frobenius coordinates of `λ`. -/
def GiambelliFormula : Prop :=
  ∀ (n : ℕ) (p : n.Partition), (numSYT p : ℚ) / n.factorial = (giambelliMat p).det

section FinConversion

/-- A sequence decreasing on `{0, …, k-1}`, listed in increasing order in `Fin m`. -/
def toFin (m : ℕ) [NeZero m] (k : ℕ) (α : ℕ → ℕ) : Fin k → Fin m :=
  fun t => Fin.ofNat m (α (k - 1 - t))

/-- An increasing map `Fin k → Fin m`, listed in decreasing order. -/
def ofFin {k m : ℕ} (f : Fin k → Fin m) : ℕ → ℕ :=
  fun i => if h : i < k then (f (Fin.rev ⟨i, h⟩) : ℕ) else 0

variable {k m : ℕ}

lemma ofFin_sAnti {f : Fin k → Fin m} (hf : StrictMono f) : SAnti k (ofFin f) := by
  intro i i' hii hi'
  unfold ofFin
  rw [dif_pos hi', dif_pos (by omega)]
  exact hf (Fin.rev_lt_rev.2 (by simpa [Fin.lt_def] using hii))

lemma sum_ofFin (f : Fin k → Fin m) : ∑ i ∈ range k, ofFin f i = ∑ t, (f t : ℕ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [ofFin, Fin.is_lt, dif_pos, Fin.eta]
  exact Fintype.sum_equiv Fin.revPerm _ _ fun t => rfl

lemma frobOK_ofFin {N : ℕ} {f g : Fin k → Fin m} (hf : StrictMono f) (hg : StrictMono g)
    (hw : frobWt f g = N) : FrobOK k N (ofFin f) (ofFin g) :=
  ⟨ofFin_sAnti hf, ofFin_sAnti hg, by rw [sum_ofFin, sum_ofFin, ← hw]; rfl⟩

variable [NeZero m]

lemma toFin_val {α : ℕ → ℕ} (t : Fin k) (h : α (k - 1 - t) < m) :
    (toFin m k α t : ℕ) = α (k - 1 - t) := by
  simp [toFin, Nat.mod_eq_of_lt h]

lemma toFin_ofFin (f : Fin k → Fin m) : toFin m k (ofFin f) = f := by
  funext t
  apply Fin.ext
  have e : Fin.rev (⟨k - 1 - t, by omega⟩ : Fin k) = t := Fin.ext (by simp; omega)
  have h1 : ofFin f (k - 1 - t) = f t := by
    unfold ofFin; rw [dif_pos (by omega), e]
  rw [toFin_val t (by rw [h1]; exact (f t).is_lt), h1]

lemma toFin_congr {α α' : ℕ → ℕ} (h : ∀ i < k, α i = α' i) : toFin m k α = toFin m k α' := by
  funext t; unfold toFin; rw [h _ (by omega)]

lemma ofFin_toFin {α : ℕ → ℕ} (hb : ∀ i < k, α i < m) {i : ℕ} (hi : i < k) :
    ofFin (toFin m k α) i = α i := by
  unfold ofFin; rw [dif_pos hi]
  have : k - 1 - ((Fin.rev (⟨i, hi⟩ : Fin k) : ℕ)) = i := by simp; omega
  rw [toFin_val _ (by rw [this]; exact hb i hi), this]

lemma toFin_strictMono {α : ℕ → ℕ} (hα : SAnti k α) (hb : ∀ i < k, α i < m) :
    StrictMono (toFin m k α) := by
  intro t t' htt
  rw [Fin.lt_def, toFin_val t (hb _ (by omega)), toFin_val t' (hb _ (by omega))]
  exact hα _ _ (by rw [Fin.lt_def] at htt; omega) (by omega)

lemma frobWt_toFin {N : ℕ} {α β : ℕ → ℕ} (h : FrobOK k N α β) (hbα : ∀ i < k, α i < m)
    (hbβ : ∀ i < k, β i < m) : frobWt (toFin m k α) (toFin m k β) = N := by
  unfold frobWt
  rw [← sum_ofFin, ← sum_ofFin, sum_congr rfl fun i hi => ofFin_toFin hbα (mem_range.1 hi),
    sum_congr rfl fun i hi => ofFin_toFin hbβ (mem_range.1 hi)]
  exact h.2.2

end FinConversion

section Bijection

variable {N m k : ℕ}

lemma arm_lt {p : N.Partition} (hm : N < m) {i : ℕ} (hi : i < durfee p) : arm p i < m := by
  have := (frobOK_partition p).bound hi; omega

lemma leg_lt {p : N.Partition} (hm : N < m) {i : ℕ} (hi : i < durfee p) : leg p i < m := by
  have := (frobOK_partition p).2.2
  have := single_le_sum (f := leg p) (fun _ _ => Nat.zero_le _) (mem_range.2 hi)
  omega

lemma frobOK_of_mem {x : (Fin k → Fin m) × (Fin k → Fin m)}
    (hx : x ∈ (smono k m ×ˢ smono k m).filter fun x => frobWt x.1 x.2 = N) :
    FrobOK k N (ofFin x.1) (ofFin x.2) := by
  simp only [mem_filter, mem_product, mem_smono] at hx
  exact frobOK_ofFin hx.1.1 hx.1.2 hx.2

/-- **Frobenius coordinates**: partitions of `N` with Durfee square `k` correspond to pairs of
strictly increasing maps `f, g : Fin k → Fin m` with `∑ f + ∑ g + k = N` (for `m > N`). -/
theorem sum_durfee_eq_sum_smono [NeZero m] (hm : N < m) (T : (Fin k → Fin m) → (Fin k → Fin m) → ℚ) :
    ∑ p ∈ (univ : Finset N.Partition).filter (fun p => durfee p = k),
        T (toFin m k (arm p)) (toFin m k (leg p))
      = ∑ x ∈ (smono k m ×ˢ smono k m).filter (fun x => frobWt x.1 x.2 = N), T x.1 x.2 := by
  refine sum_bij' (fun p _ => (toFin m k (arm p), toFin m k (leg p)))
    (fun x hx => ofFrob (frobOK_of_mem hx)) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have h := frobOK_partition p
    have ha : ∀ i < k, arm p i < m := fun i hi => arm_lt hm (by omega)
    have hl : ∀ i < k, leg p i < m := fun i hi => leg_lt hm (by omega)
    rw [hp] at h
    simp only [mem_filter, mem_product, mem_smono]
    exact ⟨⟨toFin_strictMono h.1 ha, toFin_strictMono h.2.1 hl⟩, frobWt_toFin h ha hl⟩
  · intro x hx
    simp only [mem_filter, mem_univ, true_and]
    exact durfee_ofFrob _
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    refine partition_ext_col _ fun j => ?_
    rw [col_ofFrob, col_eq_cOf, hp]
    dsimp only
    exact congrFun (cOf_congr
      (fun i hi => ofFin_toFin (fun i hi => arm_lt (p := p) hm (by omega)) hi)
      (fun i hi => ofFin_toFin (fun i hi => leg_lt (p := p) hm (by omega)) hi)) j
  · intro x hx
    have h := frobOK_of_mem hx
    refine Prod.ext ?_ ?_
    · show toFin m k (arm (ofFrob h)) = x.1
      rw [toFin_congr fun i hi => arm_ofFrob h hi, toFin_ofFin]
    · show toFin m k (leg (ofFrob h)) = x.2
      rw [toFin_congr fun i hi => leg_ofFrob h hi, toFin_ofFin]

lemma summand_eq [NeZero m] (hm : N < m) (W : ℕ → ℚ) (p : N.Partition) :
    (∏ i ∈ range (durfee p), W (arm p i)) * (giambelliMat p).det ^ 2
      = (∏ t, W (toFin m (durfee p) (arm p) t : ℕ)) *
          (frobMat (K := ℚ) (toFin m (durfee p) (arm p)) (toFin m (durfee p) (leg p))).det ^ 2 := by
  have hv : ∀ t : Fin (durfee p), (toFin m (durfee p) (arm p) t : ℕ) = arm p (Fin.rev t) := by
    intro t; rw [toFin_val t (arm_lt hm (by omega)), Fin.val_rev]; congr 1; omega
  have hv' : ∀ t : Fin (durfee p), (toFin m (durfee p) (leg p) t : ℕ) = leg p (Fin.rev t) := by
    intro t; rw [toFin_val t (leg_lt hm (by omega)), Fin.val_rev]; congr 1; omega
  congr 1
  · rw [← Fin.prod_univ_eq_prod_range (fun i => W (arm p i))]
    simp only [hv]
    exact Fintype.prod_equiv Fin.revPerm _ _ fun t => by simp
  · have : frobMat (K := ℚ) (toFin m (durfee p) (arm p)) (toFin m (durfee p) (leg p))
        = (giambelliMat p).submatrix Fin.revPerm Fin.revPerm := by
      ext t s
      simp only [frobMat, giambelliMat, Matrix.of_apply, Matrix.submatrix_apply, hv, hv',
        Fin.revPerm_apply]
    rw [this, det_submatrix_equiv_self]

end Bijection

section Coefficients

lemma coeff_det_HH (N m : ℕ) (W : ℕ → ℚ) :
    coeff (2 * N) (1 + diagonal (fun a : Fin m => C (W a)) * (Hm ℚ m * Hm ℚ m)).det
      = ∑ k ∈ range (m + 1), ∑ x ∈ (smono k m ×ˢ smono k m).filter (fun x => frobWt x.1 x.2 = N),
          (∏ t, W (x.1 t : ℕ)) * (frobMat x.1 x.2).det ^ 2 := by
  rw [det_one_add_diag_HH m (fun a => W a)]
  simp only [map_sum, coeff_C_mul_X_pow]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun f _ => sum_congr rfl fun g _ => ?_
  exact if_congr (by dsimp only; omega) rfl rfl

/-- The `r^{2N}` coefficient of `det(1 + diag(W) H²)` as a sum over partitions of `N`
(for truncation size `m > N`). -/
theorem coeff_det_HH_eq_sum_partitions (N m : ℕ) [NeZero m] (hm : N < m) (W : ℕ → ℚ) :
    coeff (2 * N) (1 + diagonal (fun a : Fin m => C (W a)) * (Hm ℚ m * Hm ℚ m)).det
      = ∑ p : N.Partition, (∏ i ∈ range (durfee p), W (arm p i)) * (giambelliMat p).det ^ 2 := by
  rw [coeff_det_HH, ← sum_fiberwise_of_maps_to (g := durfee) (t := range (m + 1))
    (fun p _ => mem_range.2 (by have := durfee_le p; omega))]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_durfee_eq_sum_smono hm (fun f g => (∏ t, W (f t : ℕ)) * (frobMat f g).det ^ 2)]
  refine sum_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  subst hp
  exact (summand_eq hm W p).symm

/-- **Lemma 5.4** (`lem:durfeedet`), conditional on Giambelli's formula: the coefficients of the formal Fredholm
determinants `D = det(1 + z H²)` and `D_Z = det(1 + Z H²)` are the Durfee generating
functions. -/
theorem durfeeGF_of_giambelli (hG : GiambelliFormula) (z : ℚ) : DurfeeGF ℚ z := by
  intro N
  have hm : N < 2 * N + 1 + 2 := by omega
  constructor
  · rw [LD, xlim, coeff_mk]
    rw [Dm, Bm, smul_eq_diagonal_mul,
      show (diagonal fun _ => C z : Matrix (Fin (2 * N + 1 + 2)) _ ℚ⟦X⟧)
        = diagonal fun a : Fin (2 * N + 1 + 2) => C ((fun _ : ℕ => z) (a : ℕ)) from rfl,
      coeff_det_HH_eq_sum_partitions N _ hm (fun _ => z)]
    refine sum_congr rfl fun p _ => ?_
    rw [prod_const, card_range, ← hG]
  · rw [LDZ, xlim, coeff_mk]
    rw [DZm, Zm, show (diagonal fun a : Fin (2 * N + 1 + 2) => if (a : ℕ) < 2 then 1 else C z)
        = diagonal fun a : Fin (2 * N + 1 + 2) =>
          C ((fun b : ℕ => if b < 2 then (1 : ℚ) else z) (a : ℕ)) from
        congrArg diagonal (funext fun a => by dsimp only; split_ifs <;> simp),
      coeff_det_HH_eq_sum_partitions N _ hm (fun b => if b < 2 then (1 : ℚ) else z)]
    refine sum_congr rfl fun p _ => ?_
    rw [prod_ite, prod_const_one, one_mul, prod_const, ← hG, numN2_eq]
    congr 3
    exact filter_congr fun i _ => not_lt

end Coefficients

/-- **Theorem 2.1 (shift identity)**, conditional on Giambelli's formula. -/
theorem shift_identity_of_giambelli (hG : GiambelliFormula) (k N : ℕ) (hk : 2 ≤ k) :
    boxAbsentSum (N + 1) k k = (N + 1) * boxAbsentSum N (k - 1) (k + 1) :=
  shift_identity_of_durfeeGF (fun z _ _ => durfeeGF_of_giambelli hG z) k N hk

/-- **Giambelli's formula** for `F(λ) = f_λ / |λ|!` (Macdonald, *Symmetric Functions and Hall
Polynomials*, I.3, Example 9, under the exponential specialization).  Proved by showing that the
Giambelli determinant satisfies the branching rule `n · G(λ) = ∑_{corners c} G(λ ∖ c)`
(`GD_branch`, `sum_corners_eq`, `syt_div_eq_GD`). -/
theorem giambelli_formula : GiambelliFormula := by
  intro n p
  exact syt_div_eq_GD n p.parts (durfee p) (arm p) (leg p) (fun _ hx => p.parts_pos hx)
    (frobOK_partition p) (fun j => congrFun (col_eq_cOf p) j)

/-- **Theorem 2.1 (shift identity), fat-hook form (Proposition 2.2(a)).**
For every `k ≥ 2` and every `N`,
`#{π ∈ S_{N+1} : (k,k) ∉ sh(π)} = (N+1) · #{σ ∈ S_N : (k-1,k+1) ∉ sh(σ)}`,
written through Robinson–Schensted as an identity of sums of `f_λ²`. -/
theorem shift_identity (k N : ℕ) (hk : 2 ≤ k) :
    boxAbsentSum (N + 1) k k = (N + 1) * boxAbsentSum N (k - 1) (k + 1) :=
  shift_identity_of_giambelli giambelli_formula k N hk

end AvgRS
