module

public import RequestProject.ShiftIdentity
public import RequestProject.Formal.Transfer

@[expose] public section

/-!
# From the formal identity (C) to the shift identity (Lemma 5.5, `lem:Cprime`)

`durfee λ` is the side of the Durfee square and `numN2 λ = #{i : λ_i - i ≥ 2}`.  If the
coefficients of the formal Fredholm determinants are the Durfee generating functions
(Lemma 5.4, `lem:durfeedet`; `DurfeeGF`), then (C) (`formal_C`) is equivalent to the shift identity for all `k`.
-/

namespace AvgRS

open Finset PowerSeries

/-- The Durfee square size `d(λ) = #{i ≥ 1 : (i,i) ∈ λ}`. -/
def durfee {n : ℕ} (p : n.Partition) : ℕ :=
  ((Finset.range n).filter fun i => HasBox p (i + 1) (i + 1)).card

/-- `N₂(λ) = #{i ≥ 1 : λ_i - i ≥ 2} = #{i ≥ 1 : (i, i+2) ∈ λ}`. -/
def numN2 {n : ℕ} (p : n.Partition) : ℕ :=
  ((Finset.range n).filter fun i => HasBox p (i + 1) (i + 3)).card

lemma HasBox.mono {n : ℕ} {p : n.Partition} {i j i' j' : ℕ} (h : HasBox p i j) (hi : i' ≤ i)
    (hj : j' ≤ j) : HasBox p i' j' := by
  unfold HasBox at *
  refine le_trans hi (le_trans h (Multiset.card_le_card (Multiset.monotone_filter_right _ ?_)))
  intro x hx; omega

lemma HasBox.le_n {n : ℕ} {p : n.Partition} {i j : ℕ} (h : HasBox p i j) : i ≤ n := by
  unfold HasBox at h
  have h1 : Multiset.card (p.parts.filter fun x => j ≤ x) ≤ Multiset.card p.parts :=
    Multiset.card_le_card (Multiset.filter_le _ _)
  have h2 := card_le_sum_of_pos (fun x hx => p.parts_pos hx)
  rw [p.parts_sum] at h2
  omega

lemma card_filter_lt_iff {n k : ℕ} (Q : ℕ → Prop) [DecidablePred Q]
    (hmono : ∀ i j, j ≤ i → Q i → Q j) (hn : ∀ i, Q i → i < n) (hk : 1 ≤ k) :
    ((Finset.range n).filter Q).card < k ↔ ¬ Q (k - 1) := by
  constructor
  · intro h hQ
    have : Finset.range k ⊆ (Finset.range n).filter Q := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨lt_of_le_of_lt (by omega) (hn _ hQ), hmono _ _ (by omega) hQ⟩
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    omega
  · intro h
    have : (Finset.range n).filter Q ⊆ Finset.range (k - 1) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_range]
      by_contra hc
      exact h (hmono _ _ (by omega) hi.2)
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    omega

lemma durfee_lt_iff {n : ℕ} (p : n.Partition) {k : ℕ} (hk : 1 ≤ k) :
    durfee p < k ↔ ¬ HasBox p k k := by
  unfold durfee
  rw [card_filter_lt_iff (fun i => HasBox p (i + 1) (i + 1))
    (fun i j hij h => h.mono (by omega) (by omega)) (fun i h => by have := h.le_n; omega) hk]
  rw [Nat.sub_add_cancel hk]

lemma numN2_lt_iff {n : ℕ} (p : n.Partition) {k : ℕ} (hk : 2 ≤ k) :
    numN2 p < k - 1 ↔ ¬ HasBox p (k - 1) (k + 1) := by
  unfold numN2
  rw [card_filter_lt_iff (fun i => HasBox p (i + 1) (i + 3))
    (fun i j hij h => h.mono (by omega) (by omega)) (fun i h => by have := h.le_n; omega) (by omega)]
  rw [show k - 1 - 1 + 1 = k - 1 by omega, show k - 1 - 1 + 3 = k + 1 by omega]

/-- Lemma 5.4 (`lem:durfeedet`; the Durfee generating functions as Fredholm determinants), as a property of
`z`: the `r^{2N}` coefficients of `D = det(1 + z H²)` and `D_Z = det(1 + Z H²)` are
`∑_{λ ⊢ N} z^{d(λ)} F(λ)²` and `∑_{λ ⊢ N} z^{N₂(λ)} F(λ)²`, `F(λ) = f_λ / N!`. -/
def DurfeeGF (K : Type*) [Field K] (z : K) : Prop :=
  ∀ N : ℕ, coeff (2 * N) (Formal.LD K z)
      = ∑ p : N.Partition, z ^ durfee p * ((numSYT p : K) / N.factorial) ^ 2 ∧
    coeff (2 * N) (Formal.LDZ K z)
      = ∑ p : N.Partition, z ^ numN2 p * ((numSYT p : K) / N.factorial) ^ 2

/-- Coefficient extraction from (C): `∑_{λ ⊢ N+1} z^{d(λ)} f_λ² = (N+1) z ∑_{λ ⊢ N} z^{N₂(λ)} f_λ²`. -/
lemma durfee_sum_identity (z : ℚ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (h : DurfeeGF ℚ z) (N : ℕ) :
    ∑ p : (N + 1).Partition, z ^ durfee p * (numSYT p : ℚ) ^ 2
      = (N + 1) * z * ∑ p : N.Partition, z ^ numN2 p * (numSYT p : ℚ) ^ 2 := by
  have hC := congrArg (coeff (2 * N + 1)) (Formal.formal_C z hz0 hz1)
  rw [coeff_derivative, show 2 * X * C z * Formal.LDZ ℚ z = X * (C (2 * z) * Formal.LDZ ℚ z) by
    rw [map_mul, map_ofNat]; ring, coeff_succ_X_mul, coeff_C_mul, show 2 * N + 1 + 1 = 2 * (N + 1) by ring,
    (h (N + 1)).1, (h N).2] at hC
  have hf : ((N + 1).factorial : ℚ) = (N + 1) * N.factorial := by push_cast [Nat.factorial_succ]; ring
  have hN : (N.factorial : ℚ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have e1 : ∀ (M : ℕ) (g : M.Partition → ℕ), ∑ p : M.Partition, z ^ g p * ((numSYT p : ℚ) / M.factorial) ^ 2
      = (∑ p : M.Partition, z ^ g p * (numSYT p : ℚ) ^ 2) / (M.factorial : ℚ) ^ 2 := by
    intro M g; rw [Finset.sum_div]; congr 1; ext p; ring
  rw [e1, e1, hf] at hC
  set A := ∑ p : (N + 1).Partition, z ^ durfee p * (numSYT p : ℚ) ^ 2
  set B := ∑ p : N.Partition, z ^ numN2 p * (numSYT p : ℚ) ^ 2
  push_cast at hC
  field_simp at hC
  have h1 : (2 : ℚ) * (N + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ h1
  linear_combination hC

lemma sum_range_coeff_eq {n : ℕ} (g : n.Partition → ℕ) (k : ℕ) :
    ∑ j ∈ Finset.range k, (∑ p : n.Partition,
        Polynomial.C ((numSYT p : ℚ) ^ 2) * Polynomial.X ^ g p).coeff j
      = ∑ p : n.Partition with g p < k, (numSYT p : ℚ) ^ 2 := by
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq']
  exact if_congr Finset.mem_range rfl rfl

/-- **Lemma 5.5 (`lem:Cprime`, reformulation)**: if the formal Fredholm determinants are the Durfee
generating functions (Lemma 5.4) for all rational `z ≠ 0, 1`, then the shift identity holds for
every `k ≥ 2`. -/
theorem shift_identity_of_durfeeGF (hGF : ∀ z : ℚ, z ≠ 0 → z ≠ 1 → DurfeeGF ℚ z) (k N : ℕ)
    (hk : 2 ≤ k) : boxAbsentSum (N + 1) k k = (N + 1) * boxAbsentSum N (k - 1) (k + 1) := by
  set A : Polynomial ℚ := ∑ p : (N + 1).Partition,
    Polynomial.C ((numSYT p : ℚ) ^ 2) * Polynomial.X ^ durfee p
  set B : Polynomial ℚ := ∑ p : N.Partition,
    Polynomial.C ((numSYT p : ℚ) ^ 2) * Polynomial.X ^ numN2 p
  have hAB : A = Polynomial.X * (Polynomial.C ((N : ℚ) + 1) * B) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : ({0, 1}ᶜ : Set ℚ).Infinite := Set.Finite.infinite_compl (by simp)
    refine hinf.mono fun z hz => ?_
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    have := durfee_sum_identity z hz.1 hz.2 (hGF z hz.1 hz.2) N
    simp only [Set.mem_setOf_eq, A, B, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [show ∑ p : (N + 1).Partition, (numSYT p : ℚ) ^ 2 * z ^ durfee p
        = ∑ p : (N + 1).Partition, z ^ durfee p * (numSYT p : ℚ) ^ 2 from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, this,
      show ∑ p : N.Partition, (numSYT p : ℚ) ^ 2 * z ^ numN2 p
        = ∑ p : N.Partition, z ^ numN2 p * (numSYT p : ℚ) ^ 2 from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    ring
  have hA : ∑ j ∈ Finset.range k, A.coeff j = _ := sum_range_coeff_eq (n := N + 1) durfee k
  have hB : ∑ j ∈ Finset.range (k - 1), B.coeff j = _ := sum_range_coeff_eq (n := N) numN2 (k - 1)
  have hXB : ∑ j ∈ Finset.range k, (Polynomial.X * (Polynomial.C ((N : ℚ) + 1) * B)).coeff j
      = ((N : ℚ) + 1) * ∑ j ∈ Finset.range (k - 1), B.coeff j := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Finset.sum_range_succ', Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero,
      add_zero, Nat.add_sub_cancel, Finset.mul_sum, Polynomial.coeff_C_mul]
  rw [← hAB, hA, hB] at hXB
  have e1 : ∑ p : (N + 1).Partition with durfee p < k, (numSYT p : ℚ) ^ 2
      = (boxAbsentSum (N + 1) k k : ℚ) := by
    rw [boxAbsentSum]; push_cast
    exact Finset.sum_congr (Finset.filter_congr fun p _ => durfee_lt_iff p (by omega)) (fun _ _ => rfl)
  have e2 : ∑ p : N.Partition with numN2 p < k - 1, (numSYT p : ℚ) ^ 2
      = (boxAbsentSum N (k - 1) (k + 1) : ℚ) := by
    rw [boxAbsentSum]; push_cast
    exact Finset.sum_congr (Finset.filter_congr fun p _ => numN2_lt_iff p hk) (fun _ _ => rfl)
  rw [e1, e2] at hXB
  exact_mod_cast hXB

end AvgRS
