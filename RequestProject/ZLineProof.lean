module

public import RequestProject.ZLineAlgMain
public import RequestProject.ZLineTransfer5

@[expose] public section

/-!
# Conjecture 3.2 on the line `z + z' = −2`

The formal identity (B4) for the two-matrix determinants `G₀ = det(1 + ω H_z H_{z'}ᵀ)`,
`G₂ = det(1 + Ω H_z H_{z'}ᵀ)` follows from the closed system (`zline_alg`) applied to the limit
scalars (`zdata`), after the bridge `H_z H_{z'}ᵀ ↦ C₁ = H Λ H M` (`det_one_add_diag_Czz`).
Then `zline_identity_of_formal` gives the fat-hook identity at every `t = (z+1)²`, and since both
sides are polynomials in `t`, at every `t`.
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

lemma G0m_eq_detBg (z w : ℚ) (m : ℕ) :
    G0m z w m = (Bg w (lamW ((z + 1) ^ 2)) (muW ((z + 1) ^ 2)) m).det := by
  have h := det_one_add_diag_Czz (m := m) z (fun _ => w)
  have e : ∀ M : Matrix (Fin m) (Fin m) ℚ⟦X⟧,
      Matrix.diagonal (fun _ : Fin m => C w) * M = C w • M := by
    intro M; ext i j; simp [Matrix.diagonal_mul]
  rw [e, e] at h
  exact h

lemma G2m_eq_detZg (z w : ℚ) (m : ℕ) :
    G2m z w m = (1 + Zm ℚ m w * Cg (lamW ((z + 1) ^ 2)) (muW ((z + 1) ^ 2)) m).det := by
  have h := det_one_add_diag_Czz (m := m) z (fun a => if (a : ℕ) < 2 then 1 else w)
  have e : (Matrix.diagonal fun a : Fin m => C (if (a : ℕ) < 2 then (1 : ℚ) else w))
      = Matrix.diagonal fun a : Fin m => if (a : ℕ) < 2 then 1 else C w := by
    congr 1; funext a; split_ifs <;> simp
  rw [e] at h
  exact h

lemma LG0_eq_zlD (z w : ℚ) : LG0 z w = zlD ((z + 1) ^ 2) w := by
  unfold LG0 zlD
  congr 1
  funext n
  exact G0m_eq_detBg z w (n + 2)

lemma LG2_eq_zlDZ (z w : ℚ) : LG2 z w = zlDZ ((z + 1) ^ 2) w := by
  unfold LG2 zlDZ
  congr 1
  funext n
  exact G2m_eq_detZg z w (n + 2)

/-- **(B4)** on the line `z + z' = −2`: `d/dX G₀ = 2 X ω (z z' G₂ + (X/2) d/dX G₂)`, for every
rational `z` with `(z+1)² ≠ 0, 1` and every `ω ≠ 0, 1`. -/
theorem zline_formal (z : ℚ) (hz0 : (z + 1) ^ 2 ≠ 0) (hz1 : (z + 1) ^ 2 ≠ 1) (w : ℚ)
    (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    d⁄dX ℚ (LG0 z w) = 2 * X * C w * (C (z * (-z - 2)) * LG2 z w
      + (C (1 / 2 : ℚ) * X) * d⁄dX ℚ (LG2 z w)) := by
  have h := zline_alg (zdata ((z + 1) ^ 2) w hw0) hz0 hz1 hw0 hw1
  have e : C (z * (-z - 2)) = (1 - C ((z + 1) ^ 2) : ℚ⟦X⟧) := by
    rw [← map_one C, ← map_sub]; congr 1; ring
  rw [LG0_eq_zlD, LG2_eq_zlDZ, e]
  exact h

/-- **Conjecture 3.2** (Section 3 of `avgRS.tex`), now a theorem: for all `k ≥ 2`, `N`, `t`,
`∑_{λ ⊢ N+1, λ_k ≤ k−1} w_t(λ) = (N+1)(N+1−t) ∑_{λ ⊢ N, λ_{k−1} ≤ k} w_t(λ)`.
This is the statement `zline_identity` of `ZLine.lean`, verbatim (it lives here because its proof
needs the whole resolvent development, which imports `ZLine.lean`). -/
theorem zline_identity (k N : ℕ) (hk : 2 ≤ k) (t : ℚ) :
    ∑ p : (N + 1).Partition with ¬ HasBox p k k, contentWt p t
      = (N + 1) * ((N : ℚ) + 1 - t) * ∑ p : N.Partition with ¬ HasBox p (k - 1) (k + 1), contentWt p t := by
  have main : ∀ n : ℕ, ∑ p : (N + 1).Partition with ¬ HasBox p k k, contentWt p (((n : ℚ) + 2) ^ 2)
      = (N + 1) * ((N : ℚ) + 1 - ((n : ℚ) + 2) ^ 2) *
        ∑ p : N.Partition with ¬ HasBox p (k - 1) (k + 1), contentWt p (((n : ℚ) + 2) ^ 2) := by
    intro n
    have hz0 : (((n : ℚ) + 1) + 1) ^ 2 ≠ 0 := by positivity
    have hz1 : (((n : ℚ) + 1) + 1) ^ 2 ≠ 1 := by
      have : (1 : ℚ) < ((n : ℚ) + 1) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
      nlinarith
    have := zline_identity_of_formal ((n : ℚ) + 1)
      (fun w hw0 hw1 => zline_formal _ hz0 hz1 w hw0 hw1) k N hk
    rw [show ((n : ℚ) + 1) + 1 = (n : ℚ) + 2 by ring] at this
    exact this
  set D : Polynomial ℚ := ∑ p : (N + 1).Partition with ¬ HasBox p k k, cwtPoly p
    - Polynomial.C ((N : ℚ) + 1) * (Polynomial.C ((N : ℚ) + 1) - Polynomial.X)
      * ∑ p : N.Partition with ¬ HasBox p (k - 1) (k + 1), cwtPoly p with hDdef
  have hD : ∀ t : ℚ, D.eval t = ∑ p : (N + 1).Partition with ¬ HasBox p k k, contentWt p t
      - ((N : ℚ) + 1) * ((N : ℚ) + 1 - t)
        * ∑ p : N.Partition with ¬ HasBox p (k - 1) (k + 1), contentWt p t := by
    intro t
    simp only [hDdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_finset_sum,
      Polynomial.eval_C, Polynomial.eval_X]
    simp only [← cwt_eq_eval]
    rfl
  have hD0 : D = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective fun n : ℕ => ((n : ℚ) + 2) ^ 2 := by
      intro a b hab
      have ha : (0 : ℚ) ≤ (a : ℚ) + 2 := by positivity
      have hb : (0 : ℚ) ≤ (b : ℚ) + 2 := by positivity
      have := (sq_eq_sq₀ ha hb).mp hab
      exact_mod_cast (by linarith : (a : ℚ) = b)
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hD, main n, sub_self]
  have := hD t
  rw [hD0, Polynomial.eval_zero] at this
  linarith

end AvgRS
