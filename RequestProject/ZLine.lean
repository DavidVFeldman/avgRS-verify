module

public import RequestProject.ZLineTwo

@[expose] public section

/-!
# Batch 3, item B: the shift identity on the line `z + z' = −2` of `z`-measures (Conjecture 3.2)

Boxes of `p : n.Partition` are the pairs `(i, j)` (0-indexed row `i`, column `j`) with
`i < col p j`; the content of `(i, j)` is `j − i`.  The weight of Definition 3.1, up to the
normalization `1/(n!² Z_n(t))`, is
`contentWt p t = f_λ² ∏_{(i,j) ∈ λ} ((j − i − 1)² − t)`.
Conjecture 3.2 in the form of Proposition 2.2(a) reads
`∑_{λ ⊢ N+1, (k,k) ∉ λ} w_t(λ) = (N+1)(N+1−t) ∑_{λ ⊢ N, (k−1,k+1) ∉ λ} w_t(λ)`.
Items B1, B2 are proved here; B3, B4 in `ZLineDet.lean`; the structural identities
(H1_z)–(H4_z) in `ZLineHook.lean`; the case `k = 2` (Theorem 3.6) via `ZLineTwo.lean`.
Item B5, the identity itself for `k ≥ 3`, is open.
-/

namespace AvgRS

open Finset Formal

/-- The content weight `w_t(λ) = f_λ² ∏_{(i,j) ∈ λ} ((j − i − 1)² − t)`. -/
noncomputable def contentWt {n : ℕ} (p : n.Partition) (t : ℚ) : ℚ :=
  (numSYT p : ℚ) ^ 2 * ∏ j ∈ range n, ∏ i ∈ range (col p j), (((j : ℚ) - i - 1) ^ 2 - t)

/-- `∏_{(i,j) ∈ λ} (z + (j − i))`, the content product of the specialization `ρ_z`. -/
noncomputable def contentProd {n : ℕ} (p : n.Partition) (z : ℚ) : ℚ :=
  ∏ j ∈ range n, ∏ i ∈ range (col p j), (z + (j : ℚ) - i)

/-- Item B1: with `z' = −z − 2` and `t = (z+1)²`, `(z + c)(z' + c) = (c − 1)² − t` boxwise, so
`w_t(λ) = f_λ² · contentProd λ z · contentProd λ (−z−2)`. -/
theorem contentWt_eq_prod {n : ℕ} (p : n.Partition) (z : ℚ) :
    contentWt p ((z + 1) ^ 2) = (numSYT p : ℚ) ^ 2 * contentProd p z * contentProd p (-z - 2) := by
  unfold contentWt contentProd
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-- The content product of the hook `(a | b)`: `∏_{c = −b}^{a} (z + c)`. -/
noncomputable def hookContentProd (z : ℚ) (a b : ℕ) : ℚ :=
  ∏ m ∈ range (a + b + 1), (z + (m : ℚ) - b)

/-- `G_z(a | b) = (∏_{c=−b}^{a} (z + c)) / (a! b! (a + b + 1))`, the value of `s_{(a|b)}` at `ρ_z`. -/
noncomputable def hookFz (z : ℚ) (a b : ℕ) : ℚ := hookContentProd z a b * hookF a b

/-- The arm factor `∏_{m=0}^{a} (z + m)` of `hookContentProd`. -/
noncomputable def armProd (z : ℚ) (a : ℕ) : ℚ := ∏ m ∈ range (a + 1), (z + m)

/-- The leg factor `∏_{m=1}^{b} (z − m)` of `hookContentProd`. -/
noncomputable def legProd (z : ℚ) (b : ℕ) : ℚ := ∏ m ∈ range b, (z - (m + 1))

lemma hookContentProd_eq (z : ℚ) (a b : ℕ) :
    hookContentProd z a b = armProd z a * legProd z b := by
  unfold hookContentProd armProd legProd
  rw [show a + b + 1 = b + (a + 1) by ring, Finset.prod_range_add, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    push_cast; ring
  · rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun m hm => ?_
    have hm := Finset.mem_range.mp hm
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring

/-- The content product splits along the hooks of the Frobenius decomposition:
`∏_{□ ∈ λ} (z + c(□)) = ∏_{i < d(λ)} (∏_{m=0}^{a_i} (z+m)) (∏_{m=1}^{b_i} (z−m))`. -/
lemma contentProd_eq_prod_hooks {n : ℕ} (p : n.Partition) (z : ℚ) :
    contentProd p z = (∏ i ∈ range (durfee p), armProd z (arm p i))
      * ∏ j ∈ range (durfee p), legProd z (leg p j) := by
  have hd := durfee_le p
  unfold contentProd
  have split : ∀ j ∈ range n, ∏ i ∈ range (col p j), (z + (j : ℚ) - i)
      = (∏ i ∈ (range (col p j)).filter (· ≤ j), (z + (j : ℚ) - i))
        * legProd z (leg p j) := by
    intro j _
    rw [← Finset.prod_filter_mul_prod_filter_not (range (col p j)) (· ≤ j)]
    congr 1
    have e : (range (col p j)).filter (fun i => ¬ i ≤ j) = Ico (j + 1) (col p j) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [e, Finset.prod_Ico_eq_prod_range]
    unfold legProd leg
    rw [show col p j - (j + 1) = col p j - j - 1 by omega]
    refine Finset.prod_congr rfl fun m _ => ?_
    push_cast; ring
  rw [Finset.prod_congr rfl split, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_comm' (t' := range n) (s' := fun i => Ico i (row p i))]
    · have e2 : ∀ i ∈ range n, ∏ j ∈ Ico i (row p i), (z + (j : ℚ) - i)
          = if i < durfee p then armProd z (arm p i) else 1 := by
        intro i _
        rw [Finset.prod_Ico_eq_prod_range]
        split_ifs with hi
        · have hr := lt_row_self p hi
          unfold armProd arm
          rw [show row p i - i = row p i - i - 1 + 1 by omega]
          refine Finset.prod_congr rfl fun m _ => ?_
          push_cast; ring
        · have : row p i ≤ i := by
            by_contra h
            exact hi ((lt_durfee_iff p).2 ((lt_row_iff p).1 (by omega)))
          rw [show row p i - i = 0 by omega]
          simp
      rw [Finset.prod_congr rfl e2, Finset.prod_ite, Finset.prod_const_one, mul_one]
      congr 1
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    · intro j i
      simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Ico]
      have h1 := lt_row_iff p (i := i) (j := j)
      have h2 := row_le p (i := i)
      constructor
      · rintro ⟨hj, hi, hij⟩; exact ⟨⟨hij, h1.2 hi⟩, by omega⟩
      · rintro ⟨⟨hij, hj⟩, hi⟩; exact ⟨by omega, h1.1 hj, hij⟩
  · rw [← Finset.prod_range_mul_prod_Ico _ hd]
    rw [Finset.prod_eq_one (s := Ico (durfee p) n), mul_one]
    intro j hj
    have hj := (Finset.mem_Ico.mp hj).1
    have := col_le_durfee p hj
    unfold legProd leg
    rw [show col p j - j - 1 = 0 by omega]
    simp

/-- Item B2 (weighted Giambelli): `contentProd λ z · f_λ / n! = det (G_z(a_i | b_j))_{i,j < d(λ)}`.
Proof: as `syt_div_eq_GD`, with the weighted down rule
`contentProd λ z · f_λ = ∑_{ν ⋖ λ} (z + c(λ/ν)) · contentProd ν z · f_ν`. -/
theorem giambelli_content (z : ℚ) (n : ℕ) (p : n.Partition) :
    contentProd p z * ((numSYT p : ℚ) / n.factorial)
      = (Matrix.of fun i j : Fin (durfee p) => hookFz z (arm p i) (leg p j)).det := by
  have hM : (Matrix.of fun i j : Fin (durfee p) => hookFz z (arm p i) (leg p j))
      = Matrix.of fun i j : Fin (durfee p) => armProd z (arm p i) *
          (Matrix.of fun i j : Fin (durfee p) => legProd z (leg p j) * (giambelliMat p i j)) i j := by
    ext i j
    simp only [Matrix.of_apply, hookFz, hookContentProd_eq, giambelliMat]
    ring
  rw [hM, Matrix.det_mul_column, Matrix.det_mul_row, ← giambelli_formula n p,
    contentProd_eq_prod_hooks, Fin.prod_univ_eq_prod_range (fun i => armProd z (arm p i)),
    Fin.prod_univ_eq_prod_range (fun i => legProd z (leg p i))]
  ring

/- **Conjecture 3.2** (Section 3 of `avgRS.tex`), in the fat-hook form: for all `k ≥ 2`, `N`, `t`,
`∑_{λ ⊢ N+1, λ_k ≤ k−1} w_t(λ) = (N+1)(N+1−t) ∑_{λ ⊢ N, λ_{k−1} ≤ k} w_t(λ)`.

The statement `zline_identity` that stood here (with `sorry`) is now proved, verbatim, as
`AvgRS.zline_identity` in `ZLineProof.lean`.  It had to move: its proof uses the resolvent
development (`ZLineRec.lean`, `ZLineTransfer*.lean`, `ZLineAlg*.lean`), all of which import this
file.  The original statement was:

theorem zline_identity (k N : ℕ) (hk : 2 ≤ k) (t : ℚ) :
    ∑ p : (N + 1).Partition with ¬ HasBox p k k, contentWt p t
      = (N + 1) * ((N : ℚ) + 1 - t) * ∑ p : N.Partition with ¬ HasBox p (k - 1) (k + 1), contentWt p t
-/

/-- The case `k = 2` (Theorem 3.6 of the paper).  Proved in `ZLineTwo.lean` (`cwt_identity_two`):
hooks and two-column shapes are enumerated explicitly, and the resulting identity between
convolutions of `y_n = ∏_{i<n}(i² − t)/n!²` is the `X^{N+1}` coefficient of the differential identity
`Y (ϑ⁴ − tϑ²) Y = ϑ(ϑ − t)(Y ϑ²Y − (ϑY)²)`, a consequence of the hypergeometric equation
`(1 − X) ϑ²Y = −t X Y` for `Y = ₂F₁(−s, s; 1; X)`. -/
theorem zline_identity_two (N : ℕ) (t : ℚ) :
    ∑ p : (N + 1).Partition with ¬ HasBox p 2 2, contentWt p t
      = (N + 1) * ((N : ℚ) + 1 - t) * ∑ p : N.Partition with ¬ HasBox p 1 3, contentWt p t :=
  cwt_identity_two N t

end AvgRS
