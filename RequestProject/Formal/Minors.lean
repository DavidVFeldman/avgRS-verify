module

public import Mathlib

@[expose] public section

/-!
# Cauchy–Binet and the principal-minor expansion

Two classical facts of linear algebra used in Lemma 5.4 (`lem:durfeedet`):

* the Cauchy–Binet formula `det (A B) = ∑_g det (A_{·,g}) det (B_{g,·})`, the sum over strictly
  increasing `g : Fin k → Fin m`;
* the expansion `det (1 + diag(w) M) = ∑_{f} (∏ w ∘ f) det (M_{f,f})` over all principal minors.
-/

namespace AvgRS.Formal

open Matrix Finset Equiv

variable {R : Type*} [CommRing R]

/-- Strictly increasing maps `Fin k → Fin m`. -/
def smono (k m : ℕ) : Finset (Fin k → Fin m) := Finset.univ.filter StrictMono

lemma mem_smono {k m : ℕ} {g : Fin k → Fin m} : g ∈ smono k m ↔ StrictMono g := by
  simp [smono]

/-- Sum over injective maps, split as strictly increasing map composed with a permutation. -/
lemma sum_injective_eq {M : Type*} [AddCommMonoid M] {k m : ℕ} (T : (Fin k → Fin m) → M) :
    ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => Function.Injective f), T f
      = ∑ g ∈ smono k m, ∑ π : Perm (Fin k), T (g ∘ π) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij' (fun f _ => (f ∘ Tuple.sort f, (Tuple.sort f)⁻¹))
    (fun x _ => x.1 ∘ x.2) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [Finset.mem_product, mem_smono, Finset.mem_univ, and_true]
    exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  · intro x hx
    simp only [Finset.mem_product, mem_smono, Finset.mem_univ, and_true] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx.injective.comp x.2.injective
  · intro f _
    ext i
    simp
  · intro x hx
    simp only [Finset.mem_product, mem_smono, Finset.mem_univ, and_true] at hx
    have hs : x.2⁻¹ = Tuple.sort (x.1 ∘ x.2) := by
      rw [Tuple.eq_sort_iff]
      refine ⟨?_, fun i j hij _ => ?_⟩
      · have : (x.1 ∘ ⇑x.2) ∘ ⇑x.2⁻¹ = x.1 := by ext i; simp
        rw [this]; exact hx.monotone
      · have h1 : x.1 (x.2 (x.2⁻¹ i)) = x.1 i := by simp
        have h2 : x.1 (x.2 (x.2⁻¹ j)) = x.1 j := by simp
        simp only [Function.comp_apply, h1, h2] at *
        exact absurd (hx.injective ‹_›) (ne_of_lt hij)
    ext1
    · dsimp only; rw [← hs]; ext i; simp
    · dsimp only; rw [← hs, inv_inv]
  · intro f _
    dsimp only; congr 1; ext i; simp

/-- **Cauchy–Binet formula.** -/
theorem det_mul_eq_sum_smono {k m : ℕ} (A : Matrix (Fin k) (Fin m) R)
    (B : Matrix (Fin m) (Fin k) R) :
    (A * B).det = ∑ g ∈ smono k m, (A.submatrix id g).det * (B.submatrix g id).det := by
  have step1 : (A * B).det
      = ∑ f : Fin k → Fin m, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    simp only [det_apply', mul_apply, prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
      submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [step1, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun f : Fin k → Fin m => Function.Injective f)]
  have hzero : ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => ¬ Function.Injective f),
      (∏ i, B (f i) i) * (A.submatrix id f).det = 0 := by
    refine Finset.sum_eq_zero fun f hf => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Injective] at hf
    push_neg at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    rw [det_zero_of_column_eq hne (fun r => by simp [hij]), mul_zero]
  rw [hzero, add_zero, sum_injective_eq]
  refine Finset.sum_congr rfl fun g _ => ?_
  have : ∀ π : Perm (Fin k), (A.submatrix id (g ∘ π)).det
      = Perm.sign π * (A.submatrix id g).det := by
    intro π
    rw [show A.submatrix id (g ∘ π) = (A.submatrix id g).submatrix id π from rfl, det_permute']
  simp only [this]
  rw [det_apply' (B.submatrix g id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [submatrix_apply, id, Function.comp_apply]
  ring

section Principal

variable {m : ℕ}

/-- Principal-minor expansion (subset form):
`det (1 + diag(w) M) = ∑_S (∏_{i ∈ S} w i) det (M_{S,S})`. -/
theorem det_one_add_diagonal_mul_subsets (w : Fin m → R) (M : Matrix (Fin m) (Fin m) R) :
    (1 + diagonal w * M).det
      = ∑ S : Finset (Fin m), (∏ i ∈ S, w i) * (Matrix.of fun i j : S => M i j).det := by
  rw [det_apply']
  simp only [Matrix.add_apply, Matrix.one_apply, diagonal_mul]
  have hexp : ∀ σ : Perm (Fin m), ∏ i, ((if σ i = i then (1 : R) else 0) + w (σ i) * M (σ i) i)
      = ∑ S : Finset (Fin m), (∏ i ∈ S, w (σ i) * M (σ i) i)
          * ∏ i ∈ Finset.univ \ S, (if σ i = i then (1 : R) else 0) := by
    intro σ
    rw [show (fun i => (if σ i = i then (1 : R) else 0) + w (σ i) * M (σ i) i)
        = fun i => w (σ i) * M (σ i) i + (if σ i = i then (1 : R) else 0) from
        funext fun i => add_comm _ _, Finset.prod_add, Finset.powerset_univ]
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  -- the permutations contributing are those fixing the complement of `S`
  rw [det_apply', Finset.mul_sum]
  have key : ∀ τ : Perm S, (∏ i ∈ S, w i) * (Perm.sign τ * ∏ i : S, (Matrix.of fun i j : S => M i j) (τ i) i)
      = Perm.sign (Perm.ofSubtype τ) * ((∏ i ∈ S, w (Perm.ofSubtype τ i) * M (Perm.ofSubtype τ i) i)
        * ∏ i ∈ Finset.univ \ S, (if Perm.ofSubtype τ i = i then (1 : R) else 0)) := by
    intro τ
    have h1 : ∏ i ∈ Finset.univ \ S, (if Perm.ofSubtype τ i = i then (1 : R) else 0) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [Finset.mem_sdiff] at hi
      rw [Perm.ofSubtype_apply_of_not_mem τ hi.2, if_pos rfl]
    have h2 : ∏ i ∈ S, w (Perm.ofSubtype τ i) * M (Perm.ofSubtype τ i) i
        = (∏ i ∈ S, w i) * ∏ i : S, M (τ i) i := by
      rw [← Finset.prod_attach S, Finset.prod_mul_distrib]
      congr 1
      · rw [← Finset.prod_attach S (f := w)]
        simp only [← Finset.univ_eq_attach]
        rw [show (∏ x : S, w (Perm.ofSubtype τ x)) = ∏ x : S, w (τ x) from
          Finset.prod_congr rfl fun x _ => by rw [Perm.ofSubtype_apply_coe]]
        exact Fintype.prod_equiv τ _ _ (fun _ => rfl)
      · simp only [← Finset.univ_eq_attach]
        exact Finset.prod_congr rfl fun x _ => by rw [Perm.ofSubtype_apply_coe]
    rw [h1, mul_one, h2, Perm.sign_ofSubtype]
    simp only [Matrix.of_apply]
    rw [mul_left_comm]
    congr 2
    convert rfl
  symm
  refine Finset.sum_bij_ne_zero (fun τ _ _ => Perm.ofSubtype τ) (fun _ _ _ => Finset.mem_univ _)
    (fun τ₁ _ _ τ₂ _ _ h => Perm.ofSubtype_injective h) ?_ (fun τ _ _ => key τ)
  intro σ _ hσ
  have hfix : ∀ i, i ∉ S → σ i = i := by
    intro i hi
    by_contra hne
    apply hσ
    rw [Finset.prod_eq_zero (s := Finset.univ \ S) (i := i) (by simp [hi]) (by simp [hne]),
      mul_zero, mul_zero]
  have h₁ : ∀ x, (σ x ∈ S) ↔ (x ∈ S) := by
    intro x
    constructor
    · intro hx
      by_contra hxS
      rw [hfix x hxS] at hx
      exact hxS hx
    · intro hx
      by_contra hσx
      have := hfix (σ x) hσx
      rw [σ.injective this] at hσx
      exact hσx hx
  have hof : Perm.ofSubtype (σ.subtypePerm h₁) = σ :=
    Perm.ofSubtype_subtypePerm _ fun x hx => by by_contra hxS; exact hx (hfix x hxS)
  exact ⟨σ.subtypePerm h₁, Finset.mem_univ _, by rw [key, hof]; exact hσ, hof⟩

/-- Principal-minor expansion:
`det (1 + diag(w) M) = ∑_k ∑_{f : Fin k → Fin m strictly increasing} (∏ w ∘ f) det (M_{f,f})`. -/
theorem det_one_add_diagonal_mul (w : Fin m → R) (M : Matrix (Fin m) (Fin m) R) :
    (1 + diagonal w * M).det
      = ∑ k ∈ Finset.range (m + 1), ∑ f ∈ smono k m, (∏ i, w (f i)) * (M.submatrix f f).det := by
  rw [det_one_add_diagonal_mul_subsets,
    ← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (m + 1))
      (fun S _ => by
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact (Finset.card_le_univ S).trans (by simp))]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_bij' (fun S hS => ((S.orderEmbOfFin (by simpa using hS)) : Fin k → Fin m))
    (fun f _ => Finset.univ.image f) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_smono]
    exact (S.orderEmbOfFin _).strictMono
  · intro f hf
    rw [mem_smono] at hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  · intro S hS
    exact Finset.image_orderEmbOfFin_univ S _
  · intro f hf
    rw [mem_smono] at hf
    funext i
    have := Finset.orderEmbOfFin_unique (s := Finset.univ.image f)
      (by rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin])
      (fun x => Finset.mem_image_of_mem f (Finset.mem_univ x)) hf
    exact (congrFun this i).symm
  · intro S hS
    have hk : S.card = k := by simpa using hS
    congr 1
    · conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S hk]
      rw [Finset.prod_image (fun x _ y _ h => (S.orderEmbOfFin hk).injective h)]
    · rw [← det_submatrix_equiv_self (S.orderIsoOfFin hk).toEquiv]
      congr 1

end Principal

end AvgRS.Formal
