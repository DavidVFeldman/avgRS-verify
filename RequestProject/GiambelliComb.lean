module

public import RequestProject.GiambelliAlg

@[expose] public section

/-!
# Giambelli's formula for `f_λ / |λ|!`

We show that `f_λ / n! = det (F(a_i | b_j))` by checking that the Giambelli determinant satisfies
the branching recursion `n · G(λ) = ∑_{corners c} G(λ ∖ c)` (`GD_branch`), matching the corners
of `λ` with the moves of its Frobenius coordinates.
-/

namespace AvgRS

open Finset

/-- The column lengths `λ'_j = #{i : λ_i > j}` of a multiset of row lengths. -/
def colM (s : Multiset ℕ) (j : ℕ) : ℕ := Multiset.card (s.filter (j < ·))

section MultisetFacts

lemma colM_cons (v : ℕ) (t : Multiset ℕ) (j : ℕ) :
    colM (v ::ₘ t) j = colM t j + if j < v then 1 else 0 := by
  unfold colM
  rw [Multiset.filter_cons]
  split_ifs <;> simp [add_comm]

lemma colM_removeBox {s : Multiset ℕ} {v : ℕ} (hv : v ∈ s) (hv1 : 1 ≤ v) (j : ℕ) :
    colM (removeBox s v) j + (if j = v - 1 then 1 else 0) = colM s j := by
  conv_rhs => rw [← Multiset.cons_erase hv]
  rw [colM_cons]
  unfold removeBox
  split_ifs <;> first | omega | (rw [colM_cons]; split_ifs <;> omega)

lemma removeBox_pos {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) {v : ℕ} :
    ∀ x ∈ removeBox s v, 0 < x := by
  intro x hx
  unfold removeBox at hx
  split_ifs at hx with h
  · exact hs x (Multiset.mem_of_mem_erase hx)
  · rcases Multiset.mem_cons.1 hx with rfl | hx
    · omega
    · exact hs x (Multiset.mem_of_mem_erase hx)

lemma mem_iff_colM {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) {v : ℕ} :
    v ∈ s ↔ 1 ≤ v ∧ colM s v < colM s (v - 1) := by
  have key : ∀ v, 1 ≤ v → Multiset.count v s + colM s v = colM s (v - 1) := by
    intro v hv
    have := card_filter_eq_col_sub (s := s) (x := v)
    rw [Multiset.count_eq_card_filter_eq]
    unfold colM
    rw [show s.filter (v - 1 < ·) = s.filter (v ≤ ·) from
      Multiset.filter_congr fun y _ => by omega]
    exact this
  constructor
  · intro h
    have h1 : 1 ≤ v := hs v h
    have := key v h1
    have := Multiset.count_pos.2 h
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    have := key v h1
    exact Multiset.count_pos.1 (by omega)

lemma eq_zero_of_colM {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) (h : colM s 0 = 0) : s = 0 := by
  unfold colM at h
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil] at h
  exact Multiset.eq_zero_of_forall_notMem fun x hx => h x hx (hs x hx)

end MultisetFacts

section Corners

variable {k : ℕ} {α β : ℕ → ℕ}

lemma GD_eq_zero_of_row {i i' : ℕ} (hi : i < k) (hi' : i' < k) (hne : i ≠ i')
    (h : α i = α i') : GD k α β = 0 := by
  unfold GD
  exact Matrix.det_zero_of_row_eq (i := (⟨i, hi⟩ : Fin k)) (j := ⟨i', hi'⟩)
    (by simp [Fin.ext_iff, hne]) (by funext j; simp [h])

lemma GD_eq_zero_of_col {j j' : ℕ} (hj : j < k) (hj' : j' < k) (hne : j ≠ j')
    (h : β j = β j') : GD k α β = 0 := by
  unfold GD
  exact Matrix.det_zero_of_column_eq (i := (⟨j, hj⟩ : Fin k)) (j := ⟨j', hj'⟩)
    (by simp [Fin.ext_iff, hne]) (by intro i; simp [h])

lemma cOf_of_lt {j : ℕ} (hj : j < k) : cOf k α β j = β j + j + 1 := by
  unfold cOf; rw [if_pos hj]

/-- A valid arm move: decreasing `α_i` by one keeps `α` strictly decreasing and nonnegative. -/
def ValidArm (k : ℕ) (α : ℕ → ℕ) (i : ℕ) : Prop := α i ≠ 0 ∧ (i + 1 = k ∨ α (i + 1) + 1 < α i)

instance (k : ℕ) (α : ℕ → ℕ) (i : ℕ) : Decidable (ValidArm k α i) := by
  unfold ValidArm; infer_instance

lemma arm_term_eq (hα : SAnti k α) {i : ℕ} (hi : i < k) :
    (if α i = 0 then 0 else GD k (Function.update α i (α i - 1)) β)
      = if ValidArm k α i then GD k (Function.update α i (α i - 1)) β else 0 := by
  by_cases h0 : α i = 0
  · simp [h0, ValidArm]
  · by_cases hv : ValidArm k α i
    · simp [h0, hv]
    · rw [if_neg h0, if_neg hv]
      have h1 : i + 1 < k := by by_contra h; exact hv ⟨h0, Or.inl (by omega)⟩
      have h2 := hα i (i + 1) (by omega) h1
      have h3 : α (i + 1) = α i - 1 := by
        by_contra h; exact hv ⟨h0, Or.inr (by omega)⟩
      refine GD_eq_zero_of_row hi h1 (by omega) ?_
      rw [Function.update_self, Function.update_of_ne (by omega), h3]

/-- The value of the Giambelli determinant after removing the corner at the end of column `j`. -/
noncomputable def cornerVal (k : ℕ) (α β : ℕ → ℕ) (j : ℕ) : ℚ :=
  if j < k then (if β j = 0 then GD (k - 1) α β else GD k α (Function.update β j (β j - 1)))
  else GD k (Function.update α (cOf k α β j - 1) (α (cOf k α β j - 1) - 1)) β

lemma leg_term_eq (hα : SAnti k α) (hβ : SAnti k β) {j : ℕ} (hj : j < k) :
    (if cOf k α β (j + 1) < cOf k α β j then cornerVal k α β j else 0)
      = (if β j = 0 then 0 else GD k α (Function.update β j (β j - 1)))
        + (if j = k - 1 then
            (if α (k - 1) = 0 ∧ β (k - 1) = 0 then GD (k - 1) α β else 0) else 0) := by
  unfold cornerVal
  rw [cOf_of_lt hj]
  simp only [hj, if_true]
  by_cases hb : β j = 0
  · have hjk := hβ.eq_last_of_eq_zero hj hb
    subst hjk
    have hc : cOf k α β (k - 1 + 1) < k - 1 + 1 ↔ α (k - 1) = 0 := by
      rw [show k - 1 + 1 = k by omega]
      have h1 := lt_cOf_iff (β := β) hα hβ (i := k - 1) (j := k) (by omega)
      have h2 := cOf_le_k (α := α) (β := β) (k := k) (j := k) le_rfl
      constructor
      · intro h; by_contra h'; have := h1.2 (by omega); omega
      · intro h; by_contra h'; have := h1.1 (by omega); omega
    simp only [hb, if_true, zero_add, and_true]
    by_cases ha : α (k - 1) = 0
    · rw [if_pos (hc.2 ha), if_pos ha]
    · rw [if_neg (fun h => ha (hc.1 h)), if_neg ha]
  · rw [if_neg hb]
    have e : (if j = k - 1 then
        (if α (k - 1) = 0 ∧ β (k - 1) = 0 then GD (k - 1) α β else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2.2) hb
      · rfl
      · rfl
    rw [e, add_zero]
    split_ifs with hc
    · rfl
    · symm
      have h1 : j + 1 < k := by
        by_contra h
        have := cOf_le_k (α := α) (β := β) (k := k) (j := j + 1) (by omega)
        omega
      rw [cOf_of_lt h1] at hc
      have h2 := hβ j (j + 1) (by omega) h1
      refine GD_eq_zero_of_col hj h1 (by omega) ?_
      rw [Function.update_self, Function.update_of_ne (by omega)]
      omega

end Corners

section Arms

variable {k : ℕ} {α β : ℕ → ℕ}

lemma validArm_ge (hα : SAnti k α) {i : ℕ} (hi : i < k) (hv : ValidArm k α i) : k ≤ α i + i := by
  rcases hv with ⟨h0, h | h⟩
  · omega
  · by_cases h1 : i + 1 < k
    · have := hα.ge h1; omega
    · omega

lemma cOf_validArm (hα : SAnti k α) (hβ : SAnti k β) {i : ℕ} (hi : i < k)
    (hv : ValidArm k α i) : cOf k α β (α i + i) = i + 1 := by
  have hge := validArm_ge hα hi hv
  refine eq_of_forall_lt_iff fun i' => ?_
  by_cases hi' : i' < k
  · rw [lt_cOf_iff hα hβ hi']
    constructor
    · intro h
      by_contra hc
      have h1 : i + 1 < k := by omega
      rcases hv with ⟨_, h2 | h2⟩
      · omega
      · have := hα.add_le (i := i + 1) (i' := i') (by omega) hi'
        omega
    · intro h
      have := hα.add_le (i := i') (i' := i) (by omega) hi
      omega
  · have := cOf_le_k (α := α) (β := β) (k := k) (j := α i + i) hge
    omega

lemma cOf_validArm_succ (hα : SAnti k α) (hβ : SAnti k β) {i : ℕ} (hi : i < k) :
    cOf k α β (α i + i + 1) ≤ i := by
  by_contra hc
  have := (lt_cOf_iff hα hβ (i := i) (j := α i + i + 1) hi).1 (by omega)
  omega

lemma corner_arm (hα : SAnti k α) (hβ : SAnti k β) {j : ℕ} (hkj : k ≤ j)
    (hc : cOf k α β (j + 1) < cOf k α β j) :
    cOf k α β j - 1 < k ∧ ValidArm k α (cOf k α β j - 1) ∧
      α (cOf k α β j - 1) + (cOf k α β j - 1) = j := by
  have hle := cOf_le_k (α := α) (β := β) (k := k) (j := j) hkj
  have hik : cOf k α β j - 1 < k := by omega
  have h1 := (lt_cOf_iff hα hβ (i := cOf k α β j - 1) (j := j) hik).1 (by omega)
  have h2 : ¬ (j + 1 < α (cOf k α β j - 1) + (cOf k α β j - 1) + 1) := fun h =>
    absurd ((lt_cOf_iff hα hβ (i := cOf k α β j - 1) (j := j + 1) hik).2 h) (by omega)
  have heq : α (cOf k α β j - 1) + (cOf k α β j - 1) = j := by omega
  refine ⟨hik, ⟨by omega, ?_⟩, heq⟩
  by_cases h3 : cOf k α β j - 1 + 1 < k
  · right
    have h4 : ¬ (cOf k α β j - 1 + 1 < cOf k α β j) := by omega
    rw [lt_cOf_iff hα hβ h3] at h4
    omega
  · left; omega

/-- The arm moves correspond to the corners in columns `j ≥ k`. -/
lemma sum_arm_corners (hα : SAnti k α) (hβ : SAnti k β) {M : ℕ}
    (hM : ∀ i < k, α i + i < M) :
    ∑ j ∈ Ico k M, (if cOf k α β (j + 1) < cOf k α β j then cornerVal k α β j else 0)
      = ∑ i ∈ range k, (if ValidArm k α i then GD k (Function.update α i (α i - 1)) β else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun j => cOf k α β j - 1) (fun i => α i + i) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_Ico] at hj
    have := corner_arm hα hβ hj.1.1 hj.2
    simp only [mem_filter, mem_range]
    exact ⟨this.1, this.2.1⟩
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    have h1 := cOf_validArm hα hβ (β := β) hi.1 hi.2
    have h2 := cOf_validArm_succ hα hβ (β := β) hi.1
    simp only [mem_filter, mem_Ico]
    exact ⟨⟨validArm_ge hα hi.1 hi.2, hM i hi.1⟩, by omega⟩
  · intro j hj
    simp only [mem_filter, mem_Ico] at hj
    exact (corner_arm hα hβ hj.1.1 hj.2).2.2
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    show cOf k α β (α i + i) - 1 = i
    rw [cOf_validArm hα hβ hi.1 hi.2]; rfl
  · intro j hj
    simp only [mem_filter, mem_Ico] at hj
    unfold cornerVal
    rw [if_neg (by omega)]

end Arms

/-- The corners of the partition with Frobenius coordinates `(α | β)`, summed with the
Giambelli determinants of the smaller partitions, give `N · GD k α β`. -/
theorem sum_corners_eq {k N : ℕ} {α β : ℕ → ℕ} (h : FrobOK k N α β) :
    ∑ j ∈ range N, (if cOf k α β (j + 1) < cOf k α β j then cornerVal k α β j else 0)
      = (N : ℚ) * GD k α β := by
  have hN : (N : ℚ) = ((∑ i ∈ range k, α i + ∑ i ∈ range k, β i + k : ℕ) : ℚ) := by
    rw [h.2.2]
  rw [hN, GD_branch k α β h.1 h.2.1, ← Finset.sum_range_add_sum_Ico _ h.k_le,
    sum_arm_corners h.1 h.2.1 (M := N) (fun i hi => by have := h.bound hi; omega),
    Finset.sum_congr rfl fun j hj => leg_term_eq h.1 h.2.1 (mem_range.1 hj),
    Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_congr rfl fun i hi => (arm_term_eq (β := β) h.1 (mem_range.1 hi)).symm]
  simp only [mem_range]
  by_cases hk : 0 < k
  · simp only [show k - 1 < k by omega, if_true, hk, true_and]; ring
  · simp only [show ¬ k - 1 < k by omega, if_false, hk, false_and]; ring

section CornerData

lemma sum_update_pred {f : ℕ → ℕ} {i k : ℕ} (hi : i < k) (h0 : f i ≠ 0) :
    ∑ x ∈ range k, Function.update f i (f i - 1) x + 1 = ∑ x ∈ range k, f x := by
  rw [Finset.sum_update_of_mem (mem_range.2 hi),
    ← Finset.add_sum_erase _ _ (mem_range.2 hi), Finset.sdiff_singleton_eq_erase]
  omega

lemma SAnti.update_pred {k : ℕ} {f : ℕ → ℕ} (hf : SAnti k f) {i : ℕ} (h0 : f i ≠ 0)
    (hv : i + 1 < k → f (i + 1) + 1 < f i) : SAnti k (Function.update f i (f i - 1)) := by
  intro a b hab hb
  by_cases hbi : b = i
  · subst hbi
    rw [Function.update_self, Function.update_of_ne (by omega)]
    have := hf a b hab hb; omega
  · rw [Function.update_of_ne hbi]
    by_cases hai : a = i
    · subst hai
      rw [Function.update_self]
      have h1 := hv (by omega)
      by_cases hb1 : b = a + 1
      · subst hb1; omega
      · have := hf (a + 1) b (by omega) hb; omega
    · rw [Function.update_of_ne hai]; exact hf a b hab hb

variable {k N : ℕ} {α β : ℕ → ℕ}

/-- Removing a corner of the partition with Frobenius coordinates `(α | β)`. -/
theorem corner_data (h : FrobOK k (N + 1) α β) {j : ℕ}
    (hc : cOf k α β (j + 1) < cOf k α β j) :
    ∃ k' α' β', FrobOK k' N α' β' ∧
      (∀ j', cOf k' α' β' j' + (if j' = j then 1 else 0) = cOf k α β j') ∧
      GD k' α' β' = cornerVal k α β j := by
  have hα := h.1
  have hβ := h.2.1
  by_cases hj : j < k
  · by_cases hb : β j = 0
    · -- the Durfee corner
      have hjk := hβ.eq_last_of_eq_zero hj hb
      subst hjk
      have ha : α (k - 1) = 0 := by
        by_contra ha
        have h1 := (lt_cOf_iff hα hβ (β := β) (i := k - 1) (j := k) hj).2 (by omega)
        rw [cOf_of_lt hj, show k - 1 + 1 = k by omega] at hc
        omega
      refine ⟨k - 1, α, β, ⟨fun a b hab hb' => hα a b hab (by omega),
        fun a b hab hb' => hβ a b hab (by omega), ?_⟩, ?_, ?_⟩
      · have := h.2.2
        obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ] at this
        simp only [Nat.add_sub_cancel] at ha hb ⊢
        omega
      · intro j'
        by_cases h1 : j' < k - 1
        · rw [cOf_of_lt h1, cOf_of_lt (by omega), if_neg (by omega)]
        · by_cases h2 : j' = k - 1
          · subst h2
            rw [if_pos rfl, cOf_of_lt hj, hb]
            unfold cOf
            rw [if_neg (lt_irrefl _), Finset.filter_true_of_mem fun i hi => by
              have := hα.ge (i := i) (by simp at hi; omega); omega]
            simp
          · rw [if_neg h2]
            unfold cOf
            rw [if_neg (by omega), if_neg (by omega)]
            obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            simp only [Nat.add_sub_cancel] at ha ⊢
            rw [Finset.range_add_one, Finset.filter_insert, if_neg (by omega), add_zero]
      · unfold cornerVal; rw [if_pos hj, if_pos hb]
    · -- a leg move
      refine ⟨k, α, Function.update β j (β j - 1), ⟨hα, hβ.update_pred hb fun h1 => ?_, ?_⟩,
        ?_, ?_⟩
      · rw [cOf_of_lt hj, cOf_of_lt h1] at hc; omega
      · have := h.2.2; have := sum_update_pred hj hb; omega
      · intro j'
        by_cases h1 : j' < k
        · rw [cOf_of_lt h1, cOf_of_lt h1]
          by_cases h2 : j' = j
          · subst h2; rw [Function.update_self, if_pos rfl]; omega
          · rw [Function.update_of_ne h2, if_neg h2]
        · unfold cOf; rw [if_neg h1, if_neg h1, if_neg (by omega), add_zero]
      · unfold cornerVal; rw [if_pos hj, if_neg hb]
  · -- an arm move
    obtain ⟨hik, hv, heq⟩ := corner_arm hα hβ (by omega) hc
    set i := cOf k α β j - 1 with hi
    refine ⟨k, Function.update α i (α i - 1), β,
      ⟨hα.update_pred hv.1 fun h1 => ?_, hβ, ?_⟩, ?_, ?_⟩
    · rcases hv.2 with h2 | h2
      · omega
      · exact h2
    · have := h.2.2; have := sum_update_pred hik hv.1; omega
    · intro j'
      by_cases h1 : j' < k
      · rw [cOf_of_lt h1, cOf_of_lt h1, if_neg (by omega), add_zero]
      · unfold cOf
        rw [if_neg h1, if_neg h1, card_filter, card_filter]
        have e : ∀ x ∈ range k, (if j' < α x + x + 1 then 1 else 0)
            = (if j' < Function.update α i (α i - 1) x + x + 1 then 1 else 0)
              + (if x = i then (if j' = j then 1 else 0) else 0) := by
          intro x _
          by_cases hx : x = i
          · rw [hx, Function.update_self, if_pos rfl]
            have := hv.1
            split_ifs <;> omega
          · rw [Function.update_of_ne hx, if_neg hx, add_zero]
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq',
          if_pos (mem_range.2 hik)]
    · unfold cornerVal; rw [if_neg hj]

end CornerData

/-- `f_λ / N! = GD` for the partition `λ` with Frobenius coordinates `(α | β)`, where `λ` is
given by its multiset of row lengths `s`. -/
theorem syt_div_eq_GD : ∀ (N : ℕ) (s : Multiset ℕ) (k : ℕ) (α β : ℕ → ℕ), (∀ x ∈ s, 0 < x) →
    FrobOK k N α β → (∀ j, colM s j = cOf k α β j) →
    (syt s : ℚ) / N.factorial = GD k α β := by
  intro N
  induction N with
  | zero =>
    intro s k α β hs h hc
    have hk : k = 0 := by have := h.k_le; omega
    subst hk
    have : s = 0 := eq_zero_of_colM hs (by rw [hc 0]; simp [cOf])
    subst this
    simp [syt_zero, GD]
  | succ N ih =>
    intro s k α β hs h hc
    have hs0 : s ≠ 0 := by
      rintro rfl
      have h0 := hc 0
      have hk : 0 < k := by
        by_contra hk
        have := h.2.2
        simp [show k = 0 by omega] at this
      rw [cOf_of_lt hk] at h0
      simp [colM] at h0
    rw [syt_of_ne_zero hs0, Nat.cast_sum]
    have hterm : ∀ v ∈ s.toFinset,
        (syt (removeBox s v) : ℚ) = N.factorial * cornerVal k α β (v - 1) := by
      intro v hv
      rw [Multiset.mem_toFinset] at hv
      have hv' := (mem_iff_colM hs).1 hv
      have hcorner : cOf k α β (v - 1 + 1) < cOf k α β (v - 1) := by
        rw [← hc, ← hc, show v - 1 + 1 = v by omega]; exact hv'.2
      obtain ⟨k', α', β', h', hcol, hGD⟩ := corner_data h hcorner
      have := ih (removeBox s v) k' α' β' (removeBox_pos hs) h' (fun j => by
        have e1 := colM_removeBox hv hv'.1 j
        have e2 := hcol j
        rw [hc j] at e1
        omega)
      rw [← hGD, ← this]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum : ∑ v ∈ s.toFinset, cornerVal k α β (v - 1)
        = ∑ j ∈ range (N + 1),
            (if cOf k α β (j + 1) < cOf k α β j then cornerVal k α β j else 0) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_nbij' (fun v => v - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
      · intro v hv
        rw [Multiset.mem_toFinset] at hv
        have hv' := (mem_iff_colM hs).1 hv
        simp only [mem_filter, mem_range]
        refine ⟨?_, ?_⟩
        · by_contra hlt
          have := cOf_eq_zero (α := α) (β := β) (fun i hi => h.bound hi) h.k_le
            (show N + 1 ≤ v - 1 by omega)
          rw [← hc] at this; omega
        · rw [← hc, ← hc, show v - 1 + 1 = v by omega]; exact hv'.2
      · intro j hj
        simp only [mem_filter, mem_range] at hj
        beta_reduce
        rw [Multiset.mem_toFinset, mem_iff_colM hs]
        refine ⟨by omega, ?_⟩
        rw [hc, hc, Nat.add_sub_cancel]; exact hj.2
      · intro v hv
        rw [Multiset.mem_toFinset] at hv
        have := hs v hv
        simp only; omega
      · intro j _; simp
      · intro v _; rfl
    rw [hsum, sum_corners_eq h, Nat.factorial_succ]
    push_cast
    field_simp

end AvgRS
