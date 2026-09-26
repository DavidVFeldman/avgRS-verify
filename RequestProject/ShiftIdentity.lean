module

public import RequestProject.Tableaux

@[expose] public section

namespace AvgRS

open Finset

lemma card_le_sum_of_pos {s : Multiset ℕ} (h : ∀ x ∈ s, 0 < x) : Multiset.card s ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, Multiset.sum_cons]
    have := h a (Multiset.mem_cons_self a s)
    have := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    omega

lemma hook_char {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x)
    (h2 : Multiset.card (s.filter (fun x => 2 ≤ x)) < 2) (hs : s ≠ 0) :
    s = hookParts (s.sum - Multiset.card s) (Multiset.card s - 1) := by
  have hsplit := Multiset.filter_add_not (fun x => 2 ≤ x) s
  set u := s.filter (fun x => 2 ≤ x)
  set t := s.filter (fun x => ¬ 2 ≤ x)
  have ht : t = Multiset.replicate (Multiset.card t) 1 := by
    apply Multiset.eq_replicate_of_mem
    intro x hx
    rw [Multiset.mem_filter] at hx
    have := hpos x hx.1
    omega
  rcases Nat.lt_succ_iff.mp h2 |>.lt_or_eq with h0 | h1
  · have hu : u = 0 := Multiset.card_eq_zero.mp (by omega)
    rw [hu, zero_add] at hsplit
    rw [← hsplit, ht]
    obtain ⟨c, hc⟩ : ∃ c, Multiset.card t = c + 1 := by
      refine ⟨Multiset.card t - 1, ?_⟩
      have : Multiset.card t ≠ 0 := by
        intro h; apply hs; rw [← hsplit, Multiset.card_eq_zero.mp h]
      omega
    rw [hc]
    simp [hookParts, Multiset.replicate_succ]
    omega
  · obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp h1
    have hx2 : 2 ≤ x := by
      have : x ∈ u := by rw [hx]; exact Multiset.mem_singleton_self x
      exact (Multiset.mem_filter.mp this).2
    have hts : t.sum = Multiset.card t := by rw [ht]; simp
    rw [hx] at hsplit
    rw [← hsplit]
    conv_lhs => rw [ht]
    simp only [hookParts, Multiset.card_add, Multiset.card_singleton, Multiset.sum_add,
      Multiset.sum_singleton]
    rw [hts, Multiset.singleton_add]
    congr 1
    · omega
    · congr 1; omega

lemma twoCol_char {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) (h3 : ∀ x ∈ s, x < 3) :
    s = twoColParts (Multiset.card (s.filter (fun x => 2 ≤ x)))
      (Multiset.card (s.filter (fun x => ¬ 2 ≤ x))) := by
  have hsplit := Multiset.filter_add_not (fun x => 2 ≤ x) s
  conv_lhs => rw [← hsplit]
  unfold twoColParts
  congr 1
  · apply Multiset.eq_replicate_of_mem
    intro x hx
    rw [Multiset.mem_filter] at hx
    have := h3 x hx.1
    omega
  · apply Multiset.eq_replicate_of_mem
    intro x hx
    rw [Multiset.mem_filter] at hx
    have := hpos x hx.1
    omega


/-- `f_λ`, the number of standard Young tableaux of shape `λ`. -/
def numSYT {n : ℕ} (p : n.Partition) : ℕ := syt p.parts

/-- The box in row `i`, column `j` (both `1`-indexed) belongs to the Young diagram of `p`,
i.e. `λ_i ≥ j`; equivalently, at least `i` parts of `p` are `≥ j`. -/
def HasBox {n : ℕ} (p : n.Partition) (i j : ℕ) : Prop :=
  i ≤ Multiset.card (p.parts.filter (fun x => j ≤ x))

instance {n : ℕ} (p : n.Partition) (i j : ℕ) : Decidable (HasBox p i j) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- `∑_{λ ⊢ N, (i,j) ∉ λ} f_λ²`: the number of permutations of `N` whose Robinson–Schensted
shape does not contain the box `(i,j)`. -/
def boxAbsentSum (N i j : ℕ) : ℕ := ∑ p : N.Partition with ¬ HasBox p i j, numSYT p ^ 2

/-- The hook partition `(N - b + 1, 1^b)` of `N + 1`. -/
def hookPartition (N b : ℕ) (hb : b ≤ N) : (N + 1).Partition where
  parts := hookParts (N - b) b
  parts_pos := by
    intro i hi
    simp only [hookParts, Multiset.mem_cons, Multiset.mem_replicate] at hi
    omega
  parts_sum := by simp [hookParts]; omega

/-- The partition `(2^j, 1^(N - 2j))` of `N`. -/
def twoColPartition (N j : ℕ) (hj : 2 * j ≤ N) : N.Partition where
  parts := twoColParts j (N - 2 * j)
  parts_pos := by
    intro i hi
    simp only [twoColParts, Multiset.mem_add, Multiset.mem_replicate] at hi
    omega
  parts_sum := by simp [twoColParts]; omega

theorem boxAbsentSum_hook (N : ℕ) : boxAbsentSum (N + 1) 2 2 = (2 * N).choose N := by
  rw [← Nat.sum_range_choose_sq, boxAbsentSum]
  symm
  refine Finset.sum_bij' (fun b hb => hookPartition N b (by simpa [Nat.lt_succ_iff] using hb))
    (fun p _ => Multiset.card p.parts - 1) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, hookPartition, hookParts,
      not_le]
    rw [Multiset.filter_cons, Multiset.filter_eq_nil.mpr (by
      intro x hx; rw [Multiset.mem_replicate] at hx; omega)]
    split_ifs <;> simp
  · intro p hp
    simp only [Finset.mem_range]
    have := card_le_sum_of_pos (fun x hx => p.parts_pos hx)
    rw [p.parts_sum] at this
    omega
  · intro b hb
    simp [hookPartition, hookParts]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le] at hp
    have hne : p.parts ≠ 0 := by
      intro h; have := p.parts_sum; rw [h] at this; simp at this
    have hc := hook_char (fun x hx => p.parts_pos hx) hp hne
    have hcard := card_le_sum_of_pos (fun x hx => p.parts_pos hx)
    have hcard0 : Multiset.card p.parts ≠ 0 := by simpa using hne
    rw [p.parts_sum] at hc hcard
    set c := Multiset.card p.parts
    ext1
    simp only [hookPartition]
    conv_rhs => rw [hc]
    congr 1
    omega
  · intro b hb
    simp only [numSYT, hookPartition, syt_hookParts]
    rw [Nat.sub_add_cancel (by simpa [Nat.lt_succ_iff] using hb)]

theorem boxAbsentSum_twoCol (N : ℕ) :
    ((N + 1 : ℕ) : ℤ) * (boxAbsentSum N 1 3 : ℤ) = ((2 * N).choose N : ℤ) := by
  rw [← sum_range_ballot_sq N]
  congr 1
  rw [boxAbsentSum]
  push_cast
  symm
  refine Finset.sum_bij' (fun j hj => twoColPartition N j (by
      have := Finset.mem_range.mp hj; omega))
    (fun p _ => Multiset.card (p.parts.filter (fun x => 2 ≤ x))) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, twoColPartition, twoColParts,
      not_le, Nat.lt_one_iff, Multiset.card_eq_zero]
    apply Multiset.filter_eq_nil.mpr
    intro x hx
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hx
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le, Nat.lt_one_iff,
      Multiset.card_eq_zero, Multiset.filter_eq_nil, not_le] at hp
    have hc := twoCol_char (fun x hx => p.parts_pos hx) hp
    have hs := p.parts_sum
    set a := Multiset.card (p.parts.filter (fun x => 2 ≤ x))
    set b := Multiset.card (p.parts.filter (fun x => ¬ 2 ≤ x))
    rw [hc] at hs
    simp [twoColParts] at hs
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [twoColPartition, twoColParts, Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega),
      Multiset.filter_eq_nil.mpr (by intro x hx; rw [Multiset.mem_replicate] at hx; omega)]
    simp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le, Nat.lt_one_iff,
      Multiset.card_eq_zero, Multiset.filter_eq_nil, not_le] at hp
    have hc := twoCol_char (fun x hx => p.parts_pos hx) hp
    have hs := p.parts_sum
    set a := Multiset.card (p.parts.filter (fun x => 2 ≤ x))
    set b := Multiset.card (p.parts.filter (fun x => ¬ 2 ≤ x))
    rw [hc] at hs
    simp [twoColParts] at hs
    ext1
    simp only [twoColPartition]
    conv_rhs => rw [hc]
    congr 1
    omega
  · intro j hj
    have := Finset.mem_range.mp hj
    simp only [numSYT, twoColPartition, syt_twoColParts]
    congr 2
    omega

theorem boxAbsentSum_twoCol_eq_catalan (N : ℕ) : boxAbsentSum N 1 3 = catalan N := by
  have h := boxAbsentSum_twoCol N
  have h2 := succ_mul_catalan_eq_centralBinom N
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  have : (N + 1) * boxAbsentSum N 1 3 = (N + 1) * catalan N := by
    rw [h2]; exact_mod_cast h
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos N) this

/-- **Theorem 2.4 (`thm:k2`, case `k = 2` of the shift identity).** -/
theorem shift_identity_two (N : ℕ) :
    boxAbsentSum (N + 1) 2 2 = (N + 1) * boxAbsentSum N 1 3 := by
  have h := boxAbsentSum_twoCol N
  rw [boxAbsentSum_hook]
  exact_mod_cast h.symm

end AvgRS
