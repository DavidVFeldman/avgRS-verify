module

public import RequestProject.ShiftProof

@[expose] public section

namespace AvgRS

open Finset
open scoped Nat

/-! ### A crude bound on `f_λ` inside a fat hook -/

lemma mem_removeBox_pos {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) (v : ℕ) :
    ∀ x ∈ removeBox s v, 0 < x := by
  intro x hx
  unfold removeBox at hx
  split_ifs at hx with h
  · exact hpos x (Multiset.mem_of_mem_erase hx)
  · rcases Multiset.mem_cons.mp hx with rfl | hx
    · omega
    · exact hpos x (Multiset.mem_of_mem_erase hx)

lemma sum_removeBox {s : Multiset ℕ} {v : ℕ} (hv : v ∈ s) (hv0 : 0 < v) :
    (removeBox s v).sum + 1 = s.sum := by
  have h1 := Multiset.sum_erase hv
  unfold removeBox
  split_ifs with h
  · obtain rfl : v = 1 := by omega
    omega
  · simp; omega

lemma card_filter_removeBox_le {s : Multiset ℕ} {v : ℕ} (hv : v ∈ s) (c : ℕ) :
    Multiset.card ((removeBox s v).filter (fun x => c ≤ x)) ≤
      Multiset.card (s.filter (fun x => c ≤ x)) := by
  have hle : Multiset.card ((s.erase v).filter (fun x => c ≤ x)) ≤
      Multiset.card (s.filter (fun x => c ≤ x)) :=
    Multiset.card_le_card (Multiset.filter_le_filter _ (Multiset.erase_le v s))
  unfold removeBox
  split_ifs with h
  · exact hle
  · rw [Multiset.filter_cons]
    split_ifs with hc
    · have e : s.filter (fun x => c ≤ x) = v ::ₘ (s.erase v).filter (fun x => c ≤ x) := by
        conv_lhs => rw [← Multiset.cons_erase hv]
        exact Multiset.filter_cons_of_pos _ (by omega)
      rw [e]
      simp
    · simpa using hle

lemma card_toFinset_le_of_fatHook {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) {a b : ℕ}
    (hab : Multiset.card (s.filter (fun x => b + 1 ≤ x)) ≤ a) :
    s.toFinset.card ≤ a + b := by
  have hsplit : s.toFinset = s.toFinset.filter (fun x => x ≤ b) ∪
      s.toFinset.filter (fun x => ¬ x ≤ b) := (Finset.filter_union_filter_not_eq _ _).symm
  rw [hsplit]
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (s.toFinset.filter (fun x => x ≤ b)).card ≤ b := by
    calc (s.toFinset.filter (fun x => x ≤ b)).card ≤ (Finset.Icc 1 b).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Multiset.mem_toFinset] at hx
          have := hpos x hx.1
          simp only [Finset.mem_Icc]; omega
      _ = b := by simp
  have h2 : (s.toFinset.filter (fun x => ¬ x ≤ b)).card ≤ a := by
    calc (s.toFinset.filter (fun x => ¬ x ≤ b)).card
        ≤ (s.filter (fun x => b + 1 ≤ x)).toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_filter] at hx ⊢
          exact ⟨hx.1, by omega⟩
      _ ≤ Multiset.card (s.filter (fun x => b + 1 ≤ x)) := Multiset.toFinset_card_le _
      _ ≤ a := hab
  omega

/-- If `λ` lies in the fat hook `H(a,b)` (i.e. `λ_{a+1} ≤ b`), then `f_λ ≤ (a+b)^{|λ|}`. -/
theorem syt_le_of_fatHook (a b : ℕ) :
    ∀ (n : ℕ) (s : Multiset ℕ), s.sum = n → (∀ x ∈ s, 0 < x) →
      Multiset.card (s.filter (fun x => b + 1 ≤ x)) ≤ a → syt s ≤ (a + b) ^ n := by
  intro n
  induction n with
  | zero =>
    intro s hs hpos _
    have : s = 0 := by
      by_contra hne
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      have := hpos x hx
      have := Multiset.le_sum_of_mem hx
      omega
    subst this
    simp [syt_zero]
  | succ n ih =>
    intro s hs hpos hab
    have hne : s ≠ 0 := by rintro rfl; simp at hs
    rw [syt_of_ne_zero hne]
    calc ∑ v ∈ s.toFinset, syt (removeBox s v)
        ≤ ∑ v ∈ s.toFinset, (a + b) ^ n := by
          apply Finset.sum_le_sum
          intro v hv
          rw [Multiset.mem_toFinset] at hv
          apply ih
          · have := sum_removeBox hv (hpos v hv); omega
          · exact mem_removeBox_pos hpos v
          · exact (card_filter_removeBox_le hv _).trans hab
      _ = s.toFinset.card * (a + b) ^ n := by simp
      _ ≤ (a + b) * (a + b) ^ n :=
          Nat.mul_le_mul_right _ (card_toFinset_le_of_fatHook hpos hab)
      _ = (a + b) ^ (n + 1) := by ring

lemma card_partition_le (N : ℕ) : Fintype.card N.Partition ≤ 2 ^ N := by
  calc Fintype.card N.Partition ≤ Fintype.card (Composition N) :=
        Fintype.card_le_of_surjective _ Nat.Partition.ofComposition_surj
    _ = 2 ^ (N - 1) := composition_card N
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `∑_{λ ⊢ N, λ_m < n} f_λ² ≤ 2^N (m+n-2)^{2N}`. -/
theorem boxAbsentSum_le (N m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    boxAbsentSum N m n ≤ 2 ^ N * ((m - 1 + (n - 1)) ^ N) ^ 2 := by
  unfold boxAbsentSum
  calc ∑ p : N.Partition with ¬ HasBox p m n, numSYT p ^ 2
      ≤ ∑ p : N.Partition with ¬ HasBox p m n, ((m - 1 + (n - 1)) ^ N) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le] at hp
        apply Nat.pow_le_pow_left
        apply syt_le_of_fatHook _ _ N p.parts p.parts_sum (fun x hx => p.parts_pos hx)
        rw [show n - 1 + 1 = n by omega]
        omega
    _ ≤ ∑ _p : N.Partition, ((m - 1 + (n - 1)) ^ N) ^ 2 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Fintype.card N.Partition * ((m - 1 + (n - 1)) ^ N) ^ 2 := by simp
    _ ≤ 2 ^ N * ((m - 1 + (n - 1)) ^ N) ^ 2 :=
        Nat.mul_le_mul_right _ (card_partition_le N)

/-! ### The function `F` -/

/-- **The average Robinson–Schensted tableau** (Definition 1.3, in the form of
Proposition 1.6, `prop:series`): `F(m,n) = ∑_{N ≥ 0} (1/N!) ∑_{λ ⊢ N, λ_m ≤ n-1} f_λ²`, i.e.
`F(m,n) = ∑_N P(T(m,n) > N) = E T(m,n)`, the expected arrival time of the box `(m,n)`
in Plancherel growth, which is also `lim_N (1/N!) ∑_{π ∈ S_N} P_π(m,n)`. -/
noncomputable def avgEntry (m n : ℕ) : ℝ := ∑' N : ℕ, (boxAbsentSum N m n : ℝ) / N !

theorem summable_avgEntry (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Summable (fun N : ℕ => (boxAbsentSum N m n : ℝ) / N !) := by
  set c : ℝ := 2 * ((m - 1 + (n - 1) : ℕ) : ℝ) ^ 2
  refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
    (Real.summable_pow_div_factorial c)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := boxAbsentSum_le N m n hm hn
  calc (boxAbsentSum N m n : ℝ) ≤ ((2 ^ N * ((m - 1 + (n - 1)) ^ N) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast this
    _ = c ^ N := by
        push_cast [c]
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 N]


lemma boxAbsentSum_zero (i j : ℕ) (hi : 1 ≤ i) : boxAbsentSum 0 i j = 1 := by
  unfold boxAbsentSum
  rw [Finset.sum_eq_single_of_mem (default : (0 : ℕ).Partition)]
  · have : (default : (0 : ℕ).Partition).parts = 0 := by
      have h1 := card_le_sum_of_pos (fun x hx => (default : (0 : ℕ).Partition).parts_pos hx)
      rw [(default : (0 : ℕ).Partition).parts_sum] at h1
      exact Multiset.card_eq_zero.mp (by omega)
    simp [numSYT, syt_zero]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le]
    have := Multiset.card_le_card (Multiset.filter_le (fun x => j ≤ x)
      (default : (0 : ℕ).Partition).parts)
    have h0 : Multiset.card (default : (0 : ℕ).Partition).parts = 0 := by
      have h1 := card_le_sum_of_pos (fun x hx => (default : (0 : ℕ).Partition).parts_pos hx)
      rw [(default : (0 : ℕ).Partition).parts_sum] at h1
      omega
    omega
  · intro b _ hb
    exact absurd (Subsingleton.elim b default) hb

/-- Shifting the series defining `F(k,k)` by one step. -/
theorem avgEntry_diag_eq_of_shift (k : ℕ) (hk : 2 ≤ k)
    (h : ∀ N, boxAbsentSum (N + 1) k k = (N + 1) * boxAbsentSum N (k - 1) (k + 1)) :
    avgEntry k k = avgEntry (k - 1) (k + 1) + 1 := by
  unfold avgEntry
  rw [(summable_avgEntry k k (by omega) (by omega)).tsum_eq_zero_add, boxAbsentSum_zero _ _ (by omega)]
  simp only [Nat.cast_one, Nat.factorial_zero, div_one]
  rw [add_comm]
  congr 1
  refine tsum_congr fun N => ?_
  rw [h N, Nat.factorial_succ]
  push_cast
  have : (N ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Theorem 2.4 / Proposition 1.10:** `F(2,2) = F(1,3) + 1`. -/
theorem avgEntry_two_two : avgEntry 2 2 = avgEntry 1 3 + 1 :=
  avgEntry_diag_eq_of_shift 2 le_rfl shift_identity_two

/-- **Corollary 5.15** (`cor:Fshift`), derived from any proof of Giambelli's formula:
`F(k,k) = F(k-1,k+1) + 1` for every `k ≥ 2`. -/
theorem avgEntry_diag_of_giambelli (hG : GiambelliFormula) (k : ℕ) (hk : 2 ≤ k) :
    avgEntry k k = avgEntry (k - 1) (k + 1) + 1 :=
  avgEntry_diag_eq_of_shift k hk (fun N => shift_identity_of_giambelli hG k N hk)

/-- **Corollary 5.15:** `F(k,k) = F(k-1,k+1) + 1` for every `k ≥ 2`
(a consequence of the shift identity). -/
theorem avgEntry_diag (k : ℕ) (hk : 2 ≤ k) : avgEntry k k = avgEntry (k - 1) (k + 1) + 1 :=
  avgEntry_diag_eq_of_shift k hk (fun N => shift_identity k N hk)

/-- **Proposition 1.10 (`prop:closed`):** `F(1,1) = 1`. -/
theorem avgEntry_one_one : avgEntry 1 1 = 1 := by
  unfold avgEntry
  rw [tsum_eq_single 0]
  · rw [boxAbsentSum_zero _ _ le_rfl]; simp
  · intro N hN
    have : boxAbsentSum N 1 1 = 0 := by
      unfold boxAbsentSum
      apply Finset.sum_eq_zero
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le,
        Nat.lt_one_iff, Multiset.card_eq_zero, Multiset.filter_eq_nil] at hp
      exfalso
      have hne : p.parts ≠ 0 := by
        intro h; have := p.parts_sum; rw [h] at this; simp at this; omega
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      exact absurd (hp x hx) (Nat.pos_iff_ne_zero.mp (p.parts_pos hx))
    simp [this]

lemma boxAbsentSum_one_two (N : ℕ) : boxAbsentSum N 1 2 = 1 := by
  let q : N.Partition :=
    ⟨Multiset.replicate N 1, fun hx => by rw [Multiset.eq_of_mem_replicate hx]; omega,
      by simp⟩
  unfold boxAbsentSum
  have hq : q ∈ (Finset.univ.filter fun p : N.Partition => ¬ HasBox p 1 2) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le, Nat.lt_one_iff,
      Multiset.card_eq_zero, Multiset.filter_eq_nil, q]
    intro x hx; rw [Multiset.eq_of_mem_replicate hx]; omega
  rw [Finset.sum_eq_single_of_mem q hq]
  · have : q.parts = twoColParts 0 N := by simp [q, twoColParts]
    have h := syt_twoColParts 0 N
    rw [← this] at h
    simp only [numSYT]
    have h2 : (syt q.parts : ℤ) = 1 := by rw [h]; simp [ballot]
    have h3 : syt q.parts = 1 := by exact_mod_cast h2
    rw [h3]; rfl
  · intro b hb hbq
    exfalso; apply hbq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox, not_le, Nat.lt_one_iff,
      Multiset.card_eq_zero, Multiset.filter_eq_nil] at hb
    have hrep : b.parts = Multiset.replicate (Multiset.card b.parts) 1 := by
      apply Multiset.eq_replicate_of_mem
      intro x hx
      have := hb x hx
      have := b.parts_pos hx
      omega
    have hs := b.parts_sum
    rw [hrep] at hs
    simp at hs
    ext1
    simp only [q]
    rw [hrep, hs]

/-- **Proposition 1.10:** `F(1,2) = e`. -/
theorem avgEntry_one_two : avgEntry 1 2 = Real.exp 1 := by
  unfold avgEntry
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp [boxAbsentSum_one_two]

/-- **Proposition 1.10:** `F(1,3) = ∑_N C_N / N!`, `C_N` the Catalan numbers. -/
theorem avgEntry_one_three : avgEntry 1 3 = ∑' N : ℕ, (catalan N : ℝ) / N ! := by
  unfold avgEntry
  simp [boxAbsentSum_twoCol_eq_catalan]

end AvgRS
