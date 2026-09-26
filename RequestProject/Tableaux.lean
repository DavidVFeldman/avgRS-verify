module

public import Mathlib

@[expose] public section

namespace AvgRS

def removeBox (s : Multiset ℕ) (v : ℕ) : Multiset ℕ :=
  if v ≤ 1 then s.erase v else (v - 1) ::ₘ s.erase v

lemma removeBox_lt {s : Multiset ℕ} {v : ℕ} (hv : v ∈ s) :
    (removeBox s v).sum + Multiset.card (removeBox s v) < s.sum + Multiset.card s := by
  have h1 := Multiset.sum_erase hv
  have h2 := Multiset.card_erase_add_one hv
  unfold removeBox
  split_ifs with h
  · omega
  · simp; omega

def syt (s : Multiset ℕ) : ℕ :=
  if s = 0 then 1 else ∑ v ∈ s.toFinset.attach, syt (removeBox s v.1)
termination_by s.sum + Multiset.card s
decreasing_by exact removeBox_lt (Multiset.mem_toFinset.mp v.2)

theorem syt_zero : syt 0 = 1 := by rw [syt]; simp

theorem syt_of_ne_zero {s : Multiset ℕ} (hs : s ≠ 0) :
    syt s = ∑ v ∈ s.toFinset, syt (removeBox s v) := by
  rw [syt, if_neg hs]
  exact Finset.sum_attach s.toFinset (fun v => syt (removeBox s v))

def hookParts (a b : ℕ) : Multiset ℕ := (a + 1) ::ₘ Multiset.replicate b 1

theorem syt_hookParts (a b : ℕ) : syt (hookParts a b) = (a + b).choose b := by
  induction h : a + b generalizing a b with
  | zero =>
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rw [syt_of_ne_zero (by simp [hookParts])]
    simp [hookParts, removeBox, syt_zero]
  | succ n ih =>
    rw [syt_of_ne_zero (by simp [hookParts])]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [show n = b by omega] at ih
      have ht : (hookParts 0 (b + 1)).toFinset = {1} := by
        ext x
        simp only [hookParts, Multiset.mem_toFinset, Multiset.mem_cons, Multiset.mem_replicate,
          Finset.mem_singleton]
        omega
      rw [ht, Finset.sum_singleton]
      have : removeBox (hookParts 0 (b + 1)) 1 = hookParts 0 b := by
        simp [removeBox, hookParts, Multiset.replicate_succ]
      rw [this, ih 0 b (by omega), show n = b by omega]
      simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [show n = a by omega] at ih
      have : hookParts (a + 1) 0 = {a + 2} := by simp [hookParts]
      rw [this]
      simp only [Multiset.toFinset_singleton, Finset.sum_singleton]
      have : removeBox {a + 2} (a + 2) = hookParts a 0 := by
        simp [removeBox, hookParts]
      rw [this, ih a 0 (by omega), show n = a by omega]
      simp
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have ht : (hookParts (a + 1) (b + 1)).toFinset = {a + 2, 1} := by
        ext x
        simp only [hookParts, Multiset.mem_toFinset, Multiset.mem_cons, Multiset.mem_replicate,
          Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [ht, Finset.sum_pair (by omega)]
      have e1 : removeBox (hookParts (a + 1) (b + 1)) (a + 2) = hookParts a (b + 1) := by
        simp [removeBox, hookParts]
      have e2 : removeBox (hookParts (a + 1) (b + 1)) 1 = hookParts (a + 1) b := by
        simp only [removeBox, hookParts, le_refl, if_true, Multiset.replicate_succ]
        simp [Multiset.erase_cons_tail]
      rw [e1, e2, ih a (b + 1) (by omega), ih (a + 1) b (by omega)]
      have : n = a + b + 1 := by omega
      subst this
      rw [Nat.choose_succ_succ (a + b + 1) b, add_comm]


/-- ballot number `C(n,j) - C(n,j-1)` (with `C(n,-1) = 0`) -/
def ballot (n j : ℕ) : ℤ := (n.choose j : ℤ) - if j = 0 then 0 else (n.choose (j - 1) : ℤ)

def twoColParts (j m : ℕ) : Multiset ℕ := Multiset.replicate j 2 + Multiset.replicate m 1

lemma ballot_succ_zero (j : ℕ) : ballot (2 * j + 2) (j + 1) = ballot (2 * j + 1) j := by
  unfold ballot
  have h1 : (2 * j + 2).choose (j + 1) = (2 * j + 1).choose j + (2 * j + 1).choose (j + 1) :=
    Nat.choose_succ_succ _ _
  have h2 := Nat.choose_symm_half j
  rcases j with _ | j
  · simp
  · have h3 : (2 * (j + 1) + 2).choose (j + 1) = (2 * (j + 1) + 1).choose j
        + (2 * (j + 1) + 1).choose (j + 1) := Nat.choose_succ_succ _ _
    simp only [add_eq_zero, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
    push_cast [h1, h2, h3]
    ring

lemma ballot_succ_succ (j m : ℕ) :
    ballot (2 * j + m + 3) (j + 1) = ballot (2 * j + m + 2) (j + 1) + ballot (2 * j + m + 2) j := by
  unfold ballot
  have h1 : (2 * j + m + 3).choose (j + 1) = (2 * j + m + 2).choose j
      + (2 * j + m + 2).choose (j + 1) := Nat.choose_succ_succ _ _
  rcases j with _ | j
  · simp; ring
  · have h3 : (2 * (j + 1) + m + 3).choose (j + 1) = (2 * (j + 1) + m + 2).choose j
        + (2 * (j + 1) + m + 2).choose (j + 1) := Nat.choose_succ_succ _ _
    simp only [add_eq_zero, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
    push_cast [h1, h3]
    ring

theorem syt_twoColParts (j m : ℕ) : (syt (twoColParts j m) : ℤ) = ballot (2 * j + m) j := by
  induction h : 2 * j + m generalizing j m with
  | zero =>
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ m = 0 := by omega
    simp [twoColParts, syt_zero, ballot]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have : twoColParts 0 (m + 1) = hookParts 0 m := by
        simp [twoColParts, hookParts, Multiset.replicate_succ]
      rw [this, syt_hookParts]
      simp [ballot]
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [syt_of_ne_zero (by simp [twoColParts])]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have ht : (twoColParts (j + 1) 0).toFinset = {2} := by
        ext x
        simp only [twoColParts, Multiset.mem_toFinset, Multiset.mem_add, Multiset.mem_replicate,
          Finset.mem_singleton]
        omega
      rw [ht, Finset.sum_singleton]
      have e : removeBox (twoColParts (j + 1) 0) 2 = twoColParts j 1 := by
        simp [removeBox, twoColParts, Multiset.replicate_succ]
        rw [add_comm, Multiset.singleton_add]
      rw [e, ih j 1 (by omega)]
      obtain rfl : n = 2 * j + 1 := by omega
      exact (ballot_succ_zero j).symm
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have ht : (twoColParts (j + 1) (m + 1)).toFinset = {2, 1} := by
        ext x
        simp only [twoColParts, Multiset.mem_toFinset, Multiset.mem_add, Multiset.mem_replicate,
          Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [ht, Finset.sum_pair (by omega)]
      have e1 : removeBox (twoColParts (j + 1) (m + 1)) 2 = twoColParts j (m + 2) := by
        simp [removeBox, twoColParts, Multiset.replicate_succ]
      have e2 : removeBox (twoColParts (j + 1) (m + 1)) 1 = twoColParts (j + 1) m := by
        simp [removeBox, twoColParts, Multiset.replicate_succ]
      push_cast
      rw [e1, e2, ih j (m + 2) (by omega), ih (j + 1) m (by omega)]
      obtain rfl : n = 2 * j + m + 2 := by omega
      rw [show 2 * j + m + 2 + 1 = 2 * j + m + 3 by ring, ballot_succ_succ]
      ring


open Finset in
lemma sum_choose_mul_choose_succ (N : ℕ) :
    ∑ i ∈ range (N + 1), N.choose i * N.choose (i + 1) = (2 * N).choose (N + 1) := by
  rw [two_mul, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ' (fun x => N.choose x * N.choose (N + 1 - x))]
  simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero, Nat.choose_succ_self, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.mp hi
  rw [show N + 1 - (i + 1) = N - i by omega, Nat.choose_symm (by omega), mul_comm]

lemma ballot_reflect (N j : ℕ) (hj : j ≤ N + 1) : ballot N (N + 1 - j) = - ballot N j := by
  unfold ballot
  rcases Nat.eq_zero_or_pos j with rfl | h0
  · simp
  rcases Nat.lt_or_ge j (N + 1) with h1 | h1
  · rw [if_neg (by omega), if_neg (by omega), show N + 1 - j = N - (j - 1) by omega,
      Nat.choose_symm (by omega), show N - (j - 1) - 1 = N - j by omega, Nat.choose_symm (by omega)]
    ring
  · obtain rfl : j = N + 1 := by omega
    simp

open Finset in
lemma sum_range_ballot_sq_full (N : ℕ) :
    ∑ j ∈ range (N + 2), ballot N j ^ 2
      = 2 * ((2 * N).choose N : ℤ) - 2 * ((2 * N).choose (N + 1) : ℤ) := by
  rw [Finset.sum_range_succ']
  have h1 := Nat.sum_range_choose_sq N
  have h2 := sum_choose_mul_choose_succ N
  have h3 : ∑ i ∈ range (N + 1), (N.choose (i + 1) : ℤ) ^ 2
      = ∑ i ∈ range (N + 1), (N.choose i : ℤ) ^ 2 - 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => (N.choose i : ℤ) ^ 2)]
    simp
  have e : ∀ i ∈ range (N + 1), ballot N (i + 1) ^ 2 = (N.choose (i + 1) : ℤ) ^ 2
      + (N.choose i : ℤ) ^ 2 - 2 * ((N.choose i * N.choose (i + 1) : ℕ) : ℤ) := by
    intro i _
    simp [ballot]; ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, h3,
    ← Finset.mul_sum, ← Nat.cast_sum, h2]
  have h1' : ∑ i ∈ range (N + 1), (N.choose i : ℤ) ^ 2 = ((2 * N).choose N : ℤ) := by
    exact_mod_cast h1
  rw [h1']
  simp [ballot]
  ring

open Finset in
lemma sum_range_ballot_sq_half (N : ℕ) :
    2 * ∑ j ∈ range (N / 2 + 1), ballot N j ^ 2 = ∑ j ∈ range (N + 2), ballot N j ^ 2 := by
  obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
  · rw [show 2 * M / 2 + 1 = M + 1 by omega, show 2 * M + 2 = (M + 1) + (M + 1) by ring,
      Finset.sum_range_add (fun j => ballot (2 * M) j ^ 2) (M + 1) (M + 1), two_mul]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx := Finset.mem_range.mp hx
    rw [show M + 1 + x = 2 * M + 1 - (M + 1 - 1 - x) by omega, ballot_reflect _ _ (by omega),
      neg_sq]
  · rw [show (2 * M + 1) / 2 + 1 = M + 1 by omega, show 2 * M + 1 + 2 = (M + 1) + (M + 2) by ring,
      Finset.sum_range_add (fun j => ballot (2 * M + 1) j ^ 2) (M + 1) (M + 2), two_mul,
      Finset.sum_range_succ' (fun k => ballot (2 * M + 1) (M + 1 + k) ^ 2)]
    have hz : ballot (2 * M + 1) (M + 1 + 0) = 0 := by
      simp [ballot, Nat.choose_symm_half]
    rw [hz]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx := Finset.mem_range.mp hx
    rw [show M + 1 + (x + 1) = 2 * M + 1 + 1 - (M + 1 - 1 - x) by omega,
      ballot_reflect _ _ (by omega), neg_sq]

lemma sum_range_ballot_sq (N : ℕ) :
    ((N + 1 : ℕ) : ℤ) * ∑ j ∈ Finset.range (N / 2 + 1), ballot N j ^ 2 = ((2 * N).choose N : ℤ) := by
  have h := sum_range_ballot_sq_half N
  rw [sum_range_ballot_sq_full] at h
  have h4 := Nat.choose_succ_right_eq (2 * N) N
  rw [show 2 * N - N = N by omega] at h4
  have h4' : ((2 * N).choose (N + 1) : ℤ) * (N + 1) = ((2 * N).choose N : ℤ) * N := by
    exact_mod_cast h4
  have h5 : 2 * (((N : ℤ) + 1) * ∑ j ∈ Finset.range (N / 2 + 1), ballot N j ^ 2
      - ((2 * N).choose N : ℤ)) = 0 := by
    linear_combination ((N : ℤ) + 1) * h - 2 * h4'
  push_cast
  linarith

end AvgRS
