module

public import RequestProject.DiagonalArrival
public import RequestProject.ShiftProof
public import RequestProject.UpRule

@[expose] public section

/-!
# Batch 3, items A2′, A2, A3: Theorem 4.1 (`thm:content0`, finite form) for all `N`

`(N+1)! · P(c_{N+1} = 0) = (N+1) (N! − rowEqSum N 0 − rowEqSum N 1)` is proved for all `N`
from `shift_identity` (Theorem 2.1) and the up branching rule `syt_up`; the steps are
`arrival_diag_box` (A2), `boxAbsentSum_one_one` and `telescope_rowEq` (A3).
-/

namespace AvgRS

open Finset
open scoped Nat

/-- The partition of `n` with parts `s` when `s` is a valid list of parts of `n`
(and an arbitrary partition otherwise). -/
def mkPart (n : ℕ) (s : Multiset ℕ) : n.Partition :=
  if h : (∀ x ∈ s, 0 < x) ∧ s.sum = n then ⟨s, fun hx => h.1 _ hx, h.2⟩
  else Nat.Partition.indiscrete n

lemma mkPart_parts {n : ℕ} {s : Multiset ℕ} (h1 : ∀ x ∈ s, 0 < x) (h2 : s.sum = n) :
    (mkPart n s).parts = s := by
  unfold mkPart; rw [dif_pos ⟨h1, h2⟩]

/-- Exchange of the down and up branching sums over partitions:
`∑_{λ ⊢ N+1} ∑_{μ ⋖ λ} Φ λ μ = ∑_{μ ⊢ N} ∑_{λ ⋗ μ} Φ λ μ`. -/
theorem sum_partition_down_eq_up {M : Type*} [AddCommMonoid M] (N : ℕ)
    (Φ : Multiset ℕ → Multiset ℕ → M) :
    ∑ p : (N + 1).Partition, ∑ v ∈ p.parts.toFinset, Φ p.parts (removeBox p.parts v)
      = ∑ q : N.Partition, ∑ ℓ ∈ insSet q.parts, Φ (addBox q.parts ℓ) q.parts := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  have hrp : ∀ (p : (N + 1).Partition) v, v ∈ p.parts →
      (mkPart N (removeBox p.parts v)).parts = removeBox p.parts v := by
    intro p v hv
    have := removeBox_sum_add_one hv (p.parts_pos hv)
    exact mkPart_parts (removeBox_pos_of_pos (fun x hx => p.parts_pos hx) v)
      (by rw [p.parts_sum] at this; omega)
  have hap : ∀ (q : N.Partition) ℓ, ℓ ∈ insSet q.parts →
      (mkPart (N + 1) (addBox q.parts ℓ)).parts = addBox q.parts ℓ := by
    intro q ℓ hℓ
    exact mkPart_parts (addBox_pos (fun x hx => q.parts_pos hx) ℓ)
      (by rw [addBox_sum hℓ, q.parts_sum])
  refine Finset.sum_bij' (fun x _ => ⟨mkPart N (removeBox x.1.parts x.2), x.2 - 1⟩)
    (fun y _ => ⟨mkPart (N + 1) (addBox y.1.parts y.2), y.2 + 1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, v⟩ h
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Multiset.mem_toFinset] at h ⊢
    rw [hrp p v h, insSet_removeBox (p.parts_pos h)]
    exact Finset.mem_insert_self _ _
  · rintro ⟨q, ℓ⟩ h
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at h ⊢
    rw [hap q ℓ h, toFinset_addBox]
    exact Finset.mem_insert_self _ _
  · rintro ⟨p, v⟩ h
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Multiset.mem_toFinset] at h
    have hv0 := p.parts_pos h
    have hl : v - 1 ∈ insSet (mkPart N (removeBox p.parts v)).parts := by
      rw [hrp p v h, insSet_removeBox hv0]; exact Finset.mem_insert_self _ _
    refine Sigma.ext ?_ (heq_of_eq (by simp only; omega))
    apply Nat.Partition.ext
    simp only
    rw [hap _ _ hl, hrp p v h, addBox_removeBox_self (fun x hx => p.parts_pos hx) h]
  · rintro ⟨q, ℓ⟩ h
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at h
    have hv : ℓ + 1 ∈ (mkPart (N + 1) (addBox q.parts ℓ)).parts := by
      rw [hap q ℓ h]; exact Multiset.mem_cons_self _ _
    refine Sigma.ext ?_ (heq_of_eq (by simp only; omega))
    apply Nat.Partition.ext
    simp only
    rw [hrp _ _ hv, hap q ℓ h, removeBox_addBox_self (fun x hx => q.parts_pos hx) h]
  · rintro ⟨p, v⟩ h
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Multiset.mem_toFinset] at h
    simp only
    rw [hrp p v h, addBox_removeBox_self (fun x hx => p.parts_pos hx) h]

/-- Item A2′: `∑_{λ ⊢ N} f_λ² = N!` (from the down and up branching rules by induction on `N`). -/
theorem sum_numSYT_sq (N : ℕ) : ∑ p : N.Partition, numSYT p ^ 2 = N ! := by
  induction N with
  | zero =>
    rw [Fintype.sum_unique]
    simp [numSYT, syt_zero]
  | succ N ih =>
    have hne : ∀ p : (N + 1).Partition, p.parts ≠ 0 := by
      intro p h
      have := p.parts_sum
      rw [h] at this; simp at this
    have e1 : ∀ p : (N + 1).Partition, numSYT p ^ 2
        = ∑ v ∈ p.parts.toFinset, syt p.parts * syt (removeBox p.parts v) := by
      intro p
      rw [← Finset.mul_sum, ← syt_of_ne_zero (hne p), numSYT, sq]
    rw [Finset.sum_congr rfl fun p _ => e1 p,
      sum_partition_down_eq_up N (fun a b => syt a * syt b)]
    have e2 : ∀ q : N.Partition, ∑ ℓ ∈ insSet q.parts, syt (addBox q.parts ℓ) * syt q.parts
        = (N + 1) * numSYT q ^ 2 := by
      intro q
      rw [← Finset.sum_mul, syt_up q.parts (fun x hx => q.parts_pos hx), q.parts_sum, numSYT]
      ring
    rw [Finset.sum_congr rfl fun q _ => e2 q, ← Finset.mul_sum, ih, Nat.factorial_succ]

lemma card_filter_le_pred_eq (s : Multiset ℕ) (k : ℕ) (hk : 1 ≤ k) :
    Multiset.card (s.filter (k - 1 ≤ ·)) = Multiset.card (s.filter (k ≤ ·)) + s.count (k - 1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Multiset.count_cons]
    split_ifs <;> simp_all <;> omega

lemma card_filter_addBox {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) {ℓ : ℕ} (hℓ : ℓ ∈ insSet s)
    {k : ℕ} (hk : 1 ≤ k) :
    Multiset.card ((addBox s ℓ).filter (k ≤ ·))
      = Multiset.card (s.filter (k ≤ ·)) + if ℓ + 1 = k then 1 else 0 := by
  by_cases h : ℓ ∈ s
  · have e : Multiset.card (s.filter (k ≤ ·))
        = (if k ≤ ℓ then 1 else 0) + Multiset.card ((s.erase ℓ).filter (k ≤ ·)) := by
      conv_lhs => rw [← Multiset.cons_erase h]
      rw [Multiset.filter_cons, Multiset.card_add]
      split_ifs <;> simp
    unfold addBox
    rw [Multiset.filter_cons, Multiset.card_add, e]
    split_ifs <;> simp <;> omega
  · have h0 : ℓ = 0 := by
      unfold insSet at hℓ
      rw [Multiset.mem_toFinset, Multiset.mem_cons] at hℓ
      tauto
    subst h0
    rw [addBox_zero hs, Multiset.filter_cons, Multiset.card_add]
    split_ifs <;> simp <;> omega

lemma diagAddable_iff {s : Multiset ℕ} {k : ℕ} (hk : 1 ≤ k) :
    DiagAddable s k ↔ Multiset.card (s.filter (k ≤ ·)) = k - 1 ∧ k - 1 ∈ insSet s := by
  unfold DiagAddable insSet
  rw [card_filter_le_pred_eq s k hk, Multiset.mem_toFinset, Multiset.mem_cons]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · left; omega
    · right; rw [← Multiset.count_pos]; omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · left; omega
    · right; rw [← Multiset.count_pos] at h2; omega

lemma addBoxRow_eq_addBox {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) {k : ℕ} (hk : 1 ≤ k) :
    addBoxRow s k = addBox s (k - 1) := by
  unfold addBoxRow
  split_ifs with h
  · subst h; rw [addBox_zero hs]
  · unfold addBox; congr 1; omega

/-- `M! − boxAbsentSum M i j = ∑_{λ ⊢ M, (i,j) ∈ λ} f_λ²`. -/
lemma factorial_sub_boxAbsentSum (M i j : ℕ) :
    ((M ! : ℤ) - boxAbsentSum M i j)
      = ∑ p : M.Partition, if HasBox p i j then ((numSYT p : ℤ) ^ 2) else 0 := by
  rw [← sum_numSYT_sq, boxAbsentSum, Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

lemma parts_ne_zero_iff {N : ℕ} (p : N.Partition) : p.parts ≠ 0 ↔ N ≠ 0 := by
  constructor
  · intro h hN
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h
    have := p.parts_pos hx
    have := Multiset.le_sum_of_mem hx
    rw [p.parts_sum] at this; omega
  · intro hN h
    have := p.parts_sum
    rw [h] at this; simp at this; omega

/-- Item A2: the number of pairs `(ν, λ)` with `ν ⊢ N`, `λ = ν + (k,k)`, weighted by `f_ν f_λ`,
equals `S_{N+1}(k) − (N+1) S_N(k)` where `S_M(k) = ∑_{μ ⊢ M, (k,k) ∈ μ} f_μ² = M! − boxAbsentSum M k k`. -/
theorem arrival_diag_box (N k : ℕ) (hk : 1 ≤ k) :
    ((∑ p : N.Partition, numSYT p *
        (if DiagAddable p.parts k then syt (addBoxRow p.parts k) else 0) : ℕ) : ℤ)
      = (((N + 1)! : ℤ) - boxAbsentSum (N + 1) k k)
        - (N + 1) * ((N ! : ℤ) - boxAbsentSum N k k) := by
  classical
  set H : Multiset ℕ → Prop := fun a => k ≤ Multiset.card (a.filter (k ≤ ·)) with hH
  set Φ : Multiset ℕ → Multiset ℕ → ℤ := fun a b => if H a then (syt a : ℤ) * syt b else 0
    with hΦ
  have hA : (((N + 1)! : ℤ) - boxAbsentSum (N + 1) k k)
      = ∑ p : (N + 1).Partition, ∑ v ∈ p.parts.toFinset, Φ p.parts (removeBox p.parts v) := by
    rw [factorial_sub_boxAbsentSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hne : p.parts ≠ 0 := (parts_ne_zero_iff p).mpr (by omega)
    simp only [hΦ, HasBox]
    split_ifs with h
    · rw [← Finset.mul_sum, sq, numSYT]
      congr 1
      exact_mod_cast syt_of_ne_zero hne
    · simp
  have hC : ∀ q : N.Partition, ∑ ℓ ∈ insSet q.parts, Φ (addBox q.parts ℓ) q.parts
      = (N + 1) * (if HasBox q k k then ((numSYT q : ℤ) ^ 2) else 0)
        + numSYT q * (if DiagAddable q.parts k then (syt (addBoxRow q.parts k) : ℤ) else 0) := by
    intro q
    have hq : ∀ x ∈ q.parts, 0 < x := fun x hx => q.parts_pos hx
    set c := Multiset.card (q.parts.filter (k ≤ ·)) with hc
    have e : ∀ ℓ ∈ insSet q.parts, Φ (addBox q.parts ℓ) q.parts
        = (if H q.parts then (syt (addBox q.parts ℓ) : ℤ) * syt q.parts else 0)
          + (if c = k - 1 then (if ℓ = k - 1 then (syt (addBox q.parts ℓ) : ℤ) * syt q.parts
              else 0) else 0) := by
      intro ℓ hℓ
      have := card_filter_addBox hq hℓ hk
      simp only [hΦ, hH] at this ⊢
      rw [this, ← hc]
      split_ifs <;> first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
    have e1 : (∑ ℓ ∈ insSet q.parts, if H q.parts then (syt (addBox q.parts ℓ) : ℤ) * syt q.parts
        else 0) = (N + 1) * (if HasBox q k k then ((numSYT q : ℤ) ^ 2) else 0) := by
      simp only [hH, HasBox, numSYT]
      split_ifs
      · rw [← Finset.sum_mul]
        have := syt_up q.parts hq
        rw [q.parts_sum] at this
        rw [sq, ← mul_assoc]
        congr 1
        exact_mod_cast this
      · simp
    rw [e1]
    congr 1
    rw [addBoxRow_eq_addBox hq hk]
    have hiff : DiagAddable q.parts k ↔ c = k - 1 ∧ k - 1 ∈ insSet q.parts := diagAddable_iff hk
    by_cases hck : c = k - 1 <;> by_cases hmem : k - 1 ∈ insSet q.parts <;>
      simp [hck, hmem, hiff, Finset.sum_ite_eq', numSYT, mul_comm]
  rw [hA, sum_partition_down_eq_up N Φ, Finset.sum_congr rfl fun q _ => hC q,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← factorial_sub_boxAbsentSum]
  push_cast
  ring

/-- The `k = 1` values: `boxAbsentSum (N+1) 1 1 = 0` and `boxAbsentSum N 1 1 = if N = 0 then 1 else 0`. -/
lemma boxAbsentSum_one_one (N : ℕ) : boxAbsentSum N 1 1 = if N = 0 then 1 else 0 := by
  split_ifs with hN
  · subst hN; exact boxAbsentSum_zero 1 1 le_rfl
  · unfold boxAbsentSum
    refine Finset.sum_eq_zero fun p hp => ?_
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox] at hp
    apply hp
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero ((parts_ne_zero_iff p).mpr hN)
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, Multiset.mem_filter.mpr ⟨hx, p.parts_pos hx⟩⟩

lemma sum_ite_one_eq_ite_exists (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ i ∈ S, ∀ j ∈ S, P i → P j → i = j) :
    (∑ i ∈ S, if P i then (1 : ℤ) else 0) = if ∃ i ∈ S, P i then 1 else 0 := by
  rw [Finset.sum_boole]
  have hle : (S.filter P).card ≤ 1 := Finset.card_le_one.mpr (by
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact h a ha.1 b hb.1 ha.2 hb.2)
  split_ifs with hex
  · obtain ⟨i, hi, hPi⟩ := hex
    have : 0 < (S.filter P).card := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hPi⟩⟩
    have : (S.filter P).card = 1 := by omega
    simp [this]
  · have : S.filter P = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact fun hx hP => hex ⟨x, hx, hP⟩
    simp [this]

lemma card_filter_anti (s : Multiset ℕ) {j j' : ℕ} (h : j ≤ j') :
    Multiset.card (s.filter (j' ≤ ·)) ≤ Multiset.card (s.filter (j ≤ ·)) :=
  Multiset.card_le_card (Multiset.monotone_filter_right s fun _ hb => le_trans h hb)

/-- `[λ_m ≥ m+2] = [λ_m ≥ m] − [λ_m = m] − [λ_m = m+1]`. -/
lemma hasBox_diag_split (s : Multiset ℕ) (m : ℕ) :
    (if m ≤ Multiset.card (s.filter (m + 2 ≤ ·)) then (1 : ℤ) else 0)
      = (if m ≤ Multiset.card (s.filter (m ≤ ·)) then 1 else 0)
        - (if RowEq s m (m + 0) then 1 else 0) - (if RowEq s m (m + 1) then 1 else 0) := by
  unfold RowEq
  simp only [Nat.add_zero]
  have h2 := card_filter_anti s (show m + 1 ≤ m + 1 + 1 by omega)
  have h3 := card_filter_anti s (show m + 1 + 1 ≤ m + 2 by omega)
  have h4 := card_filter_anti s (show m + 2 ≤ m + 1 + 1 by omega)
  have h5 := card_filter_anti s (show m ≤ m + 1 by omega)
  split_ifs <;> omega

/-- The pointwise telescoping identity behind `telescope_rowEq`. -/
lemma telescope_pointwise {N : ℕ} (p : N.Partition) (M : ℕ) (hM : M ≤ N) :
    ∑ k ∈ Icc 2 (M + 1), ((if HasBox p (k - 1) (k + 1) then (1 : ℤ) else 0)
        - if HasBox p k k then 1 else 0)
      = (if HasBox p 1 1 then 1 else 0) - (if HasBox p (M + 1) (M + 1) then 1 else 0)
        - ∑ i ∈ Icc 1 M, ((if RowEq p.parts i (i + 0) then 1 else 0)
          + (if RowEq p.parts i (i + 1) then 1 else 0)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega), Finset.sum_Icc_succ_top (by omega)]
    have := hasBox_diag_split p.parts (M + 1)
    simp only [HasBox] at this ⊢
    rw [show M + 1 + 1 - 1 = M + 1 by omega, show M + 1 + 1 + 1 = M + 1 + 2 by omega, this]
    ring

lemma telescope_partition {N : ℕ} (p : N.Partition) :
    ∑ k ∈ Icc 2 (N + 1), ((if HasBox p (k - 1) (k + 1) then (1 : ℤ) else 0)
        - if HasBox p k k then 1 else 0)
      = (if N = 0 then 0 else 1) - (if ∃ i ∈ Icc 1 N, RowEq p.parts i (i + 0) then 1 else 0)
        - (if ∃ i ∈ Icc 1 N, RowEq p.parts i (i + 1) then 1 else 0) := by
  rw [telescope_pointwise p N le_rfl, Finset.sum_add_distrib]
  have hN1 : ¬ HasBox p (N + 1) (N + 1) := by
    unfold HasBox
    rw [Multiset.card_eq_zero.mpr]
    · omega
    · rw [Multiset.filter_eq_nil]
      intro x hx
      have := Multiset.le_sum_of_mem hx
      rw [p.parts_sum] at this; omega
  have h11 : HasBox p 1 1 ↔ N ≠ 0 := by
    rw [← parts_ne_zero_iff p]
    unfold HasBox
    constructor
    · intro h h0; rw [h0] at h; simp at h
    · intro h
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h
      exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, Multiset.mem_filter.mpr ⟨hx, p.parts_pos hx⟩⟩
  have huniq : ∀ e, ∀ i ∈ Icc 1 N, ∀ j ∈ Icc 1 N, RowEq p.parts i (i + e) →
      RowEq p.parts j (j + e) → i = j := by
    intro e i _ j _ hi hj
    unfold RowEq at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := card_filter_anti p.parts (show i + e + 1 ≤ j + e by omega)
      omega
    · have := card_filter_anti p.parts (show j + e + 1 ≤ i + e by omega)
      omega
  rw [sum_ite_one_eq_ite_exists _ _ (huniq 0), sum_ite_one_eq_ite_exists _ _ (huniq 1),
    if_neg hN1]
  by_cases hN : N = 0
  · simp [hN, h11]
  · simp [hN, h11]
    ring

/-- Item A3, telescoping step: for `N ≥ 0`,
`∑_{k=2}^{N+1} (boxAbsentSum N k k − boxAbsentSum N (k−1) (k+1)) = [N ≥ 1] N! − rowEqSum N 0 − rowEqSum N 1`. -/
theorem telescope_rowEq (N : ℕ) :
    (∑ k ∈ Icc 2 (N + 1), ((boxAbsentSum N k k : ℤ) - boxAbsentSum N (k - 1) (k + 1)))
      = (if N = 0 then 0 else (N ! : ℤ)) - rowEqSum N 0 - rowEqSum N 1 := by
  have e : ∀ k, (boxAbsentSum N k k : ℤ) - boxAbsentSum N (k - 1) (k + 1)
      = ∑ p : N.Partition, (numSYT p : ℤ) ^ 2 * ((if HasBox p (k - 1) (k + 1) then 1 else 0)
          - if HasBox p k k then 1 else 0) := by
    intro k
    have h1 := factorial_sub_boxAbsentSum N k k
    have h2 := factorial_sub_boxAbsentSum N (k - 1) (k + 1)
    rw [show (boxAbsentSum N k k : ℤ) - boxAbsentSum N (k - 1) (k + 1)
      = ((N ! : ℤ) - boxAbsentSum N (k - 1) (k + 1)) - ((N ! : ℤ) - boxAbsentSum N k k) by ring,
      h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_comm]
  simp_rw [← Finset.mul_sum, telescope_partition]
  have hf : (if N = 0 then 0 else (N ! : ℤ))
      = ∑ p : N.Partition, (numSYT p : ℤ) ^ 2 * (if N = 0 then 0 else 1) := by
    split_ifs
    · simp
    · simp only [mul_one]; exact_mod_cast (sum_numSYT_sq N).symm
  rw [hf]
  simp only [rowEqSum, Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> ring

/-- **Theorem 4.1 (finite form), all `N`**: `(N+1)! P(c_{N+1} = 0) = (N+1)(N! − rowEqSum N 0 − rowEqSum N 1)`. -/
theorem content0_all (N : ℕ) :
    (diagArrival N : ℤ) = (N + 1) * ((N ! : ℤ) - rowEqSum N 0 - rowEqSum N 1) := by
  have hswap : diagArrival N = ∑ i ∈ Icc 1 (N + 1), ∑ p : N.Partition,
      numSYT p * (if DiagAddable p.parts i then syt (addBoxRow p.parts i) else 0) := by
    unfold diagArrival
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap, Nat.cast_sum, Finset.sum_congr rfl (fun i hi => arrival_diag_box N i (mem_Icc.1 hi).1),
    Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons,
    show Ioc 1 (N + 1) = Icc 2 (N + 1) from rfl]
  have hk : ∀ k ∈ Icc 2 (N + 1),
      (((N + 1)! : ℤ) - boxAbsentSum (N + 1) k k) - (N + 1) * ((N ! : ℤ) - boxAbsentSum N k k)
        = (N + 1) * ((boxAbsentSum N k k : ℤ) - boxAbsentSum N (k - 1) (k + 1)) := by
    intro k hk
    rw [shift_identity k N (mem_Icc.1 hk).1, Nat.factorial_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl hk, ← Finset.mul_sum, telescope_rowEq, boxAbsentSum_one_one,
    boxAbsentSum_one_one, Nat.factorial_succ]
  by_cases hN : N = 0
  · subst hN; simp
  · simp only [hN, if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    push_cast
    ring

end AvgRS
