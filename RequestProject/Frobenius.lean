module

public import RequestProject.DurfeeLink

@[expose] public section

/-!
# Frobenius coordinates of partitions

Column lengths `col λ j = #{i : λ_i > j}`, row lengths, arms `a_i = λ_i - i - 1` and legs
`b_j = λ'_j - j - 1` (all `0`-indexed) of the Durfee square, and the bijection between
partitions of `N` with Durfee square `k` and pairs of strictly decreasing sequences
`a_0 > ⋯ > a_{k-1} ≥ 0`, `b_0 > ⋯ > b_{k-1} ≥ 0` with `∑ a + ∑ b + k = N`.
-/

namespace AvgRS

open Finset

lemma lt_card_filter_iff {n j : ℕ} (Q : ℕ → Prop) [DecidablePred Q]
    (hmono : ∀ i j, j ≤ i → Q i → Q j) (hn : ∀ i, Q i → i < n) :
    j < ((range n).filter Q).card ↔ Q j := by
  have := card_filter_lt_iff Q hmono hn (k := j + 1) (by omega)
  simp only [Nat.add_sub_cancel] at this
  constructor
  · intro h; by_contra hq; have := this.2 hq; omega
  · intro h; by_contra hc; exact (this.1 (by omega)) h

lemma eq_of_forall_lt_iff {a b : ℕ} (h : ∀ j, j < a ↔ j < b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd ((h a).2 hab) (lt_irrefl a)
  · exact hab
  · exact absurd ((h b).1 hab) (lt_irrefl b)

lemma card_filter_range_lt {n a : ℕ} (h : a ≤ n) :
    ((range n).filter fun j => j < a).card = a := by
  have : (range n).filter (fun j => j < a) = range a := by
    ext j; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/-- The length of the `j`-th column (`0`-indexed): `#{i : λ_i > j}`. -/
def col {n : ℕ} (p : n.Partition) (j : ℕ) : ℕ := Multiset.card (p.parts.filter (j < ·))

/-- The length of the `i`-th row (`0`-indexed). -/
def row {n : ℕ} (p : n.Partition) (i : ℕ) : ℕ := ((range n).filter fun j => i < col p j).card

/-- The arm length `a_i = λ_i - i - 1` (`0`-indexed). -/
def arm {n : ℕ} (p : n.Partition) (i : ℕ) : ℕ := row p i - i - 1

/-- The leg length `b_j = λ'_j - j - 1` (`0`-indexed). -/
def leg {n : ℕ} (p : n.Partition) (j : ℕ) : ℕ := col p j - j - 1

section PartitionFacts

variable {n : ℕ} (p : n.Partition)

lemma col_anti {j j' : ℕ} (h : j ≤ j') : col p j' ≤ col p j :=
  Multiset.card_le_card (Multiset.monotone_filter_right _ fun x hx => by omega)

lemma le_of_mem_parts {x : ℕ} (hx : x ∈ p.parts) : x ≤ n := by
  rw [← p.parts_sum]; exact Multiset.le_sum_of_mem hx

lemma col_eq_zero {j : ℕ} (hj : n ≤ j) : col p j = 0 := by
  unfold col
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx; have := le_of_mem_parts p hx; omega

lemma hasBox_iff {i j : ℕ} : HasBox p (i + 1) (j + 1) ↔ i < col p j := by
  unfold HasBox col
  rw [Multiset.filter_congr (q := (j < ·)) fun x _ => by omega]
  omega

lemma sum_card_filter_lt {s : Multiset ℕ} (hs : ∀ x ∈ s, x ≤ n) :
    ∑ j ∈ range n, Multiset.card (s.filter (j < ·)) = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Multiset.sum_cons, sum_add_distrib]
    rw [ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)]
    congr 1
    conv_rhs => rw [← card_filter_range_lt (hs a (Multiset.mem_cons_self a s))]
    rw [card_filter]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp

lemma sum_col : ∑ j ∈ range n, col p j = n := by
  unfold col; rw [sum_card_filter_lt fun x hx => le_of_mem_parts p hx, p.parts_sum]

lemma card_filter_eq_col_sub {s : Multiset ℕ} {x : ℕ} :
    Multiset.card (s.filter (x = ·)) + Multiset.card (s.filter (x < ·))
      = Multiset.card (s.filter (x ≤ ·)) := by
  have := Multiset.filter_add_not (fun y => x < y) (s.filter (x ≤ ·))
  rw [Multiset.filter_filter, Multiset.filter_filter] at this
  rw [← this, Multiset.card_add, add_comm]
  congr 2
  · exact Multiset.filter_congr fun y _ => by omega
  · exact Multiset.filter_congr fun y _ => by omega

lemma partition_ext_col {q : n.Partition} (h : ∀ j, col p j = col q j) : p = q := by
  apply Nat.Partition.ext
  ext x
  rw [Multiset.count_eq_card_filter_eq, Multiset.count_eq_card_filter_eq]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Multiset.card_eq_zero.2 (Multiset.filter_eq_nil.2 fun y hy h => by
        have := p.parts_pos hy; omega),
      Multiset.card_eq_zero.2 (Multiset.filter_eq_nil.2 fun y hy h => by
        have := q.parts_pos hy; omega)]
  · have e : ∀ r : n.Partition, Multiset.card (r.parts.filter (x = ·))
        = col r (x - 1) - col r x := by
      intro r
      have := card_filter_eq_col_sub (s := r.parts) (x := x)
      have h2 : r.parts.filter (x ≤ ·) = r.parts.filter (x - 1 < ·) :=
        Multiset.filter_congr fun y _ => by omega
      unfold col; rw [h2] at this; omega
    rw [e, e, h, h]

lemma lt_row_iff {i j : ℕ} : j < row p i ↔ i < col p j :=
  lt_card_filter_iff _ (fun a b hab h => lt_of_lt_of_le h (col_anti p hab))
    (fun a h => by by_contra hc; rw [col_eq_zero p (by omega)] at h; omega)

lemma row_anti {i i' : ℕ} (h : i ≤ i') : row p i' ≤ row p i :=
  card_le_card (monotone_filter_right _ fun j _ hj => by omega)

lemma row_le : row p i ≤ n := by
  unfold row; exact (card_filter_le _ _).trans (card_range n).le

lemma durfee_eq : durfee p = ((range n).filter fun i => i < col p i).card := by
  unfold durfee
  exact congrArg card (filter_congr fun i _ => hasBox_iff p)

lemma lt_durfee_iff {i : ℕ} : i < durfee p ↔ i < col p i := by
  rw [durfee_eq]
  exact lt_card_filter_iff _ (fun a b hab h => lt_of_lt_of_le (lt_of_le_of_lt hab h) (col_anti p hab))
    (fun a h => by by_contra hc; rw [col_eq_zero p (by omega)] at h; omega)

lemma numN2_eq : numN2 p = ((range (durfee p)).filter fun i => 2 ≤ arm p i).card := by
  unfold numN2
  have : (range n).filter (fun i => HasBox p (i + 1) (i + 3))
      = (range (durfee p)).filter fun i => 2 ≤ arm p i := by
    ext i
    simp only [mem_filter, mem_range, hasBox_iff, arm]
    constructor
    · rintro ⟨hi, h⟩
      have h1 : i < col p i := lt_of_lt_of_le h (col_anti p (by omega))
      have h2 := (lt_row_iff p).2 h
      exact ⟨(lt_durfee_iff p).2 h1, by omega⟩
    · rintro ⟨hi, h⟩
      have := row_le p (i := i)
      exact ⟨by omega, (lt_row_iff p).1 (by omega)⟩
  rw [this]

end PartitionFacts

/-- The partition of `n` with prescribed (antitone) column lengths `c`. -/
def ofCols (n : ℕ) (c : ℕ → ℕ) (hanti : Antitone c) (hz : ∀ j, n ≤ j → c j = 0)
    (hs : ∑ j ∈ range n, c j = n) : n.Partition where
  parts := (range (c 0)).val.map fun i => ((range n).filter (i < c ·)).card
  parts_pos := by
    intro x hx
    simp only [Multiset.mem_map, mem_val, mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    apply card_pos.2
    refine ⟨0, ?_⟩
    simp only [mem_filter, mem_range]
    refine ⟨?_, hi⟩
    by_contra h; rw [hz 0 (by omega)] at hi; omega
  parts_sum := by
    change ∑ i ∈ range (c 0), ((range n).filter (i < c ·)).card = n
    simp_rw [card_filter]
    rw [sum_comm]
    conv_rhs => rw [← hs]
    refine sum_congr rfl fun j _ => ?_
    rw [← card_filter, card_filter_range_lt (hanti (Nat.zero_le j))]

lemma col_ofCols (n : ℕ) (c : ℕ → ℕ) (hanti : Antitone c) (hz : ∀ j, n ≤ j → c j = 0)
    (hs : ∑ j ∈ range n, c j = n) (j : ℕ) : col (ofCols n c hanti hz hs) j = c j := by
  unfold col ofCols
  simp only [Multiset.filter_map, Multiset.card_map]
  change (filter (fun i => j < ((range n).filter (i < c ·)).card) (range (c 0))).card = c j
  rw [filter_congr (q := fun i => i < c j) fun i _ =>
    lt_card_filter_iff (fun j' => i < c j') (fun a b hab h => lt_of_lt_of_le h (hanti hab))
      (fun a h => by by_contra hc; simp only [hz a (by omega)] at h; omega)]
  exact card_filter_range_lt (hanti (Nat.zero_le j))

/-- `α` is strictly decreasing on `{0, …, k-1}`. -/
def SAnti (k : ℕ) (α : ℕ → ℕ) : Prop := ∀ i i', i < i' → i' < k → α i' < α i

section FrobCols

variable {k N : ℕ} {α β : ℕ → ℕ}

lemma SAnti.add_le (h : SAnti k α) {i i' : ℕ} (hii : i ≤ i') (hk : i' < k) :
    α i' + i' ≤ α i + i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hii
  induction d with
  | zero => simp
  | succ d ih =>
    have := h (i + d) (i + (d + 1)) (by omega) hk
    have := ih (by omega) (by omega)
    omega

lemma SAnti.ge (h : SAnti k α) {i : ℕ} (hi : i < k) : k ≤ α i + i + 1 := by
  have := h.add_le (i := i) (i' := k - 1) (by omega) (by omega)
  omega

lemma SAnti.le_sum (h : SAnti k α) {i : ℕ} (hi : i < k) :
    α i + i + 1 ≤ ∑ j ∈ range k, α j + k := by
  have h1 := h.add_le (i := 0) (Nat.zero_le i) hi
  have h2 : α 0 ≤ ∑ j ∈ range k, α j :=
    single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))
  omega

/-- The column lengths of the partition with Frobenius coordinates `(α | β)` (decreasing). -/
def cOf (k : ℕ) (α β : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j < k then β j + j + 1 else ((range k).filter fun i => j < α i + i + 1).card

lemma cOf_congr {α' β' : ℕ → ℕ} (hα : ∀ i < k, α i = α' i) (hβ : ∀ i < k, β i = β' i) :
    cOf k α β = cOf k α' β' := by
  funext j
  unfold cOf
  split_ifs with hj
  · rw [hβ j hj]
  · exact congrArg card (filter_congr fun i hi => by rw [hα i (mem_range.1 hi)])

lemma cOf_le_k {j : ℕ} (hj : k ≤ j) : cOf k α β j ≤ k := by
  unfold cOf; rw [if_neg (by omega)]
  exact (card_filter_le _ _).trans (card_range k).le

lemma cOf_anti (hβ : SAnti k β) : Antitone (cOf k α β) := by
  intro j j' hjj
  by_cases hj' : j' < k
  · unfold cOf; rw [if_pos hj', if_pos (by omega)]
    have := hβ.add_le hjj hj'; omega
  · by_cases hj : j < k
    · refine (cOf_le_k (by omega)).trans ?_
      unfold cOf; rw [if_pos hj]; have := hβ.ge hj; omega
    · unfold cOf; rw [if_neg hj, if_neg hj']
      exact card_le_card (monotone_filter_right _ fun i _ h => by omega)

lemma cOf_eq_zero (hb : ∀ i < k, α i + i + 1 ≤ N) (hkN : k ≤ N) {j : ℕ} (hj : N ≤ j) :
    cOf k α β j = 0 := by
  unfold cOf; rw [if_neg (by omega), card_eq_zero, filter_eq_empty_iff]
  intro i hi; have := hb i (mem_range.1 hi); omega

lemma lt_cOf_iff (hα : SAnti k α) (hβ : SAnti k β) {i j : ℕ} (hi : i < k) :
    i < cOf k α β j ↔ j < α i + i + 1 := by
  unfold cOf
  by_cases hj : j < k
  · rw [if_pos hj]; have := hβ.ge hj; have := hα.ge hi; omega
  · rw [if_neg hj, filter_congr (q := fun i' => i' < k ∧ j < α i' + i' + 1)
      fun i' hi' => by simp [mem_range.1 hi']]
    rw [lt_card_filter_iff (fun i' => i' < k ∧ j < α i' + i' + 1)
      (fun a b hab h => ⟨by omega, by have := hα.add_le hab h.1; omega⟩) (fun a h => h.1)]
    simp [hi]

lemma sum_cOf (hα : SAnti k α) (hb : ∀ i < k, α i + i + 1 ≤ N) (hkN : k ≤ N) :
    ∑ j ∈ range N, cOf k α β j = ∑ i ∈ range k, α i + ∑ i ∈ range k, β i + k := by
  rw [← sum_range_add_sum_Ico _ hkN]
  have h1 : ∑ j ∈ range k, cOf k α β j = ∑ j ∈ range k, (β j + j + 1) :=
    sum_congr rfl fun j hj => by unfold cOf; rw [if_pos (mem_range.1 hj)]
  have h2 : ∑ j ∈ Ico k N, cOf k α β j = ∑ i ∈ range k, (α i + i + 1 - k) := by
    rw [sum_congr rfl fun j hj => by
      unfold cOf; rw [if_neg (by simp only [mem_Ico] at hj; omega)]]
    simp_rw [card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    rw [← card_filter]
    have : (Ico k N).filter (fun j => j < α i + i + 1) = Ico k (α i + i + 1) := by
      ext j; simp only [mem_filter, mem_Ico]; have := hb i (mem_range.1 hi); omega
    rw [this, Nat.card_Ico]
  rw [h1, h2]
  have h3 : ∑ i ∈ range k, (α i + i + 1 - k) + ∑ i ∈ range k, k
      = ∑ i ∈ range k, (α i + i + 1) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i hi => Nat.sub_add_cancel (hα.ge (mem_range.1 hi))
  have h4 := Finset.sum_range_id_mul_two k
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one] at h3 ⊢
  have h5 : k * (k - 1) + k = k * k := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  omega

/-- Frobenius data of size `N` with `k` hooks: strictly decreasing arms `α` and legs `β`
(on `{0, …, k-1}`) with `∑ α + ∑ β + k = N`. -/
def FrobOK (k N : ℕ) (α β : ℕ → ℕ) : Prop :=
  SAnti k α ∧ SAnti k β ∧ ∑ i ∈ range k, α i + ∑ i ∈ range k, β i + k = N

lemma FrobOK.bound (h : FrobOK k N α β) {i : ℕ} (hi : i < k) : α i + i + 1 ≤ N := by
  have := h.1.le_sum hi; have := h.2.2; omega

lemma FrobOK.k_le (h : FrobOK k N α β) : k ≤ N := by have := h.2.2; omega

/-- The partition with Frobenius coordinates `(α | β)`. -/
def ofFrob (h : FrobOK k N α β) : N.Partition :=
  ofCols N (cOf k α β) (cOf_anti h.2.1) (fun _ hj => cOf_eq_zero (fun _ hi => h.bound hi) h.k_le hj)
    (by rw [sum_cOf h.1 (fun _ hi => h.bound hi) h.k_le]; exact h.2.2)

lemma col_ofFrob (h : FrobOK k N α β) (j : ℕ) : col (ofFrob h) j = cOf k α β j :=
  col_ofCols _ _ _ _ _ j

lemma durfee_ofFrob (h : FrobOK k N α β) : durfee (ofFrob h) = k := by
  refine eq_of_forall_lt_iff fun i => ?_
  rw [lt_durfee_iff, col_ofFrob]
  by_cases hi : i < k
  · simp only [hi, iff_true]; rw [lt_cOf_iff h.1 h.2.1 hi]; have := h.1.ge hi; omega
  · simp only [hi, iff_false, not_lt]; exact (cOf_le_k (by omega)).trans (by omega)

lemma leg_ofFrob (h : FrobOK k N α β) {j : ℕ} (hj : j < k) : leg (ofFrob h) j = β j := by
  unfold leg; rw [col_ofFrob]; unfold cOf; rw [if_pos hj]; omega

lemma arm_ofFrob (h : FrobOK k N α β) {i : ℕ} (hi : i < k) : arm (ofFrob h) i = α i := by
  have : row (ofFrob h) i = α i + i + 1 := eq_of_forall_lt_iff fun j => by
    rw [lt_row_iff, col_ofFrob, lt_cOf_iff h.1 h.2.1 hi]
  unfold arm; omega

end FrobCols

section PartitionFrob

variable {n : ℕ} (p : n.Partition)

lemma col_le_durfee {j : ℕ} (hj : durfee p ≤ j) : col p j ≤ durfee p := by
  by_contra hc
  have h1 := col_anti p hj
  have h2 := (lt_durfee_iff p (i := durfee p)).2 (by omega)
  omega

lemma lt_row_self {i : ℕ} (hi : i < durfee p) : i < row p i := by
  rw [lt_row_iff]; exact (lt_durfee_iff p).1 hi

lemma col_eq_cOf : col p = cOf (durfee p) (arm p) (leg p) := by
  funext j
  unfold cOf
  split_ifs with hj
  · have := (lt_durfee_iff p).1 hj; unfold leg; omega
  · rw [filter_congr (q := fun i => i < col p j) fun i hi => by
      have := lt_row_self p (mem_range.1 hi); unfold arm
      rw [show row p i - i - 1 + i + 1 = row p i by omega, lt_row_iff]]
    rw [card_filter_range_lt (col_le_durfee p (by omega))]

lemma arm_sAnti : SAnti (durfee p) (arm p) := by
  intro i i' hii hi'
  have := row_anti p hii.le
  have := lt_row_self p hi'
  unfold arm; omega

lemma leg_sAnti : SAnti (durfee p) (leg p) := by
  intro j j' hjj hj'
  have := col_anti p hjj.le
  have := (lt_durfee_iff p).1 hj'
  unfold leg; omega

lemma durfee_le : durfee p ≤ n := by
  unfold durfee; exact (card_filter_le _ _).trans (card_range n).le

lemma frobOK_partition : FrobOK (durfee p) n (arm p) (leg p) := by
  refine ⟨arm_sAnti p, leg_sAnti p, ?_⟩
  have := sum_col p
  rw [col_eq_cOf, sum_cOf (arm_sAnti p) (fun i hi => ?_) (durfee_le p)] at this
  · exact this
  · have := lt_row_self p hi; have := row_le p (i := i); unfold arm; omega

lemma ofFrob_partition : ofFrob (frobOK_partition p) = p :=
  partition_ext_col _ fun j => by rw [col_ofFrob, col_eq_cOf]

end PartitionFrob

end AvgRS
