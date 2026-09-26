module

public import RequestProject.AverageTableau

@[expose] public section

/-!
# A verified fast evaluation of `boxAbsentSum`

We enumerate partitions as weakly decreasing lists and tabulate `f_λ` level by level
(each value obtained from the previous level through the branching rule), and prove that
the resulting list computation agrees with `boxAbsentSum`.
-/

namespace AvgRS

open Finset

/-- All partitions of `n` with largest part `≤ m`, as weakly decreasing lists. -/
def genParts : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, m => (List.range (min (n + 1) m)).flatMap
      (fun i => (genParts (n - i) (i + 1)).map (fun l => (i + 1) :: l))
termination_by n => n
decreasing_by omega

/-- A weakly decreasing list of positive integers `≤ m` summing to `n`. -/
def IsPartList (n m : ℕ) (l : List ℕ) : Prop :=
  l.Pairwise (· ≥ ·) ∧ (∀ x ∈ l, 0 < x ∧ x ≤ m) ∧ l.sum = n

lemma mem_genParts_iff (n m : ℕ) (l : List ℕ) : l ∈ genParts n m ↔ IsPartList n m l := by
  induction n using Nat.strong_induction_on generalizing m l with
  | _ n ih =>
    rcases n with _ | n
    · rw [genParts]
      constructor
      · intro h; simp at h; subst h; simp [IsPartList]
      · rintro ⟨_, hpos, hsum⟩
        simp only [List.mem_singleton]
        rcases l with _ | ⟨a, t⟩
        · rfl
        · have := (hpos a (by simp)).1; simp at hsum; omega
    · rw [genParts]
      simp only [List.mem_flatMap, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨i, hi, t, ht, rfl⟩
        rw [ih (n - i) (by omega)] at ht
        obtain ⟨hs, hpos, hsum⟩ := ht
        refine ⟨?_, ?_, ?_⟩
        · refine List.Pairwise.cons (fun b hb => (hpos b hb).2) hs
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · have := hpos x hx; omega
        · simp [hsum]; omega
      · rintro ⟨hs, hpos, hsum⟩
        rcases l with _ | ⟨a, t⟩
        · simp at hsum
        · have ha := hpos a (by simp)
          simp only [List.sum_cons] at hsum
          refine ⟨a - 1, by omega, t, ?_, by congr 1; omega⟩
          rw [ih (n - (a - 1)) (by omega)]
          refine ⟨(List.pairwise_cons.mp hs).2, fun x hx => ?_, by omega⟩
          have h1 := hpos x (List.mem_cons_of_mem a hx)
          have h2 := (List.pairwise_cons.mp hs).1 x hx
          omega

lemma nodup_genParts (n m : ℕ) : (genParts n m).Nodup := by
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    rcases n with _ | n
    · rw [genParts]; simp
    · rw [genParts]
      rw [List.nodup_flatMap]
      refine ⟨fun i _ => (ih (n - i) (by omega) (i + 1)).map (fun a b h => by simpa using h), ?_⟩
      refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
      intro i j _ _ hij
      show List.Disjoint _ _
      rw [List.disjoint_left]
      intro x hx hx'
      simp only [List.mem_map] at hx hx'
      obtain ⟨t, _, rfl⟩ := hx
      obtain ⟨t', _, h⟩ := hx'
      simp at h
      omega

/-- Sorting a multiset into a weakly decreasing list. -/
def toKey (s : Multiset ℕ) : List ℕ := s.sort (· ≥ ·)

lemma toKey_coe {l : List ℕ} (h : l.Pairwise (· ≥ ·)) : toKey (l : Multiset ℕ) = l := by
  unfold toKey
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ h

lemma coe_toKey (s : Multiset ℕ) : ((toKey s : List ℕ) : Multiset ℕ) = s := Multiset.sort_eq _ _

lemma isPartList_toKey {n : ℕ} {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) (hs : s.sum = n) :
    IsPartList n n (toKey s) := by
  refine ⟨Multiset.pairwise_sort _ _, fun x hx => ?_, ?_⟩
  · rw [toKey, Multiset.mem_sort] at hx
    exact ⟨hpos x hx, hs ▸ Multiset.le_sum_of_mem hx⟩
  · rw [← Multiset.sum_coe, coe_toKey, hs]

/-- Table of `(λ, f_λ)` for all partitions `λ ⊢ n`, each value computed from the previous
level by the branching rule. -/
def sytTable : ℕ → List (List ℕ × ℕ)
  | 0 => [([], 1)]
  | n + 1 =>
    let t := sytTable n
    (genParts (n + 1) (n + 1)).map fun l =>
      (l, ∑ v ∈ (l : Multiset ℕ).toFinset, (t.lookup (toKey (removeBox l v))).getD 0)

lemma lookup_map_self {L : List (List ℕ)} {l : List ℕ} (f : List ℕ → ℕ) (hl : l ∈ L) :
    (L.map fun x => (x, f x)).lookup l = some (f l) := by
  induction L with
  | nil => simp at hl
  | cons a L ih =>
    simp only [List.map_cons, List.lookup_cons]
    by_cases h : l = a
    · subst h; simp
    · rw [List.mem_cons] at hl
      have : (l == a) = false := by simpa using h
      rw [this]
      exact ih (hl.resolve_left h)

theorem lookup_sytTable (n : ℕ) (l : List ℕ) (hl : IsPartList n n l) :
    (sytTable n).lookup l = some (syt l) := by
  induction n generalizing l with
  | zero =>
    obtain ⟨_, hpos, hsum⟩ := hl
    have : l = [] := by
      rcases l with _ | ⟨a, t⟩
      · rfl
      · have := (hpos a (by simp)).1; simp at hsum; omega
    subst this
    simp [sytTable, syt_zero]
  | succ n ih =>
    rw [sytTable]
    rw [lookup_map_self _ ((mem_genParts_iff _ _ _).mpr hl)]
    congr 1
    have hne : (l : Multiset ℕ) ≠ 0 := by
      intro h
      have := hl.2.2
      rw [← Multiset.sum_coe, h] at this
      simp at this
    rw [syt_of_ne_zero hne]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Multiset.mem_toFinset] at hv
    have hpos : ∀ x ∈ (l : Multiset ℕ), 0 < x := fun x hx => (hl.2.1 x hx).1
    have hsum : (removeBox (l : Multiset ℕ) v).sum = n := by
      have h1 := sum_removeBox hv (hpos v hv)
      have h2 : (l : Multiset ℕ).sum = n + 1 := by rw [Multiset.sum_coe]; exact hl.2.2
      omega
    rw [ih _ (isPartList_toKey (mem_removeBox_pos hpos v) hsum), coe_toKey]
    rfl

/-- `f_λ` read off from the table. -/
lemma numSYT_eq_lookup {N : ℕ} (p : N.Partition) :
    numSYT p = ((sytTable N).lookup (toKey p.parts)).getD 0 := by
  rw [lookup_sytTable N _ (isPartList_toKey (fun x hx => p.parts_pos hx) p.parts_sum), coe_toKey]
  rfl

/-- The list-based fast evaluation of `boxAbsentSum`. -/
def boxAbsentSumFast (N i j : ℕ) : ℕ :=
  let t := sytTable N
  (((genParts N N).filter fun l : List ℕ =>
      ¬ i ≤ Multiset.card (Multiset.filter (j ≤ ·) (l : Multiset ℕ))).map
    fun l : List ℕ => (t.lookup l).getD 0 ^ 2).sum

theorem boxAbsentSum_eq_fast (N i j : ℕ) : boxAbsentSum N i j = boxAbsentSumFast N i j := by
  unfold boxAbsentSum boxAbsentSumFast
  rw [← List.sum_toFinset _ ((nodup_genParts N N).filter _)]
  refine Finset.sum_bij' (fun p _ => toKey p.parts)
    (fun l hl => ⟨(l : Multiset ℕ), fun {x} hx => by
        have := (List.mem_toFinset.mp hl)
        exact (((mem_genParts_iff _ _ _).mp (List.mem_of_mem_filter this)).2.1 x hx).1,
      by
        have := (List.mem_toFinset.mp hl)
        rw [Multiset.sum_coe]
        exact ((mem_genParts_iff _ _ _).mp (List.mem_of_mem_filter this)).2.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox] at hp
    rw [List.mem_toFinset, List.mem_filter, mem_genParts_iff, coe_toKey]
    exact ⟨isPartList_toKey (fun x hx => p.parts_pos hx) p.parts_sum, by simpa using hp⟩
  · intro l hl
    have := List.mem_filter.mp (List.mem_toFinset.mp hl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasBox]
    simpa using this.2
  · intro p hp
    ext1
    simp [coe_toKey]
  · intro l hl
    have := List.mem_filter.mp (List.mem_toFinset.mp hl)
    exact toKey_coe ((mem_genParts_iff _ _ _).mp this.1).1
  · intro p hp
    rw [numSYT_eq_lookup]

/-! ### Generic fast evaluation -/

lemma keys_sytTable (n : ℕ) : (sytTable n).map Prod.fst = genParts n n := by
  cases n with
  | zero => rw [sytTable, genParts]; rfl
  | succ n => rw [sytTable]; simp [List.map_map, Function.comp_def]

lemma mem_keys_of_lookup {L : List (List ℕ × ℕ)} {key : List ℕ} {v : ℕ}
    (h : L.lookup key = some v) : key ∈ L.map Prod.fst := by
  induction L with
  | nil => simp at h
  | cons a t ih =>
    obtain ⟨k, b⟩ := a
    by_cases hk : key = k
    · simp [hk]
    · have : (key == k) = false := by simpa using hk
      rw [List.lookup_cons, this] at h
      exact List.mem_cons_of_mem _ (ih h)

lemma lookup_sytTable_of_eq_some {n : ℕ} {key : List ℕ} {v : ℕ}
    (h : (sytTable n).lookup key = some v) : v = syt key := by
  have hmem := mem_keys_of_lookup h
  rw [keys_sytTable, mem_genParts_iff] at hmem
  rw [lookup_sytTable n key hmem] at h
  exact (Option.some.inj h).symm

/-- `f_λ` for a list of row lengths, read from a table when possible. -/
def sytFrom (t : List (List ℕ × ℕ)) (key : List ℕ) : ℕ :=
  match t.lookup key with
  | some v => v
  | none => syt key

theorem sytFrom_sytTable (n : ℕ) (key : List ℕ) : sytFrom (sytTable n) key = syt key := by
  unfold sytFrom
  split
  · exact lookup_sytTable_of_eq_some ‹_›
  · rfl

/-- Sums over the partitions of `N` as sums over `genParts N N`. -/
theorem sum_partition_eq_genParts (N : ℕ) (g : Multiset ℕ → ℕ) :
    ∑ p : N.Partition, g p.parts = ((genParts N N).map fun l : List ℕ => g (l : Multiset ℕ)).sum := by
  rw [← List.sum_toFinset _ (nodup_genParts N N)]
  refine Finset.sum_bij' (fun p _ => toKey p.parts)
    (fun l hl => ⟨(l : Multiset ℕ), fun {x} hx =>
        (((mem_genParts_iff _ _ _).mp (List.mem_toFinset.mp hl)).2.1 x hx).1,
      by rw [Multiset.sum_coe]; exact ((mem_genParts_iff _ _ _).mp (List.mem_toFinset.mp hl)).2.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro p _
    rw [List.mem_toFinset, mem_genParts_iff]
    exact isPartList_toKey (fun x hx => p.parts_pos hx) p.parts_sum
  · intro l _; exact Finset.mem_univ _
  · intro p _; ext1; simp [coe_toKey]
  · intro l hl; exact toKey_coe ((mem_genParts_iff _ _ _).mp (List.mem_toFinset.mp hl)).1
  · intro p _; rw [coe_toKey]

end AvgRS
