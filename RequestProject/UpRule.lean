module

public import RequestProject.Tableaux

@[expose] public section

/-!
# Batch 3, item A1: the up branching rule for `syt`

`syt` (= f_λ) is defined in `Tableaux.lean` by the down rule `f_λ = ∑_{μ ⋖ λ} f_μ`, with
`removeBox s v` removing the last box of the last row of length `v` (one down-neighbour per
distinct part value `v ∈ s`).  Dually, `addBox s ℓ` adds a box to the first row of length `ℓ`
(one up-neighbour per distinct part value `ℓ ∈ s`, plus `ℓ = 0`: a new row of length `1`).

The up rule `∑_{λ ⋗ ν} f_λ = (|ν| + 1) f_ν` (Tableaux/`syt_up`) is proved from the identity
`DU − UD = I` on Young's lattice (`DU_sub_UD`) by strong induction.
-/

namespace AvgRS

open Finset

/-- Add a box to the first row of length `ℓ` (for `ℓ = 0`: a new row of length `1`). -/
def addBox (s : Multiset ℕ) (ℓ : ℕ) : Multiset ℕ := (ℓ + 1) ::ₘ s.erase ℓ

/-- The set of part values `ℓ` at which a box can be added: the distinct parts and `0`. -/
def insSet (s : Multiset ℕ) : Finset ℕ := (0 ::ₘ s).toFinset

lemma removeBox_pos_of_pos {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) (v : ℕ) :
    ∀ x ∈ removeBox s v, 0 < x := by
  intro x hx
  unfold removeBox at hx
  split_ifs at hx with h
  · exact hpos x (Multiset.mem_of_mem_erase hx)
  · rcases Multiset.mem_cons.mp hx with rfl | hx
    · omega
    · exact hpos x (Multiset.mem_of_mem_erase hx)

lemma removeBox_sum_add_one {s : Multiset ℕ} {v : ℕ} (hv : v ∈ s) (hv0 : 0 < v) :
    (removeBox s v).sum + 1 = s.sum := by
  have h1 := Multiset.sum_erase hv
  unfold removeBox
  split_ifs with h
  · obtain rfl : v = 1 := by omega
    omega
  · simp; omega

lemma addBox_zero {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) : addBox s 0 = 1 ::ₘ s := by
  unfold addBox
  rw [Multiset.erase_of_notMem (fun h => (hs 0 h).false)]

lemma addBox_sum {s : Multiset ℕ} {ℓ : ℕ} (hℓ : ℓ ∈ insSet s) : (addBox s ℓ).sum = s.sum + 1 := by
  unfold addBox
  unfold insSet at hℓ
  rw [Multiset.mem_toFinset, Multiset.mem_cons] at hℓ
  rcases hℓ with rfl | hℓ
  · by_cases h0 : 0 ∈ s
    · have := Multiset.sum_erase h0
      simp; omega
    · rw [Multiset.erase_of_notMem h0]; simp; omega
  · have := Multiset.sum_erase hℓ
    simp; omega

lemma addBox_pos {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) (ℓ : ℕ) : ∀ x ∈ addBox s ℓ, 0 < x := by
  intro x hx
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · omega
  · exact hs x (Multiset.mem_of_mem_erase hx)

lemma removeBox_addBox_self {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) {ℓ : ℕ} (hℓ : ℓ ∈ insSet s) :
    removeBox (addBox s ℓ) (ℓ + 1) = s := by
  unfold insSet at hℓ
  rw [Multiset.mem_toFinset, Multiset.mem_cons] at hℓ
  rcases hℓ with rfl | hℓ
  · rw [addBox_zero hs]; simp [removeBox]
  · have h0 : ℓ ≠ 0 := fun h => by subst h; exact (hs 0 hℓ).false
    unfold removeBox addBox
    rw [if_neg (by omega)]
    simp [Multiset.cons_erase hℓ]

lemma insSet_removeBox {s : Multiset ℕ} {v : ℕ} (hv : 0 < v) :
    insSet (removeBox s v) = insert (v - 1) (0 ::ₘ s.erase v).toFinset := by
  unfold insSet removeBox
  split_ifs with h
  · obtain rfl : v = 1 := by omega
    ext x; simp only [Multiset.mem_toFinset, Finset.mem_insert, Multiset.mem_cons, Nat.sub_self]
    tauto
  · ext x; simp only [Multiset.mem_toFinset, Finset.mem_insert, Multiset.mem_cons]; tauto

lemma addBox_removeBox_self {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) {v : ℕ} (hv : v ∈ s) :
    addBox (removeBox s v) (v - 1) = s := by
  have hv0 := hs v hv
  unfold removeBox addBox
  split_ifs with h
  · obtain rfl : v = 1 := by omega
    rw [Multiset.erase_of_notMem (fun h' => (hs 0 (Multiset.mem_of_mem_erase h')).false)]
    exact Multiset.cons_erase hv
  · rw [Multiset.erase_cons_head, show v - 1 + 1 = v by omega]
    exact Multiset.cons_erase hv

lemma toFinset_addBox (s : Multiset ℕ) (ℓ : ℕ) :
    (addBox s ℓ).toFinset = insert (ℓ + 1) (s.erase ℓ).toFinset := by
  unfold addBox; simp

lemma addBox_removeBox_comm {s : Multiset ℕ} {ℓ v : ℕ} (hne : ℓ + 1 ≠ v) :
    removeBox (addBox s ℓ) v = addBox (removeBox s v) ℓ := by
  unfold addBox removeBox
  split_ifs with h
  · rw [Multiset.erase_cons_tail _ hne, Multiset.erase_comm]
  · rw [Multiset.erase_cons_tail _ hne, Multiset.erase_cons_tail _ (by omega),
      Multiset.erase_comm]
    exact Multiset.cons_swap _ _ _

/-- `DU − UD = I` on Young's lattice, as an identity of sums against an arbitrary function
`F` of partitions: for a multiset `s` of positive parts,
`∑_{ℓ ∈ ins s} ∑_{v ∈ del (addBox s ℓ)} F (removeBox (addBox s ℓ) v)
   = F s + ∑_{v ∈ del s} ∑_{ℓ ∈ ins (removeBox s v)} F (addBox (removeBox s v) ℓ)`,
where `del s = s.toFinset`. -/
theorem DU_sub_UD (s : Multiset ℕ) (hs : ∀ x ∈ s, 0 < x) (F : Multiset ℕ → ℕ) :
    ∑ ℓ ∈ insSet s, ∑ v ∈ (addBox s ℓ).toFinset, F (removeBox (addBox s ℓ) v)
      = F s + ∑ v ∈ s.toFinset, ∑ ℓ ∈ insSet (removeBox s v), F (addBox (removeBox s v) ℓ) := by
  classical
  set G : ℕ → ℕ → ℕ := fun ℓ v => F (addBox (removeBox s v) ℓ) with hG
  have hL : ∀ ℓ ∈ insSet s, ∑ v ∈ (addBox s ℓ).toFinset, F (removeBox (addBox s ℓ) v)
      = F s + ∑ v ∈ ((s.erase ℓ).toFinset).erase (ℓ + 1), G ℓ v := by
    intro ℓ hℓ
    rw [toFinset_addBox, ← Finset.insert_erase (Finset.mem_insert_self _ _),
      Finset.sum_insert (Finset.notMem_erase _ _), Finset.erase_insert_eq_erase,
      removeBox_addBox_self hs hℓ]
    congr 1
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' := Finset.mem_erase.mp hv
    have hvs : v ∈ s := Multiset.mem_of_mem_erase (Multiset.mem_toFinset.mp hv'.2)
    exact congrArg F (addBox_removeBox_comm (Ne.symm hv'.1))
  have hR : ∀ v ∈ s.toFinset, ∑ ℓ ∈ insSet (removeBox s v), F (addBox (removeBox s v) ℓ)
      = F s + ∑ ℓ ∈ ((0 ::ₘ s.erase v).toFinset).erase (v - 1), G ℓ v := by
    intro v hv
    have hvs := Multiset.mem_toFinset.mp hv
    have hv0 := hs v hvs
    rw [insSet_removeBox hv0, ← Finset.insert_erase (Finset.mem_insert_self _ _),
      Finset.sum_insert (Finset.notMem_erase _ _), Finset.erase_insert_eq_erase]
    rw [addBox_removeBox_self hs hvs]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const]
  have hI : insSet s = insert 0 s.toFinset := by
    unfold insSet; simp
  have h0 : 0 ∉ s.toFinset := fun h => (hs 0 (Multiset.mem_toFinset.mp h)).false
  rw [hI, Finset.card_insert_of_notMem h0]
  have hcomm : ∑ ℓ ∈ insert 0 s.toFinset, ∑ v ∈ ((s.erase ℓ).toFinset).erase (ℓ + 1), G ℓ v
      = ∑ v ∈ s.toFinset, ∑ ℓ ∈ ((0 ::ₘ s.erase v).toFinset).erase (v - 1), G ℓ v := by
    apply Finset.sum_comm'
    intro ℓ v
    simp only [Finset.mem_insert, Multiset.mem_toFinset, Finset.mem_erase, Multiset.mem_cons]
    constructor
    · rintro ⟨hℓ, hne, hv⟩
      have hvs : v ∈ s := Multiset.mem_of_mem_erase hv
      have hv0 := hs v hvs
      refine ⟨⟨by omega, ?_⟩, hvs⟩
      rcases hℓ with rfl | hℓ
      · exact Or.inl rfl
      · right
        by_cases hvl : v = ℓ
        · subst hvl; exact hv
        · exact (Multiset.mem_erase_of_ne (Ne.symm hvl)).mpr hℓ
    · rintro ⟨⟨hne, hℓ⟩, hvs⟩
      have hv0 := hs v hvs
      refine ⟨?_, by omega, ?_⟩
      · rcases hℓ with rfl | hℓ
        · exact Or.inl rfl
        · exact Or.inr (Multiset.mem_of_mem_erase hℓ)
      · rcases hℓ with rfl | hℓ
        · rwa [Multiset.erase_of_notMem (fun h => (hs 0 h).false)]
        · by_cases hvl : v = ℓ
          · subst hvl; exact hℓ
          · exact (Multiset.mem_erase_of_ne hvl).mpr hvs
  rw [hcomm, smul_eq_mul, smul_eq_mul]
  ring

/-- **The up branching rule**: `∑_{λ ⋗ ν} f_λ = (|ν| + 1) f_ν`. -/
theorem syt_up (s : Multiset ℕ) (hs : ∀ x ∈ s, 0 < x) :
    ∑ ℓ ∈ insSet s, syt (addBox s ℓ) = (s.sum + 1) * syt s := by
  induction h : s.sum using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  by_cases hs0 : s = 0
  · subst hs0
    simp only [Multiset.sum_zero] at h
    subst h
    have : insSet 0 = {0} := by simp [insSet]
    rw [this, Finset.sum_singleton, addBox_zero (by simp), syt_of_ne_zero (by simp)]
    simp [removeBox, syt_zero]
  have hne : ∀ ℓ, addBox s ℓ ≠ 0 := fun ℓ => Multiset.cons_ne_zero
  rw [Finset.sum_congr rfl fun ℓ _ => syt_of_ne_zero (hne ℓ), DU_sub_UD s hs syt,
    syt_of_ne_zero hs0, Finset.mul_sum]
  have hstep : ∀ v ∈ s.toFinset,
      ∑ ℓ ∈ insSet (removeBox s v), syt (addBox (removeBox s v) ℓ) = n * syt (removeBox s v) := by
    intro v hv
    have hvs := Multiset.mem_toFinset.mp hv
    have hsum := removeBox_sum_add_one hvs (hs v hvs)
    rw [ih (removeBox s v).sum (by omega) (removeBox s v) (removeBox_pos_of_pos hs v) rfl]
    congr 1; omega
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end AvgRS
