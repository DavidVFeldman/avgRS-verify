module

public import Mathlib

@[expose] public section

/-!
# `X`-adic limits of formal power series

A sequence `f : ℕ → K⟦X⟧` converges `X`-adically to `L` if for every `m`, eventually
`X ^ m ∣ f n - L`.  This is the notion of limit used to pass from finite truncations
of the hook matrix to the formal quantities of Section 5.
-/

namespace AvgRS.Formal

open PowerSeries

variable {K : Type*} [CommRing K]

/-- `X`-adic convergence of a sequence of formal power series. -/
def IsLim (f : ℕ → K⟦X⟧) (L : K⟦X⟧) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, (X : K⟦X⟧) ^ m ∣ f n - L

namespace IsLim

variable {f g : ℕ → K⟦X⟧} {L M : K⟦X⟧}

lemma const (L : K⟦X⟧) : IsLim (fun _ => L) L := fun _ => ⟨0, fun _ _ => by simp⟩

lemma add (hf : IsLim f L) (hg : IsLim g M) : IsLim (fun n => f n + g n) (L + M) := by
  intro m
  obtain ⟨N₁, h₁⟩ := hf m
  obtain ⟨N₂, h₂⟩ := hg m
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have := dvd_add (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))
  convert this using 1; ring

lemma neg (hf : IsLim f L) : IsLim (fun n => -f n) (-L) := by
  intro m
  obtain ⟨N, h⟩ := hf m
  exact ⟨N, fun n hn => by
    have := (h n hn).neg_right; convert this using 1; ring⟩

lemma sub (hf : IsLim f L) (hg : IsLim g M) : IsLim (fun n => f n - g n) (L - M) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma mul (hf : IsLim f L) (hg : IsLim g M) : IsLim (fun n => f n * g n) (L * M) := by
  intro m
  obtain ⟨N₁, h₁⟩ := hf m
  obtain ⟨N₂, h₂⟩ := hg m
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have := dvd_add (dvd_mul_of_dvd_left (h₁ n (le_of_max_le_left hn)) (g n))
    (dvd_mul_of_dvd_right (h₂ n (le_of_max_le_right hn)) L)
  convert this using 1; ring

lemma const_mul (c : K⟦X⟧) (hf : IsLim f L) : IsLim (fun n => c * f n) (c * L) :=
  (const c).mul hf

lemma pow (hf : IsLim f L) (k : ℕ) : IsLim (fun n => f n ^ k) (L ^ k) := by
  induction k with
  | zero => simpa using const (1 : K⟦X⟧)
  | succ k ih => simpa [pow_succ] using ih.mul hf

lemma X_pow_dvd_derivative_of_dvd {m : ℕ} {h : K⟦X⟧} (hd : (X : K⟦X⟧) ^ (m + 1) ∣ h) :
    (X : K⟦X⟧) ^ m ∣ d⁄dX K h := by
  obtain ⟨u, rfl⟩ := hd
  refine ⟨((m : K⟦X⟧) + 1) * u + X * d⁄dX K u, ?_⟩
  rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  push_cast
  ring

lemma deriv (hf : IsLim f L) : IsLim (fun n => d⁄dX K (f n)) (d⁄dX K L) := by
  intro m
  obtain ⟨N, h⟩ := hf (m + 1)
  exact ⟨N, fun n hn => by
    rw [← map_sub]; exact X_pow_dvd_derivative_of_dvd (h n hn)⟩

lemma unique (hf : IsLim f L) (hg : IsLim f M) : L = M := by
  ext i
  obtain ⟨N₁, h₁⟩ := hf (i + 1)
  obtain ⟨N₂, h₂⟩ := hg (i + 1)
  have := dvd_sub (h₂ (max N₁ N₂) (le_max_right _ _)) (h₁ (max N₁ N₂) (le_max_left _ _))
  rw [show f (max N₁ N₂) - M - (f (max N₁ N₂) - L) = L - M by ring, X_pow_dvd_iff] at this
  have := this i (Nat.lt_succ_self i)
  simpa [sub_eq_zero] using this

/-- If `X ^ n ∣ f n` for all `n` and `f → L`, then `L = 0`. -/
lemma eq_zero_of_dvd (hf : IsLim f L) (hd : ∀ n, (X : K⟦X⟧) ^ n ∣ f n) : L = 0 := by
  refine hf.unique ?_
  intro m
  exact ⟨m, fun n hn => by simpa using (pow_dvd_pow _ hn).trans (hd n)⟩

/-- An `X`-adically Cauchy sequence (`X ^ n ∣ f (n+1) - f n`) converges. -/
lemma of_cauchy (hf : ∀ n, (X : K⟦X⟧) ^ n ∣ f (n + 1) - f n) :
    IsLim f (PowerSeries.mk fun i => coeff i (f (i + 1))) := by
  have key : ∀ n k, (X : K⟦X⟧) ^ n ∣ f (n + k) - f n := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      have := (pow_dvd_pow (X : K⟦X⟧) (Nat.le_add_right n k)).trans (hf (n + k))
      have := dvd_add this ih
      convert this using 1
      rw [← add_assoc]; ring
  intro m
  refine ⟨m, fun n hn => ?_⟩
  rw [X_pow_dvd_iff]
  intro i hi
  rw [map_sub, coeff_mk, sub_eq_zero]
  have h1 := key (i + 1) (n - (i + 1))
  rw [Nat.add_sub_cancel' (by omega), X_pow_dvd_iff] at h1
  have := h1 i (Nat.lt_succ_self i)
  rwa [map_sub, sub_eq_zero] at this

end IsLim

end AvgRS.Formal
