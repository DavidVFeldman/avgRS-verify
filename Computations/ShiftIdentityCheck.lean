module

public import Computations.FastCount
meta import Computations.FastCount

@[expose] public section

/-!
# Computation 2.6 (`comp:main`): finite verification of the shift identity

The fat-hook identity (Proposition 2.2(a)) is checked in exact integer arithmetic, through the
verified fast evaluation `boxAbsentSum_eq_fast`.
-/

namespace AvgRS

lemma shift_identity_fast_check :
    ∀ k ∈ [3, 4, 5], ∀ N < 26,
      boxAbsentSumFast (N + 1) k k = (N + 1) * boxAbsentSumFast N (k - 1) (k + 1) := by
  native_decide

/-- **Computation 2.6 (`comp:main`) (partial range).** The shift identity holds for `3 ≤ k ≤ 5` and all
`N ≤ 25` (for `k = 2` it is proved for all `N`, see `shift_identity_two`). -/
theorem shift_identity_of_small (k N : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 5) (hN : N ≤ 25) :
    boxAbsentSum (N + 1) k k = (N + 1) * boxAbsentSum N (k - 1) (k + 1) := by
  rcases (show k = 2 ∨ k ∈ [3, 4, 5] by simp; omega) with rfl | hk3
  · exact shift_identity_two N
  · rw [boxAbsentSum_eq_fast, boxAbsentSum_eq_fast]
    exact shift_identity_fast_check k hk3 N (by omega)

end AvgRS
