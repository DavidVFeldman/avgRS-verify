module

public import RequestProject.AverageTableau

@[expose] public section

/-!
# The diagonal arrival probability (Section 4): definitions

`(N+1)! · P(c_{N+1} = 0) = ∑_{ν ⊢ N} f_ν f_{ν + □}`, where `□` is the diagonal box of `ν`
when it is addable, and Theorem 4.1 (`thm:content0`) states
`P(c_{N+1} = 0) = 1 - P_N(∃ i, λ_i = i) - P_N(∃ i, λ_i = i + 1)`.
It is proved for all `N` as `content0_all` (`DiagonalArrivalAllN.lean`).  The values of
`(N+1)! P(c_{N+1}=0)` listed in Computation 4.2 are checked by computation in the separate
library `Computations` (`Computations/DiagonalArrivalCheck.lean`), which is not imported by any
file of `RequestProject`.
-/

namespace AvgRS

open Finset
open scoped Nat

/-- The diagonal box `(i,i)` (`i ≥ 1`) is addable to the partition with parts `s`:
`λ'_i = i - 1` and `λ_i = i - 1`. -/
def DiagAddable (s : Multiset ℕ) (i : ℕ) : Prop :=
  Multiset.card (s.filter (i ≤ ·)) = i - 1 ∧ (i = 1 ∨ i ≤ Multiset.card (s.filter (i - 1 ≤ ·)))

instance (s : Multiset ℕ) (i : ℕ) : Decidable (DiagAddable s i) := by
  unfold DiagAddable; infer_instance

/-- Add a box at the end of a row of length `i - 1`. -/
def addBoxRow (s : Multiset ℕ) (i : ℕ) : Multiset ℕ :=
  if i = 1 then 1 ::ₘ s else i ::ₘ s.erase (i - 1)

/-- `λ_i = j` (for `i, j ≥ 1`). -/
def RowEq (s : Multiset ℕ) (i j : ℕ) : Prop :=
  i ≤ Multiset.card (s.filter (j ≤ ·)) ∧ Multiset.card (s.filter (j + 1 ≤ ·)) < i

instance (s : Multiset ℕ) (i j : ℕ) : Decidable (RowEq s i j) := by
  unfold RowEq; infer_instance

/-- `∑_{ν ⊢ N} f_ν f_{ν + □}` with `□` the diagonal box, i.e. `(N+1)! · P(c_{N+1} = 0)`
where `c_{N+1}` is the content of the `(N+1)`-st box of Plancherel growth. -/
def diagArrival (N : ℕ) : ℕ :=
  ∑ p : N.Partition, numSYT p *
    ∑ i ∈ Icc 1 (N + 1), if DiagAddable p.parts i then syt (addBoxRow p.parts i) else 0

/-- `∑_{λ ⊢ N, ∃ i, λ_i = i + e} f_λ²`. -/
def rowEqSum (N e : ℕ) : ℕ :=
  ∑ p : N.Partition, if ∃ i ∈ Icc 1 N, RowEq p.parts i (i + e) then numSYT p ^ 2 else 0

end AvgRS
