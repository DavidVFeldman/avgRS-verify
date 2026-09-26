module

public import RequestProject.DiagonalArrival
public import Computations.FastCount
meta import Computations.FastCount
meta import RequestProject.DiagonalArrival

@[expose] public section

/-!
# Computation 4.2: the values of `(N+1)! · P(c_{N+1} = 0)` for `N + 1 ≤ 11`

Checked with `native_decide` through a list-based evaluator proved equal to `diagArrival`.
This file is in the separate library `Computations`, off the import path of the theorems of the
paper.  (Theorem 4.1 itself is proved for all `N` as `content0_all`, without computation.)
-/

namespace AvgRS

open Finset
open scoped Nat

/-! Fast versions (list-based evaluation, proved equal to the definitions). -/

def diagArrivalFast (N : ℕ) : ℕ :=
  let t := sytTable N
  let t' := sytTable (N + 1)
  ((genParts N N).map fun l : List ℕ => sytFrom t l *
    ∑ i ∈ Icc 1 (N + 1), if DiagAddable (l : Multiset ℕ) i then
      sytFrom t' (toKey (addBoxRow (l : Multiset ℕ) i)) else 0).sum

def rowEqSumFast (N e : ℕ) : ℕ :=
  let t := sytTable N
  ((genParts N N).map fun l : List ℕ =>
    if ∃ i ∈ Icc 1 N, RowEq (l : Multiset ℕ) i (i + e) then sytFrom t l ^ 2 else 0).sum

lemma diagArrival_eq_fast (N : ℕ) : diagArrival N = diagArrivalFast N := by
  unfold diagArrival diagArrivalFast numSYT
  rw [sum_partition_eq_genParts N (fun s => syt s *
    ∑ i ∈ Icc 1 (N + 1), if DiagAddable s i then syt (addBoxRow s i) else 0)]
  simp only [sytFrom_sytTable, coe_toKey]

lemma rowEqSum_eq_fast (N e : ℕ) : rowEqSum N e = rowEqSumFast N e := by
  unfold rowEqSum rowEqSumFast numSYT
  rw [sum_partition_eq_genParts N (fun s =>
    if ∃ i ∈ Icc 1 N, RowEq s i (i + e) then syt s ^ 2 else 0)]
  simp only [sytFrom_sytTable]

lemma diagArrival_values_fast :
    (List.range 11).map diagArrivalFast =
      [1, 0, 0, 4, 30, 168, 840, 3960, 19782, 150640, 2089296] := by
  native_decide

/-- **Computation 4.2.** The values of `(N+1)! · P(c_{N+1} = 0)` for `N + 1 = 1, …, 11`. -/
theorem diagArrival_values :
    (List.range 11).map diagArrival =
      [1, 0, 0, 4, 30, 168, 840, 3960, 19782, 150640, 2089296] := by
  rw [← diagArrival_values_fast]
  congr 1
  funext N
  exact diagArrival_eq_fast N

end AvgRS
