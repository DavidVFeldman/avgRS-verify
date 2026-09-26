module

public import RequestProject.ZLineAlgRels
public import RequestProject.ZLineAlgS33
public import RequestProject.ZLineAlgBig
public import RequestProject.ZLineAlgG00
public import RequestProject.ZLineAlgG01
public import RequestProject.ZLineAlgG11
public import RequestProject.ZLineAlgFin

@[expose] public section

/-!
# The identity (B4) for the closed system on the line `z + z' = −2`

From the scalar data `ZAlgData t w` (differential equations, recurrences, first integral R2,
Jacobi and rank-two formulas, initial data), the first integrals S0, R1, R3, R6, R7, the
auxiliary relations (T2), S33, and the closed forms (E0)–(E2), (I4), (G01), (G10), (G11) give the
closed form of `D_Z / D`, and then the differential identity
`D' = 2 r ω ((1 − t) D_Z + (r/2) D_Z')`.
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

/-- **The algebraic core of Conjecture 3.2**: for scalar data on the line `z + z' = −2` with
`t ≠ 0, 1` and `ω ≠ 0, 1`, `D' = 2 r ω ((1 − t) D_Z + (r/2) D_Z')`. -/
theorem zline_alg (Z : ZAlgData t w) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    d⁄dX ℚ Z.D = 2 * X * C w * ((1 - C t) * Z.DZ + (C (1 / 2 : ℚ) * X) * d⁄dX ℚ Z.DZ) := by
  have hrel := zrels Z ht0 ht1 hw0
  have hE0 := zE0 Z ht0 ht1 hw1 hrel
  have hE1 := zE1 Z ht1 hw1 hE0
  have hE2 := zE2 Z ht1 hw1 hE1
  have hS33 := zS33 Z ht0 ht1 hrel
  have hBig := zBig Z ht0 ht1 hrel
  have hC00 := zG00 Z ht1 hw1 hE1
  have hC01 := zG01 Z ht0 ht1 hw0 hw1 hE0 hE1 hE2 hS33
  have hC11 := zG11 Z ht0 ht1 hw0 hw1 hE0 hE1 hE2 hBig
  have hC10 := zG10 Z
  exact zFinal Z ht0 ht1 (zY Z ht0 ht1 hw0 hw1 hC00 hC01 hC11 hC10) (zRfin Z ht0 ht1 hrel)

end AvgRS
