module

public import RequestProject.ZLineAlgRelsDef
public import RequestProject.ZLineAlgS0
public import RequestProject.ZLineAlgR3
public import RequestProject.ZLineAlgR1
public import RequestProject.ZLineAlgR6
public import RequestProject.ZLineAlgR7

@[expose] public section

/-!
# The closed system on the line `z + z' = −2`: first integrals, closed forms, and (B4)
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem zrels (Z : ZAlgData t w) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hw0 : w ≠ 0) : ZRels Z := by
  have hS0 := zS0 Z ht1
  have hR3 := zR3 Z ht0 ht1 hw0 hS0
  have hR1 := zR1 Z hR3
  have hR6 := zR6 Z ht0 ht1 hS0 hR3 hR1
  exact ⟨hS0, hR1, hR3, hR6, zR7 Z ht1 hS0 hR3 hR1 hR6⟩
end AvgRS
